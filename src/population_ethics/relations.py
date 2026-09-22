from __future__ import annotations

import json
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Literal, cast

import z3  # type: ignore[import-untyped]

from population_ethics.domain import ValidationError


@dataclass(frozen=True, slots=True, order=True)
class RelationAtom:
    left: str
    relation: Literal["weak"]
    right: str

    def __post_init__(self) -> None:
        if not self.left or not self.right:
            raise ValidationError("relation endpoints must be non-empty")
        if self.relation != "weak":
            raise ValidationError(f"unsupported relation {self.relation!r}")


@dataclass(frozen=True, slots=True)
class BoolConstant:
    value: bool


@dataclass(frozen=True, slots=True)
class Not:
    operand: Formula


@dataclass(frozen=True, slots=True)
class And:
    operands: tuple[Formula, ...]

    def __post_init__(self) -> None:
        if len(self.operands) < 2:
            raise ValidationError("and requires at least two operands")


@dataclass(frozen=True, slots=True)
class Or:
    operands: tuple[Formula, ...]

    def __post_init__(self) -> None:
        if len(self.operands) < 2:
            raise ValidationError("or requires at least two operands")


@dataclass(frozen=True, slots=True)
class Implies:
    antecedent: Formula
    consequent: Formula


type Formula = RelationAtom | BoolConstant | Not | And | Or | Implies

TRUE = BoolConstant(True)
FALSE = BoolConstant(False)


def weak(left: str, right: str) -> RelationAtom:
    return RelationAtom(left, "weak", right)


def strict(left: str, right: str) -> Formula:
    return conjunction(weak(left, right), Not(weak(right, left)))


def indifferent(left: str, right: str) -> Formula:
    return conjunction(weak(left, right), weak(right, left))


def incomparable(left: str, right: str) -> Formula:
    return conjunction(Not(weak(left, right)), Not(weak(right, left)))


def conjunction(*formulas: Formula) -> Formula:
    flattened: list[Formula] = []
    for formula in formulas:
        if isinstance(formula, BoolConstant):
            if not formula.value:
                return FALSE
            continue
        if isinstance(formula, And):
            flattened.extend(formula.operands)
        else:
            flattened.append(formula)
    unique = _canonical_terms(flattened)
    if not unique:
        return TRUE
    if len(unique) == 1:
        return unique[0]
    return And(unique)


def disjunction(*formulas: Formula) -> Formula:
    flattened: list[Formula] = []
    for formula in formulas:
        if isinstance(formula, BoolConstant):
            if formula.value:
                return TRUE
            continue
        if isinstance(formula, Or):
            flattened.extend(formula.operands)
        else:
            flattened.append(formula)
    unique = _canonical_terms(flattened)
    if not unique:
        return FALSE
    if len(unique) == 1:
        return unique[0]
    return Or(unique)


def _canonical_terms(formulas: list[Formula]) -> tuple[Formula, ...]:
    by_encoding = {formula_json(formula): formula for formula in formulas}
    return tuple(by_encoding[key] for key in sorted(by_encoding))


def evaluate_formula(formula: Formula, assignment: Mapping[RelationAtom, bool]) -> bool:
    match formula:
        case RelationAtom():
            try:
                value = assignment[formula]
            except KeyError as error:
                raise ValidationError(f"missing assignment for atom {formula!r}") from error
            if not isinstance(value, bool):
                raise ValidationError(f"assignment for {formula!r} must be Boolean")
            return value
        case BoolConstant(value=value):
            return value
        case Not(operand=operand):
            return not evaluate_formula(operand, assignment)
        case And(operands=operands):
            return all(evaluate_formula(operand, assignment) for operand in operands)
        case Or(operands=operands):
            return any(evaluate_formula(operand, assignment) for operand in operands)
        case Implies(antecedent=antecedent, consequent=consequent):
            return not evaluate_formula(antecedent, assignment) or evaluate_formula(
                consequent, assignment
            )


def formula_to_data(formula: Formula) -> dict[str, object]:
    match formula:
        case RelationAtom(left=left, relation=relation, right=right):
            return {"kind": "atom", "left": left, "relation": relation, "right": right}
        case BoolConstant(value=value):
            return {"kind": "constant", "value": value}
        case Not(operand=operand):
            return {"kind": "not", "operand": formula_to_data(operand)}
        case And(operands=operands):
            return {"kind": "and", "operands": [formula_to_data(item) for item in operands]}
        case Or(operands=operands):
            return {"kind": "or", "operands": [formula_to_data(item) for item in operands]}
        case Implies(antecedent=antecedent, consequent=consequent):
            return {
                "kind": "implies",
                "antecedent": formula_to_data(antecedent),
                "consequent": formula_to_data(consequent),
            }


def formula_json(formula: Formula) -> str:
    return json.dumps(formula_to_data(formula), sort_keys=True, separators=(",", ":"))


def formula_from_data(value: object) -> Formula:
    if not isinstance(value, Mapping):
        raise ValidationError("formula must be a table/object")
    kind = value.get("kind")
    allowed: dict[str, set[str]] = {
        "atom": {"kind", "left", "relation", "right"},
        "constant": {"kind", "value"},
        "not": {"kind", "operand"},
        "and": {"kind", "operands"},
        "or": {"kind", "operands"},
        "implies": {"kind", "antecedent", "consequent"},
        "strict": {"kind", "left", "right"},
        "indifferent": {"kind", "left", "right"},
        "incomparable": {"kind", "left", "right"},
    }
    if not isinstance(kind, str) or kind not in allowed:
        raise ValidationError(f"unknown formula kind {kind!r}")
    unknown = set(value) - allowed[kind]
    missing = allowed[kind] - set(value)
    if unknown or missing:
        message = (
            f"formula {kind!r} has unknown keys {sorted(unknown)} "
            f"and missing keys {sorted(missing)}"
        )
        raise ValidationError(message)
    if kind == "atom":
        left, relation, right = value["left"], value["relation"], value["right"]
        if not isinstance(left, str) or not isinstance(right, str) or relation != "weak":
            raise ValidationError("atom requires string endpoints and relation='weak'")
        return weak(left, right)
    if kind == "constant":
        constant = value["value"]
        if not isinstance(constant, bool):
            raise ValidationError("constant formula requires a Boolean value")
        return BoolConstant(constant)
    if kind == "not":
        return Not(formula_from_data(value["operand"]))
    if kind in {"and", "or"}:
        operands = value["operands"]
        if not isinstance(operands, list):
            raise ValidationError(f"{kind} operands must be a list")
        parsed = tuple(formula_from_data(operand) for operand in operands)
        return conjunction(*parsed) if kind == "and" else disjunction(*parsed)
    if kind == "implies":
        return Implies(
            formula_from_data(value["antecedent"]), formula_from_data(value["consequent"])
        )
    left, right = value["left"], value["right"]
    if not isinstance(left, str) or not isinstance(right, str):
        raise ValidationError(f"{kind} requires string endpoints")
    macro = {"strict": strict, "indifferent": indifferent, "incomparable": incomparable}[kind]
    return macro(left, right)


def collect_atoms(formula: Formula) -> frozenset[RelationAtom]:
    match formula:
        case RelationAtom():
            return frozenset((formula,))
        case BoolConstant():
            return frozenset()
        case Not(operand=operand):
            return collect_atoms(operand)
        case And(operands=operands) | Or(operands=operands):
            return frozenset().union(*(collect_atoms(operand) for operand in operands))
        case Implies(antecedent=antecedent, consequent=consequent):
            return collect_atoms(antecedent) | collect_atoms(consequent)


def encode_z3(formula: Formula, atom_map: Mapping[RelationAtom, z3.BoolRef]) -> z3.BoolRef:
    match formula:
        case RelationAtom():
            try:
                return atom_map[formula]
            except KeyError as error:
                raise ValidationError(f"missing Z3 variable for atom {formula!r}") from error
        case BoolConstant(value=value):
            return z3.BoolVal(value)
        case Not(operand=operand):
            return z3.Not(encode_z3(operand, atom_map))
        case And(operands=operands):
            return z3.And(*(encode_z3(operand, atom_map) for operand in operands))
        case Or(operands=operands):
            return z3.Or(*(encode_z3(operand, atom_map) for operand in operands))
        case Implies(antecedent=antecedent, consequent=consequent):
            return z3.Implies(encode_z3(antecedent, atom_map), encode_z3(consequent, atom_map))


def atom_key(atom: RelationAtom) -> str:
    return f"weak:{atom.left}:{atom.right}"


def assignment_to_data(assignment: Mapping[RelationAtom, bool]) -> list[dict[str, object]]:
    return [
        {**formula_to_data(atom), "value": assignment[atom]}
        for atom in sorted(assignment, key=atom_key)
    ]


def assignment_from_data(value: object) -> dict[RelationAtom, bool]:
    if not isinstance(value, list):
        raise ValidationError("relation assignment must be a list")
    assignment: dict[RelationAtom, bool] = {}
    for item in value:
        if not isinstance(item, Mapping):
            raise ValidationError("relation assignment entry must be an object")
        data = dict(item)
        truth = data.pop("value", None)
        if not isinstance(truth, bool):
            raise ValidationError("relation assignment value must be Boolean")
        atom = formula_from_data(data)
        if not isinstance(atom, RelationAtom):
            raise ValidationError("relation assignment entries must be atoms")
        if atom in assignment:
            raise ValidationError(f"duplicate relation assignment for {atom!r}")
        assignment[atom] = truth
    return assignment


def formula_label(formula: Formula) -> str:
    match formula:
        case RelationAtom(left=left, right=right):
            return f"{left}≥{right}"
        case BoolConstant(value=value):
            return "True" if value else "False"
        case Not(operand=operand):
            return f"¬({formula_label(operand)})"
        case And(operands=operands):
            return " ∧ ".join(f"({formula_label(item)})" for item in operands)
        case Or(operands=operands):
            return " ∨ ".join(f"({formula_label(item)})" for item in operands)
        case Implies(antecedent=antecedent, consequent=consequent):
            return f"({formula_label(antecedent)}) → ({formula_label(consequent)})"


def as_formula(value: object) -> Formula:
    return cast(Formula, value)
