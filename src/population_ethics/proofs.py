from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Literal, cast

from population_ethics.domain import ValidationError
from population_ethics.principles import GroundConstraint
from population_ethics.relations import (
    FALSE,
    And,
    Formula,
    Implies,
    Not,
    Or,
    conjunction,
    formula_from_data,
    formula_to_data,
    strict,
    weak,
)

CHECKER_VERSION = "population-ethics.proof-checker/v1"
ProofRule = Literal[
    "premise",
    "hypothesis",
    "conjunction-introduction",
    "conjunction-elimination",
    "implication-introduction",
    "implication-elimination",
    "disjunction-elimination",
    "contradiction",
    "negation-introduction",
    "classical-contradiction-discharge",
]
PROOF_RULES = frozenset(
    {
        "premise",
        "hypothesis",
        "conjunction-introduction",
        "conjunction-elimination",
        "implication-introduction",
        "implication-elimination",
        "disjunction-elimination",
        "contradiction",
        "negation-introduction",
        "classical-contradiction-discharge",
    }
)


@dataclass(frozen=True, slots=True)
class ProofNode:
    id: str
    formula: Formula
    rule: ProofRule
    premises: tuple[str, ...]
    scope: tuple[str, ...]
    discharged_assumptions: tuple[str, ...]
    explanation: str

    def __post_init__(self) -> None:
        if not self.id or not self.explanation:
            raise ValidationError("proof node ID and explanation must be non-empty")
        if len(set(self.premises)) != len(self.premises):
            raise ValidationError(f"proof node {self.id!r} repeats a premise")
        if tuple(sorted(set(self.scope))) != self.scope:
            raise ValidationError(f"proof node {self.id!r} scope must be sorted and unique")
        if tuple(sorted(set(self.discharged_assumptions))) != self.discharged_assumptions:
            raise ValidationError(
                f"proof node {self.id!r} discharged assumptions must be sorted and unique"
            )


@dataclass(frozen=True, slots=True)
class ProofCertificate:
    problem_id: str
    root_node_id: str
    nodes: tuple[ProofNode, ...]


@dataclass(frozen=True, slots=True)
class ProofNodeCheck:
    declared_premises: frozenset[str]
    open_hypotheses: frozenset[str]


@dataclass(frozen=True, slots=True)
class ProofCheckResult:
    checker_version: str
    root_node_id: str
    root_formula: Formula
    declared_premises: tuple[str, ...]
    open_hypotheses: tuple[str, ...]
    nodes: Mapping[str, ProofNodeCheck]


@dataclass(frozen=True, slots=True)
class _State:
    formula: Formula
    declared: frozenset[str]
    open_hypotheses: frozenset[str]


def check_proof(
    certificate: ProofCertificate,
    declared_constraints: Mapping[str, GroundConstraint],
    *,
    expected_problem_id: str | None = None,
    require_contradiction: bool = True,
) -> ProofCheckResult:
    if expected_problem_id is not None and certificate.problem_id != expected_problem_id:
        raise ValidationError(
            f"proof problem_id mismatch: expected {expected_problem_id}, "
            f"found {certificate.problem_id}"
        )
    nodes = {node.id: node for node in certificate.nodes}
    if len(nodes) != len(certificate.nodes):
        raise ValidationError("proof contains duplicate node IDs")
    collisions = set(nodes) & set(declared_constraints)
    if collisions:
        raise ValidationError(f"proof node IDs collide with constraints {sorted(collisions)}")
    if certificate.root_node_id not in nodes:
        raise ValidationError(f"unknown proof root {certificate.root_node_id!r}")
    _reject_cycles(nodes)

    states: dict[str, _State] = {}
    checks: dict[str, ProofNodeCheck] = {}
    for node in certificate.nodes:
        references = [reference for reference in node.premises if reference in nodes]
        forward = [reference for reference in references if reference not in states]
        if forward:
            raise ValidationError(f"proof node {node.id!r} has forward references {forward}")
        unknown = [
            reference
            for reference in node.premises
            if reference not in states and reference not in declared_constraints
        ]
        if unknown:
            raise ValidationError(f"proof node {node.id!r} has unavailable premises {unknown}")
        premise_states = tuple(
            states[reference]
            if reference in states
            else _State(
                declared_constraints[reference].formula,
                frozenset((reference,)),
                frozenset(),
            )
            for reference in node.premises
        )
        state = _check_node(node, premise_states, nodes, states)
        declared = state.declared
        if not declared <= set(declared_constraints):
            raise ValidationError(f"proof node {node.id!r} uses undeclared premises")
        expected_scope = tuple(sorted(state.open_hypotheses))
        if node.scope != expected_scope:
            raise ValidationError(
                f"proof node {node.id!r} declares scope {node.scope!r}, "
                f"but checker computes {expected_scope!r}"
            )
        states[node.id] = state
        checks[node.id] = ProofNodeCheck(declared, state.open_hypotheses)

    root = states[certificate.root_node_id]
    if require_contradiction and root.formula != FALSE:
        raise ValidationError("contradiction certificate root formula must be False")
    if root.open_hypotheses:
        raise ValidationError(f"proof root leaks open hypotheses {sorted(root.open_hypotheses)}")
    if not root.declared:
        raise ValidationError("proof root has no selected declared premises")
    return ProofCheckResult(
        CHECKER_VERSION,
        certificate.root_node_id,
        root.formula,
        tuple(sorted(root.declared)),
        tuple(sorted(root.open_hypotheses)),
        checks,
    )


def _check_node(
    node: ProofNode,
    premises: tuple[_State, ...],
    nodes: Mapping[str, ProofNode],
    states: Mapping[str, _State],
) -> _State:
    declared = frozenset().union(*(premise.declared for premise in premises))
    open_hypotheses = frozenset().union(*(premise.open_hypotheses for premise in premises))
    if node.rule == "premise":
        _require_shape(node, premises=1, discharged=0)
        if node.formula != premises[0].formula:
            raise ValidationError(f"premise node {node.id!r} changes the declared formula")
        return _State(node.formula, declared, open_hypotheses)
    if node.rule == "hypothesis":
        _require_shape(node, premises=0, discharged=0)
        return _State(node.formula, frozenset(), frozenset((node.id,)))
    if node.rule == "conjunction-introduction":
        if len(premises) < 2 or node.discharged_assumptions:
            raise ValidationError(f"node {node.id!r} has malformed conjunction introduction")
        expected = conjunction(*(premise.formula for premise in premises))
        if node.formula != expected:
            raise ValidationError(f"node {node.id!r} states the wrong conjunction")
        return _State(node.formula, declared, open_hypotheses)
    if node.rule == "conjunction-elimination":
        _require_shape(node, premises=1, discharged=0)
        source = premises[0].formula
        if not isinstance(source, And) or node.formula not in source.operands:
            raise ValidationError(f"node {node.id!r} has invalid conjunction elimination")
        return _State(node.formula, declared, open_hypotheses)
    if node.rule == "implication-elimination":
        _require_shape(node, premises=2, discharged=0)
        implication, argument = _implication_and_argument(premises)
        if argument.formula != implication.antecedent:
            raise ValidationError(f"node {node.id!r} applies an implication to the wrong formula")
        if node.formula != implication.consequent:
            raise ValidationError(f"node {node.id!r} states the wrong implication consequence")
        return _State(node.formula, declared, open_hypotheses)
    if node.rule in {"implication-introduction", "negation-introduction"}:
        _require_shape(node, premises=1, discharged=1)
        hypothesis_id = node.discharged_assumptions[0]
        hypothesis = _hypothesis(hypothesis_id, nodes, states, premises[0])
        if node.rule == "implication-introduction":
            discharged_formula: Formula = Implies(hypothesis.formula, premises[0].formula)
        else:
            if premises[0].formula != FALSE:
                raise ValidationError(f"node {node.id!r} negation premise is not a contradiction")
            discharged_formula = Not(hypothesis.formula)
        if node.formula != discharged_formula:
            raise ValidationError(f"node {node.id!r} states the wrong discharged formula")
        return _State(
            node.formula,
            declared,
            open_hypotheses - frozenset((hypothesis_id,)),
        )
    if node.rule == "classical-contradiction-discharge":
        _require_shape(node, premises=1, discharged=1)
        if premises[0].formula != FALSE:
            raise ValidationError(f"node {node.id!r} does not discharge a contradiction")
        hypothesis_id = node.discharged_assumptions[0]
        hypothesis = _hypothesis(hypothesis_id, nodes, states, premises[0])
        if hypothesis.formula != Not(node.formula):
            raise ValidationError(
                f"node {node.id!r} classical hypothesis is not the negation of its conclusion"
            )
        return _State(
            node.formula,
            declared,
            open_hypotheses - frozenset((hypothesis_id,)),
        )
    if node.rule == "contradiction":
        _require_shape(node, premises=2, discharged=0)
        if node.formula != FALSE or not _complementary(premises[0].formula, premises[1].formula):
            raise ValidationError(f"node {node.id!r} does not combine complementary formulas")
        return _State(FALSE, declared, open_hypotheses)
    if node.rule == "disjunction-elimination":
        if len(premises) < 3:
            raise ValidationError(f"node {node.id!r} lacks disjunction branches")
        disjunction = premises[0]
        if not isinstance(disjunction.formula, Or):
            raise ValidationError(f"node {node.id!r} first premise is not a disjunction")
        branch_states = premises[1:]
        if len(branch_states) != len(disjunction.formula.operands):
            raise ValidationError(f"node {node.id!r} has the wrong number of branches")
        if len(node.discharged_assumptions) != len(branch_states):
            raise ValidationError(f"node {node.id!r} has the wrong discharged branch count")
        unmatched = list(disjunction.formula.operands)
        branch_open: frozenset[str] = frozenset()
        for branch, hypothesis_id in zip(branch_states, node.discharged_assumptions, strict=True):
            hypothesis = _hypothesis(hypothesis_id, nodes, states, branch)
            try:
                unmatched.remove(hypothesis.formula)
            except ValueError as error:
                raise ValidationError(
                    f"node {node.id!r} branch hypothesis is not a disjunct"
                ) from error
            if branch.formula != node.formula:
                raise ValidationError(f"node {node.id!r} branches do not share its conclusion")
            branch_open |= branch.open_hypotheses - frozenset((hypothesis_id,))
        if unmatched:
            raise ValidationError(f"node {node.id!r} does not cover every disjunct")
        return _State(node.formula, declared, disjunction.open_hypotheses | branch_open)
    raise ValidationError(f"unsupported proof rule {node.rule!r}")


def _require_shape(node: ProofNode, *, premises: int, discharged: int) -> None:
    if len(node.premises) != premises or len(node.discharged_assumptions) != discharged:
        raise ValidationError(f"proof node {node.id!r} has the wrong rule shape")


def _hypothesis(
    hypothesis_id: str,
    nodes: Mapping[str, ProofNode],
    states: Mapping[str, _State],
    derivation: _State,
) -> ProofNode:
    hypothesis = nodes.get(hypothesis_id)
    if hypothesis is None or hypothesis.rule != "hypothesis":
        raise ValidationError(f"{hypothesis_id!r} is not a proof hypothesis")
    if hypothesis_id not in states:
        raise ValidationError(f"hypothesis {hypothesis_id!r} is a forward reference")
    if hypothesis_id not in derivation.open_hypotheses:
        raise ValidationError(f"derivation does not depend on hypothesis {hypothesis_id!r}")
    return hypothesis


def _implication_and_argument(premises: tuple[_State, ...]) -> tuple[Implies, _State]:
    if isinstance(premises[0].formula, Implies):
        return premises[0].formula, premises[1]
    if isinstance(premises[1].formula, Implies):
        return premises[1].formula, premises[0]
    raise ValidationError("implication elimination requires an implication")


def _complementary(left: Formula, right: Formula) -> bool:
    return (isinstance(left, Not) and left.operand == right) or (
        isinstance(right, Not) and right.operand == left
    )


def _reject_cycles(nodes: Mapping[str, ProofNode]) -> None:
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node_id: str) -> None:
        if node_id in visiting:
            raise ValidationError(f"proof contains a cycle through {node_id!r}")
        if node_id in visited:
            return
        visiting.add(node_id)
        for reference in nodes[node_id].premises:
            if reference in nodes:
                visit(reference)
        visiting.remove(node_id)
        visited.add(node_id)

    for node_id in nodes:
        visit(node_id)


def proof_node_to_data(node: ProofNode) -> dict[str, object]:
    return {
        "id": node.id,
        "formula": formula_to_data(node.formula),
        "rule": node.rule,
        "premises": list(node.premises),
        "scope": list(node.scope),
        "discharged_assumptions": list(node.discharged_assumptions),
        "explanation": node.explanation,
    }


def proof_certificate_to_data(certificate: ProofCertificate) -> dict[str, object]:
    return {
        "problem_id": certificate.problem_id,
        "root_node_id": certificate.root_node_id,
        "nodes": [proof_node_to_data(node) for node in certificate.nodes],
    }


def proof_certificate_from_data(value: object) -> ProofCertificate:
    if not isinstance(value, Mapping):
        raise ValidationError("proof certificate must be an object")
    if set(value) != {"problem_id", "root_node_id", "nodes"}:
        raise ValidationError("proof certificate has unknown or missing keys")
    raw_nodes = value["nodes"]
    if not isinstance(raw_nodes, list):
        raise ValidationError("proof certificate nodes must be a list")
    nodes = tuple(_proof_node_from_data(item, index) for index, item in enumerate(raw_nodes))
    problem_id = value["problem_id"]
    root = value["root_node_id"]
    if not isinstance(problem_id, str) or not problem_id or not isinstance(root, str) or not root:
        raise ValidationError("proof certificate IDs must be non-empty strings")
    return ProofCertificate(problem_id, root, nodes)


def _proof_node_from_data(value: object, index: int) -> ProofNode:
    if not isinstance(value, Mapping):
        raise ValidationError(f"proof node {index} must be an object")
    expected = {
        "id",
        "formula",
        "rule",
        "premises",
        "scope",
        "discharged_assumptions",
        "explanation",
    }
    if set(value) != expected:
        raise ValidationError(f"proof node {index} has unknown or missing keys")
    rule = value["rule"]
    if not isinstance(rule, str) or rule not in PROOF_RULES:
        raise ValidationError(f"proof node {index} has unsupported rule {rule!r}")
    return ProofNode(
        _required_string(value["id"], where=f"proof node {index}.id"),
        formula_from_data(value["formula"]),
        cast(ProofRule, rule),
        _string_tuple(value["premises"], where=f"proof node {index}.premises"),
        _string_tuple(value["scope"], where=f"proof node {index}.scope"),
        _string_tuple(
            value["discharged_assumptions"],
            where=f"proof node {index}.discharged_assumptions",
        ),
        _required_string(value["explanation"], where=f"proof node {index}.explanation"),
    )


def _required_string(value: object, *, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValidationError(f"{where} must be a non-empty string")
    return value


def _string_tuple(value: object, *, where: str) -> tuple[str, ...]:
    if not isinstance(value, list) or any(not isinstance(item, str) for item in value):
        raise ValidationError(f"{where} must be a string list")
    return tuple(cast(list[str], value))


def curated_arrhenius_certificate(problem_id: str) -> ProofCertificate:
    nodes: list[ProofNode] = []
    scope_by_id: dict[str, frozenset[str]] = {}

    def add(
        node_id: str,
        formula: Formula,
        rule: ProofRule,
        premises: tuple[str, ...] = (),
        scope: tuple[str, ...] | None = None,
        discharged: tuple[str, ...] = (),
        explanation: str = "Checked Boolean inference.",
    ) -> str:
        if scope is None:
            inherited = frozenset().union(
                *(scope_by_id.get(premise_id, frozenset()) for premise_id in premises)
            )
            checked_scope = inherited - frozenset(discharged)
        else:
            checked_scope = frozenset(scope)
        node = ProofNode(
            node_id,
            formula,
            rule,
            premises,
            tuple(sorted(checked_scope)),
            tuple(sorted(discharged)),
            explanation,
        )
        nodes.append(node)
        scope_by_id[node_id] = checked_scope
        return node_id

    def premise(node_id: str, constraint_id: str, formula: Formula, explanation: str) -> str:
        return add(node_id, formula, "premise", (constraint_id,), explanation=explanation)

    def reverse_from_avoidance(prefix: str, left: str, right: str, avoidance_id: str) -> str:
        complete_formula = Or(tuple(sorted((weak(left, right), weak(right, left)))))
        complete = premise(
            f"{prefix}.completeness",
            f"completeness:{min(left, right)}:{max(left, right)}",
            complete_formula,
            f"Completeness compares {left} and {right}.",
        )
        avoidance = premise(
            f"{prefix}.avoidance",
            avoidance_id,
            Not(strict(left, right)),
            f"The selected avoidance premise rules out {left} strictly above {right}.",
        )
        left_case = add(
            f"{prefix}.left-case", weak(left, right), "hypothesis", scope=(f"{prefix}.left-case",)
        )
        not_reverse = add(
            f"{prefix}.not-reverse",
            Not(weak(right, left)),
            "hypothesis",
            scope=(f"{prefix}.not-reverse",),
        )
        strict_left = add(
            f"{prefix}.strict-left",
            strict(left, right),
            "conjunction-introduction",
            (left_case, not_reverse),
            (left_case, not_reverse),
        )
        contradiction = add(
            f"{prefix}.contradiction",
            FALSE,
            "contradiction",
            (strict_left, avoidance),
            (left_case, not_reverse),
        )
        reverse_in_left_case = add(
            f"{prefix}.reverse-in-left-case",
            weak(right, left),
            "classical-contradiction-discharge",
            (contradiction,),
            (left_case,),
            (not_reverse,),
        )
        reverse_case = add(
            f"{prefix}.reverse-case",
            weak(right, left),
            "hypothesis",
            scope=(f"{prefix}.reverse-case",),
        )
        return add(
            f"{prefix}.result",
            weak(right, left),
            "disjunction-elimination",
            (complete, reverse_in_left_case, reverse_case),
            discharged=(left_case, reverse_case),
            explanation=f"Avoidance plus completeness yields {right} weakly above {left}.",
        )

    def transitive(prefix: str, left: str, middle: str, right: str, first: str, second: str) -> str:
        antecedent = conjunction(weak(left, middle), weak(middle, right))
        transitivity = premise(
            f"{prefix}.law",
            f"transitivity:{left}:{middle}:{right}",
            Implies(antecedent, weak(left, right)),
            "Selected transitivity instance.",
        )
        joined = add(
            f"{prefix}.antecedent",
            antecedent,
            "conjunction-introduction",
            (first, second),
        )
        return add(
            f"{prefix}.result",
            weak(left, right),
            "implication-elimination",
            (transitivity, joined),
        )

    a_over_d = reverse_from_avoidance("A-over-D", "D", "A", "avoid-repugnance:D-not-strict-A")
    d_over_ac = reverse_from_avoidance(
        "D-over-AC", "AC", "D", "avoid-anti-egalitarianism:AC-not-strict-D"
    )
    a_over_ac = transitive("A-over-AC", "A", "D", "AC", a_over_d, d_over_ac)

    not_ab_over_ac = add(
        "AB-over-AC.not",
        Not(weak("AB", "AC")),
        "hypothesis",
        scope=("AB-over-AC.not",),
        explanation="Assume AB is not weakly above AC.",
    )
    complete_ab_ac = premise(
        "AB-over-AC.completeness",
        "completeness:AB:AC",
        Or(tuple(sorted((weak("AB", "AC"), weak("AC", "AB"))))),
        "Completeness compares AB and AC.",
    )
    ab_case = add(
        "AB-over-AC.forward-case",
        weak("AB", "AC"),
        "hypothesis",
        scope=("AB-over-AC.forward-case",),
    )
    ab_case_false = add(
        "AB-over-AC.forward-false",
        FALSE,
        "contradiction",
        (ab_case, not_ab_over_ac),
        (ab_case, not_ab_over_ac),
    )
    ac_case = add(
        "AB-over-AC.reverse-case",
        weak("AC", "AB"),
        "hypothesis",
        scope=("AB-over-AC.reverse-case",),
    )
    not_ac_over_ab = add(
        "AB-over-AC.not-reverse",
        Not(weak("AC", "AB")),
        "hypothesis",
        scope=("AB-over-AC.not-reverse",),
    )
    ac_case_false = add(
        "AB-over-AC.reverse-false",
        FALSE,
        "contradiction",
        (ac_case, not_ac_over_ab),
        (ac_case, not_ac_over_ab),
    )
    both_cases_false = add(
        "AB-over-AC.completeness-false",
        FALSE,
        "disjunction-elimination",
        (complete_ab_ac, ab_case_false, ac_case_false),
        (not_ab_over_ac, not_ac_over_ab),
        (ab_case, ac_case),
    )
    ac_over_ab = add(
        "AB-over-AC.reverse",
        weak("AC", "AB"),
        "classical-contradiction-discharge",
        (both_cases_false,),
        (not_ab_over_ac,),
        (not_ac_over_ab,),
    )
    a_over_ab = transitive("A-over-AB", "A", "AC", "AB", a_over_ac, ac_over_ab)
    ab_over_a_hypothesis = add(
        "AB-over-AC.AB-over-A",
        weak("AB", "A"),
        "hypothesis",
        scope=("AB-over-AC.AB-over-A",),
    )
    ab_over_ac_from_chain = transitive(
        "AB-over-AC.chain",
        "AB",
        "A",
        "AC",
        ab_over_a_hypothesis,
        a_over_ac,
    )
    chain_false = add(
        "AB-over-AC.chain-false",
        FALSE,
        "contradiction",
        (ab_over_ac_from_chain, not_ab_over_ac),
        (ab_over_a_hypothesis, not_ab_over_ac),
    )
    not_ab_over_a = add(
        "AB-over-AC.not-AB-over-A",
        Not(weak("AB", "A")),
        "negation-introduction",
        (chain_false,),
        (not_ab_over_ac,),
        (ab_over_a_hypothesis,),
    )
    a_strict_ab = add(
        "AB-over-AC.A-strict-AB",
        strict("A", "AB"),
        "conjunction-introduction",
        (a_over_ab, not_ab_over_a),
        (not_ab_over_ac,),
    )
    addition = premise(
        "AB-over-AC.addition",
        "addition:A-AB-implies-AB-AC",
        Implies(strict("A", "AB"), weak("AB", "AC")),
        "Selected Addition instance.",
    )
    ab_over_ac_under_assumption = add(
        "AB-over-AC.by-addition",
        weak("AB", "AC"),
        "implication-elimination",
        (addition, a_strict_ab),
        (not_ab_over_ac,),
    )
    reductio_false = add(
        "AB-over-AC.reductio-false",
        FALSE,
        "contradiction",
        (ab_over_ac_under_assumption, not_ab_over_ac),
        (not_ab_over_ac,),
    )
    ab_over_ac = add(
        "AB-over-AC.result",
        weak("AB", "AC"),
        "classical-contradiction-discharge",
        (reductio_false,),
        discharged=(not_ab_over_ac,),
        explanation="Addition closes the reductio, so AB is weakly above AC.",
    )

    g_over_aaf = reverse_from_avoidance(
        "G-over-AAF", "AAF", "G", "avoid-anti-egalitarianism:AAF-not-strict-G"
    )
    aaf_over_aae = reverse_from_avoidance(
        "AAF-over-AAE", "AAE", "AAF", "avoid-sadism:AAE-not-strict-AAF"
    )
    aae_over_ab = premise(
        "AAE-over-AB",
        "minimal-priority:AAE-weak-AB",
        weak("AAE", "AB"),
        "Selected Minimal Non-Extreme Priority witness.",
    )
    g_over_aae = transitive("G-over-AAE", "G", "AAF", "AAE", g_over_aaf, aaf_over_aae)
    g_over_ab = transitive("G-over-AB", "G", "AAE", "AB", g_over_aae, aae_over_ab)
    g_over_ac = transitive("G-over-AC", "G", "AB", "AC", g_over_ab, ab_over_ac)
    dominance = premise(
        "AC-strict-G",
        "dominance:AC-strict-G",
        strict("AC", "G"),
        "Selected Dominance instance.",
    )
    not_g_over_ac = add(
        "not-G-over-AC",
        Not(weak("G", "AC")),
        "conjunction-elimination",
        (dominance,),
    )
    root = add(
        "contradiction",
        FALSE,
        "contradiction",
        (g_over_ac, not_g_over_ac),
        explanation="The derived chain G≥AC contradicts Dominance AC>G.",
    )
    return ProofCertificate(problem_id, root, tuple(nodes))
