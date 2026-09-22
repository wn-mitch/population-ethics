"""Shared helpers for the Arrhenius discovery turn.

Everything here is research-only. Production modules are imported, never modified.
Three decision procedures are provided and deliberately kept independent:

* ``Engine``: Z3 with assumption-only guards (blocking clauses never enter it);
* ``dpll_check``: a small pure-Python DPLL over a Tseitin CNF of the ground formulas;
* ``preorders`` / ``total_preorders``: exhaustive, duplicate-free enumerators of
  reflexive-transitive (and complete) relations as bitmasks.
"""

from __future__ import annotations

import hashlib
import json
import sys
from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import permutations
from pathlib import Path
from typing import Any, Literal, cast

import z3  # type: ignore[import-untyped]

from population_ethics.principles import (
    GroundConstraint,
    compile_completeness,
    compile_reflexivity,
    compile_transitivity,
)
from population_ethics.proofs import ProofCertificate, ProofNode, ProofRule
from population_ethics.relations import (
    FALSE,
    And,
    BoolConstant,
    Formula,
    Implies,
    Not,
    Or,
    RelationAtom,
    conjunction,
    encode_z3,
    evaluate_formula,
    strict,
    weak,
)
from population_ethics.spec import CompatibilitySpec, load_experiment, problem_id_for

ROOT = Path(__file__).resolve().parent.parent
BASELINE_PATH = ROOT / "experiments" / "arrhenius-2000-proof.toml"
RESULTS_DIR = ROOT / "research" / "results"
LEDGER_PATH = ROOT / "research" / "ledger.json"
LEDGER_SCHEMA = "population-ethics.research-ledger/v1"
RESULT_SCHEMA = "population-ethics.research-result/v1"

# The seven populations the substantive baseline formulas mention, in sorted order.
ACTIVE: tuple[str, ...] = ("A", "AAE", "AAF", "AB", "AC", "D", "G")

Decision = Literal["sat", "unsat", "unknown"]


# --------------------------------------------------------------------------- baseline


def load_baseline() -> CompatibilitySpec:
    spec = load_experiment(BASELINE_PATH)
    if not isinstance(spec, CompatibilitySpec):
        raise TypeError("baseline must be a compatibility experiment")
    return spec


def baseline_constraints(spec: CompatibilitySpec) -> dict[str, GroundConstraint]:
    return {c.id: c for group in spec.groups for c in group.constraints}


def substantive_constraints(spec: CompatibilitySpec) -> tuple[GroundConstraint, ...]:
    """The hand-grounded principle instances (every candidate group except completeness)."""
    groups = {group.id: group for group in spec.groups}
    return tuple(
        constraint
        for group_id in spec.candidate_group_ids
        if group_id != "completeness"
        for constraint in groups[group_id].constraints
    )


def background(relata: Iterable[str]) -> dict[str, tuple[GroundConstraint, ...]]:
    names = tuple(relata)
    return {
        "reflexivity": compile_reflexivity(names),
        "transitivity": compile_transitivity(names),
        "completeness": compile_completeness(names),
    }


def pair_id(left: str, right: str) -> str:
    return f"completeness:{min(left, right)}:{max(left, right)}"


def pairs(relata: Sequence[str]) -> tuple[tuple[str, str], ...]:
    names = tuple(sorted(relata))
    return tuple((a, b) for i, a in enumerate(names) for b in names[i + 1 :])


def ground(
    identifier: str, principle_id: str, formula: Formula, formalization_id: str, explanation: str
) -> GroundConstraint:
    endpoints = sorted({e for atom in _atoms(formula) for e in (atom.left, atom.right)})
    return GroundConstraint(
        identifier,
        principle_id,
        formula,
        tuple(endpoints) or ("none",),
        None,
        formalization_id,
        explanation,
    )


def _atoms(formula: Formula) -> set[RelationAtom]:
    match formula:
        case RelationAtom():
            return {formula}
        case BoolConstant():
            return set()
        case Not(operand=operand):
            return _atoms(operand)
        case And(operands=ops) | Or(operands=ops):
            return set().union(*(_atoms(op) for op in ops))
        case Implies(antecedent=a, consequent=c):
            return _atoms(a) | _atoms(c)


def incomparable_pair(left: str, right: str) -> Formula:
    return conjunction(Not(weak(left, right)), Not(weak(right, left)))


# --------------------------------------------------------------------------- Z3 engine


@dataclass
class Check:
    decision: Decision
    assignment: dict[RelationAtom, bool] | None
    core: tuple[str, ...]
    reason: str | None


class Engine:
    """Assumption-only Z3 wrapper over the full weak-atom space of ``relata``.

    ``hard`` formulas are always asserted. ``soft`` formulas are guarded and enabled per query
    by assumption literals. ``extra`` Z3 terms are added inside a push/pop scope, so the
    persistent solver only ever contains hard formulas and guard implications. SAT models are
    re-evaluated with the production ``evaluate_formula`` before being returned.
    """

    def __init__(
        self,
        relata: Sequence[str],
        hard: Sequence[GroundConstraint],
        soft: Sequence[GroundConstraint] = (),
        *,
        timeout_ms: int = 0,
    ) -> None:
        self.relata = tuple(relata)
        self.hard = tuple(hard)
        self.soft = {c.id: c for c in soft}
        if len(self.soft) != len(soft):
            raise ValueError("soft constraint ids must be unique")
        self.atoms = tuple(weak(a, b) for a in self.relata for b in self.relata)
        known = set(self.atoms)
        for constraint in (*self.hard, *self.soft.values()):
            stray = _atoms(constraint.formula) - known
            if stray:
                raise ValueError(f"{constraint.id} mentions atoms outside relata: {stray}")
        self.var = {atom: z3.Bool(f"w_{atom.left}_{atom.right}") for atom in self.atoms}
        self.guard = {cid: z3.Bool(f"g_{i}") for i, cid in enumerate(sorted(self.soft))}
        self.guard_name = {str(g): cid for cid, g in self.guard.items()}
        self.solver = z3.Solver()
        if timeout_ms:
            self.solver.set(timeout=timeout_ms)
        for constraint in self.hard:
            self.solver.add(encode_z3(constraint.formula, self.var))
        for cid, constraint in self.soft.items():
            self.solver.add(z3.Implies(self.guard[cid], encode_z3(constraint.formula, self.var)))
        self.calls = 0

    def w(self, left: str, right: str) -> z3.BoolRef:
        return self.var[weak(left, right)]

    def incomparable(self, left: str, right: str) -> z3.BoolRef:
        return z3.And(z3.Not(self.w(left, right)), z3.Not(self.w(right, left)))

    def count_incomparable(self, pair_list: Iterable[tuple[str, str]]) -> z3.ArithRef:
        return z3.Sum([z3.If(self.incomparable(a, b), 1, 0) for a, b in pair_list])

    def check(self, enabled: Iterable[str] = (), extra: Sequence[z3.BoolRef] = ()) -> Check:
        enabled = tuple(sorted(set(enabled)))
        assumptions = [self.guard[cid] for cid in enabled]
        self.calls += 1
        if extra:
            self.solver.push()
            for term in extra:
                self.solver.add(term)
        try:
            status = self.solver.check(*assumptions)
            if status == z3.sat:
                model = self.solver.model()
                assignment = {
                    atom: z3.is_true(model.eval(v, model_completion=True))
                    for atom, v in self.var.items()
                }
                for constraint in (*self.hard, *(self.soft[cid] for cid in enabled)):
                    if not evaluate_formula(constraint.formula, assignment):
                        raise AssertionError(f"Z3 model fails {constraint.id}")
                return Check("sat", assignment, (), None)
            if status == z3.unsat:
                core = tuple(
                    sorted(
                        self.guard_name[str(g)]
                        for g in self.solver.unsat_core()
                        if str(g) in self.guard_name
                    )
                )
                return Check("unsat", None, core, None)
            return Check("unknown", None, (), self.solver.reason_unknown())
        finally:
            if extra:
                self.solver.pop()

    def require(self, enabled: Iterable[str] = (), extra: Sequence[z3.BoolRef] = ()) -> Check:
        result = self.check(enabled, extra)
        if result.decision == "unknown":
            raise RuntimeError(f"solver returned unknown: {result.reason}")
        return result

    def shrink(self, enabled: Iterable[str]) -> tuple[str, ...]:
        """Deletion-based MUS over soft ids, starting from a known-UNSAT set."""
        first = self.require(enabled)
        if first.decision != "unsat":
            raise ValueError("shrink requires an UNSAT seed")
        current = sorted(first.core)
        index = 0
        while index < len(current):
            trial = current[:index] + current[index + 1 :]
            result = self.require(trial)
            if result.decision == "unsat":
                # Elements already found necessary lie in every UNSAT subset, so they survive.
                current = sorted(set(trial) & set(result.core))
            else:
                index += 1
        for cid in current:  # verify minimality
            if self.require([x for x in current if x != cid]).decision != "sat":
                raise AssertionError("shrink produced a non-minimal core")
        return tuple(sorted(current))

    def grow(self, enabled: Iterable[str]) -> tuple[str, ...]:
        """Grow a SAT soft set to a maximal SAT subset, in sorted id order."""
        current = set(enabled)
        if self.require(current).decision != "sat":
            raise ValueError("grow requires a SAT seed")
        for cid in sorted(self.soft):
            if cid in current:
                continue
            if self.require(current | {cid}).decision == "sat":
                current.add(cid)
        return tuple(sorted(current))


def marco(engine: Engine) -> tuple[list[tuple[str, ...]], list[tuple[str, ...]]]:
    """Enumerate every MUS and MSS over ``engine.soft`` (two-solver MARCO).

    The map solver holds all blocking clauses; the constraint engine is queried with
    assumptions only. Any UNKNOWN aborts (``Engine.require`` raises), so a returned result is
    complete coverage.
    """
    soft_ids = sorted(engine.soft)
    selector = {cid: z3.Bool(f"s_{i}") for i, cid in enumerate(soft_ids)}
    mapper = z3.Solver()
    muses: list[tuple[str, ...]] = []
    msses: list[tuple[str, ...]] = []
    while mapper.check() == z3.sat:
        model = mapper.model()
        seed = {
            cid for cid in soft_ids if z3.is_true(model.eval(selector[cid], model_completion=True))
        }
        if engine.require(seed).decision == "sat":
            mss = engine.grow(seed)
            msses.append(mss)
            mapper.add(z3.Or([selector[c] for c in soft_ids if c not in set(mss)] or [False]))
        else:
            mus = engine.shrink(seed)
            muses.append(mus)
            mapper.add(z3.Or([z3.Not(selector[c]) for c in mus] or [False]))
    return sorted(muses), sorted(msses)


# --------------------------------------------------------------------------- bitmask relations


def compile_predicate(formulas: Sequence[Formula], relata: Sequence[str]) -> Callable[[int], bool]:
    """Compile ground formulas into a predicate over relation bitmasks.

    Bit ``i * n + j`` of the mask is ``weak(relata[i], relata[j])``.
    """
    index = {name: i for i, name in enumerate(relata)}
    n = len(relata)

    def emit(formula: Formula) -> str:
        match formula:
            case RelationAtom(left=left, right=right):
                return f"((R >> {index[left] * n + index[right]}) & 1 == 1)"
            case BoolConstant(value=value):
                return "True" if value else "False"
            case Not(operand=operand):
                return f"(not {emit(operand)})"
            case And(operands=ops):
                return "(" + " and ".join(emit(op) for op in ops) + ")"
            case Or(operands=ops):
                return "(" + " or ".join(emit(op) for op in ops) + ")"
            case Implies(antecedent=a, consequent=c):
                return f"((not {emit(a)}) or {emit(c)})"

    body = " and ".join(emit(f) for f in formulas) or "True"
    return cast(Callable[[int], bool], eval(f"lambda R: {body}"))  # noqa: S307


def mask_to_assignment(mask: int, relata: Sequence[str]) -> dict[RelationAtom, bool]:
    n = len(relata)
    return {
        weak(a, b): bool((mask >> (i * n + j)) & 1)
        for i, a in enumerate(relata)
        for j, b in enumerate(relata)
    }


def assignment_to_mask(assignment: Mapping[RelationAtom, bool], relata: Sequence[str]) -> int:
    n = len(relata)
    mask = 0
    for i, a in enumerate(relata):
        for j, b in enumerate(relata):
            if assignment[weak(a, b)]:
                mask |= 1 << (i * n + j)
    return mask


def set_partitions(n: int) -> Iterator[tuple[int, ...]]:
    """Restricted growth strings: block index of each element, each partition once."""

    def rec(prefix: list[int], maximum: int) -> Iterator[tuple[int, ...]]:
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for block in range(maximum + 2):
            prefix.append(block)
            yield from rec(prefix, max(maximum, block))
            prefix.pop()

    if n == 0:
        yield ()
        return
    yield from rec([0], 0)


def labeled_posets(k: int) -> Iterator[tuple[int, ...]]:
    """Every labeled partial order on ``range(k)``, each exactly once.

    Returns ``above``: ``above[x]`` is the bitmask of elements strictly above ``x``. Point ``i``
    is inserted with a down-closed set ``D`` below it and an up-closed set ``U`` above it, with
    ``D`` and ``U`` disjoint and every element of ``D`` already strictly below every element of
    ``U``; the relation on the new point is then fully determined, so no poset repeats.
    """

    def rec(above: list[int], i: int) -> Iterator[tuple[int, ...]]:
        if i == k:
            yield tuple(above)
            return
        below = [0] * i  # below[x]: elements strictly below x
        for x in range(i):
            for y in range(i):
                if (above[y] >> x) & 1:
                    below[x] |= 1 << y
        for down in range(1 << i):
            if any((down >> x) & 1 and below[x] & ~down for x in range(i)):
                continue
            for up in range(1 << i):
                if up & down:
                    continue
                if any((up >> x) & 1 and above[x] & ~up for x in range(i)):
                    continue
                if any((down >> x) & 1 and (up & ~above[x]) for x in range(i)):
                    continue
                new = [above[x] | ((1 << i) if (down >> x) & 1 else 0) for x in range(i)]
                new.append(up)
                yield from rec(new, i + 1)

    yield from rec([], 0)


_POSET_CACHE: dict[int, tuple[tuple[int, ...], ...]] = {}


def _posets_cached(k: int) -> Iterable[tuple[int, ...]]:
    if k >= 7:
        return labeled_posets(k)
    if k not in _POSET_CACHE:
        _POSET_CACHE[k] = tuple(labeled_posets(k))
    return _POSET_CACHE[k]


def _block_masks(blocks: tuple[int, ...], n: int, k: int) -> list[list[int]]:
    """``m[a][b]``: bits of all weak(x, y) with x in block a and y in block b."""
    masks = [[0] * k for _ in range(k)]
    for x in range(n):
        for y in range(n):
            masks[blocks[x]][blocks[y]] |= 1 << (x * n + y)
    return masks


def preorders(n: int) -> Iterator[int]:
    """Every reflexive transitive relation on n labeled points, as a weak-relation bitmask.

    A preorder is exactly a partition into indifference classes plus a partial order on the
    classes; ``x ⪰ y`` iff class(x) is equal to or above class(y).
    """
    for blocks in set_partitions(n):
        k = max(blocks) + 1 if blocks else 0
        m = _block_masks(blocks, n, k)
        base = 0
        for a in range(k):
            base |= m[a][a]
        for above in _posets_cached(k):
            mask = base
            for lower in range(k):
                ups = above[lower]
                while ups:
                    upper = (ups & -ups).bit_length() - 1
                    mask |= m[upper][lower]
                    ups &= ups - 1
            yield mask


def total_preorders(n: int) -> Iterator[int]:
    """Every complete preorder on n labeled points (ordered set partitions)."""
    for blocks in set_partitions(n):
        k = max(blocks) + 1 if blocks else 0
        m = _block_masks(blocks, n, k)
        for order in permutations(range(k)):
            rank = {block: position for position, block in enumerate(order)}
            mask = 0
            for a in range(k):
                for b in range(k):
                    if rank[a] >= rank[b]:
                        mask |= m[a][b]
            yield mask


def is_preorder(mask: int, n: int) -> bool:
    def bit(i: int, j: int) -> bool:
        return bool((mask >> (i * n + j)) & 1)

    if not all(bit(i, i) for i in range(n)):
        return False
    return all(
        not (bit(i, j) and bit(j, k)) or bit(i, k)
        for i in range(n)
        for j in range(n)
        for k in range(n)
    )


# --------------------------------------------------------------------------- DPLL


def _tseitin(formulas: Sequence[Formula]) -> tuple[list[list[int]], dict[RelationAtom, int]]:
    variables: dict[RelationAtom, int] = {}
    clauses: list[list[int]] = []
    counter = [0]

    def fresh() -> int:
        counter[0] += 1
        return counter[0]

    def lit(formula: Formula) -> int:
        match formula:
            case RelationAtom():
                if formula not in variables:
                    variables[formula] = fresh()
                return variables[formula]
            case BoolConstant(value=value):
                v = fresh()
                clauses.append([v] if value else [-v])
                return v
            case Not(operand=operand):
                return -lit(operand)
            case And(operands=ops):
                parts = [lit(op) for op in ops]
                v = fresh()
                for p in parts:
                    clauses.append([-v, p])
                clauses.append([v, *(-p for p in parts)])
                return v
            case Or(operands=ops):
                parts = [lit(op) for op in ops]
                v = fresh()
                clauses.append([-v, *parts])
                for p in parts:
                    clauses.append([v, -p])
                return v
            case Implies(antecedent=a, consequent=c):
                return lit(Or((Not(a), c)))

    for formula in formulas:
        clauses.append([lit(formula)])
    return clauses, variables


def dpll_check(
    formulas: Sequence[Formula],
) -> tuple[Decision, dict[RelationAtom, bool] | None]:
    """Independent (non-Z3) satisfiability check of ground formulas.

    Plain DPLL with unit propagation over a Tseitin CNF. SAT answers come with a model that
    is re-checked with ``evaluate_formula``.
    """
    clauses, variables = _tseitin(formulas)
    sys.setrecursionlimit(max(10_000, sys.getrecursionlimit()))

    def propagate(assign: dict[int, bool]) -> bool:
        changed = True
        while changed:
            changed = False
            for clause in clauses:
                unassigned = None
                count = 0
                satisfied = False
                for literal in clause:
                    value = assign.get(abs(literal))
                    if value is None:
                        count += 1
                        unassigned = literal
                    elif value == (literal > 0):
                        satisfied = True
                        break
                if satisfied:
                    continue
                if count == 0:
                    return False
                if count == 1 and unassigned is not None:
                    assign[abs(unassigned)] = unassigned > 0
                    changed = True
        return True

    def solve(assign: dict[int, bool]) -> dict[int, bool] | None:
        if not propagate(assign):
            return None
        for clause in clauses:
            for literal in clause:
                if abs(literal) not in assign:
                    for value in (literal > 0, literal <= 0):
                        trial = dict(assign)
                        trial[abs(literal)] = value
                        found = solve(trial)
                        if found is not None:
                            return found
                    return None
        return assign

    result = solve({})
    if result is None:
        return "unsat", None
    model = {atom: result.get(v, False) for atom, v in variables.items()}
    for formula in formulas:
        if not evaluate_formula(formula, _complete(model, formula)):
            raise AssertionError("DPLL model failed re-evaluation")
    return "sat", model


def _complete(model: Mapping[RelationAtom, bool], formula: Formula) -> dict[RelationAtom, bool]:
    full = dict(model)
    for atom in _atoms(formula):
        full.setdefault(atom, False)
    return full


# --------------------------------------------------------------------------- proofs


class ProofBuilder:
    """Assemble natural-deduction certificates for ``population_ethics.proofs.check_proof``.

    Mirrors the helper closures of ``curated_arrhenius_certificate`` so new certificates use
    the same rule vocabulary and scope discipline.
    """

    def __init__(self) -> None:
        self.nodes: list[ProofNode] = []
        self.scope: dict[str, frozenset[str]] = {}

    def add(
        self,
        node_id: str,
        formula: Formula,
        rule: ProofRule,
        premises: tuple[str, ...] = (),
        scope: tuple[str, ...] | None = None,
        discharged: tuple[str, ...] = (),
        explanation: str = "Checked Boolean inference.",
    ) -> str:
        if scope is None:
            inherited = frozenset().union(*(self.scope.get(p, frozenset()) for p in premises))
            checked = inherited - frozenset(discharged)
        else:
            checked = frozenset(scope)
        self.nodes.append(
            ProofNode(
                node_id,
                formula,
                rule,
                premises,
                tuple(sorted(checked)),
                tuple(sorted(discharged)),
                explanation,
            )
        )
        self.scope[node_id] = checked
        return node_id

    def premise(self, node_id: str, constraint: GroundConstraint) -> str:
        return self.add(node_id, constraint.formula, "premise", (constraint.id,))

    def hypothesis(self, node_id: str, formula: Formula) -> str:
        return self.add(node_id, formula, "hypothesis", scope=(node_id,))

    def transitive(
        self, prefix: str, law: GroundConstraint, first: str, second: str, left: str, right: str
    ) -> str:
        """From ``left ⪰ middle`` and ``middle ⪰ right`` with a transitivity premise."""
        law_node = self.premise(f"{prefix}.law", law)
        if not isinstance(law.formula, Implies):
            raise ValueError("transitivity premise must be an implication")
        joined = self.add(
            f"{prefix}.antecedent",
            law.formula.antecedent,
            "conjunction-introduction",
            (first, second),
        )
        return self.add(
            f"{prefix}.result", weak(left, right), "implication-elimination", (law_node, joined)
        )

    def reverse_from_avoidance(
        self,
        prefix: str,
        completeness: GroundConstraint,
        avoidance: GroundConstraint,
        left: str,
        right: str,
    ) -> str:
        """From completeness on {left,right} and ¬(left ≻ right), derive right ⪰ left."""
        complete = self.premise(f"{prefix}.completeness", completeness)
        avoid = self.premise(f"{prefix}.avoidance", avoidance)
        left_case = self.hypothesis(f"{prefix}.left-case", weak(left, right))
        not_reverse = self.hypothesis(f"{prefix}.not-reverse", Not(weak(right, left)))
        strict_left = self.add(
            f"{prefix}.strict-left",
            strict(left, right),
            "conjunction-introduction",
            (left_case, not_reverse),
            (left_case, not_reverse),
        )
        contradiction = self.add(
            f"{prefix}.contradiction",
            FALSE,
            "contradiction",
            (strict_left, avoid),
            (left_case, not_reverse),
        )
        in_left = self.add(
            f"{prefix}.reverse-in-left-case",
            weak(right, left),
            "classical-contradiction-discharge",
            (contradiction,),
            (left_case,),
            (not_reverse,),
        )
        reverse_case = self.hypothesis(f"{prefix}.reverse-case", weak(right, left))
        return self.add(
            f"{prefix}.result",
            weak(right, left),
            "disjunction-elimination",
            (complete, in_left, reverse_case),
            discharged=(left_case, reverse_case),
        )

    def certificate(self, problem_id: str, root: str) -> ProofCertificate:
        return ProofCertificate(problem_id, root, tuple(self.nodes))


# --------------------------------------------------------------------------- outputs


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def environment() -> dict[str, str]:
    return {
        "z3_version": z3.get_version_string(),
        "python": sys.version.split()[0],
        "uv_lock_sha256": sha256_file(ROOT / "uv.lock"),
        "baseline_toml_sha256": sha256_file(BASELINE_PATH),
        "baseline_problem_id": problem_id_for(load_baseline()),
    }


def write_result(name: str, data: Mapping[str, Any], observations: Mapping[str, Any]) -> Path:
    """Write the deterministic mathematical payload plus separate run observations."""
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema": RESULT_SCHEMA,
        "name": name,
        "environment": environment(),
        "result": data,
        "result_sha256": hashlib.sha256(
            json.dumps(data, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "observations": dict(observations),
    }
    path = RESULTS_DIR / f"{name}.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    return path


LEDGER_FIELDS = (
    "candidate_id",
    "parent_problem_id",
    "hypothesis",
    "motivation",
    "exact_formal_change",
    "scope",
    "search_method",
    "result",
    "evidence_type",
    "checked",
    "minimal",
    "counterexample_if_false",
    "generalization_status",
    "novelty_status",
    "interpretation",
    "next_experiment",
    # research extensions
    "result_scope",
    "formalization_tier",
    "witness_conditions",
    "completion_status",
    "status",
    "artifacts",
)


@dataclass
class LedgerEntry:
    candidate_id: str
    hypothesis: str
    motivation: str
    exact_formal_change: str
    scope: str
    search_method: str
    result: str
    evidence_type: str
    checked: bool
    minimal: str
    interpretation: str
    next_experiment: str
    result_scope: str
    formalization_tier: str
    status: str  # "confirmed" | "refuted" | "open" | "control"
    counterexample_if_false: str = "n/a"
    generalization_status: str = "not generalized"
    novelty_status: str = "candidate-new-result"
    witness_conditions: str = "baseline W: p=1, q=2, m=19"
    completion_status: str = "complete"
    parent_problem_id: str = ""
    artifacts: list[str] = field(default_factory=list)


def record(entries: Sequence[LedgerEntry]) -> None:
    """Upsert ledger entries by candidate_id, keeping the ledger sorted and schema-tagged."""
    existing = json.loads(LEDGER_PATH.read_text())["entries"] if LEDGER_PATH.exists() else []
    by_id = {entry["candidate_id"]: entry for entry in existing}
    parent = problem_id_for(load_baseline())
    for entry in entries:
        data = {name: getattr(entry, name) for name in LEDGER_FIELDS}
        data["parent_problem_id"] = data["parent_problem_id"] or parent
        by_id[entry.candidate_id] = data
    LEDGER_PATH.write_text(
        json.dumps(
            {
                "schema": LEDGER_SCHEMA,
                "fields": list(LEDGER_FIELDS),
                "entries": [by_id[key] for key in sorted(by_id)],
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


# --------------------------------------------------------------------------- applicability

VH, VL, SN = "very_high_positive", "very_low_positive", "slightly_negative"


@dataclass(frozen=True)
class Witness:
    """A fixed-skeleton Arrhenius witness: role levels and block sizes.

    Blocks: A = p·a, A_prime = q·a_prime, B = nB·b, C = nC·c, D = nD·d, E = nE·e, F = nF·f,
    G = nG·g. Composites: AB = A⊎B, AC = A⊎C, AAF = A⊎A_prime⊎F, AAE = A⊎A_prime⊎E.
    ``categories`` maps each category name to its declared welfare levels.
    """

    levels: Mapping[str, int]
    sizes: Mapping[str, int]
    categories: Mapping[str, frozenset[int]]

    def block(self, name: str) -> tuple[int, ...]:
        return (self.levels[name],) * self.sizes[name]

    def populations(self) -> dict[str, tuple[int, ...]]:
        blocks = {name: self.block(name) for name in ("A", "A_prime", "B", "C", "D", "E", "F", "G")}
        blocks["AB"] = blocks["A"] + blocks["B"]
        blocks["AC"] = blocks["A"] + blocks["C"]
        blocks["AAF"] = blocks["A"] + blocks["A_prime"] + blocks["F"]
        blocks["AAE"] = blocks["A"] + blocks["A_prime"] + blocks["E"]
        return blocks


def _avg(values: Sequence[int]) -> Fraction:
    return Fraction(sum(values), len(values))


def _in(categories: Mapping[str, frozenset[int]], category: str, values: Sequence[int]) -> bool:
    return bool(values) and all(v in categories[category] for v in values)


def applicability(witness: Witness) -> dict[str, bool]:
    """Exact applicability of each baseline ground instance, derived from role populations.

    Each clause names the source condition it encodes (Arrhenius 2000, pp. 257–263). This is
    a research formalization (formalization tier: source-constrained fixed-skeleton
    generalization), not a source-reviewed predicate.
    """
    P = witness.populations()
    cat = witness.categories
    s = witness.sizes

    def equal(x: str) -> bool:
        return len(set(P[x])) == 1

    def unequal(x: str) -> bool:
        return len(set(P[x])) > 1

    categories_ok = (
        all(v > 0 for v in cat[VH] | cat[VL])
        and all(v < 0 for v in cat[SN])
        and max(cat[VL]) < min(cat[VH])
    )
    return {
        # Declared category structure: SN < 0 < VL < VH.
        "categories:ordered": categories_ok,
        # Non-Repugnance witness: A is a perfectly equal very-high population; D is a
        # very-low-positive population (any size).
        "repugnance:A-equal-very-high": equal("A") and _in(cat, VH, P["A"]),
        "repugnance:D-very-low": _in(cat, VL, P["D"]),
        # Non-Anti-Egalitarianism: equal population vs same-size unequal population with lower
        # average welfare.
        "anti-egal:D-equal": equal("D"),
        "anti-egal:AC-unequal": unequal("AC"),
        "anti-egal:|AC|=|D|": len(P["AC"]) == len(P["D"]),
        "anti-egal:avg(AC)<avg(D)": _avg(P["AC"]) < _avg(P["D"]),
        "anti-egal:G-equal": equal("G"),
        "anti-egal:AAF-unequal": unequal("AAF"),
        "anti-egal:|AAF|=|G|": len(P["AAF"]) == len(P["G"]),
        "anti-egal:avg(AAF)<avg(G)": _avg(P["AAF"]) < _avg(P["G"]),
        # Non-Sadism: common background A⊎A_prime; a nonempty all-negative addition E versus a
        # nonempty all-positive addition F.
        "sadism:E-nonempty-negative": s["E"] > 0 and all(v < 0 for v in P["E"]),
        "sadism:F-nonempty-positive": s["F"] > 0 and all(v > 0 for v in P["F"]),
        # Minimal Non-Extreme Priority with n = q: on background A, adding q very-high lives
        # plus one slightly negative life versus adding q+1 very-low-positive lives.
        "mnep:A_prime-q-very-high": s["A_prime"] >= 1 and _in(cat, VH, P["A_prime"]),
        "mnep:E-single-slightly-negative": s["E"] == 1 and _in(cat, SN, P["E"]),
        "mnep:B-q+1-very-low": s["B"] == s["A_prime"] + 1 and _in(cat, VL, P["B"]),
        # Dominance: equal size, every life in AC above every life in G.
        "dominance:|AC|=|G|": len(P["AC"]) == len(P["G"]),
        "dominance:min(AC)>max(G)": min(P["AC"]) > max(P["G"]),
        # Addition: on background A, B all below A, C all below B, and |C| > |B|.
        "addition:max(B)<min(A)": max(P["B"]) < min(P["A"]),
        "addition:max(C)<min(B)": max(P["C"]) < min(P["B"]),
        "addition:|C|>|B|": s["C"] > s["B"],
        # Very-low-positive roles as used by the source construction.
        "roles:B,C,F,G-very-low": all(_in(cat, VL, P[x]) for x in ("B", "C", "F", "G")),
    }


def baseline_witness(spec: CompatibilitySpec) -> Witness:
    names = spec.common.universe.names
    levels = {x: names[x][0] for x in ("A", "A_prime", "B", "C", "D", "E", "F", "G")}
    sizes = {x: len(names[x]) for x in levels}
    assert spec.common.categories is not None
    return Witness(levels, sizes, dict(spec.common.categories.values))


# --------------------------------------------------------------------------- TOML materializer


def toml_value(value: object) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False)
    if isinstance(value, Fraction):
        return toml_value({"numerator": value.numerator, "denominator": value.denominator})
    if isinstance(value, (list, tuple)):
        return "[" + ", ".join(toml_value(v) for v in value) + "]"
    if isinstance(value, Mapping):
        return "{ " + ", ".join(f"{k} = {toml_value(v)}" for k, v in value.items()) + " }"
    raise TypeError(f"cannot emit {value!r}")


def materialize_witness(
    witness: Witness,
    *,
    experiment_id: str,
    formalization_id: str,
    source_fidelity: str,
    witness_bindings: Mapping[str, int],
) -> str:
    """Emit the baseline skeleton for ``witness`` with every numeric side condition recomputed.

    Constraint ids, formulas and population names are identical to the baseline, so the
    curated ``arrhenius-2000/v1`` certificate (purely propositional over names) applies.
    """
    baseline_text = BASELINE_PATH.read_text()
    groups_text = baseline_text[baseline_text.index("[[groups]]") :]
    P = witness.populations()
    s = witness.sizes
    L = len(P["D"])
    lines = [
        'schema = "population-ethics.experiment/v2"',
        f"id = {toml_value(experiment_id)}",
        'kind = "compatibility"',
        'claim_kind = "bounded-proof-instance"',
        f"source_fidelity = {toml_value(source_fidelity)}",
        'source_ids = ["arrhenius-2000"]',
        f"formalization_id = {toml_value(formalization_id)}",
        'fixed_groups = ["reflexivity", "transitivity"]',
        'candidate_groups = ["completeness", "repugnance-avoidance", '
        '"anti-egalitarianism-avoidance", "sadism-avoidance", "minimal-non-extreme-priority", '
        '"dominance", "addition"]',
        "",
        "[resource_policy]",
        "max_populations = 100",
        "max_expanded_lives = 5000",
        "max_relation_atoms = 1000",
        "max_ground_constraints = 5000",
        "max_subsets = 256",
        "timeout_ms = 0",
        "",
        "[domain]",
        'mode = "explicit"',
    ]
    for name in ("A", "B", "C", "D", "A_prime", "E", "F", "G"):
        lines += [
            "",
            "[[domain.populations]]",
            f"name = {toml_value(name)}",
            f"groups = [{{ welfare = {witness.levels[name]}, count = {s[name]} }}]",
        ]
    for name, parts in (
        ("AB", ["A", "B"]),
        ("AC", ["A", "C"]),
        ("AAF", ["A", "A_prime", "F"]),
        ("AAE", ["A", "A_prime", "E"]),
    ):
        lines += [
            "",
            "[[domain.populations]]",
            f"name = {toml_value(name)}",
            f"values = {toml_value(list(P[name]))}",
            f"parts = {toml_value(parts)}",
        ]
    lines += ["", "[categories]"]
    for category in (SN, VL, VH):
        lines.append(f"{category} = {toml_value(sorted(witness.categories[category]))}")
    lines += ["", "[role_bindings]"]
    for name in ("A", "B", "C", "D", "A_prime", "E", "F", "G"):
        lines.append(f"source_{name} = {toml_value(name)}")
    lines += ["", "[witness_bindings]"]
    for key, value in witness_bindings.items():
        lines.append(f"{key} = {value}")

    def side(identifier: str, kind: str, data: Mapping[str, object]) -> None:
        lines.extend(
            [
                "",
                "[[side_conditions]]",
                f"id = {toml_value(identifier)}",
                f"kind = {toml_value(kind)}",
                f"data = {toml_value(data)}",
            ]
        )

    side(
        "large-population-cardinality",
        "cardinality-equal",
        {"populations": ["AC", "AAF", "D", "G"], "expected": L},
    )
    side(
        "small-population-cardinality",
        "cardinality-equal",
        {"populations": ["AB", "AAE"], "expected": len(P["AB"])},
    )
    side(
        "anti-egalitarian-average-ac",
        "average-less",
        {"population": "AC", "expected": _avg(P["AC"]), "bound": _avg(P["D"])},
    )
    side(
        "anti-egalitarian-average-aaf",
        "average-less",
        {"population": "AAF", "expected": _avg(P["AAF"]), "bound": _avg(P["G"])},
    )
    side("addition-size-gap", "integer-greater", {"left": s["C"], "right": s["B"]})
    side(
        "category-representatives",
        "category-membership",
        {
            "bindings": [
                {"category": c, "welfare": w}
                for c in (SN, VL, VH)
                for w in sorted({witness.levels[x] for x in witness.levels})
                if w in witness.categories[c]
            ]
        },
    )
    side("declared-composites", "role-disjoint-union", {"composites": ["AB", "AC", "AAF", "AAE"]})
    side("selected-witnesses", "witness-binding", {"bindings": dict(witness_bindings)})
    return "\n".join(lines) + "\n\n" + groups_text
