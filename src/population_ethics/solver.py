from __future__ import annotations

import hashlib
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from typing import Literal

import z3  # type: ignore[import-untyped]

from population_ethics.domain import ResourcePolicy, ValidationError
from population_ethics.relations import (
    Formula,
    Not,
    RelationAtom,
    collect_atoms,
    encode_z3,
    evaluate_formula,
    formula_to_data,
)
from population_ethics.spec import (
    CheckedModelEvidence,
    ConstraintGroup,
    Decision,
    EntailmentSpec,
    Evidence,
    SolverReportEvidence,
    constraint_to_data,
)


@dataclass(frozen=True, slots=True)
class SolveResult:
    decision: Decision
    evidence: tuple[Evidence, ...]
    reason_unknown: str | None
    unresolved_obligations: tuple[str, ...]
    solver_calls: int


@dataclass(frozen=True, slots=True)
class EntailmentResult:
    outcome: Literal["countermodel", "solver-entailed", "inconsistent-premises", "unknown"]
    evidence: tuple[Evidence, ...]
    unresolved_obligations: tuple[str, ...]
    solver_calls: int


@dataclass(frozen=True, slots=True)
class _QueryResult:
    decision: Decision
    assignment: Mapping[RelationAtom, bool] | None
    raw_core: tuple[str, ...]
    reason_unknown: str | None


class GuardedSolver:
    def __init__(
        self,
        groups: Sequence[ConstraintGroup],
        policy: ResourcePolicy,
        *,
        fixed_formulas: Sequence[Formula] = (),
    ) -> None:
        self.groups = tuple(groups)
        self.policy = policy
        self.fixed_formulas = tuple(fixed_formulas)
        self.constraints = tuple(
            constraint for group in self.groups for constraint in group.constraints
        )
        constraint_ids = [constraint.id for constraint in self.constraints]
        if len(constraint_ids) != len(set(constraint_ids)):
            raise ValidationError("guarded solver requires globally unique constraint IDs")
        group_ids = [group.id for group in self.groups]
        if len(group_ids) != len(set(group_ids)):
            raise ValidationError("guarded solver requires unique group IDs")
        self.constraints_by_id = {constraint.id: constraint for constraint in self.constraints}
        self.constraints_by_group = {
            group.id: tuple(constraint.id for constraint in group.constraints)
            for group in self.groups
        }
        atoms: set[RelationAtom] = set()
        for constraint in self.constraints:
            atoms.update(collect_atoms(constraint.formula))
        for formula in self.fixed_formulas:
            atoms.update(collect_atoms(formula))
        self.atoms = tuple(sorted(atoms))
        self.atom_map = {
            atom: z3.Bool(f"atom_{hashlib.sha256(repr(atom).encode()).hexdigest()}")
            for atom in self.atoms
        }
        self.guards = {
            constraint.id: z3.Bool(f"guard_{hashlib.sha256(constraint.id.encode()).hexdigest()}")
            for constraint in self.constraints
        }
        self.guard_names = {
            str(guard): constraint_id for constraint_id, guard in self.guards.items()
        }
        self.solver = z3.Solver()
        self.solver.set(timeout=policy.timeout_ms, unsat_core=True)
        for constraint in self.constraints:
            self.solver.add(
                z3.Implies(self.guards[constraint.id], encode_z3(constraint.formula, self.atom_map))
            )
        for formula in self.fixed_formulas:
            self.solver.add(encode_z3(formula, self.atom_map))
        self.calls = 0

    def constraint_ids_for_groups(self, group_ids: Iterable[str]) -> tuple[str, ...]:
        result: list[str] = []
        for group_id in group_ids:
            if group_id not in self.constraints_by_group:
                raise ValidationError(f"unknown constraint group {group_id!r}")
            result.extend(self.constraints_by_group[group_id])
        return tuple(result)

    def check_groups(self, group_ids: Iterable[str]) -> _QueryResult:
        return self.check_constraints(self.constraint_ids_for_groups(group_ids))

    def check_constraints(self, constraint_ids: Iterable[str]) -> _QueryResult:
        enabled = tuple(constraint_ids)
        if len(enabled) != len(set(enabled)):
            raise ValidationError("solver query repeats a constraint ID")
        try:
            assumptions = tuple(self.guards[constraint_id] for constraint_id in enabled)
        except KeyError as error:
            raise ValidationError(f"unknown ground constraint {error.args[0]!r}") from error
        self.calls += 1
        status = self.solver.check(*assumptions)
        if status == z3.sat:
            model = self.solver.model()
            assignment = {
                atom: z3.is_true(model.eval(variable, model_completion=True))
                for atom, variable in self.atom_map.items()
            }
            for constraint_id in enabled:
                constraint = self.constraints_by_id[constraint_id]
                if not evaluate_formula(constraint.formula, assignment):
                    raise ValidationError(
                        f"Z3 model failed independent validation for {constraint_id!r}"
                    )
            for index, formula in enumerate(self.fixed_formulas):
                if not evaluate_formula(formula, assignment):
                    raise ValidationError(
                        f"Z3 model failed independent validation for fixed formula {index}"
                    )
            return _QueryResult("sat", assignment, (), None)
        if status == z3.unsat:
            raw_core = tuple(
                sorted(
                    self.guard_names[str(guard)]
                    for guard in self.solver.unsat_core()
                    if str(guard) in self.guard_names
                )
            )
            return _QueryResult("unsat", None, raw_core, None)
        return _QueryResult("unknown", None, (), self.solver.reason_unknown())


def solve_groups(
    groups: Sequence[ConstraintGroup],
    enabled_group_ids: Sequence[str],
    policy: ResourcePolicy,
    *,
    minimize: bool = True,
    fixed_formulas: Sequence[Formula] = (),
) -> SolveResult:
    engine = GuardedSolver(groups, policy, fixed_formulas=fixed_formulas)
    enabled = tuple(sorted(enabled_group_ids))
    constraint_ids = engine.constraint_ids_for_groups(enabled)
    query = engine.check_constraints(constraint_ids)
    grounded_input = tuple(
        constraint_to_data(engine.constraints_by_id[constraint_id])
        for constraint_id in constraint_ids
    ) + tuple(
        {
            "id": f"fixed-formula:{index}",
            "principle_id": "query",
            "formula": formula_to_data(formula),
            "populations": sorted(
                {
                    endpoint
                    for atom in collect_atoms(formula)
                    for endpoint in (atom.left, atom.right)
                }
            ),
            "source_locator": None,
            "formalization_id": "query.fixed-formula/v1",
            "explanation": "Query-local fixed formula.",
        }
        for index, formula in enumerate(fixed_formulas)
    )
    if query.decision == "sat":
        assert query.assignment is not None
        evidence: tuple[Evidence, ...] = (
            CheckedModelEvidence(
                query.assignment,
                tuple(
                    sorted(
                        (
                            *constraint_ids,
                            *(f"fixed-formula:{i}" for i in range(len(fixed_formulas))),
                        )
                    )
                ),
                grounded_input,
            ),
        )
        return SolveResult("sat", evidence, None, (), engine.calls)
    if query.decision == "unknown":
        obligation = f"initial-check:{query.reason_unknown or 'unknown reason'}"
        report = SolverReportEvidence(
            "unknown",
            grounded_input,
            (),
            (),
            "not-applicable",
            (obligation,),
            query.reason_unknown,
        )
        return SolveResult("unknown", (report,), query.reason_unknown, (obligation,), engine.calls)

    grounded_core = tuple(sorted(constraint_ids))
    minimality: Literal["verified", "unresolved", "not-applicable"] = "not-applicable"
    obligations: tuple[str, ...] = ()
    trace: tuple[str, ...] = ()
    if minimize:
        grounded_core, minimality, obligations, trace = _minimize_unsat(
            engine, enabled, constraint_ids
        )
    report = SolverReportEvidence(
        "unsat",
        grounded_input,
        query.raw_core,
        grounded_core,
        minimality,
        obligations,
        None,
        trace,
    )
    return SolveResult("unsat", (report,), None, obligations, engine.calls)


def _minimize_unsat(
    engine: GuardedSolver,
    enabled_groups: Sequence[str],
    enabled_constraints: Sequence[str],
) -> tuple[
    tuple[str, ...],
    Literal["verified", "unresolved", "not-applicable"],
    tuple[str, ...],
    tuple[str, ...],
]:
    retained_groups = list(enabled_groups)
    obligations: list[str] = []
    trace: list[str] = []
    for group_id in tuple(retained_groups):
        reduced_groups = tuple(item for item in retained_groups if item != group_id)
        check = engine.check_groups(reduced_groups)
        trace.append(f"delete-group:{group_id}:{check.decision}")
        if check.decision == "unsat":
            retained_groups.remove(group_id)
        elif check.decision == "unknown":
            obligations.append(
                f"group-deletion:{group_id}:{check.reason_unknown or 'unknown reason'}"
            )

    retained_constraints = [
        constraint_id
        for constraint_id in enabled_constraints
        if any(
            constraint_id in engine.constraints_by_group[group_id] for group_id in retained_groups
        )
    ]
    for constraint_id in tuple(retained_constraints):
        reduced = tuple(item for item in retained_constraints if item != constraint_id)
        check = engine.check_constraints(reduced)
        trace.append(f"delete-ground:{constraint_id}:{check.decision}")
        if check.decision == "unsat":
            retained_constraints.remove(constraint_id)
        elif check.decision == "unknown":
            obligations.append(
                f"ground-deletion:{constraint_id}:{check.reason_unknown or 'unknown reason'}"
            )

    for constraint_id in retained_constraints:
        reduced = tuple(item for item in retained_constraints if item != constraint_id)
        check = engine.check_constraints(reduced)
        trace.append(f"verify-ground:{constraint_id}:{check.decision}")
        if check.decision == "unknown":
            obligations.append(
                f"minimality:{constraint_id}:{check.reason_unknown or 'unknown reason'}"
            )
        elif check.decision == "unsat":
            raise ValidationError(
                f"ground core minimization left removable constraint {constraint_id!r}"
            )
    minimality: Literal["verified", "unresolved", "not-applicable"] = (
        "unresolved" if obligations else "verified"
    )
    return (
        tuple(sorted(retained_constraints)),
        minimality,
        tuple(sorted(set(obligations))),
        tuple(trace),
    )


def solve_entailment(spec: EntailmentSpec) -> EntailmentResult:
    selected_groups = tuple(
        group for group in spec.groups if group.id in set(spec.selected_group_ids)
    )
    base = solve_groups(
        selected_groups,
        tuple(group.id for group in selected_groups),
        spec.common.resource_policy,
    )
    if base.decision == "unsat":
        return EntailmentResult(
            "inconsistent-premises",
            base.evidence,
            base.unresolved_obligations,
            base.solver_calls,
        )
    if base.decision == "unknown":
        return EntailmentResult(
            "unknown", base.evidence, base.unresolved_obligations, base.solver_calls
        )
    counterexample = solve_groups(
        selected_groups,
        tuple(group.id for group in selected_groups),
        spec.common.resource_policy,
        fixed_formulas=(Not(spec.goal),),
    )
    total_calls = base.solver_calls + counterexample.solver_calls
    if counterexample.decision == "sat":
        return EntailmentResult("countermodel", counterexample.evidence, (), total_calls)
    if counterexample.decision == "unsat":
        return EntailmentResult(
            "solver-entailed",
            counterexample.evidence,
            counterexample.unresolved_obligations,
            total_calls,
        )
    return EntailmentResult(
        "unknown",
        counterexample.evidence,
        counterexample.unresolved_obligations,
        total_calls,
    )
