from __future__ import annotations

from collections.abc import Iterable
from dataclasses import replace

import pytest

import population_ethics.solver as solver_module
from population_ethics.domain import ResourcePolicy
from population_ethics.principles import GroundConstraint
from population_ethics.relations import Not, weak
from population_ethics.search import _classify_node, scan_frontier
from population_ethics.solver import GuardedSolver, solve_entailment, solve_groups
from population_ethics.spec import (
    CheckedModelEvidence,
    CompatibilitySpec,
    ConstraintGroup,
    EntailmentSpec,
    SolverReportEvidence,
    load_experiment,
)


def _constraint(identifier: str, formula: object) -> GroundConstraint:
    return GroundConstraint(
        identifier,
        "test",
        formula,  # type: ignore[arg-type]
        ("A", "B"),
        None,
        "test/v1",
        "Behavioral test premise.",
    )


def _contradictory_group() -> ConstraintGroup:
    atom = weak("A", "B")
    return ConstraintGroup(
        "contradiction",
        "test",
        (
            _constraint("positive", atom),
            _constraint("negative", Not(atom)),
        ),
    )


def test_sat_models_are_independently_validated() -> None:
    atom = weak("A", "B")
    group = ConstraintGroup("premise", "test", (_constraint("positive", atom),))
    result = solve_groups((group,), ("premise",), ResourcePolicy())
    assert result.decision == "sat"
    evidence = result.evidence[0]
    assert isinstance(evidence, CheckedModelEvidence)
    assert evidence.assignment[atom]
    assert evidence.checked_constraint_ids == ("positive",)


def test_entailment_checks_base_before_goal() -> None:
    consistent = load_experiment("experiments/entailment-countermodel.toml")
    assert isinstance(consistent, EntailmentSpec)
    countermodel = solve_entailment(consistent)
    assert countermodel.outcome == "countermodel"
    assert isinstance(countermodel.evidence[0], CheckedModelEvidence)

    inconsistent = load_experiment("experiments/entailment-inconsistent.toml")
    assert isinstance(inconsistent, EntailmentSpec)
    result = solve_entailment(inconsistent)
    assert result.outcome == "inconsistent-premises"


def test_unknown_is_preserved_as_an_obligation(monkeypatch: pytest.MonkeyPatch) -> None:
    atom = weak("A", "B")
    group = ConstraintGroup("premise", "test", (_constraint("positive", atom),))

    def unknown(self: GuardedSolver, constraint_ids: Iterable[str]) -> solver_module._QueryResult:
        del self, constraint_ids
        return solver_module._QueryResult("unknown", None, (), "forced-unknown")

    monkeypatch.setattr(GuardedSolver, "check_constraints", unknown)
    result = solve_groups((group,), ("premise",), ResourcePolicy())
    assert result.decision == "unknown"
    assert result.unresolved_obligations == ("initial-check:forced-unknown",)


def test_full_set_minimization_ignores_raw_core_variation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    group = _contradictory_group()
    baseline = solve_groups((group,), (group.id,), ResourcePolicy())
    baseline_report = baseline.evidence[0]
    assert isinstance(baseline_report, SolverReportEvidence)

    original = GuardedSolver.check_constraints
    first = True

    def varied(self: GuardedSolver, constraint_ids: Iterable[str]) -> solver_module._QueryResult:
        nonlocal first
        result = original(self, constraint_ids)
        if first and result.decision == "unsat":
            first = False
            return replace(result, raw_core=("negative",))
        return result

    monkeypatch.setattr(GuardedSolver, "check_constraints", varied)
    varied_result = solve_groups((group,), (group.id,), ResourcePolicy())
    varied_report = varied_result.evidence[0]
    assert isinstance(varied_report, SolverReportEvidence)
    assert varied_report.raw_core == ("negative",)
    assert varied_report.grounded_core == baseline_report.grounded_core


def test_unknown_deletions_make_minimality_unresolved(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    group = _contradictory_group()
    original = GuardedSolver.check_constraints

    def uncertain_deletions(
        self: GuardedSolver, constraint_ids: Iterable[str]
    ) -> solver_module._QueryResult:
        ids: tuple[str, ...] = tuple(constraint_ids)
        if len(ids) == 1:
            return solver_module._QueryResult("unknown", None, (), "forced-unknown")
        return original(self, ids)

    monkeypatch.setattr(GuardedSolver, "check_constraints", uncertain_deletions)
    result = solve_groups((group,), (group.id,), ResourcePolicy())
    report = result.evidence[0]
    assert isinstance(report, SolverReportEvidence)
    assert report.minimality == "unresolved"
    assert report.unresolved_obligations


def test_frontier_boundary_requires_definitive_neighbors() -> None:
    definitive = _classify_node(1, ("x",), ("sat", "unsat"), None, 1)
    assert definitive.status == "boundary"
    assert definitive.boundary_kind == "minimal-unsat"

    unresolved = _classify_node(1, ("x",), ("unknown", "unsat"), None, 1)
    assert unresolved.status == "unknown"
    assert unresolved.boundary_kind == "unresolved-minimal-unsat"


def test_complete_scan_sizes_and_cap_preflight() -> None:
    spec = load_experiment("experiments/arrhenius-2000-proof.toml")
    assert isinstance(spec, CompatibilitySpec)
    principle = scan_frontier(spec, unit="principle", max_subsets=128)
    instance = scan_frontier(spec, unit="instance", max_subsets=256)
    assert len(principle.nodes) == 128
    assert len(instance.nodes) == 256
    assert all(
        node.status != "boundary" or node.boundary_kind in {"minimal-unsat", "maximal-sat"}
        for node in (*principle.nodes, *instance.nodes)
    )
    with pytest.raises(Exception, match="requires 128 subsets"):
        scan_frontier(spec, unit="principle", max_subsets=127)
