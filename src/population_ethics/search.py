from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Literal

from population_ethics.domain import ResourceUsage, ValidationError
from population_ethics.solver import GuardedSolver
from population_ethics.spec import CompatibilitySpec, Decision, FrontierSpec, problem_id_for

ScanUnit = Literal["principle", "instance"]
FrontierStatus = Literal["sat", "unsat", "unknown", "boundary"]
BoundaryKind = Literal[
    "none", "minimal-unsat", "maximal-sat", "unresolved-minimal-unsat", "unresolved-maximal-sat"
]


@dataclass(frozen=True, slots=True)
class ScanDimension:
    id: str
    constraint_ids: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class FrontierNode:
    index: int
    selected_units: tuple[str, ...]
    decision: Decision
    status: FrontierStatus
    boundary_kind: BoundaryKind
    reason_unknown: str | None


@dataclass(frozen=True, slots=True)
class FrontierResult:
    claim_kind: Literal["bounded-search"]
    parent_problem_id: str
    unit: ScanUnit
    fixed_group_ids: tuple[str, ...]
    dimensions: tuple[ScanDimension, ...]
    nodes: tuple[FrontierNode, ...]
    solver_calls: int


def scan_frontier(
    spec: CompatibilitySpec | FrontierSpec,
    *,
    unit: ScanUnit,
    max_subsets: int | None = None,
) -> FrontierResult:
    dimensions = _dimensions(spec, unit)
    required_subsets = 1 << len(dimensions)
    requested_cap = spec.common.resource_policy.max_subsets if max_subsets is None else max_subsets
    if isinstance(requested_cap, bool) or not isinstance(requested_cap, int) or requested_cap < 0:
        raise ValidationError("max_subsets must be a non-negative integer")
    if requested_cap < required_subsets:
        raise ValidationError(
            f"subset preflight failed: complete {unit} power set requires "
            f"{required_subsets} subsets, cap is {requested_cap}"
        )
    usage = spec.common.universe.usage
    spec.common.resource_policy.preflight(
        ResourceUsage(
            populations=usage.populations,
            expanded_lives=usage.expanded_lives,
            relation_atoms=usage.relation_atoms,
            ground_constraints=usage.ground_constraints,
            subsets=required_subsets,
        )
    )

    engine = GuardedSolver(spec.groups, spec.common.resource_policy)
    fixed_constraints = engine.constraint_ids_for_groups(spec.fixed_group_ids)
    decisions: list[Decision] = []
    reasons: list[str | None] = []
    selected_by_mask: list[tuple[str, ...]] = []
    for mask in range(required_subsets):
        selected_dimensions = tuple(
            dimension for bit, dimension in enumerate(dimensions) if mask & (1 << bit)
        )
        enabled = (
            *fixed_constraints,
            *(item for dimension in selected_dimensions for item in dimension.constraint_ids),
        )
        result = engine.check_constraints(enabled)
        decisions.append(result.decision)
        reasons.append(result.reason_unknown)
        selected_by_mask.append(tuple(dimension.id for dimension in selected_dimensions))

    nodes = tuple(
        _classify_node(
            mask,
            selected_by_mask[mask],
            decisions,
            reasons[mask],
            len(dimensions),
        )
        for mask in range(required_subsets)
    )
    return FrontierResult(
        "bounded-search",
        problem_id_for(spec),
        unit,
        spec.fixed_group_ids,
        dimensions,
        nodes,
        engine.calls,
    )


def _dimensions(
    spec: CompatibilitySpec | FrontierSpec, unit: ScanUnit
) -> tuple[ScanDimension, ...]:
    groups = {group.id: group for group in spec.groups}
    if unit == "principle":
        dimensions = tuple(
            ScanDimension(
                group_id,
                tuple(constraint.id for constraint in groups[group_id].constraints),
            )
            for group_id in spec.candidate_group_ids
        )
    elif unit == "instance":
        items: list[ScanDimension] = []
        for group_id in spec.candidate_group_ids:
            group = groups[group_id]
            if group_id == "completeness":
                items.append(ScanDimension(group_id, tuple(item.id for item in group.constraints)))
            else:
                items.extend(
                    ScanDimension(f"instance:{constraint.id}", (constraint.id,))
                    for constraint in group.constraints
                )
        dimensions = tuple(items)
    else:
        raise ValidationError(f"unsupported scan unit {unit!r}")
    if len({dimension.id for dimension in dimensions}) != len(dimensions):
        raise ValidationError("scan unit IDs must be disjoint")
    constraint_ids = [
        constraint_id for dimension in dimensions for constraint_id in dimension.constraint_ids
    ]
    if len(set(constraint_ids)) != len(constraint_ids):
        raise ValidationError("scan units must contain disjoint ground constraints")
    return dimensions


def _classify_node(
    mask: int,
    selected_units: tuple[str, ...],
    decisions: Sequence[Decision],
    reason_unknown: str | None,
    dimension_count: int,
) -> FrontierNode:
    decision = decisions[mask]
    if decision == "unknown":
        return FrontierNode(mask, selected_units, decision, "unknown", "none", reason_unknown)
    if decision == "unsat":
        neighbors = [
            decisions[mask & ~(1 << bit)] for bit in range(dimension_count) if mask & (1 << bit)
        ]
        if any(neighbor == "unknown" for neighbor in neighbors):
            return FrontierNode(
                mask,
                selected_units,
                decision,
                "unknown",
                "unresolved-minimal-unsat",
                "an immediate subset is UNKNOWN",
            )
        if all(neighbor == "sat" for neighbor in neighbors):
            return FrontierNode(mask, selected_units, decision, "boundary", "minimal-unsat", None)
        return FrontierNode(mask, selected_units, decision, "unsat", "none", None)

    neighbors = [
        decisions[mask | (1 << bit)] for bit in range(dimension_count) if not mask & (1 << bit)
    ]
    if any(neighbor == "unknown" for neighbor in neighbors):
        return FrontierNode(
            mask,
            selected_units,
            decision,
            "unknown",
            "unresolved-maximal-sat",
            "an immediate superset is UNKNOWN",
        )
    if all(neighbor == "unsat" for neighbor in neighbors):
        return FrontierNode(mask, selected_units, decision, "boundary", "maximal-sat", None)
    return FrontierNode(mask, selected_units, decision, "sat", "none", None)
