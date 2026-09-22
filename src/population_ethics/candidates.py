from __future__ import annotations

import copy
from collections.abc import Sequence
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Literal

from population_ethics.domain import PopulationUniverse, ValidationError, build_population_universe
from population_ethics.proofs import check_proof, curated_arrhenius_certificate
from population_ethics.spec import (
    CandidateRevision,
    CheckedModelEvidence,
    CheckedProofEvidence,
    CompatibilitySpec,
    ConstraintGroup,
    EntailmentSpec,
    Evidence,
    ExperimentCommon,
    ExperimentSpec,
    content_id,
    normalized_problem,
    problem_id_for,
    validate_experiment,
)

AttemptOutcome = Literal[
    "checked-model",
    "checked-proof",
    "solver-unsat",
    "unknown",
    "rejected-certificate",
    "validation-error",
    "rejected-proposal",
]
ReportedInt = int | Literal["unreported"]
ReportedCost = Fraction | Literal["unreported"]


@dataclass(frozen=True, slots=True)
class AttemptRecord:
    attempt_id: str
    candidate_id: str
    attempt_number: int
    outcome: AttemptOutcome
    artifact_ids: tuple[str, ...]
    diagnostics: tuple[str, ...]
    model_calls: int
    input_tokens: ReportedInt
    output_tokens: ReportedInt
    cost_usd: ReportedCost
    solver_calls: int
    wall_time_ms: int

    def __post_init__(self) -> None:
        if not self.attempt_id or not self.candidate_id or self.attempt_number <= 0:
            raise ValidationError("attempt identifiers and positive attempt_number are required")
        for resource_value in (self.model_calls, self.solver_calls, self.wall_time_ms):
            if resource_value < 0:
                raise ValidationError("attempt resource observations must not be negative")
        for token_value in (self.input_tokens, self.output_tokens):
            if token_value != "unreported" and token_value < 0:
                raise ValidationError("attempt token observations must not be negative")
        if self.cost_usd != "unreported" and self.cost_usd < 0:
            raise ValidationError("attempt cost observation must not be negative")


@dataclass(frozen=True, slots=True)
class CandidateLedger:
    candidates: tuple[CandidateRevision, ...]
    attempts: tuple[AttemptRecord, ...]

    def __post_init__(self) -> None:
        candidate_ids = [candidate.id for candidate in self.candidates]
        attempt_ids = [attempt.attempt_id for attempt in self.attempts]
        if len(candidate_ids) != len(set(candidate_ids)):
            raise ValidationError("candidate ledger contains duplicate candidate IDs")
        if len(attempt_ids) != len(set(attempt_ids)):
            raise ValidationError("candidate ledger contains duplicate attempt IDs")
        known = set(candidate_ids)
        unknown = {attempt.candidate_id for attempt in self.attempts} - known
        if unknown:
            raise ValidationError(f"attempts reference unknown candidates {sorted(unknown)}")
        for candidate in self.candidates:
            _validate_attempt_budget(candidate, self.for_candidate(candidate.id))

    def for_candidate(self, candidate_id: str) -> tuple[AttemptRecord, ...]:
        return tuple(
            sorted(
                (attempt for attempt in self.attempts if attempt.candidate_id == candidate_id),
                key=lambda attempt: attempt.attempt_number,
            )
        )

    def append(self, attempt: AttemptRecord) -> CandidateLedger:
        return CandidateLedger(self.candidates, (*self.attempts, attempt))


@dataclass(frozen=True, slots=True)
class CandidateProblem:
    spec: CompatibilitySpec | EntailmentSpec
    selected_group_ids: tuple[str, ...]
    parent_problem_id: str
    candidate_id: str


@dataclass(frozen=True, slots=True)
class FormalizationGuardReport:
    base_problem_id: str
    prose_preserves_problem_id: bool
    unused_alias_preserves_problem_id: bool
    welfare_edit_changes_identity: bool
    comparison_symbol_edit_changes_identity: bool
    proof_step_edit_rejected: bool


def apply_candidate(parent: CompatibilitySpec, candidate: CandidateRevision) -> CandidateProblem:
    parent_problem_id = problem_id_for(parent)
    if parent_problem_id not in candidate.provenance.parent_problem_ids:
        raise ValidationError(
            f"candidate {candidate.id!r} does not name frozen parent {parent_problem_id}"
        )
    known_groups = {group.id for group in parent.groups}
    unknown_groups = (set(candidate.add_groups) | set(candidate.remove_groups)) - known_groups
    if unknown_groups:
        raise ValidationError(
            f"candidate {candidate.id!r} references unknown groups {sorted(unknown_groups)}"
        )
    if candidate.new_constraints and candidate.provenance.review_status == "machine-checked":
        raise ValidationError(
            "new source formulas cannot become machine-checked without human fidelity review"
        )

    common = _revised_common(parent.common, candidate)
    groups = list(parent.groups)
    candidate_group_id: str | None = None
    if candidate.new_constraints:
        candidate_group_id = f"candidate:{candidate.id}"
        groups.append(ConstraintGroup(candidate_group_id, "candidate", candidate.new_constraints))
    selected = set((*parent.fixed_group_ids, *parent.candidate_group_ids))
    selected -= set(candidate.remove_groups)
    selected |= set(candidate.add_groups)
    if candidate_group_id is not None:
        selected.add(candidate_group_id)
    ordered_selected = tuple(group.id for group in groups if group.id in selected)

    if candidate.goal is not None:
        spec: CompatibilitySpec | EntailmentSpec = EntailmentSpec(
            common,
            tuple(groups),
            ordered_selected,
            candidate.goal,
        )
    else:
        fixed = parent.fixed_group_ids
        selectable = tuple(group.id for group in groups if group.id not in set(fixed))
        spec = CompatibilitySpec(
            common,
            tuple(groups),
            fixed,
            selectable,
            None,
            (),
            None,
        )
    validate_experiment(spec)
    return CandidateProblem(spec, ordered_selected, parent_problem_id, candidate.id)


def _revised_common(common: ExperimentCommon, candidate: CandidateRevision) -> ExperimentCommon:
    domain = candidate.domain_revision or common.domain
    universe = build_population_universe(domain, common.resource_policy)
    witnesses = dict(common.witness_bindings)
    witnesses.update(candidate.witness_overrides)
    return replace(
        common,
        domain=domain,
        universe=universe,
        witness_bindings=witnesses,
    )


def _validate_attempt_budget(
    candidate: CandidateRevision, attempts: Sequence[AttemptRecord]
) -> None:
    llm = candidate.provenance.llm
    if llm is None:
        return
    if len(attempts) > llm.model_call_budget:
        raise ValidationError(f"candidate {candidate.id!r} exceeds its model-call budget")
    model_calls = sum(attempt.model_calls for attempt in attempts)
    solver_calls = sum(attempt.solver_calls for attempt in attempts)
    wall_time = sum(attempt.wall_time_ms for attempt in attempts)
    if model_calls > llm.model_call_budget:
        raise ValidationError(f"candidate {candidate.id!r} exceeds its model-call budget")
    if solver_calls > llm.solver_call_budget:
        raise ValidationError(f"candidate {candidate.id!r} exceeds its solver-call budget")
    if wall_time > llm.wall_time_budget_ms:
        raise ValidationError(f"candidate {candidate.id!r} exceeds its wall-time budget")
    token_values = [
        value for attempt in attempts for value in (attempt.input_tokens, attempt.output_tokens)
    ]
    if (
        all(value != "unreported" for value in token_values)
        and sum(value for value in token_values if isinstance(value, int)) > llm.token_budget
    ):
        raise ValidationError(f"candidate {candidate.id!r} exceeds its token budget")
    costs = [attempt.cost_usd for attempt in attempts]
    if all(cost != "unreported" for cost in costs):
        total_cost = sum((cost for cost in costs if isinstance(cost, Fraction)), start=Fraction())
        if total_cost > llm.usd_budget:
            raise ValidationError(f"candidate {candidate.id!r} exceeds its USD budget")


def promotable_evidence(evidence: Sequence[Evidence]) -> tuple[Evidence, ...]:
    return tuple(
        item for item in evidence if isinstance(item, (CheckedModelEvidence, CheckedProofEvidence))
    )


def run_formalization_guard_probes(spec: ExperimentSpec) -> FormalizationGuardReport:
    base_id = problem_id_for(spec)
    prose_common = replace(
        spec.common,
        source_fidelity=spec.common.source_fidelity + " (guard-probe paraphrase)",
    )
    prose_spec = replace(spec, common=prose_common)
    prose_preserves = problem_id_for(prose_spec) == base_id

    alias_preserves = True
    if spec.common.universe.populations:
        profile = spec.common.universe.populations[0]
        names = dict(spec.common.universe.names)
        names["guard_probe_unused_alias"] = profile
        aliases = dict(spec.common.universe.aliases)
        aliases[profile] = tuple(sorted((*aliases.get(profile, ()), "guard_probe_unused_alias")))
        alias_universe = PopulationUniverse(
            spec.common.universe.populations,
            names,
            aliases,
            spec.common.universe.usage,
        )
        alias_spec = replace(spec, common=replace(spec.common, universe=alias_universe))
        alias_preserves = problem_id_for(alias_spec) == base_id

    normalized = normalized_problem(spec)
    welfare_mutation = copy.deepcopy(normalized)
    domain = welfare_mutation["domain"]
    welfare_changed = False
    if isinstance(domain, list):
        for population in domain:
            if isinstance(population, list) and population:
                population[0] += 1
                welfare_changed = True
                break
    welfare_identity_changes = welfare_changed and content_id(welfare_mutation) != base_id

    symbol_mutation = copy.deepcopy(normalized)
    symbol_changed = _replace_first_relation(symbol_mutation)
    symbol_identity_changes = symbol_changed and content_id(symbol_mutation) != base_id

    proof_step_rejected = True
    if isinstance(spec, CompatibilitySpec) and spec.proof_builder == "arrhenius-2000/v1":
        constraints = {
            constraint.id: constraint for group in spec.groups for constraint in group.constraints
        }
        certificate = curated_arrhenius_certificate(base_id)
        corrupted_nodes = list(certificate.nodes)
        corrupted_nodes[-1] = replace(
            corrupted_nodes[-1], premises=(corrupted_nodes[-1].premises[0],)
        )
        corrupted = replace(certificate, nodes=tuple(corrupted_nodes))
        try:
            check_proof(corrupted, constraints, expected_problem_id=base_id)
        except ValidationError:
            proof_step_rejected = True
        else:
            proof_step_rejected = False

    return FormalizationGuardReport(
        base_id,
        prose_preserves,
        alias_preserves,
        welfare_identity_changes,
        symbol_identity_changes,
        proof_step_rejected,
    )


def _replace_first_relation(value: object) -> bool:
    if isinstance(value, dict):
        if value.get("relation") == "weak":
            value["relation"] = "strict"
            return True
        return any(_replace_first_relation(item) for item in value.values())
    if isinstance(value, list):
        return any(_replace_first_relation(item) for item in value)
    return False
