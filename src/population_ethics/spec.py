from __future__ import annotations

import hashlib
import json
import tomllib
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import asdict, dataclass, fields, is_dataclass, replace
from fractions import Fraction
from pathlib import Path
from typing import Literal, cast

from population_ethics.domain import (
    ExplicitDomainSpec,
    GeneratedDomainSpec,
    NamedPopulation,
    PopulationUniverse,
    ResourcePolicy,
    ValidationError,
    WelfareCategories,
    build_population_universe,
    parse_population,
    prospective_usage,
)
from population_ethics.principles import (
    GroundConstraint,
    compile_completeness,
    compile_reflexivity,
    compile_transitivity,
)
from population_ethics.relations import (
    And,
    BoolConstant,
    Formula,
    Implies,
    Not,
    Or,
    RelationAtom,
    assignment_from_data,
    assignment_to_data,
    collect_atoms,
    formula_from_data,
    formula_to_data,
)

SCHEMA = "population-ethics.experiment/v2"
RESULT_SCHEMA = "population-ethics.result/v2"

ClaimKind = Literal["pedagogical", "bounded-proof-instance", "bounded-search"]
ReviewStatus = Literal["proposed", "machine-checked", "human-approved", "rejected"]
CandidateOrigin = Literal["human", "enumerator", "llm"]
Decision = Literal["sat", "unsat", "unknown"]
EvidenceStrength = Literal["exact-evaluation", "checked-model", "solver-reported", "checked-proof"]
SideConditionKind = Literal[
    "cardinality-equal",
    "average-less",
    "integer-greater",
    "category-membership",
    "role-disjoint-union",
    "witness-binding",
]


def _check_keys(
    value: Mapping[str, object],
    allowed: set[str],
    *,
    required: set[str] | frozenset[str] = frozenset(),
    where: str,
) -> None:
    unknown = set(value) - allowed
    missing = required - set(value)
    if unknown or missing:
        raise ValidationError(
            f"{where} has unknown keys {sorted(unknown)} and missing keys {sorted(missing)}"
        )


def _mapping(value: object, *, where: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping) or any(not isinstance(key, str) for key in value):
        raise ValidationError(f"{where} must be a table/object")
    return cast(Mapping[str, object], value)


def _list(value: object, *, where: str) -> list[object]:
    if not isinstance(value, list):
        raise ValidationError(f"{where} must be a list")
    return value


def _string(value: object, *, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValidationError(f"{where} must be a non-empty string")
    return value


def _strings(value: object, *, where: str) -> tuple[str, ...]:
    result = tuple(_string(item, where=where) for item in _list(value, where=where))
    if len(set(result)) != len(result):
        raise ValidationError(f"{where} must not contain duplicates")
    return result


def _integer(value: object, *, where: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValidationError(f"{where} must be an integer")
    return value


def _optional_string(value: object, *, where: str) -> str | None:
    if value is None:
        return None
    return _string(value, where=where)


def parse_fraction(value: object, *, where: str) -> Fraction:
    if isinstance(value, bool):
        raise ValidationError(f"{where} must be an exact rational")
    if isinstance(value, int):
        return Fraction(value)
    table = _mapping(value, where=where)
    _check_keys(
        table, {"numerator", "denominator"}, required={"numerator", "denominator"}, where=where
    )
    numerator = _integer(table["numerator"], where=f"{where}.numerator")
    denominator = _integer(table["denominator"], where=f"{where}.denominator")
    if denominator == 0:
        raise ValidationError(f"{where}.denominator must not be zero")
    return Fraction(numerator, denominator)


@dataclass(frozen=True, slots=True)
class EvaluatorSpec:
    id: str
    theory: Literal["total", "average", "critical-level"]
    critical_level: Fraction | None = None


@dataclass(frozen=True, slots=True)
class ComparisonSpec:
    id: str
    left: str
    right: str
    evaluators: tuple[EvaluatorSpec, ...]


@dataclass(frozen=True, slots=True)
class ConstraintGroup:
    id: str
    principle_id: str
    constraints: tuple[GroundConstraint, ...]


@dataclass(frozen=True, slots=True)
class LLMMetadata:
    provider: str
    model: str

    version: str
    prompt_template_hash: str
    prompt_hash: str
    response_hash: str
    sampling_settings: Mapping[str, str | int]
    exposed_source_ids: tuple[str, ...]
    exposed_premise_ids: tuple[str, ...]
    model_call_budget: int
    token_budget: int
    usd_budget: Fraction
    solver_call_budget: int
    wall_time_budget_ms: int
    reported_input_tokens: int | Literal["unreported"]
    reported_output_tokens: int | Literal["unreported"]
    reported_cost_usd: Fraction | Literal["unreported"]

    def __post_init__(self) -> None:
        integer_budgets = (
            self.model_call_budget,
            self.token_budget,
            self.solver_call_budget,
            self.wall_time_budget_ms,
        )
        if any(value < 0 for value in integer_budgets) or self.usd_budget < 0:
            raise ValidationError("LLM experiment budgets must not be negative")
        for value in (self.reported_input_tokens, self.reported_output_tokens):
            if value != "unreported" and value < 0:
                raise ValidationError("reported token usage must not be negative")
        if self.reported_cost_usd != "unreported" and self.reported_cost_usd < 0:
            raise ValidationError("reported cost must not be negative")


@dataclass(frozen=True, slots=True)
class CandidateProvenance:
    origin: CandidateOrigin
    parent_problem_ids: tuple[str, ...]
    operation: str
    rationale: str
    review_status: ReviewStatus
    generator: str
    exposed_artifact_ids: tuple[str, ...]
    corpus_hash: str
    llm: LLMMetadata | None = None

    def __post_init__(self) -> None:
        if not self.parent_problem_ids:
            raise ValidationError("candidate provenance requires at least one parent problem")
        if not self.operation or not self.rationale or not self.generator or not self.corpus_hash:
            raise ValidationError("candidate provenance text and hashes must be non-empty")


@dataclass(frozen=True, slots=True)
class CandidateRevision:
    id: str
    add_groups: tuple[str, ...]
    remove_groups: tuple[str, ...]
    domain_revision: GeneratedDomainSpec | ExplicitDomainSpec | None
    witness_overrides: Mapping[str, int]
    goal: Formula | None
    new_constraints: tuple[GroundConstraint, ...]
    provenance: CandidateProvenance

    def __post_init__(self) -> None:
        if not self.id:
            raise ValidationError("candidate revision ID must be non-empty")
        if set(self.add_groups) & set(self.remove_groups):
            raise ValidationError("candidate cannot add and remove the same group")


@dataclass(frozen=True, slots=True)
class EvaluationMode:
    kind: Literal["reproduction", "blind-rediscovery", "discovery"]
    target_manifest_hash: str
    source_access: bool
    proof_access: bool
    exposed_artifact_ids: tuple[str, ...]
    partition_family: str
    contamination: Literal["unknown", "known"]
    novelty: Literal["not-applicable", "novel-to-frozen-corpus", "human-reviewed"]


@dataclass(frozen=True, slots=True)
class SideCondition:
    id: str
    kind: SideConditionKind
    data: Mapping[str, object]


@dataclass(frozen=True, slots=True)
class ExperimentCommon:
    id: str
    claim_kind: ClaimKind
    source_fidelity: str
    source_ids: tuple[str, ...]
    formalization_id: str
    domain: GeneratedDomainSpec | ExplicitDomainSpec
    universe: PopulationUniverse
    categories: WelfareCategories | None
    resource_policy: ResourcePolicy
    role_bindings: Mapping[str, str]
    witness_bindings: Mapping[str, int]
    side_conditions: tuple[SideCondition, ...]
    evaluation_mode: EvaluationMode
    candidates: tuple[CandidateRevision, ...]


@dataclass(frozen=True, slots=True)
class EvaluationSpec:
    common: ExperimentCommon
    comparisons: tuple[ComparisonSpec, ...]


@dataclass(frozen=True, slots=True)
class CompatibilitySpec:
    common: ExperimentCommon
    groups: tuple[ConstraintGroup, ...]
    fixed_group_ids: tuple[str, ...]
    candidate_group_ids: tuple[str, ...]
    proof_builder: str | None
    proof_nodes: tuple[Mapping[str, object], ...]
    proof_root: str | None


@dataclass(frozen=True, slots=True)
class EntailmentSpec:
    common: ExperimentCommon
    groups: tuple[ConstraintGroup, ...]
    selected_group_ids: tuple[str, ...]
    goal: Formula


@dataclass(frozen=True, slots=True)
class FrontierSpec:
    common: ExperimentCommon
    groups: tuple[ConstraintGroup, ...]
    fixed_group_ids: tuple[str, ...]
    candidate_group_ids: tuple[str, ...]


type ExperimentSpec = EvaluationSpec | CompatibilitySpec | EntailmentSpec | FrontierSpec


@dataclass(frozen=True, slots=True)
class ExactEvaluationEvidence:
    comparison_id: str
    scores: Mapping[str, tuple[Fraction, Fraction]]
    rankings: Mapping[str, Literal["left", "right", "tie"]]
    strength: EvidenceStrength = "exact-evaluation"


@dataclass(frozen=True, slots=True)
class CheckedModelEvidence:
    assignment: Mapping[RelationAtom, bool]
    checked_constraint_ids: tuple[str, ...]
    grounded_input: tuple[Mapping[str, object], ...]
    strength: EvidenceStrength = "checked-model"


@dataclass(frozen=True, slots=True)
class SolverReportEvidence:
    decision: Decision
    grounded_input: tuple[Mapping[str, object], ...]
    raw_core: tuple[str, ...]
    grounded_core: tuple[str, ...]
    minimality: Literal["verified", "unresolved", "not-applicable"]
    unresolved_obligations: tuple[str, ...]
    reason_unknown: str | None = None
    trace: tuple[str, ...] = ()
    strength: EvidenceStrength = "solver-reported"


@dataclass(frozen=True, slots=True)
class CheckedProofEvidence:
    certificate: Mapping[str, object]
    checker_version: str
    strength: EvidenceStrength = "checked-proof"


type Evidence = (
    ExactEvaluationEvidence | CheckedModelEvidence | SolverReportEvidence | CheckedProofEvidence
)


@dataclass(frozen=True, slots=True)
class RunRecord:
    schema: Literal["population-ethics.result/v2"]
    artifact_id: str
    problem_id: str
    run_key: str
    experiment_id: str
    claim_kind: ClaimKind
    source_fidelity: str
    normalized_problem: Mapping[str, object]
    execution_configuration: Mapping[str, object]
    usage_observations: Mapping[str, object]
    outcome: Mapping[str, object]
    unresolved_obligations: tuple[str, ...]
    evidence: tuple[Evidence, ...]
    provenance: CandidateProvenance | None = None


COMMON_KEYS = {
    "schema",
    "id",
    "kind",
    "claim_kind",
    "source_fidelity",
    "source_ids",
    "formalization_id",
    "domain",
    "categories",
    "resource_policy",
    "role_bindings",
    "witness_bindings",
    "side_conditions",
    "evaluation_mode",
    "candidates",
}


def load_experiment(path: str | Path) -> ExperimentSpec:
    with Path(path).open("rb") as stream:
        raw = tomllib.load(stream)
    if raw.get("schema") != SCHEMA:
        raise ValidationError(f"unsupported experiment schema {raw.get('schema')!r}")
    kind = raw.get("kind")
    kind_keys = {
        "evaluation": {"comparisons"},
        "compatibility": {"groups", "fixed_groups", "candidate_groups", "proof"},
        "entailment": {"groups", "selected_groups", "goal"},
        "frontier": {"groups", "fixed_groups", "candidate_groups"},
    }
    if kind not in kind_keys:
        raise ValidationError(f"unsupported experiment kind {kind!r}")
    _check_keys(
        raw,
        COMMON_KEYS | kind_keys[cast(str, kind)],
        required={"schema", "id", "kind", "claim_kind", "source_fidelity", "domain"},
        where="experiment",
    )
    common = _parse_common(raw)
    if kind == "evaluation":
        comparisons = tuple(
            _parse_comparison(item, index)
            for index, item in enumerate(_list(raw["comparisons"], where="comparisons"))
        )
        _unique_ids((item.id for item in comparisons), where="comparison")
        return _validate_experiment(EvaluationSpec(common, comparisons))

    groups = tuple(
        _parse_group(item, index) for index, item in enumerate(_list(raw["groups"], where="groups"))
    )
    group_ids = {group.id for group in groups}
    if len(group_ids) != len(groups):
        raise ValidationError("group IDs must be unique")
    if kind == "entailment":
        selected = _strings(raw["selected_groups"], where="selected_groups")
        _known_ids(selected, group_ids, where="selected_groups")
        return _validate_experiment(
            EntailmentSpec(common, groups, selected, formula_from_data(raw["goal"]))
        )
    fixed = _strings(raw["fixed_groups"], where="fixed_groups")
    candidate = _strings(raw["candidate_groups"], where="candidate_groups")
    _known_ids((*fixed, *candidate), group_ids, where="group partition")
    if set(fixed) & set(candidate):
        raise ValidationError("fixed and candidate groups must be disjoint")
    if set(fixed) | set(candidate) != group_ids:
        raise ValidationError("fixed and candidate groups must partition every group")
    if kind == "frontier":
        return _validate_experiment(FrontierSpec(common, groups, fixed, candidate))
    proof_builder, proof_nodes, proof_root = _parse_proof(raw.get("proof"))
    return _validate_experiment(
        CompatibilitySpec(
            common,
            groups,
            fixed,
            candidate,
            proof_builder,
            proof_nodes,
            proof_root,
        )
    )


def _validate_experiment(spec: ExperimentSpec) -> ExperimentSpec:
    known_names = set(spec.common.universe.names)
    if known_names:
        unknown_roles = set(spec.common.role_bindings.values()) - known_names
        if unknown_roles:
            raise ValidationError(
                f"role_bindings reference unknown populations {sorted(unknown_roles)}"
            )
    _validate_side_conditions(spec.common)
    if isinstance(spec, EvaluationSpec):
        for comparison in spec.comparisons:
            if known_names and ({comparison.left, comparison.right} - known_names):
                raise ValidationError(
                    f"comparison {comparison.id!r} references an unknown population"
                )
    else:
        constraints = [constraint for group in spec.groups for constraint in group.constraints]
        constraint_ids = [constraint.id for constraint in constraints]
        if len(constraint_ids) != len(set(constraint_ids)):
            raise ValidationError("ground constraint IDs must be globally unique")
        formula_encodings: dict[str, str] = {}
        for group in spec.groups:
            for constraint in group.constraints:
                unknown_populations = set(constraint.populations) - known_names
                unknown_endpoints = {
                    endpoint
                    for atom in collect_atoms(constraint.formula)
                    for endpoint in (atom.left, atom.right)
                    if endpoint not in known_names
                }
                if known_names and (unknown_populations or unknown_endpoints):
                    unknown = sorted(unknown_populations | unknown_endpoints)
                    raise ValidationError(
                        f"constraint {constraint.id!r} references unknown populations {unknown}"
                    )
                encoding = json.dumps(
                    _formula_problem_data(constraint.formula, spec.common),
                    sort_keys=True,
                    separators=(",", ":"),
                )
                previous = formula_encodings.get(encoding)
                if previous is not None and previous != group.id:
                    raise ValidationError(
                        f"identical formula occurs in groups {previous!r} and {group.id!r}"
                    )
                formula_encodings[encoding] = group.id
        if isinstance(spec, EntailmentSpec) and known_names:
            unknown_goal = {
                endpoint
                for atom in collect_atoms(spec.goal)
                for endpoint in (atom.left, atom.right)
                if endpoint not in known_names
            }
            if unknown_goal:
                raise ValidationError(f"goal references unknown populations {sorted(unknown_goal)}")
    for candidate in spec.common.candidates:
        if set(candidate.add_groups) & set(candidate.remove_groups):
            raise ValidationError(
                f"candidate {candidate.id!r} cannot add and remove the same group"
            )
    formula_count = len(formulas_in(spec))
    usage = prospective_usage(
        spec.common.domain,
        relation_atoms=len(all_atoms(spec)),
        ground_constraints=formula_count,
    )
    spec.common.resource_policy.preflight(usage)
    return spec


def validate_experiment(spec: ExperimentSpec) -> ExperimentSpec:
    return _validate_experiment(spec)


def _validate_side_conditions(common: ExperimentCommon) -> None:
    names = common.universe.names
    explicit_entries = (
        {entry.name: entry for entry in common.domain.populations}
        if isinstance(common.domain, ExplicitDomainSpec)
        else {}
    )
    for condition in common.side_conditions:
        data = _mapping(condition.data, where=f"side condition {condition.id}")
        if condition.kind == "cardinality-equal":
            _check_keys(
                data,
                {"populations", "expected"},
                required={"populations", "expected"},
                where=condition.id,
            )
            populations = _strings(data["populations"], where=f"{condition.id}.populations")
            expected = _integer(data["expected"], where=f"{condition.id}.expected")
            for population in populations:
                if population not in names or len(names[population]) != expected:
                    actual = len(names[population]) if population in names else "unknown"
                    raise ValidationError(
                        f"{condition.id} expected |{population}|={expected}, found {actual}"
                    )
        elif condition.kind == "average-less":
            _check_keys(
                data,
                {"population", "expected", "bound"},
                required={"population", "expected", "bound"},
                where=condition.id,
            )
            population = _string(data["population"], where=f"{condition.id}.population")
            if population not in names or not names[population]:
                raise ValidationError(f"{condition.id} requires a known nonempty population")
            actual_average = Fraction(sum(names[population]), len(names[population]))
            expected_average = parse_fraction(data["expected"], where=f"{condition.id}.expected")
            bound = parse_fraction(data["bound"], where=f"{condition.id}.bound")
            if actual_average != expected_average or not actual_average < bound:
                raise ValidationError(
                    f"{condition.id} expected average {expected_average} < {bound}, "
                    f"found {actual_average}"
                )
        elif condition.kind == "integer-greater":
            _check_keys(data, {"left", "right"}, required={"left", "right"}, where=condition.id)
            left = _integer(data["left"], where=f"{condition.id}.left")
            right = _integer(data["right"], where=f"{condition.id}.right")
            if left <= right:
                raise ValidationError(f"{condition.id} requires {left} > {right}")
        elif condition.kind == "category-membership":
            _check_keys(data, {"bindings"}, required={"bindings"}, where=condition.id)
            if common.categories is None:
                raise ValidationError(f"{condition.id} requires welfare categories")
            for index, raw_binding in enumerate(
                _list(data["bindings"], where=f"{condition.id}.bindings")
            ):
                binding = _mapping(raw_binding, where=f"{condition.id}.bindings[{index}]")
                _check_keys(
                    binding,
                    {"category", "welfare"},
                    required={"category", "welfare"},
                    where=f"{condition.id}.bindings[{index}]",
                )
                category = _string(
                    binding["category"], where=f"{condition.id}.bindings[{index}].category"
                )
                welfare = _integer(
                    binding["welfare"], where=f"{condition.id}.bindings[{index}].welfare"
                )
                if not common.categories.contains(category, welfare):
                    raise ValidationError(
                        f"{condition.id} places welfare {welfare} outside {category!r}"
                    )
        elif condition.kind == "role-disjoint-union":
            _check_keys(data, {"composites"}, required={"composites"}, where=condition.id)
            composites = _strings(data["composites"], where=f"{condition.id}.composites")
            for composite in composites:
                entry = explicit_entries.get(composite)
                if entry is None or not entry.parts or len(entry.parts) != len(set(entry.parts)):
                    raise ValidationError(
                        f"{condition.id} requires {composite!r} to have distinct declared parts"
                    )
        elif condition.kind == "witness-binding":
            _check_keys(data, {"bindings"}, required={"bindings"}, where=condition.id)
            expected_bindings = _parse_integer_mapping(
                data["bindings"], where=f"{condition.id}.bindings"
            )
            if dict(expected_bindings) != dict(common.witness_bindings):
                raise ValidationError(
                    f"{condition.id} does not match the selected witness bindings"
                )


def _parse_common(raw: Mapping[str, object]) -> ExperimentCommon:
    claim_kind = raw["claim_kind"]
    if claim_kind not in {"pedagogical", "bounded-proof-instance", "bounded-search"}:
        raise ValidationError(f"unsupported claim kind {claim_kind!r}")
    domain = _parse_domain(raw["domain"])
    resource_policy = _parse_resource_policy(raw.get("resource_policy", {}))
    universe = build_population_universe(domain, resource_policy)
    categories = _parse_categories(raw.get("categories"))
    roles = _parse_string_mapping(raw.get("role_bindings", {}), where="role_bindings")
    witnesses = _parse_integer_mapping(raw.get("witness_bindings", {}), where="witness_bindings")
    side_conditions = tuple(
        _parse_side_condition(item, index)
        for index, item in enumerate(_list(raw.get("side_conditions", []), where="side_conditions"))
    )
    mode = _parse_evaluation_mode(raw.get("evaluation_mode"))
    candidates = tuple(
        _parse_candidate(item, index)
        for index, item in enumerate(_list(raw.get("candidates", []), where="candidates"))
    )
    return ExperimentCommon(
        id=_string(raw["id"], where="id"),
        claim_kind=claim_kind,
        source_fidelity=_string(raw["source_fidelity"], where="source_fidelity"),
        source_ids=_strings(raw.get("source_ids", []), where="source_ids"),
        formalization_id=_string(raw.get("formalization_id", "none"), where="formalization_id"),
        domain=domain,
        universe=universe,
        categories=categories,
        resource_policy=resource_policy,
        role_bindings=roles,
        witness_bindings=witnesses,
        side_conditions=side_conditions,
        evaluation_mode=mode,
        candidates=candidates,
    )


def _parse_domain(value: object) -> GeneratedDomainSpec | ExplicitDomainSpec:
    table = _mapping(value, where="domain")
    mode = table.get("mode")
    if mode == "generated":
        _check_keys(
            table,
            {"mode", "welfare_levels", "max_population_size"},
            required={"mode", "welfare_levels", "max_population_size"},
            where="domain",
        )
        levels = tuple(
            _integer(item, where="domain.welfare_levels")
            for item in _list(table["welfare_levels"], where="domain.welfare_levels")
        )
        return GeneratedDomainSpec(
            levels, _integer(table["max_population_size"], where="domain.max_population_size")
        )
    if mode != "explicit":
        raise ValidationError(f"unsupported domain mode {mode!r}")
    _check_keys(table, {"mode", "populations"}, required={"mode", "populations"}, where="domain")
    populations: list[NamedPopulation] = []
    for index, item in enumerate(_list(table["populations"], where="domain.populations")):
        entry = _mapping(item, where=f"domain.populations[{index}]")
        _check_keys(
            entry,
            {"name", "values", "groups", "parts"},
            required={"name"},
            where=f"domain.populations[{index}]",
        )
        if ("values" in entry) == ("groups" in entry):
            raise ValidationError(
                f"domain.populations[{index}] requires exactly one of values or groups"
            )
        encoded = entry.get("values", entry.get("groups"))
        populations.append(
            NamedPopulation(
                _string(entry["name"], where=f"domain.populations[{index}].name"),
                parse_population(encoded),
                _strings(entry.get("parts", []), where=f"domain.populations[{index}].parts"),
            )
        )
    return ExplicitDomainSpec(tuple(populations))


def _parse_resource_policy(value: object) -> ResourcePolicy:
    table = _mapping(value, where="resource_policy")
    allowed = {item.name for item in fields(ResourcePolicy)}
    _check_keys(table, allowed, where="resource_policy")
    defaults = ResourcePolicy()
    kwargs = {
        name: _integer(table.get(name, getattr(defaults, name)), where=f"resource_policy.{name}")
        for name in allowed
    }
    return ResourcePolicy(**kwargs)


def _parse_categories(value: object) -> WelfareCategories | None:
    if value is None:
        return None
    table = _mapping(value, where="categories")
    categories = {
        name: frozenset(
            _integer(item, where=f"categories.{name}")
            for item in _list(members, where=f"categories.{name}")
        )
        for name, members in table.items()
    }
    return WelfareCategories(categories)


def _parse_comparison(value: object, index: int) -> ComparisonSpec:
    table = _mapping(value, where=f"comparisons[{index}]")
    _check_keys(
        table,
        {"id", "left", "right", "evaluators"},
        required={"id", "left", "right", "evaluators"},
        where=f"comparisons[{index}]",
    )
    evaluators = tuple(
        _parse_evaluator(item, item_index)
        for item_index, item in enumerate(
            _list(table["evaluators"], where=f"comparisons[{index}].evaluators")
        )
    )
    _unique_ids((item.id for item in evaluators), where=f"comparisons[{index}] evaluator")
    return ComparisonSpec(
        _string(table["id"], where=f"comparisons[{index}].id"),
        _string(table["left"], where=f"comparisons[{index}].left"),
        _string(table["right"], where=f"comparisons[{index}].right"),
        evaluators,
    )


def _parse_evaluator(value: object, index: int) -> EvaluatorSpec:
    table = _mapping(value, where=f"evaluator[{index}]")
    _check_keys(
        table,
        {"id", "theory", "critical_level"},
        required={"id", "theory"},
        where=f"evaluator[{index}]",
    )
    theory = table["theory"]
    if theory not in {"total", "average", "critical-level"}:
        raise ValidationError(f"unsupported evaluator theory {theory!r}")
    critical = (
        parse_fraction(table["critical_level"], where="critical_level")
        if "critical_level" in table
        else None
    )
    if (theory == "critical-level") != (critical is not None):
        raise ValidationError("critical-level evaluator alone requires critical_level")
    return EvaluatorSpec(
        _string(table["id"], where="evaluator.id"),
        theory,
        critical,
    )


def _parse_group(value: object, index: int) -> ConstraintGroup:
    table = _mapping(value, where=f"groups[{index}]")
    _check_keys(
        table,
        {"id", "principle_id", "constraints", "compiler", "populations"},
        required={"id", "principle_id"},
        where=f"groups[{index}]",
    )
    explicit = "constraints" in table
    compiled = "compiler" in table or "populations" in table
    if explicit == compiled:
        raise ValidationError(
            f"groups[{index}] requires either constraints or compiler with populations"
        )
    group_id = _string(table["id"], where=f"groups[{index}].id")
    principle_id = _string(table["principle_id"], where=f"groups[{index}].principle_id")
    if explicit:
        constraints = tuple(
            _parse_constraint(item, item_index, principle_id)
            for item_index, item in enumerate(
                _list(table["constraints"], where=f"groups[{index}].constraints")
            )
        )
    else:
        if "compiler" not in table or "populations" not in table:
            raise ValidationError(
                f"groups[{index}] compiler and populations must be supplied together"
            )
        compiler_id = _string(table["compiler"], where=f"groups[{index}].compiler")
        compilers = {
            "reflexivity": compile_reflexivity,
            "transitivity": compile_transitivity,
            "completeness": compile_completeness,
        }
        if compiler_id not in compilers:
            raise ValidationError(f"unsupported principle compiler {compiler_id!r}")
        if principle_id != compiler_id:
            raise ValidationError("compiled group principle_id must equal its compiler")
        populations = _strings(table["populations"], where=f"groups[{index}].populations")
        constraints = compilers[compiler_id](populations)
    _unique_ids((item.id for item in constraints), where=f"group {group_id} constraint")
    return ConstraintGroup(group_id, principle_id, constraints)


def _parse_constraint(value: object, index: int, principle_id: str) -> GroundConstraint:
    table = _mapping(value, where=f"constraint[{index}]")
    _check_keys(
        table,
        {
            "id",
            "formula",
            "populations",
            "source_locator",
            "formalization_id",
            "explanation",
        },
        required={"id", "formula", "populations", "formalization_id", "explanation"},
        where=f"constraint[{index}]",
    )
    return GroundConstraint(
        id=_string(table["id"], where="constraint.id"),
        principle_id=principle_id,
        formula=formula_from_data(table["formula"]),
        populations=_strings(table["populations"], where="constraint.populations"),
        source_locator=_optional_string(table.get("source_locator"), where="source_locator"),
        formalization_id=_string(table["formalization_id"], where="formalization_id"),
        explanation=_string(table["explanation"], where="explanation"),
    )


def _parse_side_condition(value: object, index: int) -> SideCondition:
    table = _mapping(value, where=f"side_conditions[{index}]")
    _check_keys(
        table,
        {"id", "kind", "data"},
        required={"id", "kind", "data"},
        where=f"side_conditions[{index}]",
    )
    kind = table["kind"]
    kinds = {
        "cardinality-equal",
        "average-less",
        "integer-greater",
        "category-membership",
        "role-disjoint-union",
        "witness-binding",
    }
    if kind not in kinds:
        raise ValidationError(f"unsupported side condition kind {kind!r}")
    return SideCondition(
        _string(table["id"], where="side_condition.id"),
        cast(SideConditionKind, kind),
        dict(_mapping(table["data"], where="side_condition.data")),
    )


def _parse_proof(
    value: object,
) -> tuple[str | None, tuple[Mapping[str, object], ...], str | None]:
    if value is None:
        return None, (), None
    table = _mapping(value, where="proof")
    _check_keys(table, {"builder", "root", "nodes"}, where="proof")
    if "builder" in table:
        if set(table) != {"builder"}:
            raise ValidationError("proof builder cannot be mixed with explicit proof nodes")
        builder = _string(table["builder"], where="proof.builder")
        if builder != "arrhenius-2000/v1":
            raise ValidationError(f"unsupported proof builder {builder!r}")
        return builder, (), None
    _check_keys(table, {"root", "nodes"}, required={"root", "nodes"}, where="proof")
    root = _string(table["root"], where="proof.root")
    nodes: list[Mapping[str, object]] = []
    for index, item in enumerate(_list(table["nodes"], where="proof.nodes")):
        node = _mapping(item, where=f"proof.nodes[{index}]")
        _check_keys(
            node,
            {"id", "formula", "rule", "premises", "scope", "discharged_assumptions", "explanation"},
            required={
                "id",
                "formula",
                "rule",
                "premises",
                "scope",
                "discharged_assumptions",
                "explanation",
            },
            where=f"proof.nodes[{index}]",
        )
        nodes.append(dict(node))
    return None, tuple(nodes), root


def _parse_evaluation_mode(value: object) -> EvaluationMode:
    if value is None:
        return EvaluationMode(
            "reproduction", "unreported", True, True, (), "source", "unknown", "not-applicable"
        )
    table = _mapping(value, where="evaluation_mode")
    allowed = {
        "kind",
        "target_manifest_hash",
        "source_access",
        "proof_access",
        "exposed_artifact_ids",
        "partition_family",
        "contamination",
        "novelty",
    }
    _check_keys(table, allowed, required=allowed, where="evaluation_mode")
    kind = table["kind"]
    contamination = table["contamination"]
    novelty = table["novelty"]
    if kind not in {"reproduction", "blind-rediscovery", "discovery"}:
        raise ValidationError(f"unsupported evaluation mode {kind!r}")
    if contamination not in {"unknown", "known"}:
        raise ValidationError("contamination must be unknown or known")
    if novelty not in {"not-applicable", "novel-to-frozen-corpus", "human-reviewed"}:
        raise ValidationError(f"unsupported novelty label {novelty!r}")
    source_access = table["source_access"]
    proof_access = table["proof_access"]
    if not isinstance(source_access, bool) or not isinstance(proof_access, bool):
        raise ValidationError("evaluation mode access flags must be Boolean")
    if kind == "blind-rediscovery" and (source_access or proof_access):
        raise ValidationError("blind rediscovery cannot expose source or proof access")
    if kind == "discovery" and novelty == "not-applicable":
        raise ValidationError("discovery requires an explicit novelty decision")
    return EvaluationMode(
        kind,
        _string(table["target_manifest_hash"], where="target_manifest_hash"),
        source_access,
        proof_access,
        _strings(table["exposed_artifact_ids"], where="exposed_artifact_ids"),
        _string(table["partition_family"], where="partition_family"),
        contamination,
        novelty,
    )


def _parse_candidate(value: object, index: int) -> CandidateRevision:
    table = _mapping(value, where=f"candidates[{index}]")
    _check_keys(
        table,
        {
            "id",
            "add_groups",
            "remove_groups",
            "domain_revision",
            "witness_overrides",
            "goal",
            "new_constraints",
            "provenance",
        },
        required={"id", "provenance"},
        where=f"candidates[{index}]",
    )
    new_constraints = tuple(
        _parse_constraint(item, item_index, "candidate")
        for item_index, item in enumerate(
            _list(table.get("new_constraints", []), where="new_constraints")
        )
    )
    return CandidateRevision(
        _string(table["id"], where="candidate.id"),
        _strings(table.get("add_groups", []), where="candidate.add_groups"),
        _strings(table.get("remove_groups", []), where="candidate.remove_groups"),
        _parse_domain(table["domain_revision"]) if "domain_revision" in table else None,
        _parse_integer_mapping(table.get("witness_overrides", {}), where="witness_overrides"),
        formula_from_data(table["goal"]) if "goal" in table else None,
        new_constraints,
        _parse_provenance(table["provenance"]),
    )


def _parse_provenance(value: object) -> CandidateProvenance:
    table = _mapping(value, where="candidate.provenance")
    allowed = {
        "origin",
        "parent_problem_ids",
        "operation",
        "rationale",
        "review_status",
        "generator",
        "exposed_artifact_ids",
        "corpus_hash",
        "llm",
    }
    _check_keys(table, allowed, required=allowed - {"llm"}, where="candidate.provenance")
    origin, status = table["origin"], table["review_status"]
    if origin not in {"human", "enumerator", "llm"}:
        raise ValidationError(f"unsupported candidate origin {origin!r}")
    if status not in {"proposed", "machine-checked", "human-approved", "rejected"}:
        raise ValidationError(f"unsupported review status {status!r}")
    llm = _parse_llm(table["llm"]) if "llm" in table else None
    if (origin == "llm") != (llm is not None):
        raise ValidationError("LLM candidates require llm metadata, and other origins forbid it")
    return CandidateProvenance(
        origin,
        _strings(table["parent_problem_ids"], where="parent_problem_ids"),
        _string(table["operation"], where="operation"),
        _string(table["rationale"], where="rationale"),
        status,
        _string(table["generator"], where="generator"),
        _strings(table["exposed_artifact_ids"], where="exposed_artifact_ids"),
        _string(table["corpus_hash"], where="corpus_hash"),
        llm,
    )


def _parse_llm(value: object) -> LLMMetadata:
    table = _mapping(value, where="llm")
    allowed = {
        "provider",
        "model",
        "version",
        "prompt_template_hash",
        "prompt_hash",
        "response_hash",
        "sampling_settings",
        "exposed_source_ids",
        "exposed_premise_ids",
        "model_call_budget",
        "token_budget",
        "usd_budget",
        "solver_call_budget",
        "wall_time_budget_ms",
        "reported_input_tokens",
        "reported_output_tokens",
        "reported_cost_usd",
    }
    _check_keys(table, allowed, required=allowed, where="llm")
    sampling = _mapping(table["sampling_settings"], where="sampling_settings")
    if any(
        isinstance(item, float) or not isinstance(item, (str, int)) for item in sampling.values()
    ):
        raise ValidationError("sampling settings allow only strings and integers")
    return LLMMetadata(
        provider=_string(table["provider"], where="provider"),
        model=_string(table["model"], where="model"),
        version=_string(table["version"], where="version"),
        prompt_template_hash=_string(table["prompt_template_hash"], where="prompt_template_hash"),
        prompt_hash=_string(table["prompt_hash"], where="prompt_hash"),
        response_hash=_string(table["response_hash"], where="response_hash"),
        sampling_settings=cast(Mapping[str, str | int], dict(sampling)),
        exposed_source_ids=_strings(table["exposed_source_ids"], where="exposed_source_ids"),
        exposed_premise_ids=_strings(table["exposed_premise_ids"], where="exposed_premise_ids"),
        model_call_budget=_integer(table["model_call_budget"], where="model_call_budget"),
        token_budget=_integer(table["token_budget"], where="token_budget"),
        usd_budget=parse_fraction(table["usd_budget"], where="usd_budget"),
        solver_call_budget=_integer(table["solver_call_budget"], where="solver_call_budget"),
        wall_time_budget_ms=_integer(table["wall_time_budget_ms"], where="wall_time_budget_ms"),
        reported_input_tokens=_reported_integer(
            table["reported_input_tokens"], where="reported_input_tokens"
        ),
        reported_output_tokens=_reported_integer(
            table["reported_output_tokens"], where="reported_output_tokens"
        ),
        reported_cost_usd=(
            "unreported"
            if table["reported_cost_usd"] == "unreported"
            else parse_fraction(table["reported_cost_usd"], where="reported_cost_usd")
        ),
    )


def _reported_integer(value: object, *, where: str) -> int | Literal["unreported"]:
    if value == "unreported":
        return "unreported"
    return _integer(value, where=where)


def _parse_string_mapping(value: object, *, where: str) -> Mapping[str, str]:
    table = _mapping(value, where=where)
    return {key: _string(item, where=f"{where}.{key}") for key, item in table.items()}


def _parse_integer_mapping(value: object, *, where: str) -> Mapping[str, int]:
    table = _mapping(value, where=where)
    return {key: _integer(item, where=f"{where}.{key}") for key, item in table.items()}


def _unique_ids(values: Iterable[str], *, where: str) -> None:
    ids = tuple(values)
    if len(ids) != len(set(ids)):
        raise ValidationError(f"{where} IDs must be unique")


def _known_ids(values: Sequence[str], known: set[str], *, where: str) -> None:
    unknown = set(values) - known
    if unknown:
        raise ValidationError(f"{where} references unknown IDs {sorted(unknown)}")


def constraint_to_data(constraint: GroundConstraint) -> dict[str, object]:
    return {
        "id": constraint.id,
        "principle_id": constraint.principle_id,
        "formula": formula_to_data(constraint.formula),
        "populations": list(constraint.populations),
        "source_locator": constraint.source_locator,
        "formalization_id": constraint.formalization_id,
        "explanation": constraint.explanation,
    }


def constraint_from_data(value: object) -> GroundConstraint:
    table = _mapping(value, where="ground constraint")
    expected = {
        "id",
        "principle_id",
        "formula",
        "populations",
        "source_locator",
        "formalization_id",
        "explanation",
    }
    _check_keys(table, expected, required=expected, where="ground constraint")
    return GroundConstraint(
        id=_string(table["id"], where="ground constraint.id"),
        principle_id=_string(table["principle_id"], where="ground constraint.principle_id"),
        formula=formula_from_data(table["formula"]),
        populations=tuple(
            _string(item, where="ground constraint.populations")
            for item in _list(table["populations"], where="ground constraint.populations")
        ),
        source_locator=_optional_string(
            table["source_locator"], where="ground constraint.source_locator"
        ),
        formalization_id=_string(
            table["formalization_id"], where="ground constraint.formalization_id"
        ),
        explanation=_string(table["explanation"], where="ground constraint.explanation"),
    )


def _endpoint_problem_data(endpoint: str, common: ExperimentCommon) -> object:
    population = common.universe.names.get(endpoint)
    return {"population": list(population)} if population is not None else {"symbol": endpoint}


def _formula_problem_data(formula: Formula, common: ExperimentCommon) -> dict[str, object]:
    match formula:
        case RelationAtom(left=left, relation=relation, right=right):
            return {
                "kind": "atom",
                "left": _endpoint_problem_data(left, common),
                "relation": relation,
                "right": _endpoint_problem_data(right, common),
            }
        case BoolConstant(value=value):
            return {"kind": "constant", "value": value}
        case Not(operand=operand):
            return {"kind": "not", "operand": _formula_problem_data(operand, common)}
        case And(operands=operands):
            return {
                "kind": "and",
                "operands": [_formula_problem_data(item, common) for item in operands],
            }
        case Or(operands=operands):
            return {
                "kind": "or",
                "operands": [_formula_problem_data(item, common) for item in operands],
            }
        case Implies(antecedent=antecedent, consequent=consequent):
            return {
                "kind": "implies",
                "antecedent": _formula_problem_data(antecedent, common),
                "consequent": _formula_problem_data(consequent, common),
            }


def _group_problem_data(group: ConstraintGroup, common: ExperimentCommon) -> dict[str, object]:
    formulas = [_formula_problem_data(item.formula, common) for item in group.constraints]
    return {
        "principle_id": group.principle_id,
        "formulas": sorted(formulas, key=lambda item: canonical_bytes(item)),
    }


def normalized_problem(spec: ExperimentSpec) -> dict[str, object]:
    common = spec.common
    categories = (
        {name: sorted(values) for name, values in sorted(common.categories.values.items())}
        if common.categories
        else None
    )
    base: dict[str, object] = {
        "kind": type(spec).__name__,
        "domain": [list(population) for population in common.universe.populations],
        "categories": categories,
        "role_bindings": {
            role: _endpoint_problem_data(endpoint, common)
            for role, endpoint in sorted(common.role_bindings.items())
        },
        "witness_bindings": dict(sorted(common.witness_bindings.items())),
    }
    if isinstance(spec, EvaluationSpec):
        comparisons = [
            {
                "left": _endpoint_problem_data(item.left, common),
                "right": _endpoint_problem_data(item.right, common),
                "evaluators": sorted(
                    [
                        {
                            "theory": evaluator.theory,
                            "critical_level": evaluator.critical_level,
                        }
                        for evaluator in item.evaluators
                    ],
                    key=lambda evaluator: canonical_bytes(evaluator),
                ),
            }
            for item in spec.comparisons
        ]
        base["comparisons"] = sorted(
            comparisons, key=lambda comparison: canonical_bytes(comparison)
        )
        return base
    groups = {group.id: _group_problem_data(group, common) for group in spec.groups}
    group_tokens = {group_id: content_id(data) for group_id, data in groups.items()}
    base["groups"] = sorted(groups.values(), key=lambda group: canonical_bytes(group))
    if isinstance(spec, EntailmentSpec):
        base["selected_groups"] = sorted(
            group_tokens[group_id] for group_id in spec.selected_group_ids
        )
        base["goal"] = _formula_problem_data(spec.goal, common)
    else:
        base["fixed_groups"] = sorted(group_tokens[group_id] for group_id in spec.fixed_group_ids)
        base["candidate_groups"] = sorted(
            group_tokens[group_id] for group_id in spec.candidate_group_ids
        )
    return base


def canonical_data(value: object) -> object:
    if isinstance(value, Fraction):
        return {"numerator": value.numerator, "denominator": value.denominator}
    if isinstance(value, (RelationAtom, BoolConstant, Not, And, Or, Implies)):
        return formula_to_data(value)
    if is_dataclass(value) and not isinstance(value, type):
        return canonical_data(asdict(value))
    if isinstance(value, Mapping):
        if any(not isinstance(key, str) for key in value):
            raise ValidationError("canonical JSON keys must be strings")
        return {key: canonical_data(value[key]) for key in sorted(value)}
    if isinstance(value, (tuple, list)):
        return [canonical_data(item) for item in value]
    if isinstance(value, (set, frozenset)):
        canonical = [canonical_data(item) for item in value]
        return sorted(
            canonical, key=lambda item: json.dumps(item, sort_keys=True, separators=(",", ":"))
        )
    if isinstance(value, float):
        raise ValidationError("floating-point mathematical values are forbidden")
    if value is None or isinstance(value, (str, int, bool)):
        return value
    raise ValidationError(f"cannot canonicalize value of type {type(value).__name__}")


def canonical_bytes(value: object) -> bytes:
    return json.dumps(
        canonical_data(value), sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode()


def content_id(value: object) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def problem_id_for(spec: ExperimentSpec) -> str:
    return content_id(normalized_problem(spec))


def run_key_for(
    problem_id: str,
    *,
    selected_groups: Sequence[str],
    fixed_groups: Sequence[str],
    encoding_hash: str,
    lockfile_hash: str,
    solver_version: str,
    solver_configuration: Mapping[str, object],
    resource_policy: ResourcePolicy,
    minimization_policy: str,
    subset_order: Sequence[str],
) -> str:
    return content_id(
        {
            "problem_id": problem_id,
            "selected_groups": sorted(selected_groups),
            "fixed_groups": sorted(fixed_groups),
            "encoding_hash": encoding_hash,
            "lockfile_hash": lockfile_hash,
            "solver_version": solver_version,
            "solver_configuration": solver_configuration,
            "resource_policy": resource_policy,
            "minimization_policy": minimization_policy,
            "subset_order": list(subset_order),
        }
    )


def evidence_to_data(evidence: Evidence) -> dict[str, object]:
    if isinstance(evidence, ExactEvaluationEvidence):
        return {
            "kind": "exact-evaluation",
            "strength": evidence.strength,
            "comparison_id": evidence.comparison_id,
            "scores": evidence.scores,
            "rankings": evidence.rankings,
        }
    if isinstance(evidence, CheckedModelEvidence):
        return {
            "kind": "checked-model",
            "strength": evidence.strength,
            "assignment": assignment_to_data(evidence.assignment),
            "checked_constraint_ids": list(evidence.checked_constraint_ids),
            "grounded_input": list(evidence.grounded_input),
        }
    if isinstance(evidence, SolverReportEvidence):
        return {"kind": "solver-report", **asdict(evidence)}
    return {"kind": "checked-proof", **asdict(evidence)}


def provenance_to_data(provenance: CandidateProvenance) -> dict[str, object]:
    data: dict[str, object] = {
        "origin": provenance.origin,
        "parent_problem_ids": list(provenance.parent_problem_ids),
        "operation": provenance.operation,
        "rationale": provenance.rationale,
        "review_status": provenance.review_status,
        "generator": provenance.generator,
        "exposed_artifact_ids": list(provenance.exposed_artifact_ids),
        "corpus_hash": provenance.corpus_hash,
    }
    if provenance.llm is not None:
        data["llm"] = asdict(provenance.llm)
    return data


def run_record_to_data(record: RunRecord, *, include_artifact_id: bool = True) -> dict[str, object]:
    data: dict[str, object] = {
        "schema": record.schema,
        "problem_id": record.problem_id,
        "run_key": record.run_key,
        "experiment_id": record.experiment_id,
        "claim_kind": record.claim_kind,
        "source_fidelity": record.source_fidelity,
        "normalized_problem": record.normalized_problem,
        "execution_configuration": record.execution_configuration,
        "usage_observations": record.usage_observations,
        "outcome": record.outcome,
        "unresolved_obligations": list(record.unresolved_obligations),
        "evidence": [evidence_to_data(item) for item in record.evidence],
        "provenance": provenance_to_data(record.provenance) if record.provenance else None,
    }
    if include_artifact_id:
        data["artifact_id"] = record.artifact_id
    return cast(dict[str, object], canonical_data(data))


def seal_run_record(record: RunRecord) -> RunRecord:
    artifact_id = content_id(run_record_to_data(record, include_artifact_id=False))
    return replace(record, artifact_id=artifact_id)


def run_record_json(record: RunRecord) -> str:
    return (
        json.dumps(run_record_to_data(record), sort_keys=True, indent=2, ensure_ascii=False) + "\n"
    )


def load_run_record(path: str | Path) -> RunRecord:
    raw = json.loads(Path(path).read_text())
    table = _mapping(raw, where="result")
    allowed = {
        "schema",
        "artifact_id",
        "problem_id",
        "run_key",
        "experiment_id",
        "claim_kind",
        "source_fidelity",
        "normalized_problem",
        "execution_configuration",
        "usage_observations",
        "outcome",
        "unresolved_obligations",
        "evidence",
        "provenance",
    }
    _check_keys(table, allowed, required=allowed, where="result")
    if table["schema"] != RESULT_SCHEMA:
        raise ValidationError(f"unsupported result schema {table['schema']!r}")
    evidence = tuple(
        _evidence_from_data(item) for item in _list(table["evidence"], where="evidence")
    )
    claim_kind = table["claim_kind"]
    if claim_kind not in {"pedagogical", "bounded-proof-instance", "bounded-search"}:
        raise ValidationError(f"unsupported result claim kind {claim_kind!r}")
    provenance = _parse_provenance(table["provenance"]) if table["provenance"] is not None else None
    record = RunRecord(
        cast(Literal["population-ethics.result/v2"], RESULT_SCHEMA),
        _string(table["artifact_id"], where="artifact_id"),
        _string(table["problem_id"], where="problem_id"),
        _string(table["run_key"], where="run_key"),
        _string(table["experiment_id"], where="experiment_id"),
        claim_kind,
        _string(table["source_fidelity"], where="source_fidelity"),
        dict(_mapping(table["normalized_problem"], where="normalized_problem")),
        dict(_mapping(table["execution_configuration"], where="execution_configuration")),
        dict(_mapping(table["usage_observations"], where="usage_observations")),
        dict(_mapping(table["outcome"], where="outcome")),
        _strings(table["unresolved_obligations"], where="unresolved_obligations"),
        evidence,
        provenance,
    )
    expected = content_id(run_record_to_data(record, include_artifact_id=False))
    if expected != record.artifact_id:
        raise ValidationError(
            f"artifact hash mismatch: expected {expected}, found {record.artifact_id}"
        )
    return record


def _evidence_from_data(value: object) -> Evidence:
    table = _mapping(value, where="evidence entry")
    kind = table.get("kind")
    if kind == "checked-model":
        _check_keys(
            table,
            {
                "kind",
                "strength",
                "assignment",
                "checked_constraint_ids",
                "grounded_input",
            },
            required={
                "kind",
                "strength",
                "assignment",
                "checked_constraint_ids",
                "grounded_input",
            },
            where="checked-model evidence",
        )
        return CheckedModelEvidence(
            assignment_from_data(table["assignment"]),
            _strings(table["checked_constraint_ids"], where="checked_constraint_ids"),
            tuple(
                _mapping(item, where="grounded_input")
                for item in _list(table["grounded_input"], where="grounded_input")
            ),
        )
    if kind == "solver-report":
        allowed = {
            "kind",
            "strength",
            "decision",
            "grounded_input",
            "raw_core",
            "grounded_core",
            "minimality",
            "unresolved_obligations",
            "reason_unknown",
            "trace",
        }
        _check_keys(table, allowed, required=allowed, where="solver-report evidence")
        return SolverReportEvidence(
            cast(Decision, table["decision"]),
            tuple(
                _mapping(item, where="grounded_input")
                for item in _list(table["grounded_input"], where="grounded_input")
            ),
            _strings(table["raw_core"], where="raw_core"),
            _strings(table["grounded_core"], where="grounded_core"),
            cast(Literal["verified", "unresolved", "not-applicable"], table["minimality"]),
            _strings(table["unresolved_obligations"], where="unresolved_obligations"),
            _optional_string(table["reason_unknown"], where="reason_unknown"),
            _strings(table["trace"], where="trace"),
        )
    if kind == "checked-proof":
        _check_keys(
            table,
            {"kind", "strength", "certificate", "checker_version"},
            required={"kind", "strength", "certificate", "checker_version"},
            where="checked-proof evidence",
        )
        return CheckedProofEvidence(
            dict(_mapping(table["certificate"], where="certificate")),
            _string(table["checker_version"], where="checker_version"),
        )
    if kind == "exact-evaluation":
        _check_keys(
            table,
            {"kind", "strength", "comparison_id", "scores", "rankings"},
            required={"kind", "strength", "comparison_id", "scores", "rankings"},
            where="exact-evaluation evidence",
        )
        scores_table = _mapping(table["scores"], where="scores")
        scores = {
            key: (
                parse_fraction(_list(item, where=f"scores.{key}")[0], where=f"scores.{key}.left"),
                parse_fraction(_list(item, where=f"scores.{key}")[1], where=f"scores.{key}.right"),
            )
            for key, item in scores_table.items()
        }
        rankings = cast(
            Mapping[str, Literal["left", "right", "tie"]],
            dict(_mapping(table["rankings"], where="rankings")),
        )
        return ExactEvaluationEvidence(
            _string(table["comparison_id"], where="comparison_id"), scores, rankings
        )
    raise ValidationError(f"unknown evidence kind {kind!r}")


def formulas_in(spec: ExperimentSpec) -> tuple[Formula, ...]:
    if isinstance(spec, EvaluationSpec):
        return ()
    formulas = tuple(
        constraint.formula for group in spec.groups for constraint in group.constraints
    )
    return formulas + ((spec.goal,) if isinstance(spec, EntailmentSpec) else ())


def all_atoms(spec: ExperimentSpec) -> frozenset[RelationAtom]:
    atoms: set[RelationAtom] = set()
    for formula in formulas_in(spec):
        atoms.update(collect_atoms(formula))
    return frozenset(atoms)
