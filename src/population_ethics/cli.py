from __future__ import annotations

import hashlib
import json
import time
from dataclasses import asdict
from fractions import Fraction
from pathlib import Path
from typing import Annotated, Literal, cast

import typer

from population_ethics.domain import Population, ValidationError
from population_ethics.proofs import (
    CHECKER_VERSION,
    check_proof,
    curated_arrhenius_certificate,
    proof_certificate_from_data,
    proof_certificate_to_data,
)
from population_ethics.relations import evaluate_formula, formula_label
from population_ethics.spec import (
    RESULT_SCHEMA,
    CandidateProvenance,
    CheckedModelEvidence,
    CheckedProofEvidence,
    CompatibilitySpec,
    EntailmentSpec,
    EvaluationSpec,
    ExactEvaluationEvidence,
    ExperimentSpec,
    FrontierSpec,
    RunRecord,
    SolverReportEvidence,
    canonical_data,
    constraint_from_data,
    content_id,
    load_experiment,
    load_run_record,
    normalized_problem,
    parse_fraction,
    problem_id_for,
    run_key_for,
    run_record_json,
    seal_run_record,
)
from population_ethics.theories import average, critical_level, total

app = typer.Typer(no_args_is_help=True, pretty_exceptions_enable=False)
OutputFormat = Literal["text", "json"]
ExplainView = Literal["summary", "model", "core", "proof", "provenance"]
ScanUnit = Literal["principle", "instance"]

ExperimentPath = Annotated[
    Path,
    typer.Argument(exists=True, file_okay=True, dir_okay=False, readable=True),
]
ResultPath = Annotated[
    Path,
    typer.Argument(exists=True, file_okay=True, dir_okay=False, readable=True),
]


@app.command()
def run(
    experiment: ExperimentPath,
    output_format: Annotated[OutputFormat, typer.Option("--format")] = "text",
    output: Annotated[Path | None, typer.Option("--output")] = None,
) -> None:
    """Run one evaluation, compatibility, or entailment experiment."""
    try:
        record = _run_experiment(load_experiment(experiment))
        _emit_record(record, output_format, output)
    except (ValidationError, OSError, json.JSONDecodeError) as error:
        _fail(error)


@app.command()
def explain(
    result: ResultPath,
    view: Annotated[ExplainView, typer.Option("--view")] = "summary",
) -> None:
    """Render only evidence already stored in a result artifact."""
    try:
        record = load_run_record(result)
        typer.echo(_explain_text(record, view))
    except (ValidationError, OSError, json.JSONDecodeError) as error:
        _fail(error)


@app.command()
def verify(
    result: ResultPath,
    output_format: Annotated[OutputFormat, typer.Option("--format")] = "text",
) -> None:
    """Verify hashes and checkable evidence offline, without invoking Z3."""
    try:
        record = load_run_record(result)
        checks = _verify_record(record)
        if output_format == "json":
            typer.echo(
                json.dumps(
                    {
                        "artifact_id": record.artifact_id,
                        "scope": record.claim_kind,
                        "source_fidelity": record.source_fidelity,
                        "verified": True,
                        "checks": checks,
                    },
                    sort_keys=True,
                    indent=2,
                )
            )
        else:
            typer.echo(_labels(record))
            typer.echo("verification: accepted")
            for check in checks:
                typer.echo(f"check: {check}")
    except (ValidationError, OSError, json.JSONDecodeError) as error:
        _fail(error, prefix="verification failed")


@app.command()
def scan(
    experiment: ExperimentPath,
    unit: Annotated[ScanUnit, typer.Option("--unit")],
    max_subsets: Annotated[int | None, typer.Option("--max-subsets")] = None,
    output_format: Annotated[OutputFormat, typer.Option("--format")] = "text",
    output: Annotated[Path | None, typer.Option("--output")] = None,
) -> None:
    """Enumerate a complete bounded principle or instance frontier."""
    try:
        spec = load_experiment(experiment)
        if not isinstance(spec, (CompatibilitySpec, FrontierSpec)):
            raise ValidationError("scan requires a compatibility or frontier experiment")
        record = _scan_record(spec, unit, max_subsets)
        _emit_record(record, output_format, output)
    except (ValidationError, OSError, json.JSONDecodeError) as error:
        _fail(error)


def _run_experiment(spec: ExperimentSpec) -> RunRecord:
    started = time.monotonic_ns()
    problem_id = problem_id_for(spec)
    evidence: tuple[
        ExactEvaluationEvidence
        | CheckedModelEvidence
        | SolverReportEvidence
        | CheckedProofEvidence,
        ...,
    ]
    selected_groups: tuple[str, ...] = ()
    fixed_groups: tuple[str, ...] = ()
    solver_calls = 0
    unresolved: tuple[str, ...] = ()

    if isinstance(spec, EvaluationSpec):
        evidence = _evaluate(spec)
        outcome: dict[str, object] = {
            "kind": "evaluation",
            "rankings": {item.comparison_id: dict(item.rankings) for item in evidence},
        }
    elif isinstance(spec, CompatibilitySpec):
        from population_ethics.solver import solve_groups

        fixed_groups = spec.fixed_group_ids
        selected_groups = (*spec.fixed_group_ids, *spec.candidate_group_ids)
        solved = solve_groups(spec.groups, selected_groups, spec.common.resource_policy)
        solver_calls = solved.solver_calls
        unresolved = solved.unresolved_obligations
        evidence = cast(tuple[SolverReportEvidence | CheckedModelEvidence, ...], solved.evidence)
        if solved.decision == "unsat" and spec.proof_builder == "arrhenius-2000/v1":
            constraints = {
                constraint.id: constraint
                for group in spec.groups
                for constraint in group.constraints
            }
            certificate = curated_arrhenius_certificate(problem_id)
            check_proof(certificate, constraints, expected_problem_id=problem_id)
            evidence = (
                *evidence,
                CheckedProofEvidence(proof_certificate_to_data(certificate), CHECKER_VERSION),
            )
        outcome = {"kind": "compatibility", "decision": solved.decision}
    elif isinstance(spec, EntailmentSpec):
        from population_ethics.solver import solve_entailment

        selected_groups = spec.selected_group_ids
        solved_entailment = solve_entailment(spec)
        solver_calls = solved_entailment.solver_calls
        unresolved = solved_entailment.unresolved_obligations
        evidence = cast(
            tuple[SolverReportEvidence | CheckedModelEvidence, ...],
            solved_entailment.evidence,
        )
        outcome = {"kind": "entailment", "decision": solved_entailment.outcome}
    else:
        raise ValidationError("frontier experiments must be executed with scan")

    elapsed_ms = (time.monotonic_ns() - started) // 1_000_000
    execution = _execution_configuration(spec, solver_calls > 0)
    run_key = run_key_for(
        problem_id,
        selected_groups=selected_groups,
        fixed_groups=fixed_groups,
        encoding_hash=content_id(normalized_problem(spec)),
        lockfile_hash=cast(str, execution["lockfile_hash"]),
        solver_version=cast(str, execution["solver_version"]),
        solver_configuration=cast(dict[str, object], execution["solver_configuration"]),
        resource_policy=spec.common.resource_policy,
        minimization_policy="stable-full-set-deletion/v1",
        subset_order=(),
    )
    return seal_run_record(
        RunRecord(
            cast(Literal["population-ethics.result/v2"], RESULT_SCHEMA),
            "",
            problem_id,
            run_key,
            spec.common.id,
            spec.common.claim_kind,
            spec.common.source_fidelity,
            normalized_problem(spec),
            execution,
            {"solver_calls": solver_calls, "wall_time_ms": elapsed_ms},
            outcome,
            unresolved,
            evidence,
        )
    )


def _evaluate(spec: EvaluationSpec) -> tuple[ExactEvaluationEvidence, ...]:
    result: list[ExactEvaluationEvidence] = []
    for comparison in spec.comparisons:
        left = spec.common.universe.names[comparison.left]
        right = spec.common.universe.names[comparison.right]
        scores: dict[str, tuple[Fraction, Fraction]] = {}
        rankings: dict[str, Literal["left", "right", "tie"]] = {}
        for evaluator in comparison.evaluators:
            if evaluator.theory == "total":
                pair = (total(left), total(right))
            elif evaluator.theory == "average":
                pair = (average(left), average(right))
            else:
                assert evaluator.critical_level is not None
                pair = (
                    critical_level(left, evaluator.critical_level),
                    critical_level(right, evaluator.critical_level),
                )
            scores[evaluator.id] = pair
            rankings[evaluator.id] = _ranking(*pair)
        result.append(ExactEvaluationEvidence(comparison.id, scores, rankings))
    return tuple(result)


def _ranking(left: Fraction, right: Fraction) -> Literal["left", "right", "tie"]:
    if left > right:
        return "left"
    if right > left:
        return "right"
    return "tie"


def _execution_configuration(spec: ExperimentSpec, uses_solver: bool) -> dict[str, object]:
    if uses_solver:
        import z3  # type: ignore[import-untyped]

        solver_version = z3.get_version_string()
        solver_configuration: dict[str, object] = {
            "timeout_ms": spec.common.resource_policy.timeout_ms,
            "guard_encoding": "assumption-literals/v1",
        }
    else:
        solver_version = "not-used"
        solver_configuration = {}
    lockfile = Path("uv.lock")
    lockfile_hash = (
        hashlib.sha256(lockfile.read_bytes()).hexdigest() if lockfile.is_file() else "unavailable"
    )
    return {
        "encoding": "boolean-ir/v1",
        "lockfile_hash": lockfile_hash,
        "solver_version": solver_version,
        "solver_configuration": solver_configuration,
        "resource_policy": asdict(spec.common.resource_policy),
    }


def _scan_record(
    spec: CompatibilitySpec | FrontierSpec,
    unit: ScanUnit,
    max_subsets: int | None,
) -> RunRecord:
    from population_ethics.search import scan_frontier

    started = time.monotonic_ns()
    result = scan_frontier(spec, unit=unit, max_subsets=max_subsets)
    elapsed_ms = (time.monotonic_ns() - started) // 1_000_000
    dimensions = [
        {"id": dimension.id, "constraint_ids": list(dimension.constraint_ids)}
        for dimension in result.dimensions
    ]
    scan_problem = {
        "parent_problem_id": result.parent_problem_id,
        "frozen_problem": normalized_problem(spec),
        "unit": unit,
        "dimensions": dimensions,
    }
    problem_id = content_id(scan_problem)
    execution = _execution_configuration(spec, True)
    run_key = run_key_for(
        problem_id,
        selected_groups=spec.candidate_group_ids,
        fixed_groups=spec.fixed_group_ids,
        encoding_hash=content_id(scan_problem),
        lockfile_hash=cast(str, execution["lockfile_hash"]),
        solver_version=cast(str, execution["solver_version"]),
        solver_configuration=cast(dict[str, object], execution["solver_configuration"]),
        resource_policy=spec.common.resource_policy,
        minimization_policy="not-applicable",
        subset_order=tuple(dimension.id for dimension in result.dimensions),
    )
    outcome = {
        "kind": "frontier",
        "unit": unit,
        "parent_problem_id": result.parent_problem_id,
        "fixed_background_ids": list(result.fixed_group_ids),
        "classifications": [asdict(node) for node in result.nodes],
    }
    corpus_file = Path("corpus/sources.toml")
    corpus_hash = (
        hashlib.sha256(corpus_file.read_bytes()).hexdigest()
        if corpus_file.is_file()
        else "unavailable"
    )
    provenance = CandidateProvenance(
        "enumerator",
        (result.parent_problem_id,),
        f"complete-{unit}-power-set",
        "Enumerate the frozen finite compatibility frontier in stable bit order.",
        "machine-checked",
        "population-ethics.search/v1",
        (),
        corpus_hash,
    )
    return seal_run_record(
        RunRecord(
            cast(Literal["population-ethics.result/v2"], RESULT_SCHEMA),
            "",
            problem_id,
            run_key,
            f"{spec.common.id}:{unit}",
            "bounded-search",
            spec.common.source_fidelity,
            scan_problem,
            execution,
            {"solver_calls": result.solver_calls, "wall_time_ms": elapsed_ms},
            outcome,
            (),
            (),
            provenance,
        )
    )


def _emit_record(record: RunRecord, output_format: OutputFormat, output: Path | None) -> None:
    serialized = run_record_json(record)
    if output is not None:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(serialized)
    typer.echo(serialized.rstrip() if output_format == "json" else _summary_text(record))


def _labels(record: RunRecord) -> str:
    strengths: list[str] = sorted({item.strength for item in record.evidence})
    if not strengths and record.outcome.get("kind") == "frontier":
        strengths = ["solver-reported-classifications"]
    return "\n".join(
        (
            f"scope: {record.claim_kind}",
            f"source-fidelity: {record.source_fidelity}",
            f"evidence-strength: {', '.join(strengths) if strengths else 'none'}",
        )
    )


def _summary_text(record: RunRecord) -> str:
    lines = [
        _labels(record),
        "",
        *_outcome_lines(record),
        "",
        "identifiers:",
        f"  problem:  {record.problem_id}",
        f"  run:      {record.run_key}",
        f"  artifact: {record.artifact_id}",
    ]
    if record.claim_kind == "bounded-proof-instance":
        lines.extend(("", "warning: selected finite witness instance; not an unrestricted theorem"))
    return "\n".join(lines)


def _outcome_lines(record: RunRecord) -> list[str]:
    kind = record.outcome.get("kind")
    if kind == "evaluation":
        lines = ["result: evaluation", "comparisons:"]
        for evidence in record.evidence:
            if not isinstance(evidence, ExactEvaluationEvidence):
                continue
            lines.append(f"  {evidence.comparison_id.replace('-', ' ')}:")
            for evaluator, ranking in sorted(evidence.rankings.items()):
                left, right = evidence.scores[evaluator]
                if ranking == "tie":
                    description = f"tie ({_fraction_text(left)} = {_fraction_text(right)})"
                else:
                    winner, loser = (left, right) if ranking == "left" else (right, left)
                    description = (
                        f"{ranking} preferred ({_fraction_text(winner)} > {_fraction_text(loser)})"
                    )
                lines.append(f"    {evaluator.replace('-', ' ')}: {description}")
        return lines
    if kind == "frontier":
        classifications = record.outcome.get("classifications")
        if isinstance(classifications, list):
            boundaries = sum(
                isinstance(item, dict) and item.get("status") == "boundary"
                for item in classifications
            )
            return [
                "result: frontier scan",
                f"  classifications: {len(classifications)}",
                f"  certified boundaries: {boundaries}",
            ]
    decision = record.outcome.get("decision")
    if isinstance(kind, str) and isinstance(decision, str):
        return [f"result: {kind}", f"  decision: {decision}"]
    return [f"result: {json.dumps(record.outcome, sort_keys=True)}"]


def _fraction_text(value: Fraction) -> str:
    return (
        str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"
    )


def _explain_text(record: RunRecord, view: ExplainView) -> str:
    lines = [_labels(record)]
    if record.claim_kind == "bounded-proof-instance":
        lines.extend(("", "warning: selected finite witness instance; not an unrestricted theorem"))
    if view == "summary":
        lines.extend(
            (
                "",
                *_outcome_lines(record),
                "",
                "identifiers:",
                f"  problem:  {record.problem_id}",
                f"  run:      {record.run_key}",
                f"  artifact: {record.artifact_id}",
            )
        )
    elif view == "model":
        for evidence in record.evidence:
            if isinstance(evidence, CheckedModelEvidence):
                for atom, truth in sorted(
                    evidence.assignment.items(), key=lambda item: (item[0].left, item[0].right)
                ):
                    lines.append(f"{formula_label(atom)} = {str(truth).lower()}")
    elif view == "core":
        for evidence in record.evidence:
            if isinstance(evidence, SolverReportEvidence):
                lines.append(f"decision: {evidence.decision}")
                lines.append(f"raw-core: {', '.join(evidence.raw_core)}")
                lines.append(f"grounded-core: {', '.join(evidence.grounded_core)}")
                lines.append(f"minimality: {evidence.minimality}")
    elif view == "proof":
        locators = _source_locators(record)
        for evidence in record.evidence:
            if isinstance(evidence, CheckedProofEvidence):
                certificate = proof_certificate_from_data(evidence.certificate)
                for node in certificate.nodes:
                    sources = [locators[item] for item in node.premises if item in locators]
                    lines.append(
                        f"{node.id}: {formula_label(node.formula)}; rule={node.rule}; "
                        f"premises={','.join(node.premises) or '-'}; "
                        f"scope={','.join(node.scope) or '-'}; "
                        f"source={'; '.join(sources) or '-'}"
                    )
    else:
        lines.append(
            json.dumps(
                canonical_data(asdict(record.provenance)) if record.provenance else None,
                sort_keys=True,
            )
        )
    return "\n".join(lines)


def _source_locators(record: RunRecord) -> dict[str, str]:
    locators: dict[str, str] = {}
    for evidence in record.evidence:
        grounded = (
            evidence.grounded_input
            if isinstance(evidence, (CheckedModelEvidence, SolverReportEvidence))
            else ()
        )
        for item in grounded:
            identifier = item.get("id")
            locator = item.get("source_locator")
            if isinstance(identifier, str) and isinstance(locator, str):
                locators[identifier] = locator
    return locators


def _verify_record(record: RunRecord) -> list[str]:
    checks = ["artifact hash"]
    grounded_constraints = {}
    for evidence in record.evidence:
        if isinstance(evidence, ExactEvaluationEvidence):
            _verify_exact_evaluation(record, evidence)
            checks.append(f"exact evaluation {evidence.comparison_id}")
        elif isinstance(evidence, CheckedModelEvidence):
            constraints = {
                constraint.id: constraint
                for constraint in map(constraint_from_data, evidence.grounded_input)
            }
            if set(evidence.checked_constraint_ids) != set(constraints):
                raise ValidationError("checked model constraint IDs do not match grounded input")
            for constraint in constraints.values():
                if not evaluate_formula(constraint.formula, evidence.assignment):
                    raise ValidationError(f"checked model violates constraint {constraint.id!r}")
            grounded_constraints.update(constraints)
            checks.append(f"checked model ({len(constraints)} formulas)")
        elif isinstance(evidence, SolverReportEvidence):
            constraints = {
                constraint.id: constraint
                for constraint in map(constraint_from_data, evidence.grounded_input)
            }
            if not set(evidence.grounded_core) <= set(constraints):
                raise ValidationError("grounded core references unavailable input")
            grounded_constraints.update(constraints)
            checks.append("solver report integrity (decision not independently certified)")
    for evidence in record.evidence:
        if isinstance(evidence, CheckedProofEvidence):
            certificate = proof_certificate_from_data(evidence.certificate)
            check_proof(
                certificate,
                grounded_constraints,
                expected_problem_id=record.problem_id,
            )
            checks.append(f"proof DAG ({evidence.checker_version})")
    return checks


def _verify_exact_evaluation(record: RunRecord, evidence: ExactEvaluationEvidence) -> None:
    comparisons = record.normalized_problem.get("comparisons")
    if not isinstance(comparisons, list):
        raise ValidationError("evaluation result lacks normalized comparisons")
    matches = [
        item
        for item in comparisons
        if isinstance(item, dict)
        and _comparison_scores(item) == evidence.scores
        and {
            _evaluator_key(evaluator): _ranking(*pair)
            for evaluator, pair in _comparison_score_entries(item)
        }
        == evidence.rankings
    ]
    if len(matches) != 1:
        raise ValidationError(
            f"exact evaluation {evidence.comparison_id!r} does not match normalized problem"
        )


def _comparison_scores(value: dict[str, object]) -> dict[str, tuple[Fraction, Fraction]]:
    return {_evaluator_key(evaluator): pair for evaluator, pair in _comparison_score_entries(value)}


def _comparison_score_entries(
    value: dict[str, object],
) -> list[tuple[dict[str, object], tuple[Fraction, Fraction]]]:
    left = _population_from_endpoint(value.get("left"))
    right = _population_from_endpoint(value.get("right"))
    evaluators = value.get("evaluators")
    if not isinstance(evaluators, list):
        raise ValidationError("normalized comparison lacks evaluators")
    entries: list[tuple[dict[str, object], tuple[Fraction, Fraction]]] = []
    for raw in evaluators:
        if not isinstance(raw, dict):
            raise ValidationError("normalized evaluator must be an object")
        theory = raw.get("theory")
        if theory == "total":
            pair = (total(left), total(right))
        elif theory == "average":
            pair = (average(left), average(right))
        elif theory == "critical-level":
            level = parse_fraction(raw.get("critical_level"), where="critical_level")
            pair = (critical_level(left, level), critical_level(right, level))
        else:
            raise ValidationError(f"unknown recorded evaluator theory {theory!r}")
        entries.append((raw, pair))
    return entries


def _evaluator_key(value: dict[str, object]) -> str:
    theory = value.get("theory")
    if theory == "critical-level":
        level = parse_fraction(value.get("critical_level"), where="critical_level")
        return (
            f"critical-level-{level.numerator}"
            if level.denominator == 1
            else f"critical-level-{level}"
        )
    if isinstance(theory, str):
        return theory
    raise ValidationError("recorded evaluator lacks theory")


def _population_from_endpoint(value: object) -> Population:
    if not isinstance(value, dict) or set(value) != {"population"}:
        raise ValidationError("recorded evaluation endpoint is not a population")
    population = value["population"]
    if not isinstance(population, list) or any(
        isinstance(item, bool) or not isinstance(item, int) for item in population
    ):
        raise ValidationError("recorded population must contain integers")
    return tuple(cast(list[int], population))


def _fail(error: Exception, *, prefix: str = "error") -> None:
    typer.echo(f"{prefix}: {error}", err=True)
    raise typer.Exit(code=1)
