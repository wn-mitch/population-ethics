from __future__ import annotations

from fractions import Fraction
from pathlib import Path

import pytest
import z3  # type: ignore[import-untyped]

import population_ethics.domain as domain_module
from population_ethics.candidates import run_formalization_guard_probes
from population_ethics.domain import (
    ExplicitDomainSpec,
    GeneratedDomainSpec,
    NamedPopulation,
    ResourcePolicy,
    ValidationError,
    WelfareCategories,
    build_population_universe,
    parse_population,
)
from population_ethics.relations import (
    atom_key,
    collect_atoms,
    encode_z3,
    evaluate_formula,
    formula_from_data,
    formula_to_data,
    incomparable,
    indifferent,
    strict,
)
from population_ethics.spec import CompatibilitySpec, load_experiment, problem_id_for
from population_ethics.theories import average, critical_level, total


def test_population_validation_and_aliases() -> None:
    with pytest.raises(ValidationError, match="integer"):
        parse_population([True])
    with pytest.raises(ValidationError, match="positive"):
        parse_population({"welfare": 1, "count": 0})
    with pytest.raises(ValidationError, match="unique"):
        GeneratedDomainSpec((1, 1), 2)
    with pytest.raises(ValidationError, match="overlaps"):
        WelfareCategories({"low": frozenset({1}), "high": frozenset({1})})

    spec = ExplicitDomainSpec(
        (
            NamedPopulation("A", parse_population([2, 1])),
            NamedPopulation("alias", parse_population([1, 2])),
            NamedPopulation("B", parse_population({"welfare": 3, "count": 1})),
            NamedPopulation("AB", parse_population([1, 2, 3]), ("A", "B")),
        )
    )
    universe = build_population_universe(spec, ResourcePolicy())
    assert universe.populations == ((3,), (1, 2), (1, 2, 3))
    assert universe.aliases[(1, 2)] == ("A", "alias")

    bad = ExplicitDomainSpec(
        (
            NamedPopulation("A", (1,)),
            NamedPopulation("B", (2,)),
            NamedPopulation("AB", (1, 3), ("A", "B")),
        )
    )
    with pytest.raises(ValidationError, match="does not concatenate"):
        build_population_universe(bad, ResourcePolicy())


def test_resource_preflight_happens_before_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def should_not_expand(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("generation occurred before resource preflight")

    monkeypatch.setattr(domain_module, "combinations_with_replacement", should_not_expand)
    spec = GeneratedDomainSpec(tuple(range(20)), 20)
    with pytest.raises(ValidationError, match="prospective|preflight"):
        build_population_universe(spec, ResourcePolicy(max_populations=2))


def test_exact_aggregation_rankings() -> None:
    assert total((100, 100)) == Fraction(200)
    assert average((90, 100, 100)) == Fraction(290, 3)
    assert critical_level((100, 100), Fraction(95)) == Fraction(10)
    assert total(()) == 0
    assert critical_level((), Fraction(10)) == 0
    with pytest.raises(ValidationError, match="undefined"):
        average(())


def test_formula_roundtrip_evaluation_and_z3_agree() -> None:
    formula = strict("A", "B")
    assert formula_from_data(formula_to_data(formula)) == formula
    atoms = sorted(collect_atoms(formula), key=atom_key)
    atom_map = {atom: z3.Bool(atom_key(atom).replace(":", "_")) for atom in atoms}
    for first in (False, True):
        for second in (False, True):
            assignment = {atoms[0]: first, atoms[1]: second}
            solver = z3.Solver()
            solver.add(encode_z3(formula, atom_map))
            for atom, value in assignment.items():
                solver.add(atom_map[atom] == value)
            assert (solver.check() == z3.sat) is evaluate_formula(formula, assignment)


def test_strict_indifferent_and_incomparable_are_distinct() -> None:
    atoms = collect_atoms(strict("A", "B"))
    forward = next(atom for atom in atoms if atom.left == "A")
    reverse = next(atom for atom in atoms if atom.left == "B")
    assert evaluate_formula(strict("A", "B"), {forward: True, reverse: False})
    assert evaluate_formula(indifferent("A", "B"), {forward: True, reverse: True})
    assert evaluate_formula(incomparable("A", "B"), {forward: False, reverse: False})


def test_strict_toml_rejects_unknown_keys_and_schema(tmp_path: Path) -> None:
    unknown = tmp_path / "unknown.toml"
    unknown.write_text(
        'schema="population-ethics.experiment/v2"\nid="x"\nkind="evaluation"\n'
        'claim_kind="pedagogical"\nsource_fidelity="none"\nextra=true\n'
        '[domain]\nmode="explicit"\npopulations=[]\ncomparisons=[]\n'
    )
    with pytest.raises(ValidationError, match="unknown keys"):
        load_experiment(unknown)

    schema = tmp_path / "schema.toml"
    schema.write_text('schema="population-ethics.experiment/v1"\n')
    with pytest.raises(ValidationError, match="unsupported experiment schema"):
        load_experiment(schema)


def test_identity_guard_probes_cover_aliases_and_local_edits() -> None:
    spec = load_experiment("experiments/arrhenius-2000-proof.toml")
    assert isinstance(spec, CompatibilitySpec)
    report = run_formalization_guard_probes(spec)
    assert report.base_problem_id == problem_id_for(spec)
    assert report.prose_preserves_problem_id
    assert report.unused_alias_preserves_problem_id
    assert report.welfare_edit_changes_identity
    assert report.comparison_symbol_edit_changes_identity
    assert report.proof_step_edit_rejected
