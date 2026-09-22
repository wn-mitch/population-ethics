from __future__ import annotations

import pytest
import z3  # type: ignore[import-untyped]
from typer.testing import CliRunner

from population_ethics.cli import app
from population_ethics.domain import ValidationError
from population_ethics.principles import GroundConstraint
from population_ethics.proofs import (
    ProofCertificate,
    ProofNode,
    check_proof,
    curated_arrhenius_certificate,
)
from population_ethics.relations import FALSE, Not, weak
from population_ethics.spec import CompatibilitySpec, load_experiment, problem_id_for


def _premise(identifier: str, formula: object) -> GroundConstraint:
    return GroundConstraint(
        identifier,
        "test",
        formula,  # type: ignore[arg-type]
        ("A", "B"),
        None,
        "test/v1",
        "Proof checker test premise.",
    )


def test_valid_local_assumption_discharge() -> None:
    atom = weak("A", "B")
    negative = Not(atom)
    constraints = {"not-p": _premise("not-p", negative)}
    nodes = (
        ProofNode("premise", negative, "premise", ("not-p",), (), (), "Selected premise."),
        ProofNode("hyp", atom, "hypothesis", (), ("hyp",), (), "Local assumption."),
        ProofNode(
            "false",
            FALSE,
            "contradiction",
            ("premise", "hyp"),
            ("hyp",),
            (),
            "Contradiction.",
        ),
        ProofNode(
            "not-p-derived",
            negative,
            "negation-introduction",
            ("false",),
            (),
            ("hyp",),
            "Discharge the local assumption.",
        ),
    )
    certificate = ProofCertificate("problem", "not-p-derived", nodes)
    result = check_proof(
        certificate,
        constraints,
        expected_problem_id="problem",
        require_contradiction=False,
    )
    assert not result.open_hypotheses


def test_checker_rejects_cycles_forward_references_and_missing_dependencies() -> None:
    atom = weak("A", "B")
    cyclic = ProofCertificate(
        "p",
        "a",
        (
            ProofNode("a", atom, "conjunction-elimination", ("b",), (), (), "Cycle A."),
            ProofNode("b", atom, "conjunction-elimination", ("a",), (), (), "Cycle B."),
        ),
    )
    with pytest.raises(ValidationError, match="cycle"):
        check_proof(cyclic, {}, require_contradiction=False)

    forward = ProofCertificate(
        "p",
        "a",
        (
            ProofNode("a", atom, "premise", ("b",), (), (), "Forward."),
            ProofNode("b", atom, "hypothesis", (), ("b",), (), "Later."),
        ),
    )
    with pytest.raises(ValidationError, match="forward"):
        check_proof(forward, {}, require_contradiction=False)

    missing = ProofCertificate(
        "p",
        "a",
        (ProofNode("a", atom, "premise", ("missing",), (), (), "Missing."),),
    )
    with pytest.raises(ValidationError, match="unavailable"):
        check_proof(missing, {}, require_contradiction=False)


def test_checker_rejects_wrong_shapes_formulas_and_open_assumptions() -> None:
    atom = weak("A", "B")
    constraints = {"p": _premise("p", atom)}
    wrong_formula = ProofCertificate(
        "p",
        "node",
        (ProofNode("node", Not(atom), "premise", ("p",), (), (), "Corrupted."),),
    )
    with pytest.raises(ValidationError, match="changes"):
        check_proof(wrong_formula, constraints, require_contradiction=False)

    wrong_shape = ProofCertificate(
        "p",
        "node",
        (ProofNode("node", atom, "premise", (), (), (), "Malformed."),),
    )
    with pytest.raises(ValidationError, match="shape"):
        check_proof(wrong_shape, constraints, require_contradiction=False)

    open_hypothesis = ProofCertificate(
        "p",
        "hyp",
        (ProofNode("hyp", FALSE, "hypothesis", (), ("hyp",), (), "Leaked."),),
    )
    with pytest.raises(ValidationError, match="leaks"):
        check_proof(open_hypothesis, {}, require_contradiction=True)


def test_checker_does_not_allow_arbitrary_post_contradiction_claims() -> None:
    atom = weak("A", "B")
    constraints = {
        "p": _premise("p", atom),
        "not-p": _premise("not-p", Not(atom)),
    }
    nodes = (
        ProofNode("node-p", atom, "premise", ("p",), (), (), "Positive."),
        ProofNode("node-not-p", Not(atom), "premise", ("not-p",), (), (), "Negative."),
        ProofNode(
            "false",
            FALSE,
            "contradiction",
            ("node-p", "node-not-p"),
            (),
            (),
            "False.",
        ),
        ProofNode(
            "arbitrary",
            weak("B", "A"),
            "conjunction-elimination",
            ("false",),
            (),
            (),
            "Invalid explosion.",
        ),
    )
    with pytest.raises(ValidationError, match="conjunction elimination"):
        check_proof(ProofCertificate("problem", "arbitrary", nodes), constraints)


def test_curated_arrhenius_certificate_checks() -> None:
    spec = load_experiment("experiments/arrhenius-2000-proof.toml")
    assert isinstance(spec, CompatibilitySpec)
    constraints = {
        constraint.id: constraint for group in spec.groups for constraint in group.constraints
    }
    problem_id = problem_id_for(spec)
    certificate = curated_arrhenius_certificate(problem_id)
    result = check_proof(certificate, constraints, expected_problem_id=problem_id)
    assert result.root_formula == FALSE
    assert not result.open_hypotheses


def test_offline_verify_rejects_corrupt_fixture_without_z3(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden_solver(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("offline verification invoked Z3")

    monkeypatch.setattr(z3, "Solver", forbidden_solver)
    runner = CliRunner()
    valid = runner.invoke(app, ["verify", "tests/fixtures/arrhenius-valid.json"])
    assert valid.exit_code == 0, valid.output
    corrupt = runner.invoke(app, ["verify", "tests/fixtures/arrhenius-corrupt-proof.json"])
    assert corrupt.exit_code != 0
    assert "verification failed" in corrupt.output
    assert "contradiction" in corrupt.output or "premise" in corrupt.output
