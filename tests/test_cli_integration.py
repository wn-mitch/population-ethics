from __future__ import annotations

import json
from pathlib import Path

from typer.testing import CliRunner

from population_ethics.cli import app

runner = CliRunner()


def test_tutorial_text_and_json_share_identity_and_exact_rankings(tmp_path: Path) -> None:
    output = tmp_path / "tutorial.json"
    text = runner.invoke(
        app,
        ["run", "experiments/tutorial.toml", "--format", "text", "--output", str(output)],
    )
    assert text.exit_code == 0, text.output
    data = json.loads(output.read_text())
    assert data["problem_id"] in text.output
    assert data["artifact_id"] in text.output
    assert "result: evaluation" in text.output
    assert "average versus total:" in text.output
    assert "average: left preferred (100 > 290/3)" in text.output
    assert "total: right preferred (290 > 200)" in text.output
    assert '"rankings":' not in text.output
    rankings = data["outcome"]["rankings"]
    assert rankings["average-versus-total"] == {
        "average": "left",
        "critical-level-95": "left",
        "total": "right",
    }
    assert rankings["repugnant-conclusion-shape"] == {
        "average": "left",
        "critical-level-1": "left",
        "total": "right",
    }
    verified = runner.invoke(app, ["verify", str(output), "--format", "json"])
    assert verified.exit_code == 0, verified.output
    assert json.loads(verified.output)["verified"] is True


def test_arrhenius_run_verify_and_explain(tmp_path: Path) -> None:
    output = tmp_path / "arrhenius.json"
    run = runner.invoke(
        app,
        [
            "run",
            "experiments/arrhenius-2000-proof.toml",
            "--format",
            "text",
            "--output",
            str(output),
        ],
    )
    assert run.exit_code == 0, run.output
    assert "scope: bounded-proof-instance" in run.output
    data = json.loads(output.read_text())
    assert data["outcome"]["decision"] == "unsat"
    source_formulas = [
        item["formula"]
        for evidence in data["evidence"]
        if evidence["kind"] == "solver-report"
        for item in evidence["grounded_input"]
        if item["id"].startswith("avoid-")
    ]
    assert source_formulas and all(item["kind"] == "not" for item in source_formulas)
    report = next(item for item in data["evidence"] if item["kind"] == "solver-report")
    assert report["grounded_core"]
    assert report["minimality"] in {"verified", "unresolved"}
    proof = next(item for item in data["evidence"] if item["kind"] == "checked-proof")
    root = proof["certificate"]["root_node_id"]
    root_node = next(node for node in proof["certificate"]["nodes"] if node["id"] == root)
    assert root_node["formula"] == {"kind": "constant", "value": False}
    assert root_node["scope"] == []

    verified = runner.invoke(app, ["verify", str(output), "--format", "text"])
    assert verified.exit_code == 0, verified.output
    explained = runner.invoke(app, ["explain", str(output), "--view", "proof"])
    assert explained.exit_code == 0, explained.output
    assert "source=Arrhenius 2000" in explained.output
    assert "warning: selected finite witness instance" in explained.output


def test_cli_scans_complete_power_sets_and_rejects_truncation(tmp_path: Path) -> None:
    for unit, expected in (("principle", 128), ("instance", 256)):
        output = tmp_path / f"{unit}.json"
        result = runner.invoke(
            app,
            [
                "scan",
                "experiments/arrhenius-2000-proof.toml",
                "--unit",
                unit,
                "--max-subsets",
                str(expected),
                "--format",
                "text",
                "--output",
                str(output),
            ],
        )
        assert result.exit_code == 0, result.output
        data = json.loads(output.read_text())
        nodes = data["outcome"]["classifications"]
        assert len(nodes) == expected
        assert data["claim_kind"] == "bounded-search"
        assert data["outcome"]["fixed_background_ids"] == ["reflexivity", "transitivity"]
        assert all(
            node["status"] != "boundary"
            or node["boundary_kind"] in {"minimal-unsat", "maximal-sat"}
            for node in nodes
        )

    rejected = runner.invoke(
        app,
        [
            "scan",
            "experiments/arrhenius-2000-proof.toml",
            "--unit",
            "principle",
            "--max-subsets",
            "127",
        ],
    )
    assert rejected.exit_code != 0
    assert "requires 128 subsets" in rejected.output


def test_cli_entailment_countermodel_and_inconsistent_base(tmp_path: Path) -> None:
    countermodel_path = tmp_path / "countermodel.json"
    countermodel = runner.invoke(
        app,
        [
            "run",
            "experiments/entailment-countermodel.toml",
            "--format",
            "json",
            "--output",
            str(countermodel_path),
        ],
    )
    assert countermodel.exit_code == 0, countermodel.output
    assert json.loads(countermodel_path.read_text())["outcome"]["decision"] == "countermodel"

    inconsistent = runner.invoke(
        app,
        ["run", "experiments/entailment-inconsistent.toml", "--format", "json"],
    )
    assert inconsistent.exit_code == 0, inconsistent.output
    outcome = json.loads(inconsistent.output)["outcome"]["decision"]
    assert outcome == "inconsistent-premises"
    assert outcome != "solver-entailed"
