"""Phase 0: freeze and reproduce the baseline Arrhenius artifact."""

from __future__ import annotations

import json
import subprocess
import tempfile
import time
from pathlib import Path

from research.lab import BASELINE_PATH, ROOT, LedgerEntry, record, sha256_file, write_result

STORED = ROOT / "results" / "arrhenius.json"
COMPARED = ("problem_id", "run_key", "claim_kind", "source_fidelity", "outcome")


def _cli(*args: str) -> str:
    return subprocess.run(
        ["uv", "run", "--quiet", "population-ethics", *args],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout


def main() -> None:
    started = time.monotonic()
    stored = json.loads(STORED.read_text())
    with tempfile.TemporaryDirectory() as scratch:
        rerun_path = Path(scratch) / "rerun.json"
        _cli("run", str(BASELINE_PATH), "--format", "json", "--output", str(rerun_path))
        rerun = json.loads(rerun_path.read_text())
        verify_stored = _cli("verify", str(STORED))
        verify_rerun = _cli("verify", str(rerun_path))
    by_kind = {e["kind"]: e for e in stored["evidence"]}
    rerun_kind = {e["kind"]: e for e in rerun["evidence"]}
    comparison = {key: stored[key] == rerun[key] for key in COMPARED}
    comparison["grounded_core"] = (
        by_kind["solver-report"]["grounded_core"] == rerun_kind["solver-report"]["grounded_core"]
    )
    comparison["checked_proof"] = by_kind["checked-proof"] == rerun_kind["checked-proof"]
    comparison["artifact_id (expected to differ: hashes wall time)"] = (
        stored["artifact_id"] == rerun["artifact_id"]
    )
    certificate = by_kind["checked-proof"]["certificate"]
    completeness_premises = sorted(
        p for node in certificate["nodes"] for p in node["premises"] if p.startswith("completeness")
    )
    core = by_kind["solver-report"]["grounded_core"]
    data = {
        "stored_artifact_sha256": sha256_file(STORED),
        "stored_artifact_id": stored["artifact_id"],
        "problem_id": stored["problem_id"],
        "labels": {
            "claim_kind": stored["claim_kind"],
            "source_fidelity": stored["source_fidelity"],
            "formalization_id": "arrhenius-2000.selected-witness/v1",
        },
        "rerun_matches": comparison,
        "verify_stored_accepted": "verification: accepted" in verify_stored,
        "verify_rerun_accepted": "verification: accepted" in verify_rerun,
        "curated_certificate": {
            "nodes": len(certificate["nodes"]),
            "completeness_premises": completeness_premises,
        },
        "stored_solver_core": {
            "size": len(core),
            "completeness": [c for c in core if c.startswith("completeness")],
            "transitivity": [c for c in core if c.startswith("transitivity")],
            "minimality": by_kind["solver-report"]["minimality"],
        },
    }
    write_result("p0_baseline", data, {"wall_time_s": round(time.monotonic() - started, 2)})
    record(
        [
            LedgerEntry(
                candidate_id="P0-baseline",
                hypothesis="The frozen artifact reproduces from the TOML and verifies offline.",
                motivation="Freeze the target before search.",
                exact_formal_change="none",
                scope="selected finite witness, 12 named populations",
                search_method="CLI run + verify; field comparison excluding artifact_id",
                result=json.dumps(comparison, sort_keys=True),
                evidence_type="checked-proof + solver-reported",
                checked=True,
                minimal="stored core: deletion-minimal in id order",
                interpretation=(
                    "Baseline reproduces. Curated proof uses completeness on "
                    + ", ".join(completeness_premises)
                    + "; the stored solver core uses a different 4-pair set."
                ),
                next_experiment="P1 frontier",
                result_scope="finite computational result",
                formalization_tier="frozen source-reviewed witness",
                status="confirmed",
                novelty_status="not-applicable (reproduction)",
            )
        ]
    )


if __name__ == "__main__":
    main()
