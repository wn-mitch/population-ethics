"""Phase 20: independent contradiction and model routes for Q-011.

The primitive cycles refute specified witness assignments, not every legal source witness.
The model exclusions apply only to their stated families. No weakened theorem is promoted.
"""

from __future__ import annotations

import json
import time
from typing import Any

from research.lab import LedgerEntry, record, write_result
from research.p20_beta_delta_bridge import run as bridge_run
from research.p20_contextual_priority import run as contextual_run
from research.p20_direct_reservoir import run as direct_run
from research.p20_extremal_ordinal import run as extremal_run
from research.p20_nonlinear_density import run as nonlinear_run
from research.p20_witness_adversary import run as adversary_run


def run() -> dict[str, Any]:
    direct = direct_run()
    bridge = bridge_run()
    adversary = adversary_run()
    nonlinear = nonlinear_run()
    extremal = extremal_run()
    contextual = contextual_run()

    assert direct["evidence"]["direct_cycle"]["all_edges_replayed_clean"]
    assert direct["evidence"]["direct_cycle"]["closure_unsat_for_every_variant"]
    assert all(
        row["edges"] == 82
        and not row["failures"]
        and row["closure"]["mentioned_atom_decision"] == "unsat"
        for row in bridge["evidence"]["primitive_expansion"]["runs"].values()
    )
    assert adversary["evidence"]["source_order"]["totals"]["live"] == 0
    assert nonlinear["evidence"]["consistency_of_report"]
    assert all(
        row["ladder_audit"]
        for row in extremal["evidence"]["support_determined_refutation"]["steps"]
    )
    assert contextual["evidence"]["design_unsat_by_cap"][6]["decision"] == "unsat"
    assert contextual["family_wide_exclusion"] is False

    # Execution times are observations, not part of the hashed mathematical result.
    adversary.pop("seconds", None)
    extremal["evidence"].pop("run_seconds", None)
    contextual.pop("wall_time_s", None)
    return {
        "scope": (
            "Q-011 on ordinal ladders W_-1..W_9 for chosen-witness primitive cycles and "
            "W_-1..W_6 for model-family exclusions; each bounded scan states its own cap. "
            "Every edge uses the frozen source reading and independent ladder audit."
        ),
        "route_a": {"direct": direct, "bridge": bridge, "witness_adversary": adversary},
        "route_b": {
            "nonlinear_density": nonlinear,
            "extremal_ordinal": extremal,
            "contextual_priority": contextual,
        },
        "verdicts": {
            "original": "source-general impossibility is the published 2003 theorem",
            "ranged-ne": "open: fixed-witness contradiction; no source-general proof or exact model",
            "not-worse-da": "open: fixed-witness contradiction; no source-general proof or exact model",
            "both-weakened": "open: fixed-witness contradiction; no source-general proof or exact model",
        },
    }


def main() -> None:
    started = time.monotonic()
    data = run()
    path = write_result(
        "p20_vrc_dual_routes", data, {"wall_time_s": round(time.monotonic() - started, 1)}
    )
    direct = data["route_a"]["direct"]["evidence"]["direct_cycle"]
    bridge = data["route_a"]["bridge"]["evidence"]["primitive_expansion"]["runs"]
    adversary = data["route_a"]["witness_adversary"]["evidence"]["source_order"]["totals"]
    record(
        [
            LedgerEntry(
                candidate_id="P20-vrc-dual-routes",
                hypothesis="One of the three weakened 2003 VRC sets has either a source-general contradiction or an exact model.",
                motivation="The phase-19 nesting obstruction leaves an uninstantiated bound placement and no background-sensitive model.",
                exact_formal_change="No principle changes; extend the ladder for primitive fixed-witness cycles and test three independent model families on the frozen ladder.",
                scope=data["scope"],
                search_method="source-manifest and ladder edge audits, no-completeness closure, bounded witness-adversary motifs, all-size inequalities for specified model families",
                result=json.dumps(
                    {
                        "direct_variants_unsat": direct["closure_unsat_for_every_variant"],
                        "bridge_primitive_edges": [row["edges"] for row in bridge.values()],
                        "adversary_bounded_motifs": adversary,
                        "model_families": [
                            "level-separable anchored",
                            "total-welfare/cardinality-normalized",
                            "occupied-level support",
                            "fixed-witness contextual score",
                        ],
                        "weakened_status": "open",
                    },
                    sort_keys=True,
                ),
                evidence_type="audited fixed-witness primitive cycles; bounded motifs; all-size model-family exclusions and a fixed-witness contextual-score refutation",
                checked=True,
                minimal="23-edge primitive cycle exhibited; no minimality claim",
                interpretation="Both primitive constructions close at legal chosen witnesses, but no contradiction is uniform over the source's existential witnesses. No exact model was found. Family exclusions and bounded failures do not settle the three weakenings.",
                next_experiment="resolve the adverse VRC y=3, GNEP u=4 witness without assuming shared reservoir fuel, or certify a nonseparable count-sensitive order at every size",
                result_scope=data["scope"],
                formalization_tier="agent-cross-read 2000 thesis and 2003 source conditions; phase-18 manifest and independent ladder audit",
                witness_conditions="direct and bridge: exhibited W_-1..W_9 witnesses; model exclusions: stated W_-1..W_6 families; contextual core fixed NE/GNEP/VRC counts",
                novelty_status="not claimed (fixed-witness and model-family results)",
                status="open",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            )
        ]
    )
    print(json.dumps({"result": str(path), "verdicts": data["verdicts"]}, indent=2))


if __name__ == "__main__":
    main()
