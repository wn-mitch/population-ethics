"""Source-level controls for the abstract branch-cycle theorem's limited lift.

For a fixed legal witness and only W/S conditions, the transitive closure of
all primitive source instances is a satisfying quasi-order exactly when the
entire (possibly infinite) population-instance graph has no strict cycle.
This is D-019's graph theorem, not a finite-support quotient or a claim about
all existential witnesses. The finite controls below replay source instances,
not the unrestricted theorem.
"""

from __future__ import annotations

import json
from collections import Counter
from typing import Any

from research.canon import canonical, canonical_l2
from research.census import cycle_words
from research.known import known_ground
from research.lab import LedgerEntry, record, write_result
from research.ladder import audit, instances_over
from research.p8_catalogue import LADDER, THEOREM_1, THEOREM_3, WITNESS, Frozen
from research.p8_catalogue import LADDER as CONTROL_LADDER
from research.p18_vrc_certificate import (
    CONTROL_WITNESS,
    audit_is_cheap,
    control_edges,
    verify_edge,
)
from research.readings import require_reviewed


def frozen_control(frozen: Frozen) -> dict[str, Any]:
    core = frozen.instances()
    principles = sorted({inst.principle for inst in core})
    require_reviewed(principles)
    assert {inst.shape for inst in core} <= {"W", "S"}
    generated = instances_over(frozen.populations.values(), LADDER, WITNESS, principles)
    assert set(core) <= set(generated)
    assert all(audit(inst, LADDER, WITNESS) for inst in core)
    words = cycle_words(generated, len(core))
    realized = [word for word in words if set(word.example) == set(core)]
    assert realized and any(inst.shape == "S" for inst in core)
    return {
        "theorem": frozen.id,
        "witness": WITNESS.params,
        "ladder": list(LADDER.levels),
        "populations": [list(pop) for pop in frozen.populations.values()],
        "generated_instances": len(generated),
        "audited_primitive_cycle": [
            {"principle": inst.principle, "shape": inst.shape, "args": [list(p) for p in inst.args]}
            for inst in realized[0].example
        ],
        "canonical": {
            "L0": canonical(core, "L0"),
            "L1": canonical(core, "L1"),
            "L2": canonical_l2(core),
            "principle": canonical(core, "principle"),
        },
        "catalogue": known_ground(core),
        "scope": "one fixed legal witness and exactly these source populations; not every existential witness",
    }


def primitive_expansion_control() -> dict[str, Any]:
    edges = control_edges()
    require_reviewed(edge.principle for edge in edges)
    assert all(not verify_edge(edge.record(), CONTROL_LADDER, CONTROL_WITNESS) for edge in edges)
    cheap = [edge.instance for edge in edges if audit_is_cheap(edge.instance)]
    assert all(audit(inst, CONTROL_LADDER, CONTROL_WITNESS) for inst in cheap)
    assert set(edge.shape for edge in edges) == {"W", "S"}
    return {
        "source": "P18 original 2003 primitive control, not an all-witness contradiction",
        "witness": CONTROL_WITNESS.params,
        "edges": len(edges),
        "principles": dict(sorted(Counter(edge.principle for edge in edges).items())),
        "manifest_replay": len(edges),
        "independent_exhaustive_audit": len(cheap),
        "audit_skipped_large_background": len(edges) - len(cheap),
        "canonical_L0": canonical([edge.instance for edge in edges], "L0"),
        "canonical_L1": canonical([edge.instance for edge in edges], "L1"),
        "canonical_L2": canonical_l2([edge.instance for edge in edges]),
    }


def run() -> dict[str, Any]:
    return {
        "fixed_witness_converse": "For all W/S source instances over a specified welfare domain and fixed valid witness, a quasi-order satisfying them exists iff the entire population graph has no strict cycle. If none exists, the reflexive/transitive closure of every primitive W and S edge satisfies all forward weak obligations and leaves each S edge strict: a reverse path would close a strict cycle. Conversely a strict directed cycle contradicts transitivity and asymmetry of strict preference.",
        "quantifiers": "One witness and every source instance suffice for consistency; impossibility across existential witnesses requires an independently audited contradiction for every legal witness.",
        "support_abstraction": "Support SCCs discard counts and over-approximate paths; support cycles alone are not population-cycle certificates.",
        "complete_preorder_boundary": "I-fork branch choice is not an inference for incomplete source preorders; thesis DA's N obligation stays a direct preorder constraint.",
        "P8_controls": [frozen_control(theorem) for theorem in (THEOREM_1, THEOREM_3)],
        "P18_expanded_control": primitive_expansion_control(),
        "P21_negative_control": "P21-integer-chain-both-weakened provides a satisfying model at a different valid witness. No purported universal 2003 obstruction may contain its primitive instance set as an unsatisfiable subset.",
    }


def main() -> None:
    data = run()
    path = write_result("p22_source_lift", data, {})
    record(
        [
            LedgerEntry(
                candidate_id="P22-fixed-witness-source-cycle-controls",
                hypothesis="The abstract strict-cycle obstruction lifts to reviewed fork-free W/S source instances only at a fixed valid witness.",
                motivation="Support graph cycles and complete-preorder fork branches alone cannot prove a source-general impossibility.",
                exact_formal_change="None; use reviewed ladder instance generation and independent source audit.",
                scope="W/S source instances at a fixed witness and a specified welfare domain; P8 and P18 examples are chosen-witness finite controls",
                search_method="generate and audit P8 cycles; manifest replay of P18 primitive expansion; canonical L0/L1/L2 and known-ground matching",
                result="D-019 exact infinite-instance graph converse with finite source-audited positive controls; P21 excludes a universal obstruction for the both-weakened conjunction",
                evidence_type="graph-theoretic proof, audited primitive cycles and pre-existing all-size P21 model",
                checked=True,
                minimal="no new source-level minimality or all-witness impossibility claim",
                interpretation="The W/S source fragment excludes N and I forms; count-free support SCCs never certify a concrete cycle.",
                next_experiment="probe the two singly weakened 2003 corners independently",
                result_scope="fixed-witness graph theorem and selected source-instance controls",
                formalization_tier="agent-cross-read thesis-family source readings; P8 and P18 controls",
                witness_conditions="P8 selected witness and separately P18 selected witness; P21 uses another legal witness",
                novelty_status="D-019 graph criterion and published source cycles; no new source theorem claimed",
                status="control",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            )
        ]
    )
    print(
        json.dumps(
            {
                "result": str(path),
                "P8_controls": [x["theorem"] for x in data["P8_controls"]],
                "P18_edges": data["P18_expanded_control"]["edges"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
