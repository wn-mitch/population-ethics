"""Phase 17: source-principle diagnostic at the 2003 VRC proof's five relata.

This is a finite, fixed-witness restriction, not a six-life domain sweep or a
consistency certificate. N-shaped thesis DA is never normalized into a weak edge.
"""

from __future__ import annotations

import json
import time
from typing import Any

from research.census import cycle_words
from research.lab import Engine, LedgerEntry, background, record, write_result
from research.ladder import Witness, audit, domain, instances_over
from research.p6_schema import core_constraints, name_of
from research.p8_catalogue import LADDER, THEOREM_2003, WITNESS, check
from research.schema import Instance, Pop

ED = "arrhenius-2003:egalitarian-dominance"
GNEP = "arrhenius-2003:general-non-extreme-priority"
VRC = "arrhenius-2003:vrc-avoidance"
NE_2003 = "arrhenius-2003:non-elitism"
NE_THESIS = "thesis:non-elitism"
DA_2003 = "arrhenius-2003:dominance-addition"
DA_THESIS = "thesis:dominance-addition"

# The two extra existential choices are fixed for this diagnostic alone.
SOURCE_WITNESS = Witness(
    {
        **WITNESS.params,
        "non-elitism": {"n": 1},
        "general-non-extreme-priority": {"u": 4, "y": 3, "n": 1},
    }
)
VARIANTS = (
    ("original", NE_2003, DA_2003),
    ("ranged-ne", NE_THESIS, DA_2003),
    ("not-worse-da", NE_2003, DA_THESIS),
    ("both-weakened", NE_THESIS, DA_THESIS),
)


def focused_ground(instances: list[Instance], relata: list[Pop]) -> str:
    """Solve exactly these ground clauses as a preorder, without completeness."""
    names = tuple(name_of(p) for p in relata)
    bg = background(names)
    hard = [
        *bg["reflexivity"],
        *bg["transitivity"],
        *core_constraints(instances, "p17-vrc-source-focused/v1"),
    ]
    decision = Engine(names, hard).require().decision
    if decision == "unknown":
        raise RuntimeError("focused source-level ground check returned unknown")
    return decision


def run() -> dict[str, Any]:
    derived = check(THEOREM_2003)
    assert derived["decision_without_completeness"] == "unsat"
    assert all(derived["audit"].values())
    assert derived["cli_decision"] == "unsat" and derived["cli_verify_accepted"]

    # domain supplies the six-life cap, but materializing all of its ~3000
    # populations into DA's quadratic relation encoding is not tractable.
    proof_pops = set(THEOREM_2003.populations.values())
    relata = sorted(p for p in domain(LADDER, 6) if p in proof_pops)
    assert len(relata) == len(proof_pops) == 5
    beta = THEOREM_2003.instances()[3]
    assert audit(beta, LADDER, WITNESS)
    assert not audit(Instance("thesis:condition-beta", beta.args), LADDER, WITNESS)
    da = THEOREM_2003.instances()[1]
    assert audit(da, LADDER, WITNESS)
    thesis_da = Instance(DA_THESIS, (da.args[1], da.args[0]))
    assert not audit(thesis_da, LADDER, SOURCE_WITNESS)
    all_principles = (ED, GNEP, VRC, NE_2003, NE_THESIS, DA_2003, DA_THESIS)
    by_principle = {
        principle: instances_over(relata, LADDER, SOURCE_WITNESS, (principle,))
        for principle in all_principles
    }
    assert all(
        audit(inst, LADDER, SOURCE_WITNESS)
        for generated in by_principle.values()
        for inst in generated
    )

    runs: dict[str, Any] = {}
    for label, ne, da_form in VARIANTS:
        principles = (ED, GNEP, VRC, ne, da_form)
        instances = [inst for principle in principles for inst in by_principle[principle]]
        # cycle_words interprets N as reverse W: only give it actual W/S edges.
        cycle_input = [inst for inst in instances if inst.shape in {"W", "S"}]
        words = cycle_words(cycle_input, 8)
        for word in words:
            assert all(audit(inst, LADDER, SOURCE_WITNESS) for inst in word.example)
        cycles = [
            {
                "word": list(word.word),
                "instances": [
                    {"principle": inst.principle, "shape": inst.shape, "args": list(inst.args)}
                    for inst in word.example
                ],
            }
            for word in words
        ]
        focus = sorted(
            {*relata, *(p for word in words[:1] for inst in word.example for p in inst.args)}
        )
        focused_instances = [inst for inst in instances if all(p in focus for p in inst.args)]
        runs[label] = {
            "principles": list(principles),
            "instance_counts": {
                p: sum(inst.principle == p for inst in instances) for p in principles
            },
            "shape_counts": {
                s: sum(inst.shape == s for inst in instances) for s in ("S", "W", "N")
            },
            "cycles_max_8_weak_strict_only": cycles,
            "cycle_scope": "all source instances on five relata"
            if da_form == DA_2003
            else "W/S subset only; N-shaped DA excluded",
            "focused_relata": [list(p) for p in focus],
            "focused_instance_count": len(focused_instances),
            "decision_without_completeness": focused_ground(focused_instances, focus),
            "lost_source_proof_edge": (
                "negative-background derived beta not available from ranged NE"
                if ne == NE_THESIS
                else None
            ),
            "changed_source_proof_da": (
                "source DA edge is absent: its positive addition is mixed, whereas thesis DA requires equal added lives; applicable thesis DA clauses are N-shaped, not reverse weak edges"
                if da_form == DA_THESIS
                else None
            ),
        }
    return {
        "scope": "all primitive source instances on the five frozen 2003 proof populations, each at most six lives; not the full six-life domain",
        "ladder": list(LADDER.levels),
        "max_lives": 6,
        "witness": {family: dict(params) for family, params in SOURCE_WITNESS.params.items()},
        "derived_proof_control": {
            "kind": "published derived beta/delta proof, not primitive source instances",
            "decision_without_completeness": derived["decision_without_completeness"],
            "audit": all(derived["audit"].values()),
        },
        "runs": runs,
    }


def main() -> None:
    started = time.monotonic()
    data = run()
    path = write_result(
        "p17_vrc_boundary", data, {"wall_time_s": round(time.monotonic() - started, 1)}
    )
    record(
        [
            LedgerEntry(
                candidate_id="P17-vrc-source-boundary",
                hypothesis="The Q-011 weakenings change the original 2003 source-principle contradiction at fixed witnesses.",
                motivation="Distinguish primitive-source constraints from the published derived beta/delta control.",
                exact_formal_change="Four NE/DA combinations over five frozen 2003 proof populations.",
                scope=data["scope"],
                search_method="independently audited primitive instances; W/S cycles to eight edges; focused Z3 preorder without completeness",
                result=json.dumps(data["runs"], sort_keys=True),
                evidence_type="finite fixed-witness diagnostic; independently reproduced derived proof",
                checked=True,
                minimal="not assessed",
                interpretation="No bounded SAT result proves unrestricted consistency; N-shaped DA is not a reverse weak edge.",
                next_experiment="seek replacement source lemmas or a universal background-sensitive model for Q-011",
                result_scope="finite computational result on five selected relata",
                formalization_tier="agent-cross-read source principles and frozen proof relata",
                witness_conditions="research/p17_vrc_boundary.py SOURCE_WITNESS; W_-1..W_6; at most six lives",
                novelty_status="not-applicable (diagnostic)",
                status="open",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            )
        ]
    )
    print(json.dumps(data, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
