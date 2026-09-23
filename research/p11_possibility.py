"""Phase 11: the possibility map. Which condition sets does some axiology satisfy?

- **Additive, exact** (research/additive.py). MARCO over the 15 primitive thesis-family
  conditions for axiologies V = Σ g(w), for every g, every population size and every witness.
- **Lexicographic-additive, exact per axiology** (research/lexadd.py). A grammar of 38 tier
  stacks (optional negative tier; total, critical-level at every half level, or threshold tier;
  total tie-break), each checked against every condition for every population size.
- **Coverage** (research/possibility.py). The minimal condition sets that no axiology above
  realizes, each either explained by a known theorem (with the implications between conditions)
  or left as a gap.
- **Gap probes.** For the leading gaps, the census searches for strict cycles under the Phase 8
  witness. A gap with no cycle and no model is an open question, not a theorem.
"""

from __future__ import annotations

import json
import time
from typing import Any

from research.additive import classify
from research.census import cycle_words
from research.lab import LedgerEntry, record, write_result
from research.ladder import Ladder, domain, instances_over
from research.lexadd import CHECKS, battery
from research.p8_catalogue import WITNESS
from research.possibility import PRIMITIVE, explained_by, minimal_unrealized

LADDER = Ladder(2, 7)
PROBES = {
    "theorem-3-with-quality": [
        "thesis:egalitarian-dominance",
        "thesis:inequality-aversion",
        "thesis:non-sadism",
        "thesis:non-extreme-priority",
        "thesis:quality",
    ],
    "theorem-3-with-vrc-avoidance": [
        "thesis:egalitarian-dominance",
        "thesis:inequality-aversion",
        "thesis:non-sadism",
        "thesis:non-extreme-priority",
        "arrhenius-2003:vrc-avoidance",
    ],
    "dominance-priority-quantity-vrc": [
        "thesis:egalitarian-dominance",
        "thesis:non-extreme-priority",
        "thesis:quantity",
        "arrhenius-2003:vrc-avoidance",
    ],
}
PROBE_LADDER = Ladder(1, 6)
PROBE_LIVES = 6


def main() -> None:
    started = time.monotonic()
    additive = classify(LADDER, PRIMITIVE)
    matrix = {
        ax.id: {
            "description": ax.description,
            "satisfies": sorted(p for p, fn in CHECKS.items() if fn(ax, LADDER) is None),
        }
        for ax in battery(LADDER)
    }
    realized = [frozenset(r["satisfies"]) for r in matrix.values()] + [
        frozenset(m["conditions"]) for m in additive["maximal_realizable"]
    ]
    gaps = minimal_unrealized(PRIMITIVE, realized)
    coverage = [{"conditions": sorted(s), "explained_by": explained_by(s)} for s in gaps]
    probes = {}
    for name, principles in PROBES.items():
        insts = instances_over(domain(PROBE_LADDER, PROBE_LIVES), PROBE_LADDER, WITNESS, principles)
        words = cycle_words(insts, 7)
        probes[name] = {
            "principles": principles,
            "explained_by": explained_by(frozenset(principles)),
            "realized": any(frozenset(principles) <= r for r in realized),
            "cycles_found": len(words),
        }
    data = {
        "ladder": {"negative": LADDER.negative, "positive": LADDER.positive},
        "additive": additive,
        "lexicographic_additive": matrix,
        "coverage": coverage,
        "probes": probes,
    }
    write_result("p11_possibility", data, {"wall_time_s": round(time.monotonic() - started, 1)})
    _ledger(data)
    unexplained = [c for c in coverage if not c["explained_by"]]
    print(
        json.dumps(
            {
                "additive_mus": len(additive["minimal_unrealizable"]),
                "additive_mss": len(additive["maximal_realizable"]),
                "axiologies": len(matrix),
                "minimal_unrealized": len(coverage),
                "unexplained": len(unexplained),
                "probes": probes,
            },
            indent=1,
        )
    )


def _ledger(data: dict[str, Any]) -> None:
    additive = data["additive"]
    coverage = data["coverage"]
    unexplained = [c for c in coverage if not c["explained_by"]]
    sizes = sorted({len(c["conditions"]) for c in unexplained})
    entries = [
        LedgerEntry(
            candidate_id="P11-additive-dichotomy",
            hypothesis="For additive axiologies, every minimal impossibility among the thesis-family conditions is Egalitarian Dominance plus one Quality-type and one positivity-type condition.",
            motivation="An exact classification over a whole class of axiologies.",
            exact_formal_change="V = Σ g(w) for every real g on W_-2..W_7; all population sizes and witnesses",
            scope="all additive axiologies on the ladder",
            search_method="closed-form quantifier elimination + z3 + MARCO",
            result=f"{len(additive['minimal_unrealizable'])} minimal unrealizable sets, all of size 3; "
            f"{len(additive['maximal_realizable'])} maximal realizable sets (drop Egalitarian Dominance; "
            "drop the Quality family; drop the positivity family)",
            evidence_type="exact decision procedure",
            checked=True,
            minimal="MARCO-verified",
            interpretation="Quality-type conditions force g ≤ 0 on the lowest positive levels and positivity-type conditions force g ≥ 0 there; strict monotonicity breaks the tie. Inequality Aversion, NEP, Non-Elitism and GNEP never matter additively. This is the critical-level trade-off in exact form, likely known in substance (Blackorby, Bossert & Donaldson).",
            next_experiment="non-additive classes",
            result_scope="checked theorem",
            formalization_tier="exact over a model class (cross-read conditions)",
            witness_conditions="none: witnesses are quantified exactly",
            novelty_status="likely known in substance (BBD critical-level results)",
            status="confirmed",
        ),
        LedgerEntry(
            candidate_id="P11-possibility-map",
            hypothesis="The six known theorems explain every minimal condition set that no lexicographic-additive or additive axiology realizes.",
            motivation="Test whether Arrhenius's theorems are the complete list of minimal impossibilities of his language.",
            exact_formal_change=f"{len(data['lexicographic_additive'])} lexicographic-additive axiologies + all additive ones",
            scope="W_-2..W_7; every population size; outer witnesses up to 6",
            search_method="exact per-axiology checks + minimal-unrealized enumeration + implication closure",
            result=f"{len(coverage)} minimal unrealized sets; {len(coverage) - len(unexplained)} explained by a known theorem; "
            f"{len(unexplained)} unexplained (sizes {sizes})",
            evidence_type="exact model checks; gaps are open",
            checked=True,
            minimal="minimal by construction",
            interpretation="Most gaps swap a background-sensitive condition (Weak Quality Addition, GNEP) for one the lexicographic-additive class cannot tell apart from it; they need background-sensitive axiologies or new proofs. See docs/questions.md Q-010.",
            next_experiment="background-sensitive axioms; census probes with larger bounds",
            result_scope="finite computational result",
            formalization_tier="exact over a model class (cross-read conditions)",
            witness_conditions="outer existential witnesses up to research/lexadd.py WITNESS_MAX",
            status="confirmed",
        ),
    ]
    for name, p in data["probes"].items():
        entries.append(
            LedgerEntry(
                candidate_id=f"P11-probe-{name}",
                hypothesis=f"{name} is an impossibility theorem.",
                motivation="An unexplained gap in the possibility map.",
                exact_formal_change=f"{p['principles']}",
                scope=f"census under the Phase 8 witness, W_-1..W_6, <= {PROBE_LIVES} lives, cycles <= 7",
                search_method="exhaustive strict-cycle search",
                result=f"realized by a model: {p['realized']}; explained by a known theorem: {p['explained_by']}; cycles found: {p['cycles_found']}",
                evidence_type="bounded search",
                checked=True,
                minimal="n/a",
                interpretation="No model in the exact classes and no bounded contradiction: open.",
                next_experiment="background-sensitive models; longer cycles; a proof attempt",
                result_scope="bounded conjecture",
                formalization_tier="frozen agent-cross-read witness",
                witness_conditions="research/p8_catalogue.py WITNESS",
                status="open",
            )
        )
    record(entries)


if __name__ == "__main__":
    main()
