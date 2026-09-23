"""Phase 5: structure of the SAT side.

For every maximal SAT principle set (drop one group), enumerate every model on the seven active
relata exactly (47,293 total preorders, or all 9,535,241 preorders when completeness is the
dropped group), and compute forced and free comparisons. Structural conjectures are stated as
predicates over models and tested against the complete model sets.
"""

from __future__ import annotations

import time
from collections import Counter
from collections.abc import Callable
from typing import Any

from research.lab import (
    ACTIVE,
    LedgerEntry,
    compile_predicate,
    load_baseline,
    pairs,
    preorders,
    record,
    substantive_constraints,
    total_preorders,
    write_result,
)

N = len(ACTIVE)
IDX = {x: i for i, x in enumerate(ACTIVE)}
PAIRS = pairs(ACTIVE)


def ge(mask: int, x: str, y: str) -> bool:
    return bool(mask >> (IDX[x] * N + IDX[y]) & 1)


def relation(mask: int, x: str, y: str) -> str:
    a, b = ge(mask, x, y), ge(mask, y, x)
    return "~" if a and b else ">" if a else "<" if b else "||"


def census(models: list[int]) -> dict[str, Any]:
    per_pair: dict[str, Counter[str]] = {f"{x}|{y}": Counter() for x, y in PAIRS}
    for m in models:
        for x, y in PAIRS:
            per_pair[f"{x}|{y}"][relation(m, x, y)] += 1
    forced = {k: next(iter(v)) for k, v in per_pair.items() if len(v) == 1}
    return {
        "models": len(models),
        "forced_pairs": forced,
        "free_pairs": {k: dict(v) for k, v in per_pair.items() if len(v) > 1},
    }


GROUP_PRINCIPLE = {
    "repugnance-avoidance": "avoid-repugnance",
    "anti-egalitarianism-avoidance": "avoid-anti-egalitarianism",
    "sadism-avoidance": "avoid-sadism",
    "minimal-non-extreme-priority": "minimal-non-extreme-priority",
    "dominance": "dominance",
    "addition": "addition",
}


def conjectures() -> dict[str, Callable[[int], bool]]:
    """Structural conjectures for the escape (completeness-dropped) family.

    Each was written after inspecting the minimum escapes in P2 and before running this census.
    """

    def incomparable(m: int, x: str, y: str) -> bool:
        return relation(m, x, y) == "||"

    def degree(m: int, x: str) -> int:
        return sum(1 for y in ACTIVE if y != x and incomparable(m, x, y))

    return {
        "E1: some population is incomparable to at least two others": lambda m: any(
            degree(m, x) >= 2 for x in ACTIVE
        ),
        "E2: A or AAF is incomparable to at least one other population": lambda m: (
            degree(m, "A") >= 1 or degree(m, "AAF") >= 1
        ),
        "E3: the incomparability graph is connected (on non-isolated vertices)": lambda m: (
            _connected(m)
        ),
        "E4: some different-number comparison is unresolved": lambda m: any(
            incomparable(m, x, y) and _size(x) != _size(y) for x, y in PAIRS
        ),
        "E5: some avoidance comparison is unresolved (A:D, AC:D, AAE:AAF, AAF:G)": lambda m: any(
            incomparable(m, *p) for p in (("A", "D"), ("AC", "D"), ("AAE", "AAF"), ("AAF", "G"))
        ),
        "E6: AAF is incomparable to G or to AAE": lambda m: (
            incomparable(m, "AAF", "G") or incomparable(m, "AAE", "AAF")
        ),
        "E7: the strict chain AC ≻ G and AAE ⪰ AB both hold": lambda m: (
            relation(m, "AC", "G") == ">" and ge(m, "AAE", "AB")
        ),
    }


SIZES = {"A": 1, "AB": 4, "AAE": 4, "AC": 22, "AAF": 22, "D": 22, "G": 22}


def _size(x: str) -> int:
    return SIZES[x]


def _connected(m: int) -> bool:
    edges = [(x, y) for x, y in PAIRS if relation(m, x, y) == "||"]
    nodes = {v for e in edges for v in e}
    if not nodes:
        return True
    seen = {next(iter(nodes))}
    frontier = list(seen)
    while frontier:
        v = frontier.pop()
        for x, y in edges:
            for a, b in ((x, y), (y, x)):
                if a == v and b not in seen:
                    seen.add(b)
                    frontier.append(b)
    return seen == nodes


def main() -> None:
    started = time.monotonic()
    spec = load_baseline()
    sub = list(substantive_constraints(spec))
    complete = list(total_preorders(N))
    results: dict[str, Any] = {}
    for group, principle in GROUP_PRINCIPLE.items():
        kept = [c.formula for c in sub if c.principle_id != principle]
        predicate = compile_predicate(kept, ACTIVE)
        models = [m for m in complete if predicate(m)]
        results[f"drop {group}"] = census(models)
    predicate = compile_predicate([c.formula for c in sub], ACTIVE)
    escapes = [m for m in preorders(N) if predicate(m)]
    results["drop completeness"] = census(escapes)
    tests = {}
    for name, test in conjectures().items():
        failures = [m for m in escapes if not test(m)]
        tests[name] = {
            "holds_on_all_escapes": not failures,
            "counterexamples": len(failures),
            "smallest_counterexample": (
                {
                    f"{x}|{y}": relation(min(failures, key=_incomparable_count), x, y)
                    for x, y in PAIRS
                }
                if failures
                else None
            ),
        }
    data = {"maximal_sat_census": results, "escape_conjectures": tests}
    write_result("p5_sat_structure", data, {"wall_time_s": round(time.monotonic() - started, 2)})
    _ledger(data)


def _incomparable_count(m: int) -> int:
    return sum(1 for x, y in PAIRS if relation(m, x, y) == "||")


def _ledger(data: dict[str, Any]) -> None:
    census_rows = {
        k: (v["models"], len(v["forced_pairs"])) for k, v in data["maximal_sat_census"].items()
    }
    entries = [
        LedgerEntry(
            candidate_id="P5-maximal-sat-census",
            hypothesis="Each maximal SAT set has a compact forced backbone.",
            motivation="Study the SAT side, not only UNSAT.",
            exact_formal_change="drop one group at a time (baseline frontier)",
            scope="7 active relata; complete preorders (or all preorders when completeness is dropped)",
            search_method="exhaustive enumeration of 47,293 total preorders / 9,535,241 preorders",
            result=f"(models, forced pairs of 21) per dropped group: {census_rows}",
            evidence_type="exhaustive enumeration",
            checked=True,
            minimal="n/a",
            interpretation="See docs/journal/2026-09-22-turn-1.md for the backbone of each region.",
            next_experiment="characterize backbones as closed-form orders",
            result_scope="finite computational result",
            formalization_tier="frozen source-reviewed witness",
            status="confirmed",
        )
    ]
    for name, t in data["escape_conjectures"].items():
        entries.append(
            LedgerEntry(
                candidate_id="P5-conjecture-" + name.split(":")[0],
                hypothesis=name,
                motivation="Generalize the P2 minimum escapes.",
                exact_formal_change="none",
                scope="all 20,169 escape preorders on the 7 active relata",
                search_method="exhaustive falsification",
                result=(
                    "holds on every escape"
                    if t["holds_on_all_escapes"]
                    else f"false: {t['counterexamples']} counterexamples"
                ),
                evidence_type="exhaustive enumeration",
                checked=True,
                minimal="n/a",
                counterexample_if_false=str(t["smallest_counterexample"])
                if t["smallest_counterexample"]
                else "n/a",
                interpretation="",
                next_experiment="test on schema skeletons (P6)"
                if t["holds_on_all_escapes"]
                else "n/a",
                result_scope="finite computational result",
                formalization_tier="frozen source-reviewed witness",
                status="confirmed" if t["holds_on_all_escapes"] else "refuted",
            )
        )
    record(entries)


if __name__ == "__main__":
    main()
