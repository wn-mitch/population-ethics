"""Export the article data bundle for the interactive Arrhenius article.

The article (alpacasoft ``apps/arrhenius``) draws every population, edge and count from this
one JSON file rather than from transcription. Each section names the checked artefact it comes
from, and ``provenance`` records the ``result_sha256`` of every result file read, so a stale or
hand-edited copy in the app can be detected by its test suite.

Sections:

- ``ladder``: the ordinal ladder W_-1, W_0, W_1 … W_6 the proof scenes are drawn on.
- ``theorem1``: thesis Theorem 1 frozen at the Phase 8 witness (``research/p8_catalogue.py``).
- ``theorem1999``: the 1999 witness (``research/p7_arrhenius1999.py``), with its numeric levels
  mapped ordinally onto the ladder. The map is exact for the 1999 conditions, which only
  compare levels; it gives thesis Theorem 3's populations at witness r = 5.
- ``escape``: the incompleteness results on the 2000 witness (``research/results/p2_escape.json``)
  and the seven active 2000 populations (``experiments/arrhenius-2000-proof.toml``).
- ``census``: the motif census counts (``research/results/p9_census.json``).
- ``additive``: the additive possibility map (``research/results/p11_possibility.json``) plus
  fixtures: sample ``g`` tables with per-condition verdicts decided by ``research/additive.py``,
  so the article's TypeScript port of the closed forms can be tested against the exact engine.
- ``readings``: informal and exact excerpts, with pages, for every principle the article names.

Run ``just article-data``; it writes ``research/results/article.json`` and copies it into the
app when the app directory exists.
"""

from __future__ import annotations

import hashlib
import json
import shutil
import sys
import tomllib
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any

import z3  # type: ignore[import-untyped]

from research.additive import CONDITIONS, AdditiveEngine
from research.lab import RESULTS_DIR, ROOT
from research.ladder import Ladder
from research.p7_arrhenius1999 import CORE as CORE_1999
from research.p7_arrhenius1999 import POPULATIONS as POPULATIONS_1999
from research.p8_catalogue import THEOREM_1
from research.readings import load as load_readings
from research.schema import Pop

OUTPUT = RESULTS_DIR / "article.json"
APP_COPY = (
    Path.home() / "alpacasoft" / "apps" / "arrhenius" / "src" / "lib" / "data" / "arrhenius.json"
)

# Numeric 1999 levels (gapped grid, p = q = 1, r = 5) to ladder indices. Only the order of the
# very-low levels 1 < 5 < 7 and the very-high level 14 matters to the 1999 conditions.
LADDER_OF_1999 = {-1: -1, 1: 1, 5: 2, 7: 3, 14: 4}

STRICT = {"thesis:egalitarian-dominance", "arrhenius-1999:egalitarian-dominance"}

ACTIVE_2000 = ("A", "AB", "AC", "AAE", "AAF", "D", "G")

# Principles the article names, with the reading that carries their excerpt.
ARTICLE_PRINCIPLES = (
    "thesis:egalitarian-dominance",
    "thesis:quantity",
    "thesis:quality",
    "thesis:theorem-1",
    "arrhenius-1999:egalitarian-dominance",
    "arrhenius-1999:quality-addition",
    "arrhenius-1999:minimal-inequality-aversion",
    "arrhenius-1999:non-sadism",
    "arrhenius-1999:minimal-non-extreme-priority",
    "arrhenius-1999:theorem",
    "dominance",
    "addition",
    "mnep",
    "non-sadism",
    "non-anti-egalitarianism",
    "non-repugnance",
    "arrhenius-2000-ep:theorem",
    "thesis:dominance-addition",
    "thesis:inequality-aversion",
    "thesis:non-sadism",
    "thesis:non-extreme-priority",
    "thesis:weak-quality-addition",
    "thesis:non-elitism",
    "thesis:general-non-extreme-priority",
    "thesis:weak-non-sadism",
    "arrhenius-2003:dominance-addition",
    "arrhenius-2003:non-elitism",
    "arrhenius-2003:vrc-avoidance",
    "arrhenius-2009:weak-quality-addition",
)


def _counts(pop: Pop) -> list[dict[str, int]]:
    """A population as level/count groups, lowest level first."""
    return [{"level": level, "count": n} for level, n in sorted(Counter(pop).items())]


def _population(name: str, pop: Pop) -> dict[str, Any]:
    return {"name": name, "levels": list(pop), "groups": _counts(pop)}


def _edge(principle: str, left: str, right: str, step: int) -> dict[str, Any]:
    return {
        "from": left,
        "to": right,
        "principle": principle,
        "rel": "strict" if principle in STRICT else "weak",
        "step": step,
    }


def _result(name: str) -> tuple[dict[str, Any], str]:
    data = json.loads((RESULTS_DIR / f"{name}.json").read_text())
    return data["result"], data["result_sha256"]


def _theorem1() -> dict[str, Any]:
    return {
        "source": "arrhenius-2000-thesis",
        "statement": THEOREM_1.statement,
        "populations": [_population(n, p) for n, p in THEOREM_1.populations.items()],
        "edges": [_edge(p, x, y, i + 1) for i, (p, x, y) in enumerate(THEOREM_1.core)],
        "note": THEOREM_1.note,
    }


def _theorem1999() -> dict[str, Any]:
    populations = []
    for name, pop in POPULATIONS_1999.items():
        mapped: Pop = tuple(sorted(LADDER_OF_1999[v] for v in pop))
        entry = _population(name, mapped)
        entry["source_levels"] = list(pop)
        populations.append(entry)
    by_pop = {pop: name for name, pop in POPULATIONS_1999.items()}
    edges = [
        _edge(inst.principle, by_pop[inst.args[0]], by_pop[inst.args[1]], i + 1)
        for i, inst in enumerate(CORE_1999)
    ]
    return {
        "source": "arrhenius-1999-weak-ordering",
        "witness": {"p": 1, "q": 1, "r": 5},
        "source_grid": {"very_low": [1, 5, 7], "very_high": 14, "slightly_negative": -1},
        "level_map": {str(k): v for k, v in LADDER_OF_1999.items()},
        "uses_completeness": False,
        "populations": populations,
        "edges": edges,
    }


def _escape() -> tuple[dict[str, Any], str]:
    result, sha = _result("p2_escape")
    spec = tomllib.loads((ROOT / "experiments" / "arrhenius-2000-proof.toml").read_text())
    pops: dict[str, Pop] = {}
    for entry in spec["domain"]["populations"]:
        if "values" in entry:
            pops[entry["name"]] = tuple(sorted(entry["values"]))
        else:
            pops[entry["name"]] = tuple(
                sorted(g["welfare"] for g in entry["groups"] for _ in range(g["count"]))
            )
    enumeration = result["enumeration"]
    star = [m for m in result["mcses"] if m["size"] == result["k_min"]]
    if len(star) != 1:
        raise AssertionError(f"expected one minimum MCS, found {len(star)}")
    return {
        "source": "arrhenius-2000-ep",
        "witness": dict(spec["witness_bindings"]),
        "categories": dict(spec["categories"]),
        "populations": [_population(n, pops[n]) for n in ACTIVE_2000],
        "preorders_scanned": enumeration["preorders_scanned"],
        "escape_models": enumeration["escape_models"],
        "k_min": result["k_min"],
        "k_max": result["k_max"],
        "k_distribution": {str(k): v for k, v in enumeration["k_distribution_models"].items()},
        "forced_comparable": [
            p.removeprefix("completeness:") for p in enumeration["forced_comparable"]
        ],
        "minimum_pattern": star[0],
        "single_route_min_k": {
            p.removeprefix("completeness:"): k for p, k in result["single_route_min_k"].items()
        },
        "min_k_with_same_number_complete": result["min_k_with_same_number_complete"],
        "min_unresolved_different_number_pairs": result["min_unresolved_different_number_pairs"],
    }, sha


def _census() -> tuple[dict[str, Any], str]:
    result, sha = _result("p9_census")
    l0 = result["l0"]
    family = max(result["family"], key=lambda f: (f["max_lives"], f["max_length"]))
    return {
        "cycle_minimal_cores_by_edges": l0["cycle_minimal_cores_by_edges"],
        "necklace_counts": l0["necklace_counts"],
        "cycle_counts_match_necklaces": l0["cycle_counts_match_necklaces"],
        "all_cycle_cores_are_simple_strict_cycles": l0["all_cycle_cores_are_simple_strict_cycles"],
        "one_fork_minimal_cores_by_edges": l0["one_fork_minimal_cores_by_edges"],
        "family": {
            "max_lives": family["max_lives"],
            "max_length": family["max_length"],
            "principle_words": family["words"],
            "words_by_length": family["words_by_length"],
            "role_words": len(family["role_words"]),
            "every_word_has_egalitarian_dominance": all(
                "thesis:egalitarian-dominance" in w["example"]["word"]
                or "arrhenius-2003:egalitarian-dominance" in w["example"]["word"]
                for w in family["role_words"]
            ),
        },
    }, sha


def _verdicts(ladder: Ladder, g: dict[int, Fraction]) -> dict[str, bool]:
    """Decide every condition for one concrete g with the exact additive engine."""
    engine = AdditiveEngine(ladder)
    for level, value in g.items():
        engine.solver.add(engine.g[level] == z3.RealVal(f"{value.numerator}/{value.denominator}"))
    return {cid: engine.require([cid]).decision == "sat" for cid in CONDITIONS}


def _fixture_tables(
    ladder: Ladder, exported: list[dict[str, str]]
) -> dict[str, dict[int, Fraction]]:
    levels = ladder.levels
    tables: dict[str, dict[int, Fraction]] = {
        "total": {v: Fraction(v) for v in levels},
        "critical-level-2": {v: Fraction(v - 2) for v in levels},
        "all-zero": {v: Fraction(0) for v in levels},
        "bounded-positive": {v: Fraction(0) if v <= 0 else Fraction(1, 2**v) for v in levels},
        "negative-only": {v: Fraction(min(v, 0)) for v in levels},
        "step-at-four": {v: Fraction(1 if v >= 4 else -1) for v in levels},
        "constant-positive": {v: Fraction(1) for v in levels},
        "strictly-increasing-negative": {v: Fraction(v - 10) for v in levels},
    }
    for i, table in enumerate(exported):
        tables[f"exported-maximal-{i}"] = {int(k): Fraction(v) for k, v in table.items()}
    return tables


def _additive() -> tuple[dict[str, Any], str]:
    result, sha = _result("p11_possibility")
    ladder = Ladder(**result["ladder"])
    additive = result["additive"]
    maximal = additive["maximal_realizable"]
    fixtures = []
    for name, table in _fixture_tables(ladder, [m["g"] for m in maximal]).items():
        fixtures.append(
            {
                "name": name,
                "g": {str(k): f"{v.numerator}/{v.denominator}" for k, v in table.items()},
                "verdicts": _verdicts(ladder, table),
            }
        )
    return {
        "ladder": {"levels": list(ladder.levels), **result["ladder"]},
        "conditions": list(CONDITIONS),
        "maximal_realizable": maximal,
        "minimal_unrealizable": additive["minimal_unrealizable"],
        "fixtures": fixtures,
    }, sha


def _readings() -> dict[str, Any]:
    readings = load_readings()
    out: dict[str, Any] = {}
    for principle in ARTICLE_PRINCIPLES:
        r = readings[principle]
        out[principle] = {
            "work": r.work,
            "name": r.name,
            "printed_page": r.printed_page,
            "excerpt": r.excerpt,
            "informal_excerpt": r.extra.get("informal_excerpt", ""),
            "relation": r.extra.get("relation", ""),
            "review_state": r.review_state,
        }
    return out


def build() -> dict[str, Any]:
    escape, escape_sha = _escape()
    census, census_sha = _census()
    additive, additive_sha = _additive()
    readings_sha = hashlib.sha256((ROOT / "corpus" / "readings.toml").read_bytes()).hexdigest()
    ladder = Ladder(negative=1, positive=6)
    return {
        "schema": "population-ethics.article/v1",
        "ladder": {"levels": list(ladder.levels), "negative": 1, "positive": 6},
        "theorem1": _theorem1(),
        "theorem1999": _theorem1999(),
        "escape": escape,
        "census": census,
        "additive": additive,
        "readings": _readings(),
        "provenance": {
            "p2_escape": escape_sha,
            "p9_census": census_sha,
            "p11_possibility": additive_sha,
            "readings_toml": readings_sha,
            "ledger_rows": [
                "P2-escape-sat",
                "P2-min-incomparability",
                "P2-avoidance-necessity",
                "P2-same-number-escape",
                "P9-l0-cycle-motif",
                "P9-family-N4-L5",
                "P7-arrhenius-1999-baseline",
            ],
        },
    }


def render(data: dict[str, Any]) -> str:
    return json.dumps(data, indent=1, sort_keys=True, ensure_ascii=False) + "\n"


def main(argv: list[str]) -> None:
    text = render(build())
    OUTPUT.write_text(text)
    print(f"wrote {OUTPUT.relative_to(ROOT)} ({len(text)} bytes)")
    if "--no-copy" not in argv and APP_COPY.parent.is_dir():
        shutil.copyfile(OUTPUT, APP_COPY)
        print(f"copied to {APP_COPY}")


if __name__ == "__main__":
    main(sys.argv[1:])
