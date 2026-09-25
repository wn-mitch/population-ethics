"""The article export is deterministic and its proof scenes are single strict cycles."""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction
from typing import Any

from research.export_article import LADDER_OF_1999, build, render
from research.p8_catalogue import THEOREM_3


def _cycle(scene: dict[str, Any]) -> None:
    names = {p["name"] for p in scene["populations"]}
    edges = scene["edges"]
    assert all(e["from"] in names and e["to"] in names for e in edges)
    assert sum(e["rel"] == "strict" for e in edges) == 1
    assert [e["step"] for e in edges] == list(range(1, len(edges) + 1))
    # One simple cycle: every population has exactly one out-edge and one in-edge, and
    # following the edges from any start visits every population once.
    assert Counter(e["from"] for e in edges) == Counter(names)
    assert Counter(e["to"] for e in edges) == Counter(names)
    succ = {e["from"]: e["to"] for e in edges}
    seen, node = [], next(iter(names))
    while node not in seen:
        seen.append(node)
        node = succ[node]
    assert len(seen) == len(names)


def test_export_is_deterministic_and_scenes_are_strict_cycles() -> None:
    data = build()
    assert render(data) == render(build())
    _cycle(data["theorem1"])
    _cycle(data["theorem1999"])
    assert len(data["theorem1"]["edges"]) == 5
    assert len(data["theorem1999"]["edges"]) == 5
    assert data["theorem1999"]["uses_completeness"] is False
    for p in data["theorem1999"]["populations"]:
        assert p["levels"] == sorted(LADDER_OF_1999[v] for v in p["source_levels"])


def test_1999_witness_on_the_ladder_has_the_theorem_3_level_pattern() -> None:
    # Same skeleton as thesis Theorem 3, at witness r = 5 instead of r = 3: the set of
    # levels each population occupies is the same, only the very-low group sizes differ.
    mapped = {frozenset(p["levels"]) for p in build()["theorem1999"]["populations"]}
    assert mapped == {frozenset(p) for p in THEOREM_3.populations.values()}


def test_escape_counts_and_additive_fixtures_are_consistent() -> None:
    data = build()
    escape = data["escape"]
    assert sum(escape["k_distribution"].values()) == escape["escape_models"]
    assert escape["minimum_pattern"]["star_center"] == "AAF"
    assert escape["minimum_pattern"]["size"] == escape["k_min"] == 4
    assert {p["name"] for p in escape["populations"]} == {"A", "AB", "AC", "AAE", "AAF", "D", "G"}
    additive = data["additive"]
    assert len(additive["minimal_unrealizable"]) == 20
    assert all("thesis:egalitarian-dominance" in t for t in additive["minimal_unrealizable"])
    by_name = {f["name"]: f for f in additive["fixtures"]}
    total = by_name["total"]["verdicts"]
    assert total["thesis:egalitarian-dominance"] and total["thesis:quantity"]
    assert not total["thesis:quality"]
    # Each exported maximal g satisfies exactly its listed conditions, and every minimal
    # unrealizable triple is violated by every exported g.
    for i, maximal in enumerate(additive["maximal_realizable"]):
        verdicts = by_name[f"exported-maximal-{i}"]["verdicts"]
        assert {c for c, ok in verdicts.items() if ok} == set(maximal["conditions"])
        for triple in additive["minimal_unrealizable"]:
            assert not all(verdicts[c] for c in triple)
    for fixture in additive["fixtures"]:
        for value in fixture["g"].values():
            Fraction(value)  # parseable rationals
    json.dumps(data)
