"""Known proof skeletons and a matcher that measures how much of a core is already known.

A skeleton is a set of hyperedges over relata. Each edge carries a principle *role*, a logical
shape, and its ordered relata. Roles put principles from different papers into one vocabulary:
Arrhenius's 1999 Minimal Inequality Aversion and the 2000 Non-Anti-Egalitarianism both play
``inequality-aversion``. The correspondence is this project's judgment, recorded per principle
in ``ROLE``. It is not a claim that the principles are equivalent.

Shapes are normalized for the complete branch, where ``¬(X ≻ Y)`` is ``Y ⪰ X``. Matching is
therefore only meaningful for cores found under completeness (the rank-encoded schema search).

Only skeletons whose every role has a v0 counterpart are catalogued. Arrhenius's Dominance
Addition, Quantity, Non-Elitism lemma chains, and Very Repugnant Conclusion avoidance have
none, so thesis Theorems 1, 2 and 4, the 2003 theorem, and the 2009/2011 theorem are listed in
``UNCATALOGUED`` and cannot be matched.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any

from research.schema import BASELINE_SKELETON, Instance, Pop

Edge = tuple[str, str, tuple[int, ...]]  # (role, shape, relata indices)

# Principle id -> role. v0 ids come from research.schema; arrhenius-1999:* from research.p7.
ROLE = {
    "dominance": "dominance",
    "non-anti-egalitarianism": "inequality-aversion",
    "non-repugnance": "quality",  # Quality Addition on an empty background
    "non-sadism": "sadism-avoidance",
    "mnep": "priority",
    "addition": "addition",
    "arrhenius-1999:egalitarian-dominance": "dominance",
    "arrhenius-1999:minimal-inequality-aversion": "inequality-aversion",
    "arrhenius-1999:quality-addition": "quality",
    "arrhenius-1999:non-sadism": "sadism-avoidance",
    "arrhenius-1999:minimal-non-extreme-priority": "priority",
}


def normalize(core: Sequence[Instance]) -> tuple[list[Pop], list[Edge]]:
    """Relata in sorted order and complete-branch edges over their indices."""
    nodes = sorted({x for inst in core for x in inst.args})
    index = {x: i for i, x in enumerate(nodes)}
    edges: list[Edge] = []
    for inst in core:
        shape = inst.shape
        args = tuple(index[x] for x in inst.args)
        if shape == "N":
            shape, args = "W", (args[1], args[0])
        edges.append((ROLE[inst.principle], shape, args))
    return nodes, edges


@dataclass(frozen=True)
class KnownSkeleton:
    id: str
    sources: tuple[
        str, ...
    ]  # corpus/literature.toml work ids, or docs/journal/2026-09-22-turn-1.md results
    relata: tuple[str, ...]
    edges: tuple[Edge, ...]
    note: str


def _from_instances(
    identifier: str, sources: tuple[str, ...], names: Sequence[str], core: list[Instance], note: str
) -> KnownSkeleton:
    nodes, edges = normalize(core)
    if len(names) != len(nodes):
        raise ValueError(f"{identifier}: {len(names)} names for {len(nodes)} relata")
    return KnownSkeleton(identifier, sources, tuple(names), tuple(edges), note)


def _p(i: int) -> Pop:
    return (i,)


# Placeholder populations (i,) keep relata distinct; names follow the sorted placeholder order.
CATALOGUE: tuple[KnownSkeleton, ...] = (
    _from_instances(
        "arrhenius-2000-ep",
        ("arrhenius-2000-ep",),
        ("A", "AB", "AC", "AAE", "AAF", "D", "G"),
        BASELINE_SKELETON,
        "The frozen E&P 2000 witness skeleton.",
    ),
    _from_instances(
        "arrhenius-1999",
        (
            "arrhenius-1999-weak-ordering",
            "arrhenius-2000-thesis",  # Theorem 3, and Lemma 5.3 with lemma-derived conditions
            "arrhenius-2001-osterberg",
            "arrhenius-2009-one-more",  # Lemma 4
            "arrhenius-2011-impossibility",  # Lemma 1.4
            "thomas-2016-reconstructing",  # Theorem 3
        ),
        ("A∪A'∪E", "A∪B", "B∪C", "G", "A∪A'∪F"),
        [
            Instance("arrhenius-1999:minimal-non-extreme-priority", (_p(0), _p(1))),
            Instance("arrhenius-1999:quality-addition", (_p(1), _p(2))),
            Instance("arrhenius-1999:egalitarian-dominance", (_p(2), _p(3))),
            Instance("arrhenius-1999:minimal-inequality-aversion", (_p(3), _p(4))),
            Instance("arrhenius-1999:non-sadism", (_p(4), _p(0))),
        ],
        "A single weak cycle closed by one strict Egalitarian Dominance link; no completeness.",
    ),
    _from_instances(
        "project-r5-triangle",
        ("docs/journal/2026-09-22-turn-1.md#R5",),
        ("bundle", "(q+1)·b", "(q+1)·c"),
        [
            Instance("mnep", (_p(0), _p(1))),
            Instance("dominance", (_p(1), _p(2))),
            Instance("non-anti-egalitarianism", (_p(0), _p(2))),
        ],
        "Formalization diagnostic: fires when very-high and very-low are only ordinal.",
    ),
    _from_instances(
        "project-r6-gapped",
        ("docs/journal/2026-09-22-turn-1.md#R6",),
        ("A", "AB", "AC'", "AAE", "AAF", "7⁷", "6⁷", "5⁷"),
        [
            Instance("addition", (_p(0), _p(1), _p(2))),
            Instance("mnep", (_p(3), _p(1))),
            Instance("mnep", (_p(2), _p(6))),
            Instance("non-repugnance", (_p(5), _p(0))),
            Instance("non-sadism", (_p(3), _p(4))),
            Instance("non-anti-egalitarianism", (_p(4), _p(7))),
            Instance("dominance", (_p(5), _p(6))),
            Instance("dominance", (_p(6), _p(7))),
        ],
        "Solver-found on the gapped grid; the 1999 frame with an Addition-based closing link.",
    ),
)

UNCATALOGUED = {
    "arrhenius-2000-thesis#theorem-1": "Quantity has no v0 counterpart.",
    "arrhenius-2000-thesis#theorem-2": "Dominance Addition has no v0 counterpart.",
    "arrhenius-2000-thesis#theorem-4": "Non-Elitism and GNEP lemma chains have no v0 counterpart.",
    "arrhenius-2003-vrc": "Dominance Addition and VRC avoidance have no v0 counterpart.",
    "arrhenius-2009-one-more": "Only Lemma 4 is catalogued, as arrhenius-1999.",
    "arrhenius-2022-without-transitivity": "Maximality over finite sets has no v0 counterpart.",
}


@dataclass(frozen=True)
class Match:
    known_id: str
    matched: int  # known edges embedded in the core
    known_edges: int
    exact: bool  # the core is isomorphic to the known skeleton
    mapping: dict[int, int]  # known relatum index -> core relatum index
    residual: tuple[int, ...]  # core edges no maximum embedding covers


def best_embedding(
    known: Sequence[Edge], core: Sequence[Edge]
) -> tuple[int, dict[int, int], set[int]]:
    """Maximum number of known edges embeddable into distinct core edges by one injective map.

    Branch and bound over known edges: each is either skipped or sent to a compatible unused
    core edge consistent with the partial relatum map. Returns the maximum count, the map of
    the first maximum embedding found, and the core edges used by *any* maximum embedding.
    """
    best: tuple[int, dict[int, int], set[int]] = (0, {}, set())

    def extend(i: int, mapping: dict[int, int], used: set[int], count: int) -> None:
        nonlocal best
        if count > best[0]:
            best = (count, dict(mapping), set(used))
        elif count == best[0] and count:
            best[2].update(used)
        if i == len(known) or count + (len(known) - i) < best[0]:
            return
        role, shape, args = known[i]
        for j, (c_role, c_shape, c_args) in enumerate(core):
            if j in used or c_role != role or c_shape != shape or len(c_args) != len(args):
                continue
            added: list[int] = []
            ok = True
            for a, b in zip(args, c_args, strict=True):
                if a in mapping:
                    ok = mapping[a] == b
                elif b in mapping.values():
                    ok = False
                else:
                    mapping[a] = b
                    added.append(a)
                if not ok:
                    break
            if ok:
                used.add(j)
                extend(i + 1, mapping, used, count + 1)
                used.discard(j)
            for a in added:
                del mapping[a]
        extend(i + 1, mapping, used, count)

    extend(0, {}, set(), 0)
    return best


def match(core: Sequence[Instance], known: KnownSkeleton) -> Match:
    nodes, edges = normalize(core)
    count, mapping, used = best_embedding(known.edges, edges)
    exact = count == len(known.edges) == len(edges) and len(known.relata) == len(nodes)
    residual = tuple(j for j in range(len(edges)) if j not in used)
    return Match(known.id, count, len(known.edges), exact, mapping, residual)


def known_ground(
    core: Sequence[Instance], catalogue: Sequence[KnownSkeleton] = CATALOGUE
) -> dict[str, Any]:
    """How much of ``core`` the catalogue already covers.

    ``exact_known`` names a catalogued skeleton isomorphic to the core. ``largest_fragment`` is
    the catalogued skeleton with the most edges embedded; ties go to catalogue order.
    ``residual`` lists the core instances that no maximum embedding of that skeleton covers.
    ``uncovered_by_published`` lists the core instances that no maximum embedding of any
    published (non-``project-``) skeleton covers; a novelty claim rests on these.
    ``uncovered_by_catalogue`` does the same over the whole catalogue, so it also discounts
    steps the project has already found. Smaller
    embeddings are ignored, since a single edge of the right role always embeds.
    """
    matches = [match(core, k) for k in catalogue]
    exact = next((m.known_id for m in matches if m.exact), None)
    top = max(matches, key=lambda m: m.matched)
    published = [m for m in matches if not m.known_id.startswith("project-")]
    covered = {j for j in range(len(core)) if any(j not in m.residual for m in published)}
    anywhere = {j for j in range(len(core)) if any(j not in m.residual for m in matches)}
    return {
        "exact_known": exact,
        "largest_fragment": top.known_id,
        "largest_fragment_edges": f"{top.matched}/{top.known_edges}",
        "residual": [_describe(core[j]) for j in top.residual],
        "uncovered_by_published": [
            _describe(core[j]) for j in range(len(core)) if j not in covered
        ],
        "uncovered_by_catalogue": [
            _describe(core[j]) for j in range(len(core)) if j not in anywhere
        ],
        "per_known": {m.known_id: f"{m.matched}/{m.known_edges}" for m in matches},
    }


def novelty_rank(entry: dict[str, Any]) -> tuple[bool, bool, int, int]:
    """Sort key for spending verification on new ground.

    Cores isomorphic to a catalogued skeleton go last. Before them go cores whose every
    instance lies in a maximum embedding of some catalogued skeleton, published or project.
    Within each group smaller cores come first.
    """
    kg = entry["known_ground"]
    return (
        kg["exact_known"] is not None,
        not kg["uncovered_by_catalogue"],
        entry["instances"],
        entry["relata"],
    )


def _describe(inst: Instance) -> str:
    return f"{inst.principle}({', '.join(str(list(x)) for x in inst.args)})"
