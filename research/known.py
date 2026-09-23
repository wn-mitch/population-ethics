"""Known proof skeletons and a matcher that measures how much of a core is already known.

A skeleton is a set of hyperedges over relata. Each edge carries a principle *role*, a logical
shape, and its ordered relata. Roles put principles from different papers into one vocabulary:
Arrhenius's 1999 Minimal Inequality Aversion and the 2000 Non-Anti-Egalitarianism both play
``inequality-aversion``. The correspondence is this project's judgment, recorded per principle
in ``research/roles.toml``. It is not a claim that the principles are equivalent.

Shapes are normalized for the complete branch, where ``¬(X ≻ Y)`` is ``Y ⪰ X``. Matching is
therefore only meaningful for cores found under completeness (the rank-encoded schema search).

The catalogue holds every ordering-based Arrhenius theorem from 1999 to 2011. Thesis Theorem 3,
thesis Theorem 4 (at Lemma 5.3) and 2009 Lemma 4 are the 1999 skeleton at the role level, which
research/p8_catalogue.py confirms; Theorems 4 and 2009 are catalogued at the level of their
final lemma, whose derived conditions (β, δ, Restricted Quality Addition) are edge
realizations of Non-Elitism, GNEP and Weak Quality Addition. ``UNCATALOGUED`` lists theorems
the schema cannot express.
"""

from __future__ import annotations

import tomllib
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from research.readings import require_reviewed
from research.schema import BASELINE_SKELETON, Instance, Pop

Edge = tuple[str, str, tuple[int, ...]]  # (role, shape, relata indices)

ROLES_PATH = Path(__file__).with_name("roles.toml")


def load_roles(path: Path = ROLES_PATH) -> dict[str, str]:
    """Principle id -> role from research/roles.toml; every id must pass the review gate."""
    rows = tomllib.loads(path.read_text())["principles"]
    roles: dict[str, str] = {}
    for row in rows:
        if row["id"] in roles:
            raise ValueError(f"{row['id']}: two role entries")
        if not row.get("reason"):
            raise ValueError(f"{row['id']}: role entry has no reason")
        roles[row["id"]] = row["role"]
    require_reviewed(roles)
    return roles


ROLE = load_roles()


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
    # corpus/literature.toml work ids, or docs/journal/2026-09-22-turn-1.md results
    sources: tuple[str, ...]
    relata: tuple[str, ...]
    edges: tuple[Edge, ...]
    note: str


def _from_instances(
    identifier: str, sources: tuple[str, ...], names: Sequence[str], core: list[Instance], note: str
) -> KnownSkeleton:
    require_reviewed(i.principle for i in core)
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
            "arrhenius-2009-one-more",  # Lemma 4 (with Restricted Quality Addition, β, δ)
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
    # Frozen and verified in research/p8_catalogue.py; relata follow the placeholder order.
    _from_instances(
        "arrhenius-thesis-theorem-1",
        ("arrhenius-2000-thesis",),
        ("A1", "A2", "A3", "A4", "B"),
        [
            Instance("thesis:quantity", (_p(1), _p(0))),
            Instance("thesis:quantity", (_p(2), _p(1))),
            Instance("thesis:quantity", (_p(3), _p(2))),
            Instance("thesis:egalitarian-dominance", (_p(4), _p(3))),
            Instance("thesis:quality", (_p(0), _p(4))),
        ],
        "A Quantity chain down the ladder, one level per step, closed by Egalitarian Dominance "
        "and Quality; the chain length grows with the height of the quality range.",
    ),
    _from_instances(
        "arrhenius-thesis-theorem-2",
        ("arrhenius-2000-thesis",),
        ("A", "B", "C", "E∪D"),
        [
            Instance("thesis:inequality-aversion", (_p(2), _p(3))),
            Instance("thesis:dominance-addition", (_p(0), _p(3))),
            Instance("thesis:egalitarian-dominance", (_p(1), _p(2))),
            Instance("thesis:quality", (_p(0), _p(1))),
        ],
        "A ⪰ B ≻ C ⪰ E∪D against the not-worse form of Dominance Addition; no completeness.",
    ),
    _from_instances(
        "arrhenius-2003-vrc",
        ("arrhenius-2003-vrc",),
        ("A1", "A2", "A3∪B1∪C1∪D1", "A3∪B2∪C1∪D2", "A4∪B3∪C2∪D2"),
        [
            Instance("arrhenius-2003:egalitarian-dominance", (_p(1), _p(0))),
            Instance("arrhenius-2003:dominance-addition", (_p(2), _p(1))),
            Instance("arrhenius-2003:condition-delta", (_p(3), _p(2))),
            Instance("arrhenius-2003:condition-beta", (_p(4), _p(3))),
            Instance("arrhenius-2003:vrc-avoidance", (_p(0), _p(4))),
        ],
        "A weak cycle through Dominance Addition, δ and β, closed by one strict Egalitarian "
        "Dominance link and VRC avoidance; no completeness.",
    ),
)

UNCATALOGUED = {
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


def substantial(m: Match) -> bool:
    """An embedding counts as coverage when it maps at least 3 edges and most of the skeleton."""
    return m.matched >= 3 and 2 * m.matched > m.known_edges


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
    steps the project has already found. Only substantial embeddings count as coverage
    (``substantial``, docs/decisions.md D-015): a one- or two-edge fragment of the right roles
    embeds almost anywhere, so counting it would let coverage grow with the catalogue alone.
    """
    matches = [match(core, k) for k in catalogue]
    exact = next((m.known_id for m in matches if m.exact), None)
    top = max(matches, key=lambda m: m.matched)
    counted = [m for m in matches if substantial(m)]
    published = [m for m in counted if not m.known_id.startswith("project-")]
    covered = {j for j in range(len(core)) if any(j not in m.residual for m in published)}
    anywhere = {j for j in range(len(core)) if any(j not in m.residual for m in counted)}
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
