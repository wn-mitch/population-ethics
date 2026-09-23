"""Consistency certificates for fork-free condition sets.

For conditions whose instances are all ⪰ or ≻ edges (every thesis-family condition), a set
with fixed witnesses is consistent iff its instance graph over all populations has no strict
cycle: the transitive closure of the edges is then a quasi-ordering satisfying every instance,
and the thesis family does not require completeness (docs/decisions.md D-019).

A certificate uses an abstraction of that graph. A population's *support* is the set of levels
it occupies. Every instance maps to an edge between supports, and every concrete cycle maps to
a closed walk in the support graph, so its edges lie in one strongly connected component. The
abstraction over-approximates: any bag may occupy any nonempty subset of its levels, whatever
the witness sizes, and backgrounds range over every subset of their allowed levels (a test
checks that every concrete instance's supports appear). Therefore:

- a condition none of whose support edges lies inside a component is *inert*: none of its
  instances is on any cycle;
- if some axiology satisfies every non-inert condition exactly, at the same level witnesses,
  then no strict cycle exists, and the set is consistent.

A certificate names the level witnesses, the inert conditions, and the axiology.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass
from itertools import combinations, product
from typing import Any

from research.ladder import FORM, WITNESS_OF, Ladder, Witness
from research.schema import SHAPE

Support = frozenset[int]


def _subsets(levels: Iterable[int]) -> list[Support]:
    items = sorted(levels)
    return [frozenset(c) for k in range(len(items) + 1) for c in combinations(items, k)]


def _nonempty(levels: Iterable[int]) -> list[Support]:
    return [s for s in _subsets(levels) if s]


def _support_cores(
    form: str, ladder: Ladder, w: Mapping[str, int]
) -> Iterator[tuple[Support, Support, tuple[int, ...] | None]]:
    """(left support, right support, allowed background levels) for every core of a form.

    Mirrors research/ladder.py ``_moves`` at the level of supports: counts never change which
    levels a part occupies, so any bag becomes any nonempty subset of its allowed levels.
    ``()`` means no background; ``None`` means any background.
    """
    lv = ladder.levels
    pos = [v for v in lv if v > 0]
    neg = [v for v in lv if v < 0]
    one = frozenset
    if form == "egalitarian-dominance":
        for x in lv:
            for s in _nonempty(v for v in lv if v < x):
                yield one({x}), s, ()
    elif form == "quantity":
        for y in pos:
            if ladder.has(y + 1):
                yield one({y}), one({y + 1}), ()
    elif form == "quality":
        for z in ladder.range(w["u"], w["v"]):
            for s in _nonempty(ladder.range(1, w["y"])):
                yield one({z}), s, ()
    elif form in {"dominance-addition-not-worse", "dominance-addition-weak"}:
        for sa in _nonempty(lv):
            for sb in _nonempty(v for v in lv if v > max(sa)):
                if form == "dominance-addition-not-worse":
                    for y in pos:
                        yield sa, sb | {y}, ()  # shape N: ¬(A ≻ B ∪ C)
                else:
                    for sc in _nonempty(pos):
                        yield sb | sc, sa, ()
    elif form == "inequality-aversion":
        for x in lv:
            for y in lv:
                for z in lv:
                    if x > y > z:
                        yield one({y}), one({x, z}), ()
    elif form == "non-sadism-equal":
        for x in pos:
            for y in neg:
                yield one({x}), one({y}), None
    elif form == "non-extreme-priority":
        for u in (v for v in lv if v >= w["x"]):
            for s in _nonempty(ladder.range(1, w["z"])):
                yield one({u, w["y"]}), s, None
    elif form == "weak-quality-addition":
        for z in (v for v in lv if v >= w["x"]):
            for s in _nonempty(ladder.range(1, w["y"])):
                yield one({z}), s, None
    elif form in {"non-elitism-ranged", "non-elitism-any"}:
        for x in lv:
            for y in lv:
                if x - 1 > y and ladder.has(x - 1):
                    bg = ladder.range(y, x) if form == "non-elitism-ranged" else None
                    yield one({x - 1}), one({x, y}), bg
    elif form == "general-non-extreme-priority":
        for z in lv:
            if ladder.has(z + 1):
                for x in (v for v in lv if v >= w["u"]):
                    for s in _nonempty(ladder.range(1, w["y"])):
                        yield one({x, z}), s | {z + 1}, None
    elif form == "weak-non-sadism":
        for y in pos:
            yield one({y}), one({w["x"]}), None
    elif form in {"vrc-avoidance", "weak-quality-addition-negative"}:
        allowed: tuple[int, ...] | None = () if form == "vrc-avoidance" else None
        for z in (v for v in lv if v >= w["u"]):
            for s in _nonempty(ladder.range(1, w["y"])):
                yield one({z}), s | {w["x"]}, allowed
    else:
        raise ValueError(f"no support abstraction for {form}")


def support_edges(
    principle: str, ladder: Ladder, levels: Mapping[str, int]
) -> set[tuple[Support, Support, bool]]:
    """(from, to, strict) support edges of one condition, directed as ⪰/≻ after N→W."""
    form = FORM[principle]
    shape = SHAPE[principle]
    subsets_of: dict[tuple[int, ...] | None, list[Support]] = {}
    out: set[tuple[Support, Support, bool]] = set()
    for left, right, allowed in _support_cores(form, ladder, levels):
        if allowed not in subsets_of:
            subsets_of[allowed] = (
                [frozenset()]
                if allowed == ()
                else _subsets(ladder.levels if allowed is None else allowed)
            )
        for bg in subsets_of[allowed]:
            a, b = left | bg, right | bg
            if shape == "N":
                a, b = b, a
            out.add((a, b, shape == "S"))
    return out


def _components(edges: Iterable[tuple[Support, Support, bool]]) -> dict[Support, int]:
    """Strongly connected component id per support (iterative Tarjan)."""
    graph: dict[Support, list[Support]] = {}
    for a, b, _ in edges:
        graph.setdefault(a, []).append(b)
        graph.setdefault(b, [])
    index: dict[Support, int] = {}
    low: dict[Support, int] = {}
    comp: dict[Support, int] = {}
    stack: list[Support] = []
    on: set[Support] = set()
    counter = 0
    for root in graph:
        if root in index:
            continue
        work = [(root, iter(graph[root]))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on.add(root)
        while work:
            node, it = work[-1]
            advanced = False
            for nxt in it:
                if nxt not in index:
                    index[nxt] = low[nxt] = counter
                    counter += 1
                    stack.append(nxt)
                    on.add(nxt)
                    work.append((nxt, iter(graph[nxt])))
                    advanced = True
                    break
                if nxt in on:
                    low[node] = min(low[node], index[nxt])
            if advanced:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[node])
            if low[node] == index[node]:
                cid = len(set(comp.values()))
                while True:
                    x = stack.pop()
                    on.discard(x)
                    comp[x] = cid
                    if x == node:
                        break
    return comp


@dataclass(frozen=True)
class Abstract:
    inert: frozenset[str]  # conditions with no support edge inside a component
    strict_cycle_possible: bool  # some strict support edge lies inside a component


def analyse(
    principles: Iterable[str], ladder: Ladder, levels: Mapping[str, Mapping[str, int]]
) -> Abstract:
    """Support-graph analysis of a condition set with the given level witnesses per family."""
    per: dict[str, set[tuple[Support, Support, bool]]] = {}
    for p in principles:
        family = WITNESS_OF.get(FORM[p])
        per[p] = support_edges(p, ladder, levels.get(family, {}) if family else {})
    comp = _components(e for es in per.values() for e in es)
    inside = {p: [e for e in es if comp[e[0]] == comp[e[1]]] for p, es in per.items()}
    return Abstract(
        inert=frozenset(p for p, es in inside.items() if not es),
        strict_cycle_possible=any(s for es in inside.values() for _, _, s in es),
    )


def witness_of(levels: Mapping[str, Mapping[str, int]]) -> Witness:
    return Witness({k: dict(v) for k, v in levels.items()})


def level_options(family: str, ladder: Ladder) -> list[dict[str, int]]:
    """A small spread of level witnesses per family: low range R(1, 3), high levels varied."""
    pos = [v for v in ladder.levels if v > 0]
    neg = [v for v in ladder.levels if v < 0]
    top = pos[-1]
    highs = [u for u in pos if u >= 4 and u + 2 <= top]
    if family == "quality":
        return [{"u": u, "v": u + 2, "y": 3} for u in highs]
    if family == "weak-quality-addition":
        return [{"x": u, "w": u + 2, "y": 3} for u in highs]
    if family == "non-extreme-priority":
        return [{"x": x, "y": y, "z": 3} for x in pos if x >= 4 for y in neg]
    if family == "general-non-extreme-priority":
        return [{"u": u, "y": 3} for u in pos if u >= 4]
    if family == "weak-non-sadism":
        return [{"x": x} for x in neg]
    if family in {"vrc-avoidance", "weak-quality-addition-negative"}:
        return [{"x": x, "u": u, "v": u + 2, "y": 3} for x in neg for u in highs]
    return [{}]


@dataclass(frozen=True)
class Certificate:
    conditions: tuple[str, ...]
    levels: dict[str, dict[str, int]]
    inert: tuple[str, ...]
    axiology: str | None  # None: the support graph has no strict cycle at all


class Certifier:
    """Searches level witnesses and axiologies for a consistency certificate, with caches."""

    def __init__(self, ladder: Ladder, axiologies: Iterable[Any]) -> None:
        self.ladder = ladder
        self.axiologies = list(axiologies)
        self._edges: dict[
            tuple[str, tuple[tuple[str, int], ...]], set[tuple[Support, Support, bool]]
        ] = {}
        self._checks: dict[tuple[str, str, tuple[tuple[str, int], ...]], bool] = {}

    def _edges_of(self, p: str, levels: Mapping[str, int]) -> set[tuple[Support, Support, bool]]:
        key = (p, tuple(sorted(levels.items())))
        if key not in self._edges:
            self._edges[key] = support_edges(p, self.ladder, levels)
        return self._edges[key]

    def _satisfies(self, p: str, ax: Any, levels: Mapping[str, int]) -> bool:
        from research.lexadd import check_at

        key = (p, ax.id, tuple(sorted(levels.items())))
        if key not in self._checks:
            self._checks[key] = check_at(p, ax, self.ladder, levels) is None
        return self._checks[key]

    def certify(
        self,
        conditions: Iterable[str],
        *,
        level_overrides: Mapping[str, Sequence[dict[str, int]]] | None = None,
    ) -> Certificate | None:
        conds = tuple(sorted(conditions))
        families = sorted({f for p in conds if (f := WITNESS_OF.get(FORM[p])) is not None})
        grids = [
            level_overrides[f]
            if level_overrides is not None and f in level_overrides
            else level_options(f, self.ladder)
            for f in families
        ]
        for choice in product(*grids):
            levels = dict(zip(families, choice, strict=True))
            per = {
                p: self._edges_of(p, levels.get(WITNESS_OF.get(FORM[p]) or "", {})) for p in conds
            }
            comp = _components(e for es in per.values() for e in es)
            inside = {p: [e for e in es if comp[e[0]] == comp[e[1]]] for p, es in per.items()}
            inert = tuple(p for p in conds if not inside[p])
            if not any(s for es in inside.values() for _, _, s in es):
                return Certificate(conds, levels, inert, None)
            live = [p for p in conds if p not in inert]
            for ax in self.axiologies:
                if all(
                    self._satisfies(p, ax, levels.get(WITNESS_OF.get(FORM[p]) or "", {}))
                    for p in live
                ):
                    return Certificate(conds, levels, inert, ax.id)
        return None


NO_BACKGROUND = {
    "egalitarian-dominance",
    "quantity",
    "quality",
    "dominance-addition-not-worse",
    "dominance-addition-weak",
    "inequality-aversion",
    "vrc-avoidance",
}


def component_order(
    comp: Mapping[Support, int], edges: Iterable[tuple[Support, Support, bool]]
) -> dict[int, int]:
    """σ per component: every edge between components goes from higher σ to lower σ."""
    succ: dict[int, set[int]] = {c: set() for c in set(comp.values())}
    for a, b, _ in edges:
        if comp[a] != comp[b]:
            succ[comp[a]].add(comp[b])
    rank: dict[int, int] = {}

    def depth(c: int) -> int:  # longest path to a sink; the condensation is acyclic
        stack = [(c, iter(sorted(succ[c])))]
        while stack:
            node, it = stack[-1]
            nxt = next((d for d in it if d not in rank), None)
            if nxt is not None:
                stack.append((nxt, iter(sorted(succ[nxt]))))
                continue
            stack.pop()
            rank[node] = 1 + max((rank[d] for d in succ[node]), default=0)
        return rank[c]

    for c in succ:
        if c not in rank:
            depth(c)
    return rank


class HybridCertifier(Certifier):
    """Certificates whose key is (component rank, axiology): the axiology need only satisfy the
    instances whose two supports share a component (docs/decisions.md D-020)."""

    def __init__(self, ladder: Ladder, axiologies: Iterable[Any], per_gap: int = 8) -> None:
        super().__init__(ladder, axiologies)
        self.per_gap = per_gap  # axiologies tried per condition set, most promising first

    def _ranked(self, conds: Sequence[str]) -> list[Any]:

        def score(ax: Any) -> int:
            return sum(1 for p in conds if self._cached_full(p, ax))

        return sorted(self.axiologies, key=lambda ax: -score(ax))[: self.per_gap]

    def _cached_full(self, p: str, ax: Any) -> bool:
        from research.lexadd import CHECKS

        key = (p, ax.id, ())
        if key not in self._checks:
            self._checks[key] = CHECKS[p](ax, self.ladder) is None
        return self._checks[key]

    def certify(
        self,
        conditions: Iterable[str],
        *,
        level_overrides: Mapping[str, Sequence[dict[str, int]]] | None = None,
    ) -> Certificate | None:
        from research.lexadd import Restriction, check_restricted

        conds = tuple(sorted(conditions))
        candidates = self._ranked(conds)
        families = sorted({f for p in conds if (f := WITNESS_OF.get(FORM[p])) is not None})
        grids = [
            level_overrides[f]
            if level_overrides is not None and f in level_overrides
            else level_options(f, self.ladder)
            for f in families
        ]
        for choice in product(*grids):
            levels = dict(zip(families, choice, strict=True))
            lv_of = {p: levels.get(WITNESS_OF.get(FORM[p]) or "", {}) for p in conds}
            per = {p: self._edges_of(p, lv_of[p]) for p in conds}
            comp = _components(e for es in per.values() for e in es)
            inside = {p: [e for e in es if comp[e[0]] == comp[e[1]]] for p, es in per.items()}
            inert = tuple(p for p in conds if not inside[p])
            if not any(s for es in inside.values() for _, _, s in es):
                return Certificate(conds, levels, inert, None)
            live = [p for p in conds if p not in inert]
            for ax in candidates:
                ok = True
                for p in live:
                    bg = () if FORM[p] in NO_BACKGROUND else None
                    r = Restriction(comp, tuple(self.ladder.levels), bg)
                    if check_restricted(p, ax, self.ladder, lv_of[p], r) is not None:
                        ok = False
                        break
                if ok:
                    return Certificate(conds, levels, inert, f"component-rank then {ax.id}")
        return None
