"""The motif census: minimal proof skeletons, from shape logic down to principle labellings.

Under completeness every principle instance is one of three rank constraints (research/known.py
normalization): ``W(a, b)`` is r(a) ≥ r(b), ``S(a, b)`` is r(a) > r(b), and the Addition shape
``I(a, b, c)``, (a ≻ b) → (b ⪰ c), is r(b) ≥ r(a) ∨ r(b) ≥ r(c). Whether a set of instances is
consistent with a complete preorder therefore depends only on its shape hypergraph (L0).

``minimal_cores(k)`` enumerates, up to isomorphism, every connected shape hypergraph with at most
``k`` edges that is unsatisfiable under ranks while every proper subset is satisfiable. It grows
satisfiable hypergraphs one edge at a time (a connected hypergraph always has an edge order that
stays connected), so the enumeration is exhaustive up to the bound.

``cycle_words(instances, k)`` finds every principle word that closes a simple strict cycle in an
audited instance graph. For a fork-free principle set these are all of its minimal cores up to
``k`` instances.
"""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import dataclass
from itertools import permutations, product

from research.canon import canonical_form
from research.schema import Instance, Pop

ShapeEdge = tuple[str, tuple[int, ...]]  # ("W" | "S" | "I", relata indices)
Core = tuple[int, tuple[ShapeEdge, ...]]  # (relata count, sorted edges): a canonical L0 form


# ---------------------------------------------------------------------------------------------
# Rank satisfiability of shape hypergraphs.


def _difference_sat(
    n: int, weak: Iterable[tuple[int, ...]], strict: Iterable[tuple[int, ...]]
) -> bool:
    """r(a) ≥ r(b) for weak, r(a) > r(b) for strict: SAT iff no strict edge lies on a cycle."""
    reach = [[i == j for j in range(n)] for i in range(n)]
    strict = list(strict)
    for a, b in [*weak, *strict]:
        reach[a][b] = True
    for k in range(n):
        rk = reach[k]
        for i in range(n):
            if reach[i][k]:
                ri = reach[i]
                for j in range(n):
                    if rk[j]:
                        ri[j] = True
    return not any(reach[b][a] for a, b in strict)


def rank_sat(n: int, edges: Sequence[ShapeEdge]) -> bool:
    weak: list[tuple[int, ...]] = [e[1] for e in edges if e[0] == "W"]
    strict = [e[1] for e in edges if e[0] == "S"]
    forks = [e[1] for e in edges if e[0] == "I"]
    for choice in product((0, 1), repeat=len(forks)):
        # I(a, b, c): r(b) ≥ r(a) (choice 0) or r(b) ≥ r(c) (choice 1).
        extra = [
            ((b, a) if c == 0 else (b, cc)) for (a, b, cc), c in zip(forks, choice, strict=True)
        ]
        if _difference_sat(n, [*weak, *extra], strict):
            return True
    return False


# ---------------------------------------------------------------------------------------------
# Exhaustive enumeration of minimal L0 cores.


def _canon(n: int, edges: Sequence[ShapeEdge]) -> Core:
    relata, form = canonical_form(n, edges)
    return relata, tuple((label.strip("'"), args) for label, args in form)


def _candidates(n: int, first: bool) -> Iterator[ShapeEdge]:
    """New edges over existing relata 0..n-1 plus fresh ones, touching an existing relatum."""
    for shape, arity in (("W", 2), ("S", 2), ("I", 3)):
        pool = range(n + arity)
        for args in permutations(pool, arity):
            fresh = sorted(a for a in args if a >= n)
            if fresh != list(range(n, n + len(fresh))):
                continue  # fresh relata are numbered in order of first use
            if not first and len(fresh) == arity:
                continue
            if first and fresh != list(range(arity)):
                continue
            yield shape, args


@dataclass(frozen=True)
class Census:
    minimal: tuple[Core, ...]
    satisfiable_explored: int


def minimal_cores(
    k: int, shapes: frozenset[str] = frozenset({"W", "S", "I"}), max_forks: int | None = None
) -> Census:
    frontier: set[Core] = {(0, ())}
    seen: set[Core] = set(frontier)
    minimal: set[Core] = set()
    explored = 0
    for _ in range(k):
        nxt: set[Core] = set()
        for n, edges in frontier:
            for edge in _candidates(n, not edges):
                if edge[0] not in shapes or edge in edges:
                    continue
                forks = sum(1 for s, _ in edges if s == "I")
                if max_forks is not None and edge[0] == "I" and forks >= max_forks:
                    continue
                size = max(n, max(edge[1]) + 1)
                grown = _canon(size, [*edges, edge])
                if grown in seen:
                    continue
                seen.add(grown)
                gn, ge = grown
                if rank_sat(gn, ge):
                    nxt.add(grown)
                    explored += 1
                elif all(rank_sat(gn, ge[:i] + ge[i + 1 :]) for i in range(len(ge))):
                    minimal.add(grown)
        frontier = nxt
    return Census(tuple(sorted(minimal, key=lambda c: (len(c[1]), c))), explored)


def is_fork_motif(core: Core) -> bool:
    """One fork I(a, b, c) plus two strict paths a ⇝ b and c ⇝ b, and nothing else.

    With the fork's two disjuncts b ⪰ a and b ⪰ c, each path closes a strict cycle, so the core
    is UNSAT; this checks that the core is exactly the fork and the union of two such paths.
    """
    n, edges = core
    forks = [args for s, args in edges if s == "I"]
    if len(forks) != 1:
        return False
    a, b, c = forks[0]
    rest = [(s, args) for s, args in edges if s != "I"]

    def strict_paths(src: int) -> list[frozenset[int]]:
        out: list[frozenset[int]] = []

        def walk(node: int, used: frozenset[int], strict: bool, seen: frozenset[int]) -> None:
            if node == b and used:
                if strict:
                    out.append(used)
                return
            for j, (s, (x, y)) in enumerate(rest):
                if x == node and j not in used and y not in seen:
                    walk(y, used | {j}, strict or s == "S", seen | {y})

        walk(src, frozenset(), False, frozenset({src}))
        return out

    everything = frozenset(range(len(rest)))
    return any(p | q == everything for p in strict_paths(a) for q in strict_paths(c))


def is_simple_cycle(core: Core) -> bool:
    """Every edge binary, every relatum on exactly one in- and one out-edge, one component."""
    n, edges = core
    if any(len(args) != 2 for _, args in edges) or len(edges) != n:
        return False
    out = {a: b for _, (a, b) in edges}
    if len(out) != n or len({b for _, (_, b) in edges}) != n:
        return False
    node, steps = 0, 0
    while True:
        node = out[node]
        steps += 1
        if node == 0:
            return steps == n


# ---------------------------------------------------------------------------------------------
# Cycle words: the principle-level census for fork-free principle sets.


def _directed(inst: Instance) -> tuple[Pop, Pop, bool] | None:
    """(from, to, strict) for a binary instance after N→W normalization; None for forks."""
    if inst.shape == "S":
        return inst.args[0], inst.args[1], True
    if inst.shape == "W":
        return inst.args[0], inst.args[1], False
    if inst.shape == "N":
        return inst.args[1], inst.args[0], False
    return None


def _rotation_min(word: tuple[str, ...]) -> tuple[str, ...]:
    return min(word[i:] + word[:i] for i in range(len(word)))


@dataclass(frozen=True)
class CycleWord:
    word: tuple[str, ...]  # principles along the cycle, rotation-minimal
    example: tuple[Instance, ...]  # one realizing simple cycle, in word order


def cycle_words(instances: Iterable[Instance], max_len: int) -> list[CycleWord]:
    """Every principle word of length <= max_len that some simple cycle with a strict edge
    realizes, with one example each. Every such cycle is a minimal core (a minimal infeasible
    set of ≥/> constraints is a simple cycle through a strict edge).
    """
    succ: dict[Pop, list[tuple[str, Pop, Instance, bool]]] = defaultdict(list)
    for inst in instances:
        d = _directed(inst)
        if d is not None:
            succ[d[0]].append((inst.principle, d[1], inst, d[2]))
    for edges in succ.values():
        edges.sort(key=lambda e: (e[0], e[1]))
    found: dict[tuple[str, ...], CycleWord] = {}
    starts = sorted(succ)
    order = {p: i for i, p in enumerate(starts)}

    def walk(
        start: Pop, node: Pop, path: list[Instance], labels: list[str], strict: bool, seen: set[Pop]
    ) -> None:
        for principle, nxt, inst, is_strict in succ.get(node, ()):
            s = strict or is_strict
            if nxt == start:
                if s:
                    key = _rotation_min((*labels, principle))
                    if key not in found:
                        found[key] = CycleWord(key, (*path, inst))
                continue
            # Canonical start: the cycle's smallest population, so each cycle is walked once.
            if nxt in seen or order.get(nxt, -1) < order[start] or len(path) + 1 >= max_len:
                continue
            seen.add(nxt)
            walk(start, nxt, [*path, inst], [*labels, principle], s, seen)
            seen.discard(nxt)

    for start in starts:
        walk(start, start, [], [], False, {start})
    return sorted(found.values(), key=lambda w: (len(w.word), w.word))
