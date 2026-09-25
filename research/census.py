"""The motif census: minimal proof skeletons, from shape logic down to principle labellings.

Under completeness every principle instance is one of three rank constraints (research/known.py
normalization): ``W(a, b)`` is r(a) ≥ r(b), ``S(a, b)`` is r(a) > r(b), and the Addition shape
``I(a, b, c)``, (a ≻ b) → (b ⪰ c), is r(b) ≥ r(a) ∨ r(b) ≥ r(c). Whether a set of instances is
consistent with a complete preorder therefore depends only on its shape hypergraph (L0).

``rank_sat`` decides such a shape set. ``rank_certificate`` decides it and returns replayable
evidence: either one branch choice per I fork plus integer ranks, or one simple strict cycle per
fork branch, which together exclude every model. ``verify_rank_certificate`` rechecks that evidence
from the input alone, without consulting the search that produced it.

``minimal_cores(k)`` enumerates, up to isomorphism, every connected shape hypergraph with at most
``k`` edges that is unsatisfiable under ranks while every proper subset is satisfiable. It grows
satisfiable hypergraphs one edge at a time (a connected hypergraph always has an edge order that
stays connected), so the enumeration is exhaustive up to the bound.

``cycle_words(instances, k)`` finds every principle word that closes a simple strict cycle in an
audited instance graph. For a fork-free principle set these are all of its minimal cores up to
``k`` instances.
"""

from __future__ import annotations

from collections import defaultdict, deque
from collections.abc import Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass
from itertools import permutations, product
from typing import Any

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
# Certificate-producing decision: a replayable integer model, or one strict cycle per branch.


_SHAPE_ARITY: dict[str, int] = {"W": 2, "S": 2, "I": 3}


def _checked(
    n: int, edges: Sequence[ShapeEdge]
) -> tuple[list[tuple[int, int]], list[tuple[int, int]], list[tuple[int, int, int]]]:
    """(weak, strict, fork) edge lists with duplicates kept, refusing anything unrankable."""
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError(f"relata count must be a non-negative integer, got {n!r}")
    weak: list[tuple[int, int]] = []
    strict: list[tuple[int, int]] = []
    forks: list[tuple[int, int, int]] = []
    for edge in edges:
        try:
            shape, args = edge
            arity = _SHAPE_ARITY[shape]
            relata = tuple(args)
        except TypeError, ValueError, KeyError:
            raise ValueError(f"malformed shape edge: {edge!r}") from None
        if len(relata) != arity:
            raise ValueError(f"shape {shape!r} takes {arity} relata, got {edge!r}")
        if any(not isinstance(a, int) or isinstance(a, bool) or not 0 <= a < n for a in relata):
            raise ValueError(f"relata outside range({n}): {edge!r}")
        if shape == "I":
            forks.append((relata[0], relata[1], relata[2]))
        elif shape == "S":
            strict.append((relata[0], relata[1]))
        else:
            weak.append((relata[0], relata[1]))
    return weak, strict, forks


def _branch_edges(
    weak: Sequence[tuple[int, int]],
    strict: Sequence[tuple[int, int]],
    forks: Sequence[tuple[int, int, int]],
    choices: Sequence[int],
) -> list[tuple[int, int]]:
    """One branch's directed edges, in the index order its certificate cycle names.

    Every W edge in input order, then every S edge in input order, then one disjunct per I fork in
    fork input order: ``I(a, b, c)`` contributes ``(b, a)`` for choice 0 and ``(b, c)`` for choice
    1, the weak edge a complete preorder lets that fork take.
    """
    return [
        *weak,
        *strict,
        *(
            (b, a) if choice == 0 else (b, c)
            for (a, b, c), choice in zip(forks, choices, strict=True)
        ),
    ]


def _reach(n: int, edges: Sequence[tuple[int, int]]) -> list[list[bool]]:
    """Reflexive-transitive closure: ``reach[a][b]`` iff a directed walk a ⇝ b exists."""
    reach = [[i == j for j in range(n)] for i in range(n)]
    for a, b in edges:
        reach[a][b] = True
    for k in range(n):
        row_k = reach[k]
        for i in range(n):
            if reach[i][k]:
                row_i = reach[i]
                for j in range(n):
                    if row_k[j]:
                        row_i[j] = True
    return reach


def _shortest_walk(
    n: int, edges: Sequence[tuple[int, int]], src: int, dst: int
) -> list[int] | None:
    """Edge indices of a shortest walk src ⇝ dst ([] when src == dst), relata never revisited.

    Breadth first over edges in index order, so the reported walk is the same on every run.
    """
    if src == dst:
        return []
    incoming: dict[int, tuple[int, int]] = {}
    seen = [False] * n
    seen[src] = True
    queue = deque([src])
    while queue:
        node = queue.popleft()
        for index, (tail, head) in enumerate(edges):
            if tail == node and not seen[head]:
                seen[head] = True
                incoming[head] = (index, node)
                if head == dst:
                    walk: list[int] = []
                    step = dst
                    while step != src:
                        step_index, back = incoming[step]
                        walk.append(step_index)
                        step = back
                    walk.reverse()
                    return walk
                queue.append(head)
    return None


def _refuting_cycle(
    n: int,
    weak: Sequence[tuple[int, int]],
    strict: Sequence[tuple[int, int]],
    forks: Sequence[tuple[int, int, int]],
    choices: Sequence[int],
) -> list[int] | None:
    """A simple strict cycle refuting one branch, or None when the branch is rankable.

    A branch is infeasible exactly when some strict edge ``a > b`` has a walk ``b ⇝ a``: the strict
    edge forces ``r(a) > r(b)`` while the walk forces ``r(b) ≥ r(a)``. The strict edge plus a
    shortest return walk is then a simple cycle, and naming the strict edge is what makes the cycle
    an S-bearing refutation rather than a consistent weak rotation.
    """
    edges = _branch_edges(weak, strict, forks, choices)
    reach = _reach(n, edges)
    for offset, (a, b) in enumerate(strict):
        if not reach[b][a]:
            continue
        walk = _shortest_walk(n, edges, b, a)
        if walk is not None:
            return [len(weak) + offset, *walk]
    return None


def _ranks(
    n: int, edges: Sequence[tuple[int, int]], weak_count: int, strict_count: int
) -> list[int]:
    """Integer ranks for a rankable branch: SCCs and longest strict-weighted paths.

    In a rankable branch every cycle is weak, so its strongly connected relata
    have equal rank. Condensation edges have weight 1 for S and 0 for W;
    the longest path to a sink satisfies every strict and weak inequality.
    """
    reach = _reach(n, edges)
    component = [-1] * n
    count = 0
    for i in range(n):
        if component[i] >= 0:
            continue
        component[i] = count
        for j in range(i + 1, n):
            if component[j] < 0 and reach[i][j] and reach[j][i]:
                component[j] = count
        count += 1
    successors: list[dict[int, int]] = [{} for _ in range(count)]
    for index, (a, b) in enumerate(edges):
        if component[a] != component[b]:
            downstream = successors[component[a]]
            target = component[b]
            weight = int(weak_count <= index < weak_count + strict_count)
            downstream[target] = max(downstream.get(target, 0), weight)
    indegree = [0] * count
    for downstream in successors:
        for c in downstream:
            indegree[c] += 1
    queue = deque(c for c in range(count) if indegree[c] == 0)
    order: list[int] = []
    while queue:
        c = queue.popleft()
        order.append(c)
        for d in sorted(successors[c]):
            indegree[d] -= 1
            if indegree[d] == 0:
                queue.append(d)
    height = [0] * count
    for c in reversed(order):
        height[c] = max((weight + height[d] for d, weight in successors[c].items()), default=0)
    return [height[component[v]] for v in range(n)]


def rank_certificate(n: int, edges: Sequence[ShapeEdge]) -> dict[str, Any]:
    """Decide a finite W/S/I shape set under a complete preorder, with replayable evidence.

    ``rank_sat`` answers the same question; this returns the certificate. Under completeness a
    model is a map from the ``n`` relata to integer ranks, and the three shapes are the rank
    constraints W(a, b): ``r(a) ≥ r(b)``, S(a, b): ``r(a) > r(b)``, and I(a, b, c), that is
    ``(r(a) > r(b)) → (r(b) ≥ r(c))``, which is ``r(b) ≥ r(a)`` or ``r(b) ≥ r(c)``.

    Every model of the forks picks at least one true disjunct per I, so the satisfying assignments
    are exactly the union, over the ``2 ** forks`` branch assignments, of the difference systems
    formed by the W and S edges plus one weak disjunct per fork. Enumerating the branches is
    therefore necessary and sufficient: a rankable branch exhibits a model, and a refutation of
    every branch excludes every model.

    A difference system is infeasible exactly when some strict edge lies on a directed cycle,
    because a cycle ``a > b ≥ … ≥ a`` is contradictory while contracting the SCCs of a cycle-free
    system and weighting the condensation by longest path yields ranks (see ``_ranks``). Necessity
    and sufficiency of the reported cycles: each names a strict edge plus a return walk, and the
    strict edge is what makes the cycle unsatisfiable, since weak-only cycles are consistent.

    SAT payload ``{"decision": "sat", "choices": list[int], "ranks": list[int]}``: one disjunct per
    fork, in fork input order, and one rank per relatum. UNSAT payload
    ``{"decision": "unsat", "branches": [{"choices": list[int], "cycle": list[int]}, ...]}`` with
    one branch per assignment in ``itertools.product`` order; each ``cycle`` lists edge indices of
    that branch's own edges (all W in input order, then all S in input order, then the fork
    disjuncts in fork input order) forming a closed directed walk of distinct tails through at
    least one S edge.

    Raises ``ValueError`` for an unknown shape, a wrong arity, or a relatum outside ``range(n)``.
    The run is exponential in the number of I edges, as any exhaustive branch rule must be.
    """
    weak, strict, forks = _checked(n, edges)
    exhausted: list[dict[str, Any]] = []
    for choices in product((0, 1), repeat=len(forks)):
        cycle = _refuting_cycle(n, weak, strict, forks, choices)
        if cycle is None:
            return {
                "decision": "sat",
                "choices": list(choices),
                "ranks": _ranks(
                    n, _branch_edges(weak, strict, forks, choices), len(weak), len(strict)
                ),
            }
        exhausted.append({"choices": list(choices), "cycle": cycle})
    return {"decision": "unsat", "branches": exhausted}


def _int_tuple(value: Any, length: int) -> tuple[int, ...] | None:
    """``value`` as a length-``length`` sequence of plain integers, else None."""
    if not isinstance(value, (list, tuple)) or len(value) != length:
        return None
    if any(not isinstance(x, int) or isinstance(x, bool) for x in value):
        return None
    return tuple(value)


def _satisfies(
    weak: Sequence[tuple[int, int]],
    strict: Sequence[tuple[int, int]],
    forks: Sequence[tuple[int, int, int]],
    choices: tuple[int, ...],
    ranks: tuple[int, ...],
) -> bool:
    """Do ``ranks`` model every original W/S/I formula, with ``choices`` the forks' true disjuncts?

    The I test reads the disjunct the certificate names, which is one of the formula's two
    disjuncts, so this is direct satisfaction of each original formula.
    """
    if any(ranks[b] > ranks[a] for a, b in weak):  # W(a, b): r(a) ≥ r(b)
        return False
    if any(ranks[b] >= ranks[a] for a, b in strict):  # S(a, b): r(a) > r(b)
        return False
    for (a, b, c), choice in zip(forks, choices, strict=True):
        # I(a, b, c): r(b) ≥ r(a) under choice 0, r(b) ≥ r(c) under choice 1.
        if ranks[a if choice == 0 else c] > ranks[b]:
            return False
    return True


def _is_refuting_cycle(
    edges: Sequence[tuple[int, int]], weak_count: int, strict_count: int, cycle: Any
) -> bool:
    """Is ``cycle`` a closed walk of distinct tails through an S edge of these branch edges?

    Distinct tails with consecutive head = tail make the walk a simple directed cycle, so the
    check is complete for the certificate's claim and costs one pass per branch.
    """
    if not isinstance(cycle, (list, tuple)) or not cycle:
        return False
    if any(not isinstance(j, int) or isinstance(j, bool) or not 0 <= j < len(edges) for j in cycle):
        return False
    tails = [edges[j][0] for j in cycle]
    if len(set(tails)) != len(tails):
        return False
    for position, j in enumerate(cycle):
        if edges[j][1] != edges[cycle[(position + 1) % len(cycle)]][0]:
            return False
    return any(weak_count <= j < weak_count + strict_count for j in cycle)


def verify_rank_certificate(
    n: int, edges: Sequence[ShapeEdge], certificate: Mapping[str, Any]
) -> bool:
    """Replay a ``rank_certificate`` payload from scratch, never trusting the producer's search.

    SAT: ``choices`` must name one disjunct per fork and ``ranks`` must satisfy every original W, S
    and I formula, which is an explicit complete-preorder model. UNSAT: the branches must cover
    every assignment of the ``2 ** forks`` exactly once, and each must carry a valid simple closed
    directed walk through an S edge of that branch's selected edges, which refutes that branch on
    its own.

    Returns False for a malformed instance, an unrecognised decision, a malformed, duplicated or
    incomplete payload, an edge index out of range, a cycle that is not a simple closed walk, a
    cycle without a strict edge, or ranks that fail a formula. Independent of ``rank_sat``.
    """
    try:
        weak, strict, forks = _checked(n, edges)
    except TypeError, ValueError:
        return False
    if not isinstance(certificate, Mapping):
        return False
    decision = certificate.get("decision")
    if decision == "sat":
        choices = _int_tuple(certificate.get("choices"), len(forks))
        ranks = _int_tuple(certificate.get("ranks"), n)
        if choices is None or ranks is None or any(c not in (0, 1) for c in choices):
            return False
        return _satisfies(weak, strict, forks, choices, ranks)
    if decision != "unsat":
        return False
    branches = certificate.get("branches")
    if not isinstance(branches, (list, tuple)) or len(branches) != 2 ** len(forks):
        return False
    seen: set[tuple[int, ...]] = set()
    for branch in branches:
        if not isinstance(branch, Mapping):
            return False
        choices = _int_tuple(branch.get("choices"), len(forks))
        if choices is None or any(c not in (0, 1) for c in choices) or choices in seen:
            return False
        seen.add(choices)
        selected = _branch_edges(weak, strict, forks, choices)
        if not _is_refuting_cycle(selected, len(weak), len(strict), branch.get("cycle")):
            return False
    return True


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
