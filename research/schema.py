"""Schema v0 (``arrhenius-2000.schema/v0-unreviewed``): principle schemas over bounded domains.

Every predicate below formalizes a source clause whose cross-read reading, with verbatim excerpt
and recorded deviations, is in ``corpus/readings.toml`` (docs/decisions.md D-013); generation
refuses principles that have not passed that gate. Existential principles are
fixed by an explicit witness W = (A = p·a, MNEP n = q); universal principles are instantiated
over every population in the bounded domain D_N (all nonempty multisets of at most N lives over
the declared levels). A finite UNSAT result therefore refutes "v0 schema + W" only.
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Iterable, Iterator, Mapping
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations_with_replacement, permutations, product

import z3  # type: ignore[import-untyped]

from research.lab import Check
from research.readings import require_reviewed

Pop = tuple[int, ...]  # sorted multiset of welfare levels

SCHEMA_ID = "arrhenius-2000.schema/v0-unreviewed"

SOURCE_CLAUSES = {
    "dominance": "Dominance: for equal-size populations, if every life in one has higher "
    "welfare than every life in the other, the former is better.",
    "addition": "Addition: if adding a lower-welfare group is bad, adding a larger group at an "
    "even lower welfare is at least as bad.",
    "mnep": "Minimal Non-Extreme Priority: there is an n such that n very-high lives plus one "
    "slightly negative life, with any background, are at least as good as n+1 very-low-positive "
    "lives with the same background.",
    "non-sadism": "Avoid the Sadistic Conclusion: adding negative lives is not better than "
    "adding positive lives.",
    "non-anti-egalitarianism": "Avoid the Anti-Egalitarian Conclusion: a population with "
    "perfect equality is not worse than a same-size unequal population with lower average.",
    "non-repugnance": "Avoid the Repugnant Conclusion: some perfectly equal very-high "
    "population is not worse than any very-low-positive population.",
}

# Logical shapes, used for skeleton canonicalization.
SHAPE = {
    "dominance": "S",  # X ≻ Y
    "non-anti-egalitarianism": "N",  # ¬(X ≻ Y)
    "non-repugnance": "N",
    "non-sadism": "N",
    "mnep": "W",  # X ⪰ Y
    "addition": "I",  # (X ≻ Y) → (Y ⪰ Z)
    # Arrhenius (1999), frozen in research/p7_arrhenius1999.py; every condition but
    # Egalitarian Dominance is stated in at-least-as-good form.
    "arrhenius-1999:egalitarian-dominance": "S",
    "arrhenius-1999:minimal-inequality-aversion": "W",
    "arrhenius-1999:quality-addition": "W",
    "arrhenius-1999:non-sadism": "W",
    "arrhenius-1999:minimal-non-extreme-priority": "W",
    # Thesis-family conditions (research/ladder.py). Egalitarian Dominance is the only strict
    # condition; thesis Dominance Addition says "not worse"; every other one is at-least-as-good.
    "thesis:egalitarian-dominance": "S",
    "arrhenius-2003:egalitarian-dominance": "S",
    "arrhenius-2009:egalitarian-dominance": "S",
    "thesis:dominance-addition": "N",
    **{
        p: "W"
        for p in (
            "thesis:quantity",
            "thesis:quality",
            "arrhenius-2003:dominance-addition",
            "thesis:inequality-aversion",
            "thesis:non-sadism",
            "thesis:non-extreme-priority",
            "thesis:weak-quality-addition",
            "thesis:non-elitism",
            "arrhenius-2009:non-elitism",
            "arrhenius-2003:non-elitism",
            "thesis:general-non-extreme-priority",
            "arrhenius-2003:general-non-extreme-priority",
            "arrhenius-2009:general-non-extreme-priority",
            "thesis:weak-non-sadism",
            "arrhenius-2009:weak-non-sadism",
            "arrhenius-2003:vrc-avoidance",
            "arrhenius-2009:weak-quality-addition",
            "thesis:condition-beta",
            "arrhenius-2009:condition-beta",
            "arrhenius-2003:condition-beta",
            "thesis:condition-delta",
            "arrhenius-2003:condition-delta",
            "arrhenius-2009:condition-delta",
            "arrhenius-2009:restricted-quality-addition",
        )
    },
}


@dataclass(frozen=True)
class Grid:
    name: str
    levels: tuple[int, ...]
    very_high: frozenset[int]
    very_low: frozenset[int]
    slightly_negative: frozenset[int]


@dataclass(frozen=True)
class Instance:
    principle: str
    args: tuple[Pop, ...]

    @property
    def shape(self) -> str:
        return SHAPE[self.principle]


def domain(grid: Grid, max_lives: int) -> list[Pop]:
    return [
        pop
        for size in range(1, max_lives + 1)
        for pop in combinations_with_replacement(sorted(grid.levels), size)
    ]


def _plus(*parts: Pop) -> Pop:
    return tuple(sorted(v for part in parts for v in part))


def _avg(pop: Pop) -> Fraction:
    return Fraction(sum(pop), len(pop))


def _multisets(levels: list[int], size: int) -> list[Pop]:
    return [tuple(c) for c in combinations_with_replacement(sorted(levels), size)] if size else [()]


V0_PRINCIPLES = (
    "dominance",
    "non-anti-egalitarianism",
    "non-repugnance",
    "non-sadism",
    "mnep",
    "addition",
)


def instances(grid: Grid, max_lives: int, p: int, q: int) -> Iterator[Instance]:
    """Every v0 instance over D_N for witness W = (A = p lives at max VH, MNEP n = q).

    Raises UnreviewedPrinciple before generating anything if a v0 principle has not passed the
    review-first gate (corpus/readings.toml).
    """
    require_reviewed(V0_PRINCIPLES)
    return _instances(grid, max_lives, p, q)


def sub_bags(pops: Iterable[Pop]) -> list[Pop]:
    """Every sub-multiset (including the empty one) of some population in ``pops``.

    A shared background only has to be a sub-bag of both compared populations, so generation
    over a universe must range over these, not over the universe's members.
    """
    out: set[Pop] = {()}
    for pop in set(pops):
        counts = sorted(Counter(pop).items())
        for picks in product(*(range(c + 1) for _, c in counts)):
            out.add(tuple(v for (v, _), k in zip(counts, picks, strict=True) for _ in range(k)))
    return sorted(out, key=lambda x: (len(x), x))


def instances_over(pops: Iterable[Pop], grid: Grid, p: int, q: int) -> list[Instance]:
    """Every v0 instance whose populations all lie in ``pops`` (the lazy primitive).

    Backgrounds and bases range over ``pops`` only, so the cost follows the universe, not
    D_N. ``instances(grid, N, p, q)`` equals ``instances_over(domain(grid, N), grid, p, q)``.
    """
    require_reviewed(V0_PRINCIPLES)
    universe = set(pops)
    max_lives = max((len(x) for x in universe), default=0)
    return [
        inst
        for inst in _instances(grid, max_lives, p, q, universe)
        if all(x in universe for x in inst.args)
    ]


def _instances(
    grid: Grid, max_lives: int, p: int, q: int, universe: set[Pop] | None = None
) -> Iterator[Instance]:
    pops = (
        domain(grid, max_lives) if universe is None else sorted(universe, key=lambda x: (len(x), x))
    )
    in_d = set(pops)
    by_size: dict[int, list[Pop]] = {}
    for pop in pops:
        by_size.setdefault(len(pop), []).append(pop)
    positive = [v for v in grid.levels if v > 0]
    backgrounds: list[Pop] = [(), *pops] if universe is None else sub_bags(pops)
    witness_a: Pop = (max(grid.very_high),) * p

    # Dominance (universal): same size, min X > max Y.
    for group in by_size.values():
        for x in group:
            for y in group:
                if x[0] > y[-1]:
                    yield Instance("dominance", (x, y))
    # Non-Anti-Egalitarianism (universal): Y perfectly equal, X same size, unequal, lower average.
    for group in by_size.values():
        for y in group:
            if len(set(y)) != 1:
                continue
            for x in group:
                if len(set(x)) > 1 and _avg(x) < _avg(y):
                    yield Instance("non-anti-egalitarianism", (x, y))
    # Non-Repugnance (existential A fixed by W; universal over very-low-positive X).
    if witness_a in in_d:
        for x in pops:
            if all(v in grid.very_low for v in x):
                yield Instance("non-repugnance", (x, witness_a))
    # Non-Sadism (universal over background B, possibly empty; nonempty all-negative N versus
    # nonempty all-positive P): ¬(B⊎N ≻ B⊎P).
    negative_levels = [v for v in grid.levels if v < 0]
    seen: set[tuple[Pop, Pop]] = set()
    for b in backgrounds:
        room = max_lives - len(b)
        for n_size in range(1, room + 1):
            for neg in _multisets(negative_levels, n_size):
                for p_size in range(1, room + 1):
                    for pos in _multisets(positive, p_size):
                        pair = (_plus(b, neg), _plus(b, pos))
                        if pair not in seen:
                            seen.add(pair)
                            yield Instance("non-sadism", pair)
    # MNEP (existential n = q fixed by W; universal over background X, possibly empty, and over
    # the very-high, slightly-negative and very-low-positive levels used).
    seen_mnep: set[tuple[Pop, Pop]] = set()
    for x in backgrounds:
        if len(x) + q + 1 > max_lives:
            continue
        for high in _multisets(sorted(grid.very_high), q):
            for sn in sorted(grid.slightly_negative):
                for low in _multisets(sorted(grid.very_low), q + 1):
                    pair = (_plus(x, high, (sn,)), _plus(x, low))
                    if pair not in seen_mnep:
                        seen_mnep.add(pair)
                        yield Instance("mnep", pair)
    # Addition (universal): P nonempty; Q nonempty all below min P; R nonempty all below min Q;
    # |R| > |Q|: (P ≻ P⊎Q) → (P⊎Q ⪰ P⊎R).
    for base in pops:
        for q_size in range(1, max_lives - len(base) + 1):
            for added in _multisets([v for v in grid.levels if v < base[0]], q_size):
                for r_size in range(q_size + 1, max_lives - len(base) + 1):
                    for lower in _multisets([v for v in grid.levels if v < added[0]], r_size):
                        yield Instance("addition", (base, _plus(base, added), _plus(base, lower)))


def check_instance(instance: Instance, grid: Grid, p: int, q: int) -> bool:
    """Re-derive applicability of one instance from its populations (vacuity/applicability audit).

    Written separately from the generator: it recovers the decomposition from the populations.
    """
    a = instance.args
    if any(not x for x in a) or len(set(a)) != len(a):
        return False
    if instance.principle == "dominance":
        return len(a[0]) == len(a[1]) and min(a[0]) > max(a[1])
    if instance.principle == "non-anti-egalitarianism":
        x, y = a
        return len(x) == len(y) and len(set(y)) == 1 and len(set(x)) > 1 and _avg(x) < _avg(y)
    if instance.principle == "non-repugnance":
        x, w = a
        return w == (max(grid.very_high),) * p and all(v in grid.very_low for v in x)
    if instance.principle == "non-sadism":
        return _sadism_decomposes(Counter(a[0]), Counter(a[1]))
    if instance.principle == "mnep":
        u, v = Counter(a[0]), Counter(a[1])
        common = u & v
        extra_u, extra_v = u - common, v - common
        return _mnep_decomposes(extra_u, extra_v, common, grid, q)
    if instance.principle == "addition":
        base, pq, pr = (Counter(x) for x in a)
        added, lower = pq - base, pr - base
        return (
            not (base - pq)
            and not (base - pr)
            and bool(added)
            and bool(lower)
            and max(added) < min(base)
            and max(lower) < min(added)
            and sum(lower.values()) > sum(added.values())
        )
    return False


def _sadism_decomposes(u: Counter[int], v: Counter[int]) -> bool:
    """U = B ⊎ N and V = B ⊎ P with N nonempty all negative and P nonempty all positive.

    Any valid background contains the non-negative lives of U and the non-positive lives of V;
    the smallest such background is their union, and enlarging it only shrinks N and P, so it
    suffices to test that one background.
    """
    background = Counter({k: c for k, c in u.items() if k >= 0}) | Counter(
        {k: c for k, c in v.items() if k <= 0}
    )
    if background - u or background - v:
        return False
    neg, pos = u - background, v - background
    return (
        bool(neg)
        and bool(pos)
        and all(x < 0 for x in neg.elements())
        and all(x > 0 for x in pos.elements())
    )


def _mnep_decomposes(
    extra_u: Counter[int], extra_v: Counter[int], common: Counter[int], grid: Grid, q: int
) -> bool:
    """U = X ⊎ H ⊎ {s}, V = X ⊎ L with |H| = q very-high, s slightly negative, |L| = q+1 VL.

    The maximal common part may contain lives that belong to H or L when levels coincide; try
    every way of moving lives from the common part back into the additions.
    """
    for move in _sub_counters(common):
        hu = extra_u + move
        lv = extra_v + move
        negs = [x for x in hu.elements() if x in grid.slightly_negative]
        highs = [x for x in hu.elements() if x in grid.very_high]
        if (
            len(negs) == 1
            and len(highs) == q
            and sum(hu.values()) == q + 1
            and sum(lv.values()) == q + 1
            and all(x in grid.very_low for x in lv.elements())
        ):
            return True
    return False


def _sub_counters(c: Counter[int]) -> Iterator[Counter[int]]:
    items = sorted(c.items())

    def rec(i: int, acc: Counter[int]) -> Iterator[Counter[int]]:
        if i == len(items):
            yield Counter(acc)
            return
        k, n = items[i]
        for take in range(n + 1):
            acc[k] = take
            yield from rec(i + 1, acc)
        del acc[k]

    yield from rec(0, Counter())


# --------------------------------------------------------------------------- rank encoding


class RankEngine:
    """Complete-preorder branch only: X ⪰ Y iff r(X) ≥ r(Y) for integer ranks.

    Sound and complete for total preorders on a finite domain. Never used for incomplete or
    weakened-transitivity questions.
    """

    def __init__(self, pops: list[Pop], insts: list[Instance]) -> None:
        self.rank = {pop: z3.Int(f"r{i}") for i, pop in enumerate(pops)}
        self.instances = insts
        self.guard = [z3.Bool(f"i{j}") for j in range(len(insts))]
        self.solver = z3.Solver()
        for g, inst in zip(self.guard, insts, strict=True):
            self.solver.add(z3.Implies(g, self.encode(inst)))
        self.calls = 0

    def encode(self, inst: Instance) -> z3.BoolRef:
        r = self.rank
        a = inst.args
        if inst.shape == "S":
            return r[a[0]] > r[a[1]]
        if inst.shape == "N":
            return r[a[0]] <= r[a[1]]
        if inst.shape == "W":
            return r[a[0]] >= r[a[1]]
        return z3.Implies(r[a[0]] > r[a[1]], r[a[1]] >= r[a[2]])

    def check(self, enabled: list[int]) -> tuple[str, list[int], dict[Pop, int] | None]:
        self.calls += 1
        status = self.solver.check(*(self.guard[j] for j in enabled))
        if status == z3.sat:
            model = self.solver.model()
            ranks = {
                pop: model.eval(v, model_completion=True).as_long() for pop, v in self.rank.items()
            }
            return "sat", [], ranks
        if status == z3.unsat:
            names = {str(g): j for j, g in enumerate(self.guard)}
            return "unsat", sorted(names[str(g)] for g in self.solver.unsat_core()), None
        raise RuntimeError(f"rank engine returned unknown: {self.solver.reason_unknown()}")

    # MARCO interface (research.lab.marco): soft ids are "i<index>" over the instance list.

    @property
    def soft(self) -> dict[str, Instance]:
        return {f"i{j}": inst for j, inst in enumerate(self.instances)}

    def require(self, enabled: Iterable[str] = ()) -> Check:
        decision, core, _ = self.check(sorted(int(cid[1:]) for cid in set(enabled)))
        return Check(
            "sat" if decision == "sat" else "unsat",
            None,
            tuple(sorted(f"i{j}" for j in core)),
            None,
        )

    def shrink(self, enabled: Iterable[str]) -> tuple[str, ...]:
        """Deletion-based MUS over soft ids, from a known-UNSAT seed, verified minimal."""
        first = self.require(enabled)
        if first.decision != "unsat":
            raise ValueError("shrink requires an UNSAT seed")
        mus = [f"i{j}" for j in self.minimize([int(c[1:]) for c in first.core])]
        for cid in mus:
            if self.require([x for x in mus if x != cid]).decision != "sat":
                raise AssertionError("shrink produced a non-minimal core")
        return tuple(sorted(mus))

    def grow(self, enabled: Iterable[str]) -> tuple[str, ...]:
        """Grow a SAT soft set to a maximal SAT subset, in sorted id order."""
        current = set(enabled)
        if self.require(current).decision != "sat":
            raise ValueError("grow requires a SAT seed")
        for cid in sorted(self.soft):
            if cid not in current and self.require(current | {cid}).decision == "sat":
                current.add(cid)
        return tuple(sorted(current))

    def minimize(self, core: list[int]) -> list[int]:
        current = sorted(core)
        index = 0
        while index < len(current):
            trial = current[:index] + current[index + 1 :]
            decision, sub_core, _ = self.check(trial)
            if decision == "unsat":
                current = sorted(set(trial) & set(sub_core))
            else:
                index += 1
        return current


def holds(inst: Instance, ranks: Mapping[Pop, int]) -> bool:
    """Independent evaluation of an instance on the total preorder induced by ``ranks``."""
    a = inst.args
    if inst.shape == "S":
        return ranks[a[0]] > ranks[a[1]]
    if inst.shape == "N":
        return not ranks[a[0]] > ranks[a[1]]
    if inst.shape == "W":
        return ranks[a[0]] >= ranks[a[1]]
    return not ranks[a[0]] > ranks[a[1]] or ranks[a[1]] >= ranks[a[2]]


# --------------------------------------------------------------------------- skeletons


def canonical_skeleton(core: list[Instance], *, principle_colors: bool) -> tuple[object, ...]:
    """Canonical form of a colored directed incidence hypergraph up to relabeling relata.

    Hyperedges carry the logical shape (S, N, W, I) and, optionally, the principle. Brute force
    over permutations of the extracted relata; callers keep cores small (<= 9 relata).
    """
    nodes = sorted({x for inst in core for x in inst.args})
    if len(nodes) > 9:
        return _refined_skeleton(core, nodes, principle_colors=principle_colors)
    best: tuple[object, ...] | None = None
    for perm in permutations(range(len(nodes))):
        label = dict(zip(nodes, perm, strict=True))
        edges = tuple(
            sorted(
                (
                    inst.shape,
                    inst.principle if principle_colors else "",
                    tuple(label[x] for x in inst.args),
                )
                for inst in core
            )
        )
        if best is None or edges < best:
            best = edges
    assert best is not None
    return (len(nodes), best)


def _refined_skeleton(
    core: list[Instance], nodes: list[Pop], *, principle_colors: bool
) -> tuple[object, ...]:
    """Isomorphism-invariant (not necessarily complete) form for skeletons over 9 relata.

    Colour refinement over the incidence structure; equal forms are necessary, not sufficient,
    for isomorphism, so results using it are flagged as inexact.
    """

    def tag(inst: Instance) -> tuple[str, str]:
        return (inst.shape, inst.principle if principle_colors else "")

    color: dict[Pop, object] = {x: () for x in nodes}
    for _ in range(len(nodes)):
        refined = {
            x: (
                color[x],
                tuple(
                    sorted(
                        (tag(inst), position, tuple(repr(color[y]) for y in inst.args))
                        for inst in core
                        for position, z in enumerate(inst.args)
                        if z == x
                    )
                ),
            )
            for x in nodes
        }
        palette = {c: i for i, c in enumerate(sorted({repr(c) for c in refined.values()}))}
        color = {x: palette[repr(refined[x])] for x in nodes}
    edges = tuple(sorted((*tag(inst), tuple(color[x] for x in inst.args)) for inst in core))
    return ("inexact-color-refinement", len(nodes), edges)


# The frozen baseline skeleton, with each named population replaced by a distinct placeholder
# multiset (only identity matters for canonicalization).
_A, _AB, _AC, _AAE, _AAF, _D, _G = ((i,) for i in range(7))
BASELINE_SKELETON = [
    Instance("non-repugnance", (_D, _A)),
    Instance("non-anti-egalitarianism", (_AC, _D)),
    Instance("non-anti-egalitarianism", (_AAF, _G)),
    Instance("non-sadism", (_AAE, _AAF)),
    Instance("mnep", (_AAE, _AB)),
    Instance("dominance", (_AC, _G)),
    Instance("addition", (_A, _AB, _AC)),
]
