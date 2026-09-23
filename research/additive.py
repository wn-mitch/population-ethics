"""Exact additive realizability of the thesis-family conditions.

An additive axiology ranks populations by V(X) = Σ_{lives} g(level) for some real g on the
ladder's levels (generalized utilitarianism: total, critical-level, prioritarian, bounded, …).
For such an axiology a shared background cancels, so each condition of research/ladder.py
reduces to a first-order constraint on the finitely many values g(W_i). The universal
quantifiers over population sizes are eliminated in closed form here:

- ``∀n ≥ 1 ∃m > n: m·a ≥ n·b`` holds iff a > 0, or a = 0 ∧ b ≤ 0, or a < 0 ∧ b ≤ 2a
  (for a < 0 the best m is n + 1, and the n = 1 case is the binding one).
- ``∃n ≥ 1 ∀i: n·a_i ≥ K_i`` is kept as an integer n with z3 (nonlinear in n·g, but tiny).
- A sum over an arbitrary nonempty population within a range is bounded above only if g ≤ 0
  on the range, and then its supremum is the range's largest g (one life).

Each condition's derivation is in its docstring. ``AdditiveEngine.require(ids)`` asks whether
some g satisfies all of them; ``classify`` enumerates every minimal unrealizable set and every
maximal realizable set with MARCO, with a witness g for each maximal set. Unlike the census,
these are statements about all population sizes and all witnesses on the given ladder, not
bounded ones.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from itertools import product
from typing import Any

import z3  # type: ignore[import-untyped]

from research.lab import Check
from research.ladder import Ladder

G = dict[int, z3.ArithRef]
Formula = Callable[[Ladder, G, "Fresh"], z3.BoolRef]


@dataclass
class Fresh:
    """Fresh integer witnesses for ∃n ≥ 1 quantifiers."""

    count: int = 0
    made: list[z3.ArithRef] = field(default_factory=list)

    def n(self) -> z3.ArithRef:
        self.count += 1
        v = z3.Int(f"n{self.count}")
        self.made.append(v)
        return v


def _ranges(ladder: Ladder, low: bool) -> list[tuple[int, int]]:
    """Positive ranges R(lo, hi) of at least three levels; low ones start at W_1."""
    pos = [v for v in ladder.levels if v > 0]
    return [(lo, hi) for lo in pos for hi in pos if hi - lo >= 2 and (lo == 1) == low]


def _forall_m_greater(a: z3.ArithRef, b: z3.ArithRef) -> z3.BoolRef:
    """∀n ≥ 1 ∃m > n: m·a ≥ n·b."""
    return z3.Or(a > 0, z3.And(a == 0, b <= 0), z3.And(a < 0, b <= 2 * a))


def _exists_n(fresh: Fresh, terms: Iterable[tuple[z3.ArithRef, z3.ArithRef]]) -> z3.BoolRef:
    """∃n ≥ 1 ∀i: n·a_i ≥ K_i."""
    n = fresh.n()
    return z3.And(n >= 1, *[n * a >= k for a, k in terms])


def _levels(ladder: Ladder, pred: Callable[[int], bool]) -> list[int]:
    return [v for v in ladder.levels if pred(v)]


def egalitarian_dominance(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """n lives at W_x beat any n lives all below W_x: n = 1 is binding, so g is strictly
    increasing."""
    lv = ladder.levels
    return z3.And(*[g[a] < g[b] for a, b in zip(lv, lv[1:], strict=False)])


def quantity(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """∀ positive y with W_{y+1}, ∀n ∃m > n: m·g(y) ≥ n·g(y+1)."""
    pos = _levels(ladder, lambda v: v > 0)
    return z3.And(*[_forall_m_greater(g[y], g[y + 1]) for y in pos if y + 1 in g])


def quality(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """∃ R(u, v) above R(1, y), ∃n: n·g(z) ≥ V(B) for z in R(u, v) and nonempty B ⊂ R(1, y).
    V(B) is bounded only if g ≤ 0 on R(1, y), with supremum max g there; then n = 1 is best."""
    options = []
    for (_, y), (u, v) in product(_ranges(ladder, True), _ranges(ladder, False)):
        if u > y:
            low = ladder.range(1, y)
            options.append(
                z3.And(
                    *[g[lvl] <= 0 for lvl in low],
                    *[g[z] >= g[lvl] for z in ladder.range(u, v) for lvl in low],
                )
            )
    return z3.Or(*options) if options else z3.BoolVal(False)


def dominance_addition(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """V(B) + V(C) ≥ V(A) for same-size A below a threshold, B at or above it, and any
    positive (thesis: perfectly equal) C: g nondecreasing (else large n fails) and g ≥ 0 on the
    positive levels (else many C-lives fail)."""
    lv = ladder.levels
    return z3.And(
        *[g[a] <= g[b] for a, b in zip(lv, lv[1:], strict=False)],
        *[g[y] >= 0 for y in lv if y > 0],
    )


def inequality_aversion(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """∀x > y > z ∀n ∃m > n: (m+n)·g(y) ≥ n·g(x) + m·g(z)."""
    lv = ladder.levels
    return z3.And(
        *[
            _forall_m_greater(g[y] - g[z], g[x] - g[y])
            for x in lv
            for y in lv
            for z in lv
            if x > y > z
        ]
    )


def non_sadism(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """k·g(x) ≥ j·g(y) for positive x, negative y and all k, j ≥ 1."""
    return z3.And(
        *[g[v] >= 0 for v in ladder.levels if v > 0], *[g[v] <= 0 for v in ladder.levels if v < 0]
    )


def non_extreme_priority(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """∃W_x, W_y (y < 0), R(1, z) (x > z), ∃n: n·g(u) + g(y) ≥ V(B) for u ≥ x and |B| = n+1 in
    R(1, z). The worst B is n+1 lives at the range's top g, and the inequality is monotone in
    that value, so it suffices over every level lvl of the range."""
    options = []
    for (_, z), x, y in product(
        _ranges(ladder, True), ladder.levels, _levels(ladder, lambda v: v < 0)
    ):
        if x > z:
            terms = [
                (g[u] - g[lvl], g[lvl] - g[y])
                for u in ladder.levels
                if u >= x
                for lvl in ladder.range(1, z)
            ]
            options.append(_exists_n(fresh, terms))
    return z3.Or(*options) if options else z3.BoolVal(False)


def weak_quality_addition(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """As Quality, with A at any level ≥ W_x (not only within R(x, w)); the background C
    cancels, so the witness can be uniform."""
    options = []
    for (_, y), (x, _w) in product(_ranges(ladder, True), _ranges(ladder, False)):
        if x > y:
            low = ladder.range(1, y)
            options.append(
                z3.And(
                    *[g[lvl] <= 0 for lvl in low],
                    *[g[z] >= g[lvl] for z in ladder.levels if z >= x for lvl in low],
                )
            )
    return z3.Or(*options) if options else z3.BoolVal(False)


def non_elitism(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """∀x, y (x−1 > y) ∃n ≥ 1: (n+1)·g(x−1) ≥ g(x) + n·g(y); the background cancels."""
    lv = ladder.levels
    return z3.And(
        *[
            _exists_n(fresh, [(g[x - 1] - g[y], g[x] - g[x - 1])])
            for x in lv
            for y in lv
            if x - 1 in g and x - 1 > y
        ]
    )


def general_non_extreme_priority(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """∀W_z ∃ positive W_u above R(1, y), ∃n: n·g(x) + g(z) ≥ V(B) + g(z+1) for x ≥ u and |B| = n
    in R(1, y); monotone in B's top value as for NEP."""
    parts = []
    for z in ladder.levels:
        if z + 1 not in g:
            continue
        options = []
        for (_, y), u in product(_ranges(ladder, True), _levels(ladder, lambda v: v > 0)):
            if u > y:
                terms = [
                    (g[x] - g[lvl], g[z + 1] - g[z])
                    for x in ladder.levels
                    if x >= u
                    for lvl in ladder.range(1, y)
                ]
                options.append(_exists_n(fresh, terms))
        parts.append(z3.Or(*options) if options else z3.BoolVal(False))
    return z3.And(*parts)


def weak_non_sadism(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """∃ negative W_x, ∃n: k·g(y) ≥ n·g(x) for positive y and k ≥ 1: g ≥ 0 on positive levels
    (else many y-lives fail), and then k = 1 is binding."""
    options = [
        _exists_n(fresh, [(-g[x], -g[y]) for y in ladder.levels if y > 0])
        for x in ladder.levels
        if x < 0
    ]
    return z3.And(
        *[g[y] >= 0 for y in ladder.levels if y > 0],
        z3.Or(*options) if options else z3.BoolVal(False),
    )


def vrc_avoidance(ladder: Ladder, g: G, fresh: Fresh) -> z3.BoolRef:
    """∃ negative W_x, R(u, v) above R(1, y), ∃n, m: n·g(z) ≥ V(B) + m·g(x) for z ≥ u and
    nonempty B ⊂ R(1, y). Needs g ≤ 0 on R(1, y); then either g(x) < 0 (m large settles it) or
    m = 1 is best."""
    options = []
    for (_, y), (u, _v), x in product(
        _ranges(ladder, True), _ranges(ladder, False), _levels(ladder, lambda v: v < 0)
    ):
        if u > y:
            low = ladder.range(1, y)
            highs = [z for z in ladder.levels if z >= u]
            options.append(
                z3.And(
                    *[g[lvl] <= 0 for lvl in low],
                    z3.Or(
                        g[x] < 0,
                        _exists_n(fresh, [(g[z], g[lvl] + g[x]) for z in highs for lvl in low]),
                    ),
                )
            )
    return z3.Or(*options) if options else z3.BoolVal(False)


# Primitive thesis-family conditions. Additively, the ranged and any-background forms of
# Non-Elitism coincide, as do the two Dominance Addition forms and 2009 Weak Quality Addition
# with VRC avoidance; they are kept separate so the classification speaks in source terms.
CONDITIONS: dict[str, Formula] = {
    "thesis:egalitarian-dominance": egalitarian_dominance,
    "thesis:quantity": quantity,
    "thesis:quality": quality,
    "thesis:dominance-addition": dominance_addition,
    "arrhenius-2003:dominance-addition": dominance_addition,
    "thesis:inequality-aversion": inequality_aversion,
    "thesis:non-sadism": non_sadism,
    "thesis:non-extreme-priority": non_extreme_priority,
    "thesis:weak-quality-addition": weak_quality_addition,
    "thesis:non-elitism": non_elitism,
    "arrhenius-2003:non-elitism": non_elitism,
    "thesis:general-non-extreme-priority": general_non_extreme_priority,
    "thesis:weak-non-sadism": weak_non_sadism,
    "arrhenius-2003:vrc-avoidance": vrc_avoidance,
    "arrhenius-2009:weak-quality-addition": vrc_avoidance,
}


class AdditiveEngine:
    """Guarded z3 encoding of the conditions over one ladder, with the MARCO interface."""

    def __init__(self, ladder: Ladder, ids: Sequence[str] = tuple(CONDITIONS)) -> None:
        self.ladder = ladder
        self.g: G = {v: z3.Real(f"g{v}".replace("-", "m")) for v in ladder.levels}
        self.fresh = Fresh()
        self.solver = z3.SolverFor("QF_NIRA")
        self.guard = {cid: z3.Bool(f"c{i}") for i, cid in enumerate(ids)}
        self.soft = {cid: cid for cid in ids}
        self.name = {str(b): cid for cid, b in self.guard.items()}
        for cid, b in self.guard.items():
            self.solver.add(z3.Implies(b, CONDITIONS[cid](ladder, self.g, self.fresh)))
        self.calls = 0

    def require(self, enabled: Iterable[str] = ()) -> Check:
        self.calls += 1
        status = self.solver.check(*[self.guard[c] for c in set(enabled)])
        if status == z3.sat:
            return Check("sat", None, (), None)
        if status == z3.unsat:
            core = tuple(sorted(self.name[str(b)] for b in self.solver.unsat_core()))
            return Check("unsat", None, core, None)
        raise RuntimeError(f"additive engine returned unknown: {self.solver.reason_unknown()}")

    def model(self, enabled: Iterable[str]) -> dict[int, str] | None:
        if self.require(enabled).decision != "sat":
            return None
        m = self.solver.model()
        return {v: str(m.eval(x, model_completion=True)) for v, x in self.g.items()}

    def shrink(self, enabled: Iterable[str]) -> tuple[str, ...]:
        current = sorted(self.require(enabled).core)
        i = 0
        while i < len(current):
            trial = current[:i] + current[i + 1 :]
            if self.require(trial).decision == "unsat":
                current = trial
            else:
                i += 1
        for c in current:
            if self.require([x for x in current if x != c]).decision != "sat":
                raise AssertionError("shrink produced a non-minimal core")
        return tuple(current)

    def grow(self, enabled: Iterable[str]) -> tuple[str, ...]:
        current = set(enabled)
        for c in sorted(self.soft):
            if c not in current and self.require(current | {c}).decision == "sat":
                current.add(c)
        return tuple(sorted(current))


def classify(ladder: Ladder, ids: Sequence[str] = tuple(CONDITIONS)) -> dict[str, Any]:
    """Minimal additively unrealizable condition sets and maximal realizable ones, with a g."""
    from research.lab import marco

    engine = AdditiveEngine(ladder, ids)
    muses, msses = marco(engine)  # type: ignore[arg-type]
    return {
        "minimal_unrealizable": [list(m) for m in muses],
        "maximal_realizable": [{"conditions": list(m), "g": engine.model(m)} for m in msses],
        "solver_calls": engine.calls,
    }
