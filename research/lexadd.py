"""Exact condition checks for lexicographic-additive axiologies.

A lexicographic-additive axiology ranks populations by the vector (V_1, …, V_k) of additive
tiers V_t(X) = Σ g_t(level) over X's lives, compared lexicographically: total and
critical-level utilitarianism (one tier), lexical threshold views, negative-lexical views,
and so on. Every tier is additive, so a shared background cancels, and a condition becomes a
statement about integer counts at finitely many levels. z3 searches for a counterexample of
any size, so "satisfies" here holds for every population size. Only a condition's outer
existential witnesses (Quality's n, NEP's n, …) are searched over a finite grid, up to
``WITNESS_MAX``. The "∀n ∃m > n" witnesses (Quantity, Inequality Aversion) are decided exactly
in closed form (``forall_exists_m``), and the "∀(x, y) ∃n" witness of Non-Elitism by an
existential z3 query with no bound.

Every violation comes back as a concrete counterexample (``Violation``) that tests turn into a
ladder instance, check against research/ladder.py's audit, and evaluate directly.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator, Mapping, Sequence
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Any

import z3  # type: ignore[import-untyped]

from research.ladder import Ladder

WITNESS_MAX = 6
Tier = dict[int, Fraction]


@dataclass(frozen=True)
class LexAxiology:
    id: str
    description: str
    tiers: tuple[Tier, ...]

    def key(self, pop: Sequence[int]) -> tuple[Fraction, ...]:
        return tuple(sum((t[v] for v in pop), Fraction(0)) for t in self.tiers)


def tiers_of(ladder: Ladder, *fns: Callable[[int], Fraction | int]) -> tuple[Tier, ...]:
    return tuple({v: Fraction(f(v)) for v in ladder.levels} for f in fns)


Counts = dict[int, z3.ArithRef]  # level -> nonnegative integer count


def _diff(ax: LexAxiology, left: Counts, right: Counts) -> list[z3.ArithRef]:
    levels = set(left) | set(right)
    return [
        z3.Sum(
            [z3.RealVal(t[lvl]) * left.get(lvl, 0) for lvl in levels]
            + [-z3.RealVal(t[lvl]) * right.get(lvl, 0) for lvl in levels]
        )
        for t in ax.tiers
    ]


def _lex_less(d: list[z3.ArithRef]) -> z3.BoolRef:
    """(V(L) − V(R)) is lexicographically negative."""
    return z3.Or(*[z3.And(*[d[s] == 0 for s in range(t)], d[t] < 0) for t in range(len(d))])


def _lex_leq(d: list[z3.ArithRef]) -> z3.BoolRef:
    return z3.Or(z3.And(*[x == 0 for x in d]), _lex_less(d))


def _violates(shape: str, d: list[z3.ArithRef]) -> z3.BoolRef:
    if shape == "W":  # L ⪰ R fails iff L − R is lex-negative
        return _lex_less(d)
    if shape == "S":  # L ≻ R fails iff L − R is lex ≤ 0
        return _lex_leq(d)
    if shape == "N":  # ¬(L ≻ R) fails iff L − R is lex-positive, i.e. R − L lex-negative
        return _lex_less([-x for x in d])
    raise ValueError(shape)


class _Fresh:
    def __init__(self) -> None:
        self.i = 0

    def var(self, name: str) -> z3.ArithRef:
        self.i += 1
        return z3.Int(f"{name}_{self.i}")

    def bag(self, levels: Sequence[int], name: str) -> tuple[Counts, list[z3.BoolRef]]:
        counts = {lvl: self.var(f"{name}{lvl}".replace("-", "m")) for lvl in levels}
        return counts, [c >= 0 for c in counts.values()]


def _size(c: Counts) -> z3.ArithRef:
    return z3.Sum(list(c.values())) if c else z3.IntVal(0)


def _find(formula: z3.BoolRef) -> z3.ModelRef | None:
    s = z3.Solver()
    s.add(formula)
    r = s.check()
    if r == z3.sat:
        return s.model()
    if r == z3.unsat:
        return None
    raise RuntimeError(f"z3 unknown: {s.reason_unknown()}")


@dataclass(frozen=True)
class Violation:
    """A concrete counterexample: the instance's two populations and its shape."""

    left: tuple[int, ...]
    right: tuple[int, ...]
    shape: str
    note: str


def _pops(
    model: z3.ModelRef, left: Counts, right: Counts
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    def realize(c: Counts) -> tuple[int, ...]:
        return tuple(
            sorted(
                lvl
                for lvl, v in c.items()
                for _ in range(model.eval(v, model_completion=True).as_long())
            )
        )

    return realize(left), realize(right)


def _ranges(ladder: Ladder, low: bool) -> list[tuple[int, int]]:
    pos = [v for v in ladder.levels if v > 0]
    return [(lo, hi) for lo in pos for hi in pos if hi - lo >= 2 and (lo == 1) == low]


def _const(level: int, n: z3.ArithRef | int) -> Counts:
    return {level: n if isinstance(n, z3.ArithRef) else z3.IntVal(n)}


def _plus(*cs: Counts) -> Counts:
    out: Counts = {}
    for c in cs:
        for lvl, v in c.items():
            out[lvl] = out[lvl] + v if lvl in out else v
    return out


# Each checker returns None if the axiology satisfies the condition on this ladder, or a
# Violation otherwise. Witness-bounded checkers try every grid witness and fail only if all fail.


def _universal(
    ax: LexAxiology, shape: str, spaces: Iterator[tuple[Counts, Counts, list[z3.BoolRef], str]]
) -> Violation | None:
    for left, right, side, note in spaces:
        m = _find(z3.And(*side, _violates(shape, _diff(ax, left, right))))
        if m is not None:
            lvl, r = _pops(m, left, right)
            return Violation(lvl, r, shape, note)
    return None


def egalitarian_dominance(ax: LexAxiology, ladder: Ladder) -> Violation | None:
    f = _Fresh()

    def spaces() -> Iterator[tuple[Counts, Counts, list[z3.BoolRef], str]]:
        for x in ladder.levels:
            below = [v for v in ladder.levels if v < x]
            if not below:
                continue
            n = f.var("n")
            b, side = f.bag(below, "b")
            yield _const(x, n), b, [n >= 1, _size(b) == n, *side], f"W_{x}"

    return _universal(ax, "S", spaces())


def _lex_nonneg(v: Sequence[Fraction]) -> bool:
    for x in v:
        if x != 0:
            return x > 0
    return True


def forall_exists_m(a: Sequence[Fraction], b: Sequence[Fraction]) -> int | None:
    """Decide ∀n ≥ 1 ∃m > n: m·a − n·b is lexicographically ≥ 0, exactly.

    Returns None if it holds, else an n for which no m works. At the first tier with
    (a_t, b_t) ≠ 0: a_t > 0 lets m grow; a_t = 0 leaves the sign of −b_t; a_t < 0 makes m = n + 1
    the only candidate, whose tier value a_t + n·(a_t − b_t) must stay ≥ 0 for every n, with the
    one tie point n* (if any) decided by the remaining tiers at m = n* + 1.
    """
    for t, (at, bt) in enumerate(zip(a, b, strict=True)):
        if at == 0 and bt == 0:
            continue
        if at > 0:
            return None
        if at == 0:
            return None if bt < 0 else 1
        slope = at - bt
        if slope <= 0:
            # a_t + n·slope < 0 for every n (a_t < 0 and slope <= 0)
            return 1
        if 2 * at - bt < 0:
            # value at n = 1 is negative; it grows with n, so find the first n that fails
            return 1
        # value at n >= 1 is >= value at n = 1 >= 0; a tie happens only if 2a_t − b_t == 0 (n = 1)
        if 2 * at - bt == 0:
            rest = [(2 * x - y) for x, y in zip(a[t + 1 :], b[t + 1 :], strict=True)]
            return None if _lex_nonneg(rest) else 1
        return None
    return None


def _forall_exists_m(
    ax: LexAxiology, make: Callable[[int, int], tuple[Counts, Counts]], note: str
) -> Violation | None:
    """∀n ≥ 1 ∃m > n: W(L(n, m), R(n, m)), where L − R is linear: m·a − n·b per tier."""

    def diff(n: int, m: int) -> list[Fraction]:
        left, right = make(n, m)
        out = []
        for tier in ax.tiers:
            total = Fraction(0)
            for level, count in left.items():
                total += tier[level] * z3.simplify(count).as_long()
            for level, count in right.items():
                total -= tier[level] * z3.simplify(count).as_long()
            out.append(total)
        return out

    d01, d10 = diff(0, 1), diff(1, 0)  # a = d(0, 1), −b = d(1, 0)
    bad = forall_exists_m(d01, [-x for x in d10])
    if bad is None:
        return None
    left, right = make(bad, bad + 1)
    lp = tuple(sorted(k for k, v in left.items() for _ in range(z3.simplify(v).as_long())))
    rp = tuple(sorted(k for k, v in right.items() for _ in range(z3.simplify(v).as_long())))
    return Violation(lp, rp, "W", f"{note}: no m > n works at n = {bad} (shown with m = n + 1)")


def quantity(ax: LexAxiology, ladder: Ladder) -> Violation | None:
    for y in (v for v in ladder.levels if v > 0 and ladder.has(v + 1)):

        def make(n: int, m: int, y: int = y) -> tuple[Counts, Counts]:
            return _const(y, m), _const(y + 1, n)

        v = _forall_exists_m(ax, make, f"y = W_{y}")
        if v:
            return v
    return None


def inequality_aversion(ax: LexAxiology, ladder: Ladder) -> Violation | None:
    lv = ladder.levels
    for x, y, z in product(lv, lv, lv):
        if x > y > z:

            def make(n: int, m: int, x: int = x, y: int = y, z: int = z) -> tuple[Counts, Counts]:
                return _const(y, m + n), _plus(_const(x, n), _const(z, m))

            v = _forall_exists_m(ax, make, f"(W_{x}, W_{y}, W_{z})")
            if v:
                return v
    return None


def non_elitism(ax: LexAxiology, ladder: Ladder) -> Violation | None:
    """∀x, y (x−1 > y) ∃n ≥ 1: (n+1) at W_{x−1} ⪰ one at W_x plus n at W_y."""
    lv = ladder.levels
    for x, y in product(lv, lv):
        if ladder.has(x - 1) and x - 1 > y:
            n = z3.Int("n")
            left, right = _const(x - 1, n + 1), _plus(_const(x, 1), _const(y, n))
            ok = z3.Not(_violates("W", _diff(ax, left, right)))
            if _find(z3.And(n >= 1, ok)) is None:
                return Violation(
                    (x - 1, x - 1), tuple(sorted((x, y))), "W", f"no n works for (W_{x}, W_{y})"
                )
    return None


def non_sadism(ax: LexAxiology, ladder: Ladder) -> Violation | None:
    f = _Fresh()

    def spaces() -> Iterator[tuple[Counts, Counts, list[z3.BoolRef], str]]:
        for x, y in product(
            [v for v in ladder.levels if v > 0], [v for v in ladder.levels if v < 0]
        ):
            k, j = f.var("k"), f.var("j")
            yield _const(x, k), _const(y, j), [k >= 1, j >= 1], f"(W_{x}, W_{y})"

    return _universal(ax, "W", spaces())


def _dominance_addition(ax: LexAxiology, ladder: Ladder, equal_c: bool) -> Violation | None:
    f = _Fresh()
    lv = ladder.levels
    pos = [v for v in lv if v > 0]

    def spaces() -> Iterator[tuple[Counts, Counts, list[z3.BoolRef], str]]:
        for t in lv[1:]:
            a, sa = f.bag([v for v in lv if v < t], "a")
            b, sb = f.bag([v for v in lv if v >= t], "b")
            base = [*sa, *sb, _size(a) == _size(b), _size(a) >= 1]
            if equal_c:
                for y in pos:
                    k = f.var("k")
                    # thesis: ¬(A ≻ B ∪ C), shape N with left = A.
                    yield a, _plus(b, _const(y, k)), [*base, k >= 1], f"threshold W_{t}, C at W_{y}"
            else:
                c, sc = f.bag(pos, "c")
                # 2003: B ∪ C ⪰ A, shape W with left = B ∪ C.
                yield _plus(b, c), a, [*base, *sc, _size(c) >= 1], f"threshold W_{t}"

    return _universal(ax, "N" if equal_c else "W", spaces())


def dominance_addition_thesis(ax: LexAxiology, ladder: Ladder) -> Violation | None:
    return _dominance_addition(ax, ladder, True)


def dominance_addition_2003(ax: LexAxiology, ladder: Ladder) -> Violation | None:
    return _dominance_addition(ax, ladder, False)


def _range_fix(fix: Mapping[str, int], open_top: bool) -> tuple[int, int, int]:
    """Quality's (u, v, y) or Weak Quality Addition's (x, w, y) as one (low, high, y) triple."""
    return (fix["x"], fix["w"], fix["y"]) if open_top else (fix["u"], fix["v"], fix["y"])


def _witnessed(checks: Iterator[Callable[[], Violation | None]]) -> Violation | None:
    """Satisfied if some witness's universal check finds no violation; else the last violation."""
    last: Violation | None = None
    for check in checks:
        v = check()
        if v is None:
            return None
        last = v
    return last or Violation((), (), "W", "no valid witness on this ladder")


def _quality_like(
    ax: LexAxiology, ladder: Ladder, open_top: bool, fix: Mapping[str, int] | None = None
) -> Violation | None:
    def checks() -> Iterator[Callable[[], Violation | None]]:
        for (_, y), (u, v) in product(_ranges(ladder, True), _ranges(ladder, False)):
            if u <= y or (fix is not None and (u, v, y) != _range_fix(fix, open_top)):
                continue
            tops = [z for z in ladder.levels if z >= u and (open_top or z <= v)]
            for n in range(1, WITNESS_MAX + 1):

                def check(y: int = y, tops: list[int] = tops, n: int = n) -> Violation | None:
                    f = _Fresh()

                    def spaces() -> Iterator[tuple[Counts, Counts, list[z3.BoolRef], str]]:
                        for z in tops:
                            b, sb = f.bag(ladder.range(1, y), "b")
                            yield _const(z, n), b, [*sb, _size(b) >= 1], f"A = {n} at W_{z}"

                    return _universal(ax, "W", spaces())

                yield check

    return _witnessed(checks())


def quality(
    ax: LexAxiology, ladder: Ladder, fix: Mapping[str, int] | None = None
) -> Violation | None:
    return _quality_like(ax, ladder, open_top=False, fix=fix)


def weak_quality_addition(
    ax: LexAxiology, ladder: Ladder, fix: Mapping[str, int] | None = None
) -> Violation | None:
    return _quality_like(ax, ladder, open_top=True, fix=fix)


def non_extreme_priority(
    ax: LexAxiology, ladder: Ladder, fix: Mapping[str, int] | None = None
) -> Violation | None:
    def checks() -> Iterator[Callable[[], Violation | None]]:
        for (_, z), x, y in product(
            _ranges(ladder, True), ladder.levels, [v for v in ladder.levels if v < 0]
        ):
            if x <= z or (fix is not None and (x, y, z) != (fix["x"], fix["y"], fix["z"])):
                continue
            for n in range(1, WITNESS_MAX + 1):

                def check(x: int = x, y: int = y, z: int = z, n: int = n) -> Violation | None:
                    f = _Fresh()

                    def spaces() -> Iterator[tuple[Counts, Counts, list[z3.BoolRef], str]]:
                        for u in (v for v in ladder.levels if v >= x):
                            b, sb = f.bag(ladder.range(1, z), "b")
                            left = _plus(_const(u, n), _const(y, 1))
                            yield left, b, [*sb, _size(b) == n + 1], f"u = W_{u}"

                    return _universal(ax, "W", spaces())

                yield check

    return _witnessed(checks())


def general_non_extreme_priority(
    ax: LexAxiology, ladder: Ladder, fix: Mapping[str, int] | None = None
) -> Violation | None:
    for z in ladder.levels:
        if not ladder.has(z + 1):
            continue

        def checks(z: int = z) -> Iterator[Callable[[], Violation | None]]:
            for (_, y), u in product(_ranges(ladder, True), [v for v in ladder.levels if v > 0]):
                if u <= y or (fix is not None and (u, y) != (fix["u"], fix["y"])):
                    continue
                for n in range(1, WITNESS_MAX + 1):

                    def check(y: int = y, u: int = u, n: int = n) -> Violation | None:
                        f = _Fresh()

                        def spaces() -> Iterator[tuple[Counts, Counts, list[z3.BoolRef], str]]:
                            for x in (v for v in ladder.levels if v >= u):
                                b, sb = f.bag(ladder.range(1, y), "b")
                                left = _plus(_const(x, n), _const(z, 1))
                                right = _plus(b, _const(z + 1, 1))
                                yield left, right, [*sb, _size(b) == n], f"z = W_{z}, x = W_{x}"

                        return _universal(ax, "W", spaces())

                    yield check

        v = _witnessed(checks())
        if v:
            return v
    return None


def weak_non_sadism(
    ax: LexAxiology, ladder: Ladder, fix: Mapping[str, int] | None = None
) -> Violation | None:
    def checks() -> Iterator[Callable[[], Violation | None]]:
        for x in (v for v in ladder.levels if v < 0):
            if fix is not None and x != fix["x"]:
                continue
            for n in range(1, WITNESS_MAX + 1):

                def check(x: int = x, n: int = n) -> Violation | None:
                    f = _Fresh()

                    def spaces() -> Iterator[tuple[Counts, Counts, list[z3.BoolRef], str]]:
                        for y in (v for v in ladder.levels if v > 0):
                            k = f.var("k")
                            yield _const(y, k), _const(x, n), [k >= 1], f"W_{y}"

                    return _universal(ax, "W", spaces())

                yield check

    return _witnessed(checks())


def vrc_avoidance(
    ax: LexAxiology, ladder: Ladder, fix: Mapping[str, int] | None = None
) -> Violation | None:
    def checks() -> Iterator[Callable[[], Violation | None]]:
        for (_, y), (u, _v), x in product(
            _ranges(ladder, True), _ranges(ladder, False), [v for v in ladder.levels if v < 0]
        ):
            if u <= y or (fix is not None and (x, u, y) != (fix["x"], fix["u"], fix["y"])):
                continue
            for n, m in product(range(1, WITNESS_MAX + 1), repeat=2):

                def check(
                    y: int = y, u: int = u, x: int = x, n: int = n, m: int = m
                ) -> Violation | None:
                    f = _Fresh()

                    def spaces() -> Iterator[tuple[Counts, Counts, list[z3.BoolRef], str]]:
                        for z in (v for v in ladder.levels if v >= u):
                            b, sb = f.bag(ladder.range(1, y), "b")
                            right = _plus(b, _const(x, m))
                            yield _const(z, n), right, [*sb, _size(b) >= 1], f"z = W_{z}"

                    return _universal(ax, "W", spaces())

                yield check

    return _witnessed(checks())


CHECKS: dict[str, Callable[[LexAxiology, Ladder], Violation | None]] = {
    "thesis:egalitarian-dominance": egalitarian_dominance,
    "thesis:quantity": quantity,
    "thesis:quality": quality,
    "thesis:dominance-addition": dominance_addition_thesis,
    "arrhenius-2003:dominance-addition": dominance_addition_2003,
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


def battery(ladder: Ladder) -> tuple[LexAxiology, ...]:
    """Lexicographic-additive axiologies built from a small grammar of tiers.

    An optional first tier sums negative welfare (negatives are lexically bad). The next tier is
    total welfare, critical-level welfare Σ(w − c) for c at every half level between the lowest
    and highest positive level, or the welfare of lives at or above a threshold W_h. A final
    total-welfare tier breaks remaining ties.
    """
    pos = [v for v in ladder.levels if v > 0]
    middles: list[tuple[str, str, Callable[[int], Fraction | int]]] = [
        ("total", "total welfare", lambda v: v)
    ]

    def critical(c: Fraction) -> Callable[[int], Fraction | int]:
        return lambda v: Fraction(v) - c

    def threshold(h: int) -> Callable[[int], Fraction | int]:
        return lambda v: v if v >= h else 0

    for twice_c in range(2 * pos[0], 2 * pos[-1] + 1):
        c = Fraction(twice_c, 2)
        middles.append((f"critical-level-{c}", f"Σ(w − {c})", critical(c)))
    for h in pos[2:]:
        middles.append((f"threshold-{h}", f"welfare of lives at or above W_{h}", threshold(h)))
    out = []
    for negative_first in (False, True):
        for name, desc, fn in middles:
            fns: list[Callable[[int], Fraction | int]] = [fn, lambda v: v]
            label, text = name, desc
            if negative_first:
                fns = [lambda v: min(v, 0), *fns]
                label, text = f"negative-then-{name}", f"total negative welfare, then {desc}"
            out.append(LexAxiology(label, f"{text}, then total welfare", tiers_of(ladder, *fns)))
    return tuple(out)


_LEVEL_WITNESSED = {
    "thesis:quality",
    "thesis:weak-quality-addition",
    "thesis:non-extreme-priority",
    "thesis:general-non-extreme-priority",
    "thesis:weak-non-sadism",
    "arrhenius-2003:vrc-avoidance",
    "arrhenius-2009:weak-quality-addition",
}


def check_at(
    principle: str, ax: LexAxiology, ladder: Ladder, levels: Mapping[str, int] | None
) -> Violation | None:
    """CHECKS[principle] with the condition's level witnesses fixed (counts still searched)."""
    fn = CHECKS[principle]
    if levels and principle in _LEVEL_WITNESSED:
        return fn(ax, ladder, fix=levels)  # type: ignore[call-arg]
    return fn(ax, ladder)


def from_additive(ladder: Ladder, name: str, g: Mapping[Any, str]) -> LexAxiology:
    """A one-tier axiology from an additive g (z3 model values as rational strings), keyed by
    level or, after a JSON round trip, by the level's string."""
    values = {v: Fraction(g[v] if v in g else g[str(v)]) for v in ladder.levels}
    return LexAxiology(name, "additive V = Σ g(w)", (values,))
