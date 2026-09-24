"""Independent SMT/CHC obligations for P21's integer-chain construction.

The solver checks every integer parameter and every finite path through an abstract
transition system. The connection from source prose to these edge schemas is a
separate reading judgment; the bounded source audit tests that translation.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

import z3  # type: ignore[import-untyped]

EXPECTED_WITNESS = {
    "non-elitism": {"n": 1},
    "general-non-extreme-priority": {"u": 5, "y": 3, "n": 1},
    "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
}


def _weight(level: z3.ArithRef) -> z3.ArithRef:
    return z3.If(level <= 0, 1, z3.If(level >= 5, -1, 0))


def _unsat(label: str, *conditions: z3.BoolRef) -> None:
    solver = z3.Solver()
    solver.add(*conditions)
    result = solver.check()
    if result != z3.unsat:
        detail = f"; counterexample: {solver.model()}" if result == z3.sat else ""
        raise AssertionError(f"{label}: expected unsat, got {result}{detail}")


def _positive_sums() -> None:
    """Spacer induction: every nonempty finite sum of positive gains is positive."""
    count, total, gain = z3.Int("sum_count"), z3.Real("sum_total"), z3.Real("sum_gain")
    sum_of_gains = z3.Function(
        "p21_sum_of_positive_gains", z3.IntSort(), z3.RealSort(), z3.BoolSort()
    )
    failure = z3.Function("p21_nonpositive_gain_sum", z3.BoolSort())
    solver = z3.Fixedpoint()
    solver.set(engine="spacer")
    solver.register_relation(sum_of_gains, failure)
    solver.declare_var(count, total, gain)
    solver.fact(sum_of_gains(0, 0))
    solver.rule(sum_of_gains(count + 1, total + gain), [sum_of_gains(count, total), gain > 0])
    solver.rule(failure(), [sum_of_gains(count, total), count > 0, total <= 0])
    result = solver.query(failure())
    if result != z3.unsat:
        raise AssertionError(f"finite positive-gain sums: expected unsat, got {result}")


def _signed_sums() -> None:
    """Spacer induction for arbitrary finite bags of signed invariant weights."""
    count, total, weight = z3.Int("weight_count"), z3.Int("weight_total"), z3.Int("life_weight")
    nonnegative = z3.Function("p21_nonnegative_bag", z3.IntSort(), z3.IntSort(), z3.BoolSort())
    nonpositive = z3.Function("p21_nonpositive_bag", z3.IntSort(), z3.IntSort(), z3.BoolSort())
    failure = z3.Function("p21_bad_signed_bag", z3.BoolSort())
    solver = z3.Fixedpoint()
    solver.set(engine="spacer")
    solver.register_relation(nonnegative, nonpositive, failure)
    solver.declare_var(count, total, weight)
    solver.fact(nonnegative(0, 0))
    solver.fact(nonpositive(0, 0))
    solver.rule(
        nonnegative(count + 1, total + weight),
        [nonnegative(count, total), weight >= 0],
    )
    solver.rule(
        nonpositive(count + 1, total + weight),
        [nonpositive(count, total), weight <= 0],
    )
    solver.rule(failure(), [nonnegative(count, total), total < 0])
    solver.rule(failure(), [nonpositive(count, total), total > 0])
    result = solver.query(failure())
    if result != z3.unsat:
        raise AssertionError(f"finite signed bag sums: expected unsat, got {result}")


def _potential_gaps() -> None:
    """Induct over every additional adjacent gain in the NE and GNEP gaps."""
    count = z3.Int("gap_count")
    difference, previous, current, added = z3.Reals(
        "gap_difference previous_gain current_gain added_gain"
    )
    ne_gap = z3.Function(
        "p21_ne_gain_gap",
        z3.IntSort(),
        z3.RealSort(),
        z3.RealSort(),
        z3.RealSort(),
        z3.BoolSort(),
    )
    high_gap = z3.Function("p21_high_gain_gap", z3.IntSort(), z3.RealSort(), z3.BoolSort())
    failure = z3.Function("p21_bad_gain_gap", z3.BoolSort())
    solver = z3.Fixedpoint()
    solver.set(engine="spacer")
    solver.register_relation(ne_gap, high_gap, failure)
    solver.declare_var(count, difference, previous, current, added)
    # F(m)-F(y) for y<m contains g(m-1), plus any finite number of
    # positive earlier gains. It must exceed g(m).
    solver.rule(ne_gap(1, previous, previous, current), [previous > current, current > 0])
    solver.rule(
        ne_gap(count + 1, difference + added, previous, current),
        [ne_gap(count, difference, previous, current), added > 0],
    )
    solver.rule(failure(), [ne_gap(count, difference, previous, current), difference <= current])
    # F(h)-F(b) for h>=5,b<=3 contains g(3)+g(4) and possibly other
    # positive gains. Every adjacent GNEP offset is <2.
    high_to_low = z3.RealVal(10) / 9 + z3.RealVal(18) / 17
    solver.fact(high_gap(0, high_to_low))
    solver.rule(high_gap(count + 1, difference + added), [high_gap(count, difference), added > 0])
    solver.rule(failure(), [high_gap(count, difference), difference <= 2])
    result = solver.query(failure())
    if result != z3.unsat:
        raise AssertionError(f"unbounded potential gaps: expected unsat, got {result}")


def _path_closure() -> None:
    """Spacer induction over paths of arbitrary finite length and population size.

    Each same-size edge lowers the potential and preserves I>=1; when its
    source is a singleton it also lowers that life. A growing VRC edge starts
    at a singleton of level >=4, ends at size >=2, and sets I=1. The numeric
    edge conditions are checked below; the structural shape comes from the
    reviewed source schemas.
    """
    integer, real, boolean = z3.IntSort(), z3.RealSort(), z3.BoolSort()
    reach = z3.Function(
        "p21_abstract_reach",
        integer,
        real,
        integer,
        integer,  # original size, potential, I, singleton level
        integer,
        real,
        integer,
        integer,  # current size, potential, I, singleton level
        boolean,
        boolean,
        boolean,  # has grown, has moved, predicate
    )
    failure = z3.Function("p21_bad_path", boolean)
    solver = z3.Fixedpoint()
    solver.set(engine="spacer")
    solver.register_relation(reach, failure)
    origin_size, size, next_size = z3.Ints("origin_size size next_size")
    origin_potential, potential, next_potential = z3.Reals(
        "origin_potential potential next_potential"
    )
    origin_i, current_i, next_i = z3.Ints("origin_i current_i next_i")
    origin_level, level, next_level = z3.Ints("origin_level level next_level")
    grown, moved = z3.Bools("grown moved")
    solver.declare_var(
        origin_size,
        size,
        next_size,
        origin_potential,
        potential,
        next_potential,
        origin_i,
        current_i,
        next_i,
        origin_level,
        level,
        next_level,
        grown,
        moved,
    )
    solver.rule(
        reach(
            origin_size,
            origin_potential,
            origin_i,
            origin_level,
            origin_size,
            origin_potential,
            origin_i,
            origin_level,
            False,
            False,
        ),
        origin_size >= 0,
    )
    solver.rule(
        reach(
            origin_size,
            origin_potential,
            origin_i,
            origin_level,
            size,
            next_potential,
            next_i,
            next_level,
            grown,
            True,
        ),
        [
            reach(
                origin_size,
                origin_potential,
                origin_i,
                origin_level,
                size,
                potential,
                current_i,
                level,
                grown,
                moved,
            ),
            size >= 1,
            next_potential < potential,
            z3.Implies(current_i >= 1, next_i >= 1),
            z3.Implies(size == 1, next_level < level),
        ],
    )
    solver.rule(
        reach(
            origin_size,
            origin_potential,
            origin_i,
            origin_level,
            next_size,
            next_potential,
            1,
            next_level,
            True,
            True,
        ),
        [
            reach(
                origin_size,
                origin_potential,
                origin_i,
                origin_level,
                size,
                potential,
                current_i,
                level,
                grown,
                moved,
            ),
            size == 1,
            level >= 4,
            next_size >= 2,
        ],
    )
    here = reach(
        origin_size,
        origin_potential,
        origin_i,
        origin_level,
        size,
        potential,
        current_i,
        level,
        grown,
        moved,
    )
    solver.rule(failure(), [here, moved, size == origin_size, potential >= origin_potential])
    solver.rule(failure(), [here, origin_size >= 2, size > origin_size])
    solver.rule(failure(), [here, origin_size == 1, origin_level < 4, size > 1])
    solver.rule(failure(), [here, grown, current_i < 1])
    solver.rule(failure(), [here, origin_size == 0, moved])
    result = solver.query(failure())
    if result != z3.unsat:
        raise AssertionError(f"unbounded closure paths: expected unsat, got {result}")


def machine_certificate(witness: Mapping[str, Mapping[str, int]]) -> dict[str, Any]:
    """Discharge P21's universal local lemmas and their reachability consequence.

    The certificate is conditional on the reviewed source-to-edge translation.
    No finite welfare or population bound is used in these SMT/CHC queries.
    """
    if witness != EXPECTED_WITNESS:
        raise ValueError("machine certificate only covers the stated P21 witness")

    q, extra = z3.Reals("q extra_potential_gain")
    gain = 1 + 1 / (1 + q)
    next_gain = 1 + 1 / (1 + 2 * q)
    _unsat("adjacent gain lower bound", q > 0, gain <= 1)
    _unsat("adjacent gain upper bound", q > 0, gain >= 2)
    _unsat("strict adjacent concavity", q > 0, gain <= next_gain)
    _positive_sums()
    _signed_sums()
    _potential_gaps()
    # NE: F(m)-F(y)=g(m-1)+extra for y<m; F(m+1)-F(m)=g(m).
    # The extra terms form a finite positive-gain sum, checked above.
    _unsat("ranged NE potential descent", q > 0, extra >= 0, gain + extra <= next_gain)
    # GNEP: h>=5 and b in 1..3 make F(h)-F(b) include g(3)+g(4).
    h, b = z3.Ints("gnep_high gnep_low")
    _unsat("GNEP gain containment", h >= 5, b >= 1, b <= 3, h - b < 2)
    high_to_low = z3.RealVal(10) / 9 + z3.RealVal(18) / 17
    _unsat("GNEP potential descent", q > 0, extra >= 0, high_to_low + extra <= gain)

    m, y, d = z3.Ints("ne_middle ne_low ne_background_weight")
    source_i = 2 * _weight(m) + d
    delta_i = _weight(m + 1) + _weight(y) - 2 * _weight(m)
    background_level = z3.Int("ne_background_level")
    _unsat(
        "ranged NE excludes positive weight",
        y < m,
        y > 0,
        y <= background_level,
        background_level <= m + 1,
        _weight(background_level) > 0,
    )
    _unsat(
        "ranged NE excludes negative weight",
        y < m,
        m + 1 < 5,
        y <= background_level,
        background_level <= m + 1,
        _weight(background_level) < 0,
    )
    # A ranged background D lies in [y,m+1]. If y>0 it has no +1 weights;
    # if m+1<5 it has no -1 weights. Its size is otherwise unrestricted.
    _unsat(
        "ranged NE invariant",
        y < m,
        z3.Implies(y > 0, d <= 0),
        z3.Implies(m + 1 < 5, d >= 0),
        source_i >= 1,
        source_i + delta_i < 1,
    )
    x, low, count = z3.Ints("ed_high ed_low ed_count")
    _unsat("ED invariant", count > 0, low < x, count * _weight(x) >= 1, _weight(low) != 1)
    z = z3.Int("gnep_adjacent_low")
    _unsat(
        "GNEP invariant",
        h >= 5,
        b >= 1,
        b <= 3,
        _weight(b) + _weight(z + 1) - _weight(h) - _weight(z) < 0,
    )
    bag_size = z3.Int("vrc_low_bag_size")
    bag_level = z3.Int("vrc_low_bag_level")
    _unsat(
        "VRC image invariant",
        bag_size >= 0,
        bag_level >= 1,
        bag_level <= 3,
        _weight(z3.IntVal(-1)) + bag_size * _weight(bag_level) != 1,
    )
    _unsat(
        "VRC low bag has zero weight",
        bag_level >= 1,
        bag_level <= 3,
        _weight(bag_level) != 0,
    )
    # DA with singleton A=a>=4 has B=b>a and a nonempty positive C.
    a, da_high, c_weight = z3.Ints("da_singleton da_high da_added_weight")
    _unsat(
        "DA target invariant", a >= 4, da_high > a, c_weight <= 0, _weight(da_high) + c_weight > -1
    )
    c_level = z3.Int("da_positive_level")
    _unsat("DA positive life has nonpositive weight", c_level > 0, _weight(c_level) > 0)
    # The restriction on D is load-bearing: without it, the NE instance
    # m=4,y=1,D=(0) takes I from 1 to 0.
    control = z3.Solver()
    control.add(m == 4, y == 1, d == 1, source_i >= 1, source_i + delta_i < 1)
    if control.check() != z3.sat:
        raise AssertionError("unrestricted-background NE control must be satisfiable")
    _path_closure()
    return {
        "engine": "Z3 exact SMT and Spacer constrained-Horn induction",
        "universal_local_arithmetic_checks": True,
        "arbitrary_finite_positive_sums": True,
        "arbitrary_finite_signed_bag_sums": True,
        "unbounded_ne_and_gnep_potential_gaps": True,
        "all_finite_path_lengths_checked": True,
        "unrestricted_ne_negative_control": True,
        "depends_on_reviewed_source_translation": True,
    }
