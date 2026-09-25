"""Least-preorder models for the both-weakened Q-011 condition set.

On the finite ladder W_-1,...,W_6, and separately on every indexed level W_i
(i in Z), the domain contains every finite multiset, including an isolated empty
population. The relation pulls back to populations of individuated lives by welfare-level
multiset; different finite sets of lives with the same profile are indifferent.
Let G contain all primitive ED, thesis ranged NE, 2003 GNEP, and 2003 VRC
weak edges at WITNESS below.
The ordering is the reflexive/transitive closure of G; thesis Dominance Addition (DA) is
an N-shaped obligation, NOT a reverse edge. The four edge schemas are:

  ED:   x^k -> B                         |B|=k>0, every B level below x
  NE:   (x-1)^2 + D -> x + y + D         y<x-1, D in R(y,x)
  GNEP: h + z + E -> b + (z+1) + E      h>=5, b in {1,2,3}, E arbitrary
  VRC:  h -> B + (-1)                    h>=4, B nonempty in R(1,3)

Every edge preserves population size except VRC, which grows only from a singleton
when its bag is nonempty. With an empty bag VRC is already a singleton ED edge.
On the finite ladder, f(t)=20t-t^2 gives a strictly decreasing potential Phi=sum f
on every size-preserving edge. On all of Z the exact adjacent gains
g(t)=F(t+1)-F(t)=1+1/(1+2^t) are strictly decreasing and between 1 and 2;
g(3)+g(4)>2 bounds every GNEP adjacent gain. Both potentials make G acyclic
and ED strict. They are proof devices, not additive representations of the order.

Write I(P)=#{t<=0}-#{t>=5}. Every VRC output has I=1; ED, GNEP and ranged
NE preserve I>=1 for arbitrary backgrounds and sizes. On all of Z the only
negative-Delta NE cases have middle x-1=0 with y<0 (the source has I>=2),
or middle 4 with y in {1,2,3} (its ranged background has no weight +1).
GNEP has Delta I=1-[z=0]-[z=4]>=0.

For thesis DA, A and B have the same nonzero size and all A lives are below all
B lives; C is a nonempty perfectly equal positive bag. A target B+C is
strictly larger than A, and no edge grows a population of size at least two,
so |A|>=2 is already unreachable. For |A|=1 the source is one life: NE and
GNEP need two source lives, ED keeps the size and lowers the level, and only
VRC grows, from a single life at level >= u = 4. So a source below W_4 cannot
reach a VRC source at all; at or above W_4 the threshold satisfies
x > a >= 4, hence x >= 5, so every B life is at or above W_5 and C is
positive, giving I(B+C) <= -1. Every VRC image has I = 1 and the invariant is
preserved afterwards, so such a target is unreachable. Thus A cannot reach
B+C, proving not(A strictly better than B+C) without assuming completeness.

VRC's low bag B and thesis DA's C can be empty. B empty is a direct ED edge;
C empty would require a same-size path to a strictly higher potential, so DA
still holds. If A=B=empty, DA holds because the empty population is isolated;
strict ED implicitly excludes empty A=B, or it would contradict reflexivity.
The finite ladder's exhaustive level checks and bounded source-instance scan
are diagnostics. research.p21_machine_check verifies the universal gain,
invariant, and abstract path-closure obligations with SMT and CHC induction.
The source translation is reviewed separately; neither singly weakened variant
is claimed.
"""

from __future__ import annotations

import json
from collections import defaultdict, deque
from fractions import Fraction
from itertools import combinations_with_replacement
from typing import Any

from research.lab import RESULTS_DIR, LedgerEntry, record, write_result
from research.ladder import Ladder, Witness, audit, domain, instances_over, validate
from research.p20_contextual_priority import (
    DA,
    ED,
    GNEP,
    NE,
    VRC,
    source_instances,
)
from research.p21_machine_check import machine_certificate
from research.schema import Instance, Pop

LADDER = Ladder(negative=1, positive=6)
LEVELS = LADDER.levels
WITNESS = Witness(
    {
        "non-elitism": {"n": 1},
        "general-non-extreme-priority": {"u": 5, "y": 3, "n": 1},
        "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
    }
)
WITNESS_PARAMS = {"ne_n": 1, "g_u": 5, "g_y": 3, "g_n": 1, "v_n": 1, "v_m": 1}
PRINCIPLES = {"ED": ED, "NE": NE, "GNEP": GNEP, "VRC": VRC, "DA": DA}


def potential(level: int) -> int:
    """An exact integer potential strictly decreasing along every size-preserving edge."""
    return 20 * level - level * level


def invariant_weight(level: int) -> int:
    return int(level <= 0) - int(level >= 5)


def invariant_preserved(base: int, delta: int, support: tuple[int, ...]) -> bool:
    """Check I(source)>=1 => I(target)>=1 for every finite bag on support.

    A background contributes any integer in [0,+infinity), (-infinity,0],
    all integers, or {0}, according to whether its support has levels of
    weight +1 and/or -1. Levels of weight zero do not affect this interval.
    The implication is weakest at its least admissible background weight.
    """
    has_positive = any(invariant_weight(level) > 0 for level in support)
    has_negative = any(invariant_weight(level) < 0 for level in support)
    least = 1 - base if has_negative else max(0, 1 - base)
    if least > 0 and not has_positive:
        return True  # The premise I(source)>=1 is impossible on this support.
    return base + least + delta >= 1


def integer_gain(level: int) -> Fraction:
    """Exact gain F(level + 1) - F(level) on the unbounded integer chain."""
    if level >= 0:
        power = 1 << level
        return Fraction(power + 2, power + 1)
    power = 1 << -level
    return Fraction(2 * power + 1, power + 1)


def integer_potential(level: int) -> Fraction:
    """Anchor F(0) = 0; used only to stress-test finite windows of the proof."""
    if level >= 0:
        return sum((integer_gain(t) for t in range(level)), Fraction())
    return -sum((integer_gain(t) for t in range(level, 0)), Fraction())


def integer_certificate() -> dict[str, Any]:
    """Prove the same closure works for every integer-indexed welfare level.

    Write q = 2**t > 0 and g(t) = F(t+1)-F(t) = 1+1/(1+q).
    Exact real arithmetic below proves 1 < g(t) < 2 and g(t) > g(t+1)
    for every t, since q at t+1 is 2q. Thus F is increasing and strictly
    concave over all integers. Every size-preserving generator lowers Phi:

    * ED lowers every life.
    * For NE let m=x-1 and y<m. F(m)-F(y) >= g(m-1) > g(m)
      = F(m+1)-F(m), independently of its common background.
    * For GNEP h>=5 and b in {1,2,3}, F(h)-F(b) >= g(3)+g(4)>2>g(z)
      for every z and arbitrary common background.
    * VRC with an empty low bag h->(-1) is already an ED edge.

    Cardinality never falls, so these inequalities make the closure
    antisymmetric and its ED comparisons strict. Unbounded descending
    paths are harmless: reachability requires a finite path.

    For I(P)=#{t<=0}-#{t>=5}, ED can start with I>=1 only at x<=0;
    all its target lives then also weigh +1. For ranged NE let m=x-1:
    m<0 gives Delta I=0; m=0,y<0 gives Delta=-1 but source I>=2
    because R(y,1) has no weight -1; 1<=m<=3 gives Delta=w(y)>=0;
    m=4,y<=0 gives Delta=0; m=4,1<=y<=3 gives Delta=-1 but
    R(y,5) has no weight +1, so the source cannot have I>=1;
    m>=5 gives Delta=1+w(y)>=0. GNEP has
    Delta=1-[z=0]-[z=4]>=0. Each VRC image has I=1.

    In thesis DA, |A|=|B|>0 and C nonempty means a larger target:
    a source of size >=2 cannot grow. A singleton below W_4 cannot
    grow either. For a singleton a>=4, the first growing VRC edge
    makes I=1, whereas every DA target has b>a>=4, hence b>=5
    and I<=-1. If C is empty, A and B have the same size and every
    B life is above every A life, so increasing Phi forbids reachability.
    If A=B=empty, the empty population is an isolated reflexive point:
    it is not strictly better than C, including when C is empty. ED's
    strict premise implicitly requires nonempty populations, since its
    literal empty instance would demand empty > empty.

    The finite-window checks below are only diagnostics. The independent
    machine certificate checks the unbounded arithmetic, invariant cases,
    and an abstract closure over all finite path lengths. The connection
    between these schemas and the source text remains a reviewed reading.
    """
    machine = machine_certificate(WITNESS.params)

    high_to_low = integer_gain(3) + integer_gain(4)
    assert high_to_low > 2
    sample = range(-3, 11)
    for m in sample:
        if m + 1 not in sample:
            continue
        for y in sample:
            if y >= m:
                continue
            assert 2 * integer_potential(m) > (integer_potential(m + 1) + integer_potential(y)), (
                m,
                y,
            )
            base = 2 * invariant_weight(m)
            delta = invariant_weight(m + 1) + invariant_weight(y) - base
            assert invariant_preserved(base, delta, tuple(range(y, m + 2))), (m, y)
    for z in sample:
        if z + 1 not in sample:
            continue
        for h in sample:
            if h < 5:
                continue
            for b in (1, 2, 3):
                assert integer_potential(h) + integer_potential(z) > (
                    integer_potential(b) + integer_potential(z + 1)
                ), (h, z, b)
                delta = (
                    invariant_weight(b)
                    + invariant_weight(z + 1)
                    - invariant_weight(h)
                    - invariant_weight(z)
                )
                assert delta >= 0, (h, z, b)
    return {
        "scope": "all finite multisets over every W_i, i in Z, including empty",
        "gain": "1+1/(1+2^t)",
        "gain_bounds_verified_for_every_positive_real_q": True,
        "machine_certificate": machine,
        "high_to_low_gain": str(high_to_low),
        "gnep_adjacent_gain_upper_bound": "2 (strict)",
        "invariant": "#{t<=0}-#{t>=5}",
        "source_empty_population": "isolated reflexive point",
        "sampled_levels_only_a_diagnostic": [min(sample), max(sample)],
    }


def integer_window_diagnostic() -> dict[str, Any]:
    """Independently audit source instances beyond the original finite ladder.

    This bounded graph is a counterexample search, not the all-integer proof.
    The analytic certificate above handles arbitrary level indices and sizes.
    """
    ladder = Ladder(negative=3, positive=10)
    cap = 3
    populations = domain(ladder, cap)
    instances = instances_over(populations, ladder, WITNESS, PRINCIPLES.values())
    scores = {level: integer_potential(level) for level in ladder.levels}
    weights = {level: invariant_weight(level) for level in ladder.levels}
    edges: dict[Pop, set[Pop]] = defaultdict(set)
    counts: dict[str, int] = defaultdict(int)

    def score(pop: Pop) -> Fraction:
        return sum((scores[level] for level in pop), Fraction())

    def weight(pop: Pop) -> int:
        return sum(weights[level] for level in pop)

    for row in instances:
        assert audit(row, ladder, WITNESS), row
        left, right = row.args
        counts[row.principle] += 1
        if row.principle == DA:
            continue
        edges[left].add(right)
        assert len(left) <= len(right)
        if len(left) == len(right):
            assert score(left) > score(right), row
            if len(left) == 1:
                assert right[0] < left[0], row
        else:
            assert row.principle == VRC and len(left) == 1, row
        if row.principle == VRC:
            assert weight(right) == 1, row
        elif weight(left) >= 1:
            assert weight(right) >= 1, row

    assert all(counts[principle] > 0 for principle in PRINCIPLES.values())
    assert all(
        (WITNESS.get("vrc-avoidance")["x"],) in edges[(high,)]
        for high in ladder.levels
        if high >= WITNESS.get("vrc-avoidance")["u"]
    )
    reached: dict[Pop, set[Pop]] = {}

    def reachable(start: Pop) -> set[Pop]:
        if start not in reached:
            seen = {start}
            queue = deque([start])
            while queue:
                for target in edges[queue.popleft()]:
                    if target not in seen:
                        seen.add(target)
                        queue.append(target)
            reached[start] = seen
        return reached[start]

    assert reachable(()) == {()}
    for row in instances:
        left, right = row.args
        if row.principle == ED:
            assert left not in reachable(right), row
        elif row.principle == DA:
            assert right not in reachable(left), row
    return {
        "ladder": [min(ladder.levels), max(ladder.levels)],
        "population_cap": cap,
        "source_instances_audited": len(instances),
        "principle_counts": dict(counts),
        "empty_population_is_isolated": True,
        "not_an_all_integer_proof": True,
    }


def dominance_addition_cases() -> dict[str, Any]:
    """Check the two blocking cases of the thesis DA obligation by level parameters.

    A DA source ``A`` has ``|A| = n >= 1`` and its target ``B+C`` has ``|B| = n`` lives
    at or above the threshold ``W_x`` and ``C`` a nonempty bag at one positive level.

    * ``n >= 2``: no edge grows a population of size at least two, and every edge is
      size-preserving otherwise, so the strictly larger target is unreachable.
    * ``n = 1``: the source is one life. NE and GNEP need at least two source lives, and
      ED keeps the size while strictly lowering the level, so the only possible growth is
      VRC, whose source is a single life at level ``>= u``. Below ``W_u`` nothing grows;
      at or above it, ``x > a >= u = 4`` forces ``x >= 5``, so every ``B`` life weighs
      ``-1`` and ``C`` (positive) weighs at most ``0``, giving ``I(B+C) <= -1`` while
      every VRC image has ``I = 1``.
    """
    floor = WITNESS.get("vrc-avoidance")["u"]
    assert LADDER.has(floor)
    instances = source_instances(3, WITNESS_PARAMS)

    # DA instances are obligations, not edges, and their targets are larger by construction.
    edge_instances = [row for row in instances if row[0] != "DA"]
    growers = [
        (kind, left, right) for kind, left, right, _ in edge_instances if len(right) > len(left)
    ]
    assert growers, "the VRC schema must produce growth"
    assert all(kind == "VRC" and len(left) == 1 for kind, left, _ in growers)
    assert all(left[0] >= floor for _, left, _ in growers)

    # Below W_u a single-life source can only move strictly downward.
    below_floor = [level for level in LEVELS if level < floor]
    for kind, left, right, _ in edge_instances:
        if len(left) != 1 or left[0] not in below_floor:
            continue
        assert len(right) == 1 and right[0] < left[0], (kind, left, right)

    singleton_da = 0
    for a in [level for level in LEVELS if level >= floor]:
        for x in LEVELS:
            if x <= a:
                continue
            for b in [v for v in LEVELS if v >= x]:
                for y in [v for v in LEVELS if v > 0]:
                    # C contributes k >= 1 copies of a positive weight, so one copy bounds it.
                    assert invariant_weight(b) + invariant_weight(y) <= -1, (a, x, b, y)
                    singleton_da += 1
    return {
        "vrc_floor": floor,
        "growth_edges_are_singleton_vrc": True,
        "levels_unreachable_from_vrc": below_floor,
        "da_singleton_target_invariant_upper_bound": -1,
        "da_singleton_parameter_checks": singleton_da,
        "unreachable_singleton_sources": len(below_floor),
    }


def source_empty_cases() -> dict[str, Any]:
    """Discharge empty source parts without dropping their obligations.

    VRC with B empty is h >= (-1), already a one-life ED edge for every
    h >= 4. DA with C empty forbids a same-size upward path by Phi.
    A=B=empty is also a legal DA reading: add the empty population as
    an isolated reflexive point. Its only reachable target is itself,
    so it is not strictly better than any positive C. Strict ED must
    have nonempty A and B: its literal empty instance would demand
    empty > empty and contradict reflexivity.
    """
    floor = WITNESS.get("vrc-avoidance")["u"]
    instances = source_instances(1, WITNESS_PARAMS)
    ed_edges = {(left, right) for kind, left, right, _ in instances if kind == "ED"}
    vrc = WITNESS.get("vrc-avoidance")
    assert vrc["m"] == 1 and invariant_weight(vrc["x"]) == 1
    singleton_paths = {
        high: {"reaches_negative_level": ((high,), (vrc["x"],)) in ed_edges}
        for high in LEVELS
        if high >= floor
    }
    assert singleton_paths and all(
        entry["reaches_negative_level"] for entry in singleton_paths.values()
    )
    assert all(left and right for _, left, right, _ in instances)
    assert all(potential(high) > potential(low) for high in LEVELS for low in LEVELS if high > low)
    return {
        "vrc_empty_bag_is_a_source_instance": True,
        "vrc_empty_bag_images": singleton_paths,
        "vrc_empty_bag_image_invariant": invariant_weight(vrc["x"]),
        "dominance_addition_empty_c_target_is_unreachable": True,
        "empty_population_is_isolated": True,
        "potential_is_strictly_increasing_on_the_ladder": True,
    }


def witness_separation() -> dict[str, Any]:
    """Separate this witness from earlier fixed-witness contradictions.

    P17, P18 and P20's contextual design use the same parameters apart
    from GNEP's floor u=4 rather than 5. Their instance sets strictly
    contain ours; the extra GNEP edge (4,2)->(3,3) closes a weak
    two-cycle with the shared ranged NE edge (3,3)->(4,2). The higher
    floor removes that cycle and permits this proof's descending
    potential; it is not by itself sufficient for a model. P20's
    direct-route grids include u=5 but use different VRC bags and
    GNEP low ranges. The checks below compare the named design at cap
    three and inspect the recorded direct-route VRC edges separately.
    """
    from research.p18_vrc_certificate import CONTROL_WITNESS

    floor = WITNESS.get("general-non-extreme-priority")["u"]
    assert floor == 5
    assert CONTROL_WITNESS.get("general-non-extreme-priority")["u"] == floor - 1
    cap = 3
    ours = {row[:3] for row in source_instances(cap, WITNESS_PARAMS)}
    lower = {row[:3] for row in source_instances(cap, {**WITNESS_PARAMS, "g_u": floor - 1})}
    extra = lower - ours
    assert ours < lower, "a lower GNEP floor must strictly enlarge the instance set"
    assert all(kind == "GNEP" for kind, _, _ in extra)

    lower_only = ("GNEP", (2, 4), (3, 3))
    shared = ("NE", (3, 3), (2, 4))
    assert lower_only in extra and shared in ours
    assert 2 * potential(3) > potential(2) + potential(4)

    recorded = json.loads((RESULTS_DIR / "p20_vrc_dual_routes.json").read_text())
    runs = recorded["result"]["route_a"]["direct"]["evidence"]["witness_grid"]["runs"]
    both_weakened = [
        row
        for row in runs
        if row["ne_form"] == NE
        and row["da_form"] == DA
        and row["closure"]["decision_without_completeness"] == "unsat"
    ]
    low_levels = set(LADDER.range(1, WITNESS.get("vrc-avoidance")["y"]))
    assert both_weakened
    for row in both_weakened:
        vrc_image = row["populations"]["VRC_B_union_C"]
        assert set(row["principles"]) == set(PRINCIPLES.values())
        assert any(level > 0 and level not in low_levels for level in vrc_image), row["label"]

    return {
        "gnep_high_floor": floor,
        "phase_17_18_20_gnep_high_floor": floor - 1,
        "lower_floor_two_cycle": [[2, 4], [3, 3], [2, 4]],
        "instance_set_is_a_strict_subset_at_the_lower_floor": True,
        "extra_instances_are_all_gnep": True,
        "direct_route_unsat_chains_with_vrc_edge_outside_model": len(both_weakened),
        "reference_instance_counts": {"this_witness": len(ours), "lower_floor": len(lower)},
        "population_cap_for_the_comparison": cap,
    }


def certify_all_sizes() -> dict[str, Any]:
    """Exhaust level parameters, not population sizes, for every proof lemma."""
    for family in ("non-elitism", "general-non-extreme-priority", "vrc-avoidance"):
        validate(family, LADDER, WITNESS.get(family))

    adjacent = [(z, z + 1) for z in LEVELS if LADDER.has(z + 1)]
    assert all(potential(above) > potential(below) for below, above in adjacent)
    ed_levels = len(adjacent)
    # A uniform ED source with I>=1 must have level 0: the only lower level is -1.
    assert invariant_weight(0) == invariant_weight(-1) == 1
    assert all(invariant_weight(x) <= 0 for x in LEVELS if x > 0)

    ne_cases = 0
    negative_ne: list[tuple[int, int]] = []
    for middle in LEVELS:
        if not LADDER.has(middle + 1):
            continue
        for y in LEVELS:
            if y >= middle:
                continue
            assert 2 * potential(middle) > potential(middle + 1) + potential(y), (middle, y)
            base = 2 * invariant_weight(middle)
            delta = invariant_weight(middle + 1) + invariant_weight(y) - base
            assert invariant_preserved(base, delta, LADDER.range(y, middle + 1)), (middle, y)
            if delta < 0:
                negative_ne.append((middle, y))
            ne_cases += 1
    assert set(negative_ne) == {(0, -1), (4, 1), (4, 2), (4, 3)}

    gnep_cases = 0
    for high in LEVELS:
        if high < 5:
            continue
        for z, above in adjacent:
            for low in LADDER.range(1, 3):
                assert potential(high) + potential(z) > potential(low) + potential(above)
                base = invariant_weight(high) + invariant_weight(z)
                delta = invariant_weight(low) + invariant_weight(above) - base
                assert invariant_preserved(base, delta, LEVELS), (high, z, low)
                gnep_cases += 1
    assert invariant_weight(-1) == 1
    assert all(invariant_weight(b) == 0 for b in LADDER.range(1, 3))
    return {
        "ed_levels": ed_levels,
        "ne_level_pairs": ne_cases,
        "gnep_level_triples": gnep_cases,
        "negative_ne_delta_cases": negative_ne,
        "dominance_addition": dominance_addition_cases(),
        "source_empty_cases": source_empty_cases(),
        "minimum_high_to_low_potential_drop": potential(5) - potential(3),
        "maximum_adjacent_potential_gain": max(
            potential(above) - potential(below) for below, above in adjacent
        ),
        "vrc_image_invariant": 1,
        "all_size_lemmas_checked": True,
    }


def bounded_diagnostic(cap: int = 6) -> dict[str, Any]:
    """Audit primitive instances and scan their truncated graph for counterexamples."""
    instances = source_instances(cap, WITNESS_PARAMS)
    for kind, left, right, _ in instances:
        assert audit(Instance(PRINCIPLES[kind], (left, right)), LADDER, WITNESS), (
            kind,
            left,
            right,
        )

    edges: dict[Pop, set[Pop]] = defaultdict(set)
    for kind, left, right, _ in instances:
        if kind != "DA":
            edges[left].add(right)

    # VRC with an empty bag is already an ED edge; generators omit that VRC
    # decomposition but must still imply its weak comparison.
    vrc = WITNESS.get("vrc-avoidance")
    empty_vrc = [((high,), (vrc["x"],) * vrc["m"]) for high in LEVELS if high >= vrc["u"]]
    assert empty_vrc and all(right in edges[left] for left, right in empty_vrc)

    reached: dict[Pop, set[Pop]] = {}

    def reachable(start: Pop) -> set[Pop]:
        if start not in reached:
            seen: set[Pop] = {start}
            queue = deque([start])
            while queue:
                for next_pop in edges[queue.popleft()]:
                    if next_pop not in seen:
                        seen.add(next_pop)
                        queue.append(next_pop)
            reached[start] = seen
        return reached[start]

    ed_reversals = 0
    da_forward_paths = 0
    for kind, left, right, _ in instances:
        if kind == "ED" and left in reachable(right):
            ed_reversals += 1
        elif kind == "DA" and right in reachable(left):
            da_forward_paths += 1
    assert ed_reversals == da_forward_paths == 0
    assert reachable(()) == {()}
    assert all(() not in targets for targets in edges.values())

    # C-empty DA targets are unreachable; the isolated empty A=B case
    # cannot be strictly better than any positive C.
    empty_da = 0
    for size in range(1, 4):
        for a in combinations_with_replacement(LEVELS, size):
            above = [level for level in LEVELS if level > max(a)]
            for b in combinations_with_replacement(above, size):
                assert b not in reachable(a), (a, b)
                empty_da += 1
    return {
        "population_cap": cap,
        "audited_instances": len(instances),
        "ed_reversals": ed_reversals,
        "da_forward_paths": da_forward_paths,
        "empty_vrc_bag_obligations": len(empty_vrc),
        "empty_da_c_obligations": empty_da,
        "empty_population_is_isolated": True,
        "empty_da_c_sizes_checked": 3,
        "not_an_all_size_proof": True,
    }


def run() -> dict[str, Any]:
    separation = witness_separation()
    assert (
        separation["instance_set_is_a_strict_subset_at_the_lower_floor"]
        and separation["extra_instances_are_all_gnep"]
    )
    return {
        "scope": "all finite multisets on W_-1..W_6 and, separately, on every indexed W_i (i in Z); one legal witness",
        "finite_ladder_scope": "all finite multisets on W_-1..W_6, including empty",
        "integer_chain_scope": "all finite multisets on W_i for every i in Z, including empty",
        "witness": WITNESS.params,
        "relation": "reflexive/transitive closure of primitive ED, ranged NE, GNEP, VRC edges",
        "thesis_dominance_addition": "not(A strictly better than B+C), not a reverse edge",
        "certificate": certify_all_sizes(),
        "integer_certificate": integer_certificate(),
        "integer_window_diagnostic": integer_window_diagnostic(),
        "bounded_diagnostic": bounded_diagnostic(),
        "witness_separation": separation,
        "source_general_q011": "both-weakened set realized on one source-permitted full indexed integer chain; extension to off-chain welfare levels and singly weakened sets remain open",
    }


def main() -> None:
    data = run()
    path = write_result("p21_least_preorder", data, {})
    record(
        [
            LedgerEntry(
                candidate_id="P21-least-preorder-both-weakened",
                hypothesis="The both-weakened Q-011 conditions admit a preorder for every finite population size, including zero, on one reviewed finite ladder.",
                motivation="Prior bounded satisfiability checks gave no all-size model for the weakest 2003 variant.",
                exact_formal_change="None; use thesis ranged NE and N-shaped thesis DA alongside 2003 ED, GNEP, and VRC.",
                scope=data["finite_ladder_scope"],
                search_method="least reflexive/transitive closure of primitive edges; exact integer descent potential and size-uniform invariant; bounded independent instance audit",
                result="all-size preorder on populations of individuated lives (partial order on welfare profiles) on W_-1..W_6",
                evidence_type="finite level-parameter certificate with mathematical path proof; audited bounded source instances as a diagnostic",
                checked=True,
                minimal="no witness or ladder minimality claim",
                interpretation="The finite ladder illustrates the least-preorder construction; its independent full integer-chain extension is recorded separately. Neither singly weakened variant is resolved.",
                next_experiment="check the two singly weakened Q-011 variants at source-general witnesses",
                result_scope="checked finite-ladder theorem (all finite population sizes including zero)",
                formalization_tier="agent-cross-read 2000 thesis and 2003 source conditions; independently audited finite-ladder instances",
                witness_conditions="NE n=1; GNEP (u,y,n)=(5,3,1); VRC (x,u,v,y,n,m)=(-1,4,6,3,1,1)",
                novelty_status="not claimed; independent publication of this precise finite-ladder model unchecked",
                status="confirmed",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            ),
            LedgerEntry(
                candidate_id="P21-integer-chain-both-weakened",
                hypothesis="The both-weakened Q-011 conditions admit a preorder over all finite populations on the full indexed integer welfare chain.",
                motivation="The quadratic finite-ladder potential cannot grow monotonically in both unbounded directions, but that bound need not constrain the least preorder.",
                exact_formal_change="None; use the same thesis ranged NE and not-worse DA, 2003 ED/GNEP/VRC, and one legal witness over every indexed W_i.",
                scope=data["integer_chain_scope"],
                search_method="least reflexive/transitive closure; exact rational adjacent gains, universal SMT edge and invariant checks, and constrained-Horn induction over arbitrary finite sums and paths",
                result="all-integer-chain preorder for the both-weakened set; the other two weakened variants remain open",
                evidence_type="compositional SMT/CHC certificate conditional on reviewed source schemas; bounded independent source-instance diagnostics",
                checked=True,
                minimal="no witness, welfare-order, or closure minimality claim",
                interpretation="One full unbounded integer chain is a source-permitted welfare domain; no claim is made about every possible richer welfare quasi-order, nor about the original 2003 condition set.",
                next_experiment="seek a primary-literature collision and independent human review of the exact two thesis weakenings",
                result_scope="checked theorem (all finite welfare profiles over W_i for i in Z, including empty; pulled back to populations of individuated lives)",
                formalization_tier="agent-cross-read 2000 thesis and 2003 source clauses; solver-checked universal obligations and abstract path induction",
                witness_conditions="NE n=1; GNEP (u,y,n)=(5,3,1); VRC (x,u,v,y,n,m)=(-1,4,6,3,1,1)",
                novelty_status="not claimed; targeted literature comparison incomplete",
                status="confirmed",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            ),
        ]
    )
    print(
        json.dumps(
            {
                "result": str(path),
                "certificate": data["certificate"],
                "integer_certificate": data["integer_certificate"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
