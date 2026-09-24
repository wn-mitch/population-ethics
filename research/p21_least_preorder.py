"""An all-size, finite-ladder model of Q-011's both-weakened conditions.

The domain consists of every nonempty finite multiset over W_-1,...,W_6. Let G contain
all primitive ED, thesis ranged NE, 2003 GNEP, and 2003 VRC weak edges at WITNESS below.
The ordering is the reflexive/transitive closure of G; thesis Dominance Addition (DA) is
an N-shaped obligation, NOT a reverse edge. The four edge schemas are:

  ED:   x^k -> B                         |B|=k>0, every B level below x
  NE:   (x-1)^2 + D -> x + y + D         y<x-1, D in R(y,x)
  GNEP: h + z + E -> b + (z+1) + E      h>=5, b in {1,2,3}, E arbitrary
  VRC:  h -> B + (-1)                    h>=4, B nonempty in R(1,3)

All edges preserve the population size except VRC, which increases it from a single
life when its bag is nonempty and is size-preserving when the bag is empty; the
empty-bag case is covered by the potential and by the single-life ED chain below.
For f(t)=20t-t^2, Phi(P)=sum(f(t) for t in P) strictly decreases on every
size-preserving edge: f increases throughout the ladder; strict concavity handles NE;
f(5)-f(3)=24 exceeds max_z(f(z+1)-f(z))=21 for GNEP. Hence G has no cycle,
and ED cannot be reversed in the closure. Phi is only a proof potential, NOT an
additive representation of the ordering.

Write I(P)=#{t<=0}-#{t>=5}. Every VRC output has I=1, and ED/NE/GNEP preserve
I>=1 on populations of size >=2. The only NE cases with negative Delta I are
(x-1,y)=(0,-1), where the source has I>=2 and Delta=-1, and (4,1),(4,2),
(4,3), where the ranged background cannot contain a nonpositive life, so its
source cannot have I>=1. GNEP has Delta I=1-[z=0]-[z=4]>=0.

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

The readings leave VRC's bag B and thesis DA's C unconstrained in size, so the
empty sub-populations are source instances as well. They are discharged below
rather than dropped: with B empty the VRC instance is size-preserving and holds
along the single-life ED chain down to W_-1, and with C empty the DA target has
A's size with every level above every level of A, so the strictly increasing
potential puts it out of reach.

The exhaustive level-parameter checks below certify the local inequalities and
background invariant for arbitrary population sizes. The bounded graph scan is
an independent source-instance diagnostic, not the all-size proof. No claim is
made about welfare levels outside this ladder or the other Q-011 variants.
"""

from __future__ import annotations

import json
from collections import defaultdict, deque
from itertools import combinations_with_replacement
from typing import Any

from research.lab import LedgerEntry, record, write_result
from research.ladder import Ladder, Witness, audit, validate
from research.p20_contextual_priority import (
    DA,
    ED,
    GNEP,
    NE,
    VRC,
    source_instances,
)
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
    """Cover the two empty sub-populations the source readings leave open.

    ``corpus/readings.toml`` leaves VRC's ``B`` size unconstrained (``N(B)`` unrestricted), so
    ``B = empty`` is a source instance: the single life at ``A``'s level must satisfy
    ``(h) >= (-1)^m``. The closure carries it along the single-life Egalitarian Dominance chain
    ``h -> h-1 -> ... -> W_-1``, every link of which is an ED instance, and the same chain shows
    the potential decreases there too. Note that a VRC instance with ``B`` empty is
    size-preserving, so the potential, not size, is what rules out cycles through it.

    The thesis Dominance Addition reading leaves ``N(C)`` unconstrained, so ``C = empty`` is a
    source instance whose target ``B`` has the same size as ``A`` with every level above every
    level of ``A``. The potential is strictly increasing, so ``Phi(B) > Phi(A)`` termwise; a
    same-size path cannot grow and return to that size, so ``B`` is unreachable from ``A``.
    """
    floor = WITNESS.get("vrc-avoidance")["u"]
    instances = source_instances(1, WITNESS_PARAMS)
    ed_steps = {(left[0], right[0]) for kind, left, right, _ in instances if kind == "ED"}
    ladder_steps = {(above, above - 1) for above in LEVELS if LADDER.has(above - 1)}
    assert ladder_steps and ladder_steps <= ed_steps, ladder_steps - ed_steps
    assert all(
        potential(high) > potential(low)
        for high, low in ((a, b) for a in LEVELS for b in LEVELS if a > b)
    )

    singleton_paths = {}
    for high in [level for level in LEVELS if level >= floor]:
        walk = list(range(high, min(LEVELS) - 1, -1))
        assert all((above, above - 1) in ed_steps for above in walk[:-1]), high
        singleton_paths[high] = {"reaches_negative_level": walk[-1] == min(LEVELS)}

    # The VRC image with an empty bag is m copies of the negative level: nonempty for m >= 1.
    vrc = WITNESS.get("vrc-avoidance")
    assert vrc["m"] >= 1 and invariant_weight(vrc["x"]) == 1
    return {
        "vrc_empty_bag_is_a_source_instance": True,
        "vrc_empty_bag_images": singleton_paths,
        "vrc_empty_bag_image_invariant": vrc["m"] * invariant_weight(vrc["x"]),
        "dominance_addition_empty_c_target_is_unreachable": True,
        "potential_is_strictly_increasing_on_the_ladder": True,
    }


def witness_separation() -> dict[str, Any]:
    """Compare this witness with the repo's other fixed-witness Q-011 constructions.

    Phases 17, 18 and phase 20's contextual design all fix GNEP's high floor at ``u = 4``,
    one level below this model's ``u = 5``. With every other parameter equal, their
    five-condition instance sets over the same ladder are strict supersets of this model's,
    and their fixed-witness UNSAT results are statements about that larger set. A fixed
    witness at a *lower* floor admits strictly more GNEP sources, and ``W_4`` carries
    invariant weight 0 while ``W_5`` carries ``-1``, so raising the floor is exactly what
    lets the invariant and the descent potential survive. GNEP's floor is an existential
    witness the source leaves free, so both witnesses are legal; the recursion would have
    to be an UNSAT subset of this model's instance set to conflict with it, which cannot
    exist once the closure below satisfies every one of those instances.
    """
    from research.p18_vrc_certificate import CONTROL_WITNESS

    floor = WITNESS.get("general-non-extreme-priority")["u"]
    assert floor >= 5, floor
    assert CONTROL_WITNESS.get("general-non-extreme-priority")["u"] == floor - 1
    assert invariant_weight(floor - 1) == 0 and invariant_weight(floor) == -1

    cap = 3
    ours = {row[:3] for row in source_instances(cap, WITNESS_PARAMS)}
    lower = {row[:3] for row in source_instances(cap, {**WITNESS_PARAMS, "g_u": floor - 1})}
    extra = lower - ours
    assert ours < lower, "a lower GNEP floor must strictly enlarge the instance set"
    assert all(kind == "GNEP" for kind, _, _ in extra)
    return {
        "gnep_high_floor": floor,
        "phase_17_18_20_gnep_high_floor": floor - 1,
        "weight_of_the_lower_floor": invariant_weight(floor - 1),
        "weight_of_this_floor": invariant_weight(floor),
        "instance_set_is_a_strict_subset_at_the_lower_floor": True,
        "extra_instances_are_all_gnep": True,
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

    # Source-legal instances the generators drop, kept here as required weak pairs: VRC with an
    # empty bag (size-preserving, potential-decreasing) and DA with C empty (the target keeps A's
    # size with every level above every level of A).
    vrc = WITNESS.get("vrc-avoidance")
    empty_vrc = [
        ((high,), (vrc["x"],) * vrc["m"])
        for high in LEVELS
        if high >= vrc["u"] and vrc["m"] * potential(vrc["x"]) < potential(high)
    ]
    assert len(empty_vrc) == len([high for high in LEVELS if high >= vrc["u"]])
    for left, right in empty_vrc:
        edges[left].add(right)

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

    # Obligations of the two dropped families, checked against the same closure.
    assert all(right in reachable(left) for left, right in empty_vrc)
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
        "scope": "all nonempty finite populations over W_-1..W_6; one legal witness",
        "witness": WITNESS.params,
        "relation": "reflexive/transitive closure of primitive ED, ranged NE, GNEP, VRC edges",
        "thesis_dominance_addition": "not(A strictly better than B+C), not a reverse edge",
        "certificate": certify_all_sizes(),
        "bounded_diagnostic": bounded_diagnostic(),
        "witness_separation": separation,
        "source_general_q011": "open; no claim about levels outside W_-1..W_6",
    }


def main() -> None:
    data = run()
    path = write_result("p21_least_preorder", data, {})
    record(
        [
            LedgerEntry(
                candidate_id="P21-least-preorder-both-weakened",
                hypothesis="The both-weakened Q-011 conditions admit a partial order for every finite population size on one reviewed finite ladder.",
                motivation="Prior bounded satisfiability checks gave no all-size model for the weakest 2003 variant.",
                exact_formal_change="None; use thesis ranged NE and N-shaped thesis DA alongside 2003 ED, GNEP, and VRC.",
                scope=data["scope"],
                search_method="least reflexive/transitive closure of primitive edges; exact integer descent potential and size-uniform invariant; bounded independent instance audit",
                result="all-size partial-order model for the both-weakened set on W_-1..W_6; unrestricted welfare-level case open",
                evidence_type="finite level-parameter certificate with mathematical path proof; audited bounded source instances as a diagnostic",
                checked=True,
                minimal="no witness or ladder minimality claim",
                interpretation="This closes the population-size dimension for one finite ladder and legal witness, but neither other weakened variant nor source-general Q-011.",
                next_experiment="test whether a level-unbounded construction can preserve the DA invariant under source-order existential witnesses",
                result_scope="checked finite-ladder theorem (all nonempty finite population sizes)",
                formalization_tier="agent-cross-read 2000 thesis and 2003 source conditions; independently audited finite-ladder instances",
                witness_conditions="NE n=1; GNEP (u,y,n)=(5,3,1); VRC (x,u,v,y,n,m)=(-1,4,6,3,1,1)",
                novelty_status="not claimed; independent publication of this precise finite-ladder model unchecked",
                status="confirmed",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            )
        ]
    )
    print(json.dumps({"result": str(path), "certificate": data["certificate"]}, indent=2))


if __name__ == "__main__":
    main()
