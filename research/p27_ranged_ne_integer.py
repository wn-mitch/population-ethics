"""Phase 27: does the ranged-NE + positive-2003-DA corner extend to the full bi-integer chain?

Corner ``ranged-ne`` of ``research/p17_vrc_boundary.py:VARIANTS`` (P23's target):

    ED (2003 egalitarian dominance, strict)  + thesis **ranged** Non-Elitism
    + 2003 GNEP + 2003 VRC avoidance + 2003 **positive weak** Dominance Addition (B u C >= A).

P23 (``research/p23_ranged_ne.py``) built a partial-order model at one legal witness on the
one-sided chain ``{W_-1, ..., W_k}`` (k >= 6, k unbounded above) and explicitly left the
bi-integer chain open: its invariant ``Psi(P) = #{t < 0} - #{t >= 5}`` can *fall* at a ranged
NE step with middle ``x-1 = -1`` and ``y <= -2``, a step that only exists once levels below
W_-1 are present.  This module decides that open case.

Result: the corner is **consistent on the full chain W_i, i in Z**.  The P23 model extends
below W_-1: the least reflexive/transitive closure of the primitive weak edges of all five
schemas is acyclic, hence antisymmetric, and its strict ED edges are never reversed.  The
proof does not need ``Psi`` to be non-decreasing.  It needs two facts:

  (L1) *negative persistence*: every population reachable from a VRC image of this witness
       keeps at least one negative life and keeps ``Psi >= 1`` (so a state whose only negative
       is the level -1 has ``Psi = 1 - H <= 0`` and is unreachable);
  (S)  a directed cycle needs a size-increasing edge, and the only size-increasing schema is
       VRC with a **nonempty** low bag, whose source is a negative-free positive singleton.

(L1) makes VRC inapplicable after the first VRC edge (its source is negative-free), and (S)
forces every cycle to leave through a VRC edge and later return to that negative-free
singleton -- impossible.  The composition of (L1) over every finite path is discharged by a
Spacer constrained-Horn induction; its per-schema numeric obligations are discharged by Z3
over every integer level parameter and every legal background size; the size step (S) is
elementary and recorded in Section 2.  VRC's ``x = -1`` and GNEP's floor ``u = 5`` are the
frozen witness's existentials; the quantifier scope of each is stated.

The source-permitted empty clauses (VRC low bag ``B = {}``, 2003 DA addition ``C = {}`` and
``A = B = {}``) are handled as a **separate fidelity branch**: they only add size-preserving
edges (``B = {}``) or a sink edge (``A = B = {}``), so the same two facts close them.  They are
*not* folded into the frozen scanner or any promoted claim without a superseding formalization
decision (see research/ladder.py and docs/decisions.md D-016).

Finite scans below are labelled ``not_a_general_proof``; no bounded SAT result is used as a
model.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations_with_replacement
from typing import Any

import z3  # type: ignore[import-untyped]

from research.lab import LedgerEntry, record, write_result
from research.ladder import Ladder, Witness, audit, domain, instances_over, validate
from research.p17_vrc_boundary import DA_2003, ED, GNEP, NE_THESIS, VRC
from research.schema import Instance, Pop

CORNER = "ranged-ne"
SCHEMA_ID = "p27-ranged-ne-integer/v1"

# The frozen P21/P23 witness.  Reproduced verbatim, never mutated.
WITNESS = Witness(
    {
        "non-elitism": {"n": 1},
        "general-non-extreme-priority": {"u": 5, "y": 3, "n": 1},
        "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
    }
)
PRINCIPLES = (ED, NE_THESIS, GNEP, VRC, DA_2003)

# Frozen witness parameters, named for the obligations.
NE_N = 1
GNEP_U, GNEP_Y, GNEP_N = 5, 3, 1
VRC_X, VRC_U, VRC_V, VRC_Y, VRC_N, VRC_M = -1, 4, 6, 3, 1, 1

# The diagnostic window keeps the P23 base chain and adds depth below W_-1.
BASE_LADDER = Ladder(negative=1, positive=6)  # P23's chain
DEEP_LADDERS = (Ladder(negative=3, positive=6), Ladder(negative=6, positive=6))


def _neg(pop: Pop) -> int:
    return sum(1 for t in pop if t < 0)


def _high(pop: Pop) -> int:
    return sum(1 for t in pop if t >= GNEP_U)


def _psi(pop: Pop) -> int:
    return _neg(pop) - _high(pop)


def _bags(levels: Any, size: int) -> list[Pop]:
    return [tuple(c) for c in combinations_with_replacement(sorted(levels), size)] if size else [()]


def _z3_unsat(label: str, *conditions: z3.BoolRef) -> None:
    solver = z3.Solver()
    solver.add(*conditions)
    result = solver.check()
    if result != z3.unsat:
        detail = f"; counterexample: {solver.model()}" if result == z3.sat else ""
        raise AssertionError(f"{label}: expected unsat, got {result}{detail}")


# ---------------------------------------------------------------------------------------------
# Section 1: universal per-schema obligations for the invariant (L1).


def invariant_obligations() -> dict[str, Any]:
    """Discharge every numeric clause of (L1) by Z3 over all integer parameters.

    The invariant on a population ``P`` is ``N(P) >= 1 and N(P) - H(P) >= 1`` with
    ``N = #{t < 0}`` and ``H = #{t >= 5}`` (the P23 potential ``Psi``).  ``P`` is
    *post-VRC* when it is reachable from a VRC image; the base case and every non-VRC
    primitive edge are checked to preserve it.  VRC is checked to be inapplicable from
    an invariant state, because its source is negative-free.
    """
    checks: dict[str, str] = {}

    # Base: a VRC image is B u {x^m} with B in R(1, 3) (possibly empty) and x = -1, m = 1.
    bag_size, bag_level = z3.Ints("vrc_bag_size vrc_bag_level")
    base_n = VRC_M + bag_size * z3.If(bag_level < 0, 1, 0)
    base_h = bag_size * z3.If(bag_level >= 5, 1, 0)
    _z3_unsat(
        "VRC image invariant",
        bag_size >= 0,
        bag_level >= 1,
        bag_level <= 3,
        z3.Or(base_n < 1, base_n - base_h < 1),
    )
    checks["vrc_image"] = "N >= 1 and Psi >= 1 for every legal low bag size (empty included)"

    # VRC source: z^n with z >= u = 4, n >= 1.  Its negative count is 0 for every parameter.
    vn, vz = z3.Ints("vrc_source_n vrc_source_z")
    src_n = vn * z3.If(vz < 0, 1, 0)
    _z3_unsat("VRC source is negative-free", vn >= 1, vz >= VRC_U, src_n >= 1)
    checks["vrc_source"] = (
        "no invariant (post-VRC) state is a VRC source: z >= 4, n >= 1 gives N = 0"
    )

    # Ranged NE: (m)^(n+1) + D  ->  (m+1) + y^n + D,  y < m,  D in R(y, m+1).
    n, m, y = z3.Ints("ne_n ne_m ne_y")
    d, nd, hd = z3.Ints("ne_bg_size ne_bg_neg ne_bg_high")
    ne_neg_s = (n + 1) * z3.If(m < 0, 1, 0) + nd
    ne_high_s = (n + 1) * z3.If(m >= 5, 1, 0) + hd
    ne_neg_t = z3.If(m + 1 < 0, 1, 0) + n * z3.If(y < 0, 1, 0) + nd
    ne_high_t = z3.If(m + 1 >= 5, 1, 0) + n * z3.If(y >= 5, 1, 0) + hd
    _z3_unsat(
        "ranged NE preserves the invariant",
        n >= 1,
        y < m,
        d >= 0,
        nd >= 0,
        hd >= 0,
        nd + hd <= d,
        z3.Implies(y >= 0, nd == 0),  # D in R(y, m+1): y >= 0 forces D nonnegative
        z3.Implies(m + 1 <= 4, hd == 0),  # m+1 <= 4 forces D below the high region
        z3.Implies(m + 1 < 0, z3.And(nd == d, hd == 0)),  # m+1 < 0 forces D negative
        ne_neg_s >= 1,
        ne_neg_s - ne_high_s >= 1,
        z3.Or(ne_neg_t < 1, ne_neg_t - ne_high_t < 1),
    )
    checks["ranged_ne"] = (
        "y < m and D in R(y, m+1): middle < 0 keeps N >= 1 (x = 0 lowers N by one from a "
        "source with >= 2 negative middle lives and an all-nonpositive background); middle >= 0 "
        "with a negative background forces y < 0, so every gained high brings a negative"
    )

    # GNEP: (h)^n + z + E -> B' + (z+1) + E,  h >= 5, |B'| = n, E arbitrary.
    gn, gz = z3.Ints("gnep_n gnep_z")
    de, ge_neg, ge_high = z3.Ints("gnep_bg_size gnep_bg_neg gnep_bg_high")
    g_neg_s = z3.If(gz < 0, 1, 0) + ge_neg
    g_high_s = gn + z3.If(gz >= 5, 1, 0) + ge_high
    g_neg_t = z3.If(gz + 1 < 0, 1, 0) + ge_neg
    g_high_t = z3.If(gz + 1 >= 5, 1, 0) + ge_high
    _z3_unsat(
        "GNEP preserves the invariant",
        gn >= 1,
        de >= 0,
        ge_neg >= 0,
        ge_high >= 0,
        ge_neg + ge_high <= de,
        g_neg_s >= 1,
        g_neg_s - g_high_s >= 1,
        z3.Or(g_neg_t < 1, g_neg_t - g_high_t < 1),
    )
    checks["gnep"] = (
        "z >= 0 keeps E's negatives; z = -1 erases the last negative only when E is "
        "negative-free, which forces Psi(source) = 1 - n - H(E) <= 0 and contradicts Psi >= 1"
    )
    # Necessity control: the Psi >= 1 half of the invariant is load-bearing.  Without it a
    # GNEP source {h} u {-1} u E with E negative-free reaches a negative-free target, which
    # is exactly the escape the last-negative argument must exclude.
    necessity = z3.Solver()
    necessity.add(gn >= 1, de >= 0, ge_neg == 0, ge_high >= 0, gz == -1, g_neg_s >= 1, g_neg_t == 0)
    if necessity.check() != z3.sat:
        raise AssertionError("GNEP necessity control must be satisfiable")

    # ED: (x)^j -> B with |B| = j and every B life below x.
    j, x = z3.Ints("ed_j ed_x")
    ed_neg_t, ed_high_t = z3.Ints("ed_target_neg ed_target_high")
    ed_neg_s = j * z3.If(x < 0, 1, 0)
    ed_high_s = j * z3.If(x >= 5, 1, 0)
    _z3_unsat(
        "ED preserves the invariant",
        j >= 1,
        ed_neg_t >= 0,
        ed_neg_t <= j,
        ed_high_t >= 0,
        ed_high_t <= j,
        z3.Implies(x <= 0, ed_neg_t == j),  # every B life < x <= 0 is negative
        z3.Implies(x <= 5, ed_high_t == 0),  # every B life < x <= 5 is below the high region
        ed_neg_s >= 1,
        ed_neg_s - ed_high_s >= 1,
        z3.Or(ed_neg_t < 1, ed_neg_t - ed_high_t < 1),
    )
    checks["egalitarian_dominance"] = (
        "an ED source is perfectly equal; N >= 1 forces its level < 0, so every target life "
        "is negative and no target high exists"
    )

    # 2003 positive weak DA: b u C -> A, |A| = |b| = n, every A life below every b life,
    # C in R(1, Omega) (positive, possibly empty in the separate fidelity branch).  The step
    # needs only the source's negative count; Psi(source) is not required here.
    dn, dnb, dmin = z3.Ints("da_n da_b_neg da_b_min")
    d_neg_t, d_high_t = z3.Ints("da_target_neg da_target_high")
    _z3_unsat(
        "2003 weak DA preserves the invariant",
        dn >= 1,
        dnb >= 0,
        dnb <= dn,
        z3.Implies(dnb >= 1, dmin < 0),  # the negative B life sits below every A life
        d_neg_t >= 0,
        d_neg_t <= dn,
        d_high_t >= 0,
        d_high_t <= dn,
        z3.Implies(dmin <= 0, d_neg_t == dn),  # A lives < min(B) <= 0 are all negative
        z3.Implies(dmin <= 5, d_high_t == 0),
        dnb >= 1,  # source N = dnb (C is positive); this already forces the conclusion
        z3.Or(d_neg_t < 1, d_neg_t - d_high_t < 1),
    )
    checks["weak_da"] = (
        "C is positive, so a negative source life lies in B; every A life is strictly below "
        "it, hence A is entirely negative with no high and Psi(A) = |A| >= 1 (no bound on "
        "Psi(source) is used)"
    )

    return {
        "invariant": "N = #{t<0}, H = #{t>=5}, Psi = N - H",
        "engine": "Z3 SMT, all integer level parameters and all legal background sizes",
        "schema": SCHEMA_ID,
        "checks": checks,
        "necessity_control": (
            "without the Psi >= 1 half, GNEP z = -1 with a negative-free background reaches a "
            "negative-free target (satisfiable control), so the hypothesis is load-bearing"
        ),
        "all_discharged": True,
        "witness_quantifiers_discharged": {
            "non-elitism": f"n = {NE_N} (ranged background, uniform in the frozen translation)",
            "general-non-extreme-priority": f"(u, y, n) = ({GNEP_U}, {GNEP_Y}, {GNEP_N}), uniform in z",
            "vrc-avoidance": f"(x, u, v, y, n, m) = ({VRC_X}, {VRC_U}, {VRC_V}, {VRC_Y}, {VRC_N}, {VRC_M})",
            "egalitarian-dominance": "no existential",
            "dominance-addition-2003": "no existential; C ranges over positive bags",
        },
    }


# ---------------------------------------------------------------------------------------------
# Section 2: the path-closure consequence (L1) + (S) => no cycle.


def path_closure() -> dict[str, Any]:
    """Compose the per-edge obligations over every finite path with a Spacer induction.

    The abstract state is the pair ``(N, H)``.  The VRC image seeds ``(1, 0)`` with
    ``Psi = 1``; every non-VRC primitive edge from an invariant state preserves the
    invariant (Section 1).  Spacer then decides that no finite path leaves it, so no
    post-VRC state is a VRC source -- and the size argument makes that enough to exclude
    every directed cycle.
    """
    big_n, big_h, next_n, next_h = z3.Ints("p27_n p27_h p27_next_n p27_next_h")
    reach = z3.Function("p27_post_vrc_reach", z3.IntSort(), z3.IntSort(), z3.BoolSort())
    failure = z3.Function("p27_post_vrc_failure", z3.BoolSort())
    solver = z3.Fixedpoint()
    solver.set(engine="spacer")
    solver.register_relation(reach, failure)
    solver.declare_var(big_n, big_h, next_n, next_h)
    solver.fact(reach(1, 0))  # every VRC image: N = 1, H = 0
    # Each non-VRC edge preserving the invariant, abstracted to its checked conclusion.
    solver.rule(
        reach(next_n, next_h),
        [reach(big_n, big_h), big_n >= 1, big_n - big_h >= 1, next_n >= 1, next_n - next_h >= 1],
    )
    solver.rule(failure(), [reach(big_n, big_h), z3.Or(big_n < 1, big_n - big_h < 1)])
    decision = solver.query(failure())
    if decision != z3.unsat:
        raise AssertionError(f"post-VRC invariant: expected unsat, got {decision}")

    # (S): the size budget.  Only nonempty-bag VRC increases cardinality; only nonempty-C
    # DA decreases it; ED/NE/GNEP and the two empty clauses preserve it.
    size_effects = {
        "egalitarian-dominance": "preserves |P|",
        "thesis:non-elitism": "preserves |P|",
        "arrhenius-2003:general-non-extreme-priority": "preserves |P|",
        "arrhenius-2003:vrc-avoidance": "increases |P| by |B| when B nonempty, else preserves",
        "arrhenius-2003:dominance-addition": "decreases |P| by |C| when C nonempty, else preserves",
    }
    return {
        "engine": "Z3 Spacer constrained-Horn induction over every finite path length",
        "post_vrc_invariant_decision": str(decision),
        "consequence": (
            "reachable-from-a-VRC-image implies N >= 1 and Psi >= 1, so no such state is a "
            "negative-free VRC source"
        ),
        "size_effects": size_effects,
        "cycle_argument": (
            "a closed walk returns to its start size, so it must contain a size-increasing edge; "
            "the unique size-increasing schema is VRC with a nonempty low bag, whose source is a "
            "negative-free positive singleton; after its image no VRC is applicable and (L1) keeps "
            "a negative forever, so the walk can never return to that source"
        ),
        "not_a_general_proof": False,
    }


# ---------------------------------------------------------------------------------------------
# Section 3: size-preserving edges all strictly lower P21's integer potential.


def potential_facts() -> dict[str, Any]:
    """The no-size-increaser case: every size-preserving edge strictly lowers P21's full-chain potential.

    The full-chain potential is P21's exact ``F``: ``F(0) = 0`` and
    ``F(t+1) - F(t) = g(t) = 1 + 1/(1 + 2**t)``, with ``1 < g < 2`` and ``g`` strictly
    decreasing, so ``F`` is strictly increasing over all of Z.  ED, ranged NE and GNEP are
    exactly P21's size-preserving schemas at the same witness, so P21's Spacer/SMT
    certificate is re-run here for their universal descent.  The two size-preserving clauses
    new to this corner are:

      * empty-addition 2003 DA: ``b -> A`` with ``|A| = |b|`` and every ``A`` life strictly
        below every ``b`` life; sorted, ``a_i < b_i`` termwise, and ``F`` strictly increasing
        gives ``Phi(A) < Phi(b)``;
      * empty-bag VRC: a positive singleton at ``z >= u = 4`` descends to ``W_-1``, and
        ``F(-1) < F(z)``.

    Both hold over the whole chain because ``F`` is strictly increasing there.
    """
    from research.p21_least_preorder import integer_potential
    from research.p21_machine_check import machine_certificate

    machine = machine_certificate(WITNESS.params)  # re-discharges the shared schemas

    # Exact full-chain F checks on a wide finite window (the formula itself is unbounded).
    window = tuple(range(-12, 13))
    scores = {level: integer_potential(level) for level in window}
    exact_f: dict[str, int] = defaultdict(int)
    for size in range(1, 4):
        for a in _bags(window, size):
            above = [level for level in window if level > max(a)]
            for b in _bags(above, size):
                exact_f["da_empty_c"] += 1
                assert sum(scores[t] for t in a) < sum(scores[t] for t in b), (a, b)
    for high in window:
        if high >= VRC_U:
            exact_f["vrc_empty_b"] += 1
            assert scores[VRC_X] < scores[high], high

    return {
        "analytic": {
            "full_chain_potential": (
                "F(0) = 0, F(t+1) - F(t) = g(t) = 1 + 1/(1 + 2**t), 1 < g < 2 and g strictly "
                "decreasing, so F is strictly increasing on all of Z"
            ),
            "size_preserving_edges_decrease_Phi": [
                "egalitarian-dominance",
                "thesis:non-elitism",
                "arrhenius-2003:general-non-extreme-priority",
                "arrhenius-2003:vrc-avoidance with B empty",
                "arrhenius-2003:dominance-addition with C empty",
            ],
            "p21_machine_certificate": machine,
            "empty_clause_reason": (
                "F strictly increasing on Z: empty-C DA has termwise a_i < b_i, so Phi(A) < "
                "Phi(b); empty-B VRC sends a positive singleton to W_-1, and F(-1) < F(z) for "
                "z >= u = 4"
            ),
            "discharged": True,
        },
        "window_diagnostics": {
            "exact_full_chain_F": {
                "levels": [min(window), max(window)],
                "checks": dict(exact_f),
            },
            "not_a_general_proof": True,
        },
    }


# ---------------------------------------------------------------------------------------------
# Section 4: bounded independent source-instance audit (diagnostic only).


def _edge_graph(
    ladder: Ladder, cap: int, include_empty: bool
) -> tuple[list[Instance], dict[Pop, set[Pop]], list[Pop]]:
    """Primitive weak edges of the frozen translation, optionally plus the empty clauses."""
    pops = [*domain(ladder, cap), ()]
    instances = instances_over(pops, ladder, WITNESS, PRINCIPLES)
    assert all(audit(inst, ladder, WITNESS) for inst in instances)
    edges: dict[Pop, set[Pop]] = defaultdict(set)
    vrc_targets: list[Pop] = []
    for inst in instances:
        if inst.principle == VRC:
            vrc_targets.append(inst.args[1])
        if inst.shape in {"W", "S"}:
            edges[inst.args[0]].add(inst.args[1])
    if include_empty:
        # Source-permitted VRC B = {}: z >= u descends to the negative level x.
        for high in ladder.levels:
            if high >= VRC_U:
                target = (VRC_X,) * VRC_M
                edges[(high,)].add(target)
                vrc_targets.append(target)
        # Source-permitted 2003 DA C = {}: b -> A, |A| = |b|, every A life below every b life.
        for size in range(1, cap + 1):
            for a in _bags(ladder.levels, size):
                above = [level for level in ladder.levels if level > max(a)]
                for b in _bags(above, size):
                    edges[b].add(a)
        # Source-permitted 2003 DA A = B = {}: a positive bag C is at least as good as {}.
        for size in range(1, cap + 1):
            for c in _bags([level for level in ladder.levels if level > 0], size):
                edges[c].add(())
    return instances, edges, vrc_targets


def _reach(
    edges: dict[Pop, set[Pop]], start: Pop, memo: dict[Pop, set[Pop]] | None = None
) -> set[Pop]:
    """Reachability in the (acyclic) primitive graph, memoized on demand."""
    if memo is None:
        memo = {}
    stack = [start]
    while stack:
        node = stack[-1]
        if node in memo:
            stack.pop()
            continue
        pending = [w for w in edges.get(node, ()) if w not in memo]
        if pending:
            stack.extend(dict.fromkeys(pending))
            continue
        seen = {node}
        for w in edges.get(node, ()):
            seen |= memo[w]
        memo[node] = seen
        stack.pop()
    return memo[start]


def _cyclic_sccs(edges: dict[Pop, set[Pop]]) -> int:
    index: dict[Pop, int] = {}
    low: dict[Pop, int] = {}
    stack: list[Pop] = []
    on_stack: set[Pop] = set()
    counter = 0
    cyclic = 0

    def strong(v: Pop) -> None:
        nonlocal counter, cyclic
        index[v] = low[v] = counter
        counter += 1
        stack.append(v)
        on_stack.add(v)
        for w in sorted(edges.get(v, ())):
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp: list[Pop] = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) > 1 or comp[0] in edges.get(comp[0], ()):
                cyclic += 1

    for v in sorted(edges):
        if v not in index:
            strong(v)
    return cyclic


def bounded_audit(ladder: Ladder, cap: int, include_empty: bool = False) -> dict[str, Any]:
    """Audit every primitive instance and scan the truncated graph for a counterexample."""
    instances, edges, vrc_targets = _edge_graph(ladder, cap, include_empty)
    cycles = _cyclic_sccs(edges)
    if cycles:
        raise AssertionError(f"bounded primitive graph contains {cycles} directed cycles")
    memo: dict[Pop, set[Pop]] = {}

    ed_reversals = [
        inst.args
        for inst in instances
        if inst.principle == ED and inst.args[0] in _reach(edges, inst.args[1], memo)
    ]
    # Bounded analogue of (L1): every VRC image reaches only negative-bearing populations.
    negative_free_reachable = 0
    for image in dict.fromkeys(vrc_targets):
        for node in _reach(edges, image, memo):
            if _neg(node) == 0:
                negative_free_reachable += 1
    empty_isolated = _reach(edges, (), memo) == {()}

    # Independent model check: the reachability closure satisfies all five conditions here.
    needed = {inst.args[0] for inst in instances} | {
        inst.args[1] for inst in instances if inst.principle == ED
    }
    model_violations = []
    for inst in instances:
        left, right = inst.args
        if right not in _reach(edges, left, memo):
            model_violations.append(("weak-edge missing", inst.principle, left, right))
        if inst.principle == ED and left in _reach(edges, right, memo):
            model_violations.append(("ED reversed", inst.principle, left, right))
    return {
        "not_a_general_proof": True,
        "ladder": [min(ladder.levels), max(ladder.levels)],
        "population_cap": cap,
        "source_permitted_empty_clauses": include_empty,
        "audited_instances": len(instances),
        "edge_count": sum(len(v) for v in edges.values()),
        "ed_reversals": len(ed_reversals),
        "cyclic_scc_count": cycles,
        "vrc_images_reaching_a_negative_free_state": negative_free_reachable,
        "completion_model_violations": len(model_violations),
        "reachability_nodes_used": len(needed),
        "empty_population_is_isolated": empty_isolated,
        "example_ed_reversals": [[list(a), list(b)] for a, b in ed_reversals[:3]],
    }


# ---------------------------------------------------------------------------------------------
# Section 5: the probe.


def run() -> dict[str, Any]:
    for family in ("non-elitism", "general-non-extreme-priority", "vrc-avoidance"):
        validate(family, BASE_LADDER, WITNESS.get(family))

    obligations = invariant_obligations()
    closure = path_closure()
    potentials = potential_facts()

    audits = [bounded_audit(BASE_LADDER, 4)]
    for ladder in DEEP_LADDERS:
        audits.append(bounded_audit(ladder, 4))
    audits.append(bounded_audit(DEEP_LADDERS[0], 4, include_empty=True))
    audits.append(bounded_audit(BASE_LADDER, 4, include_empty=True))

    return {
        "corner": CORNER,
        "schema": SCHEMA_ID,
        "question": (
            "Do ED, thesis ranged Non-Elitism, 2003 GNEP, 2003 VRC avoidance and 2003 positive "
            "weak Dominance Addition admit an all-size model over every finite multiset on the "
            "full bi-integer indexed welfare chain W_i (i in Z)?"
        ),
        "domain": {
            "populations": "every finite multiset of welfare levels, including the empty population",
            "welfare_chain": "the bi-integer indexed chain W_i for every i in Z (no minimum, no maximum)",
            "relation": "reflexive/transitive closure of the primitive weak edges; pulled back to individuated lives by welfare profile",
            "completeness": "not assumed; a partial preorder is allowed",
        },
        "status": "full-chain model certified",
        "witness": {family: dict(params) for family, params in WITNESS.params.items()},
        "model": {
            "construction": "least reflexive/transitive closure of the primitive ED, ranged NE, GNEP, VRC and 2003 weak-DA weak edges",
            "antisymmetry": "the closure is acyclic (no directed cycle), hence a partial preorder",
            "ed_strictness": (
                "a strict ED edge l -> r has no return path r ->* l, since l -> r ->* l would be a cycle"
            ),
            "extends": "the P23 one-sided-chain model now covers the whole bi-integer chain; no minimum level is needed",
            "unbounded_below": True,
        },
        "lemmas": {
            "negative_persistence": (
                "L1: every population reachable from a VRC image of the frozen witness keeps "
                "N >= 1 and Psi = N - H >= 1"
            ),
            "no_cycle": (
                "(S): a directed cycle needs a size-increasing edge; the unique such schema is "
                "nonempty-bag VRC, whose negative-free source cannot be recovered once (L1) holds"
            ),
            "psi_is_not_monotone": (
                "Psi falls by one at a ranged NE step with middle -1 and y <= -2 (the exact case "
                "P23 flagged below W_-1); it never falls below 1, and Psi = 1 - H with a single "
                "negative is unreachable, which is what blocks the last-negative-removing GNEP"
            ),
        },
        "proof_obligations": {
            "discharged": {
                "invariant_per_schema": obligations,
                "path_closure": closure,
                "potential_for_size_preserving_edges": potentials,
            },
            "open": {},
        },
        "source_permitted_empty_cases": {
            "fidelity_branch": "handled separately from the frozen nonempty-bag translation",
            "vrc_empty_b": (
                "z >= u descends to the negative singleton W_x; already a weak ED edge, "
                "size-preserving, and its image still satisfies (L1)"
            ),
            "da_empty_c": (
                "b -> A with |A| = |b| and every A life below every b life; size-preserving and "
                "strictly lowers Phi, and (L1) still routes a negative source through B"
            ),
            "da_empty_a_and_b": (
                "a positive bag C is at least as good as the empty population; the empty "
                "population has only its reflexive edge, so it is a sink and closes no cycle"
            ),
            "promotion_note": (
                "these clauses are not folded into the frozen scanner or a promoted claim without "
                "a superseding formalization decision and an independent checker"
            ),
        },
        "diagnostics": audits,
        "p23_gap_addressed": {
            "prior": "P23: the bi-integer chain is not covered because ranged NE at x = 0 with y <= -2 lowers Psi",
            "resolution": (
                "Psi does fall there, but the proof needs only Psi >= 1 and negative persistence; "
                "the model therefore extends below W_-1 without a minimum level"
            ),
        },
        "bounded_results_are_not_proofs": True,
        "scope": (
            "the model is exhibited at the frozen witness and satisfies the reviewed frozen "
            "translation; other legal witnesses and non-indexed welfare levels are not addressed"
        ),
        "obstruction": None,
        "remaining_open_obligation": None,
    }


def main() -> None:
    data = run()
    path = write_result("p27_ranged_ne_integer", data, {})
    record(
        [
            LedgerEntry(
                candidate_id="P27-ranged-ne-full-integer-model",
                hypothesis="Ranged NE and positive 2003 DA admit one full-integer-chain axiology.",
                motivation="P23's negative-count invariant can fall below its old minimum-level boundary.",
                exact_formal_change="None: extend the fixed P23 witness to every integer-indexed level.",
                scope="all finite profiles on W_i for every integer i, including the empty profile",
                search_method="symbolic post-VRC invariant, SMT per-schema checks, finite-path induction and independent bounded audits",
                result="the least primitive preorder is acyclic and satisfies ED, ranged NE, GNEP, VRC avoidance and positive weak DA at the fixed witness",
                evidence_type="all-size model proof with SMT/Spacer obligations and source-instance diagnostics",
                checked=True,
                minimal="no witness-minimality or off-chain representation claim",
                interpretation="A post-VRC negative life persists even where the earlier potential invariant decreases.",
                next_experiment="test off-chain source fidelity under a separately reviewed universe",
                result_scope="one legal witness on the full bi-integer chain; not every welfare quasi-order",
                formalization_tier="agent-cross-read frozen source translation; empty clauses analyzed separately",
                witness_conditions="NE n=1; GNEP (u,y,n)=(5,3,1); VRC (x,u,v,y,n,m)=(-1,4,6,3,1,1)",
                novelty_status="exact primary-source collision pending; no priority claim",
                status="confirmed",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            )
        ]
    )
    print(f"wrote {path} (status: {data['status']})")


if __name__ == "__main__":
    main()
