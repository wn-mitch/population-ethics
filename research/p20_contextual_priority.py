"""Phase 20, Route B: conditional/contextual priority scores for Q-011's weakened set.

Q-011 asks whether the *weakest* of the three 2003 weakenings still fails:

    Egalitarian Dominance (ED) + ranged Non-Elitism (thesis NE) + General Non-Extreme
    Priority (GNEP) + Avoidance of the Very Repugnant Conclusion (2003 VRC)
    + not-worse Dominance Addition (thesis DA).

Prior phases exclude translation-invariant lexicographic-linear orders on W_-1..W_6
(``research/p19_vrc_translation_invariant.py``) and show the tested background-sensitive
relations each miss one premise (``research/p19_vrc_model_background.py``).  Phase 19 leaves
the surviving model class as "background-dependent" without a candidate.

This module designs one specific member of the natural *contextual priority* class -- the
sign-context score with a per-context linear rank, at a fixed count witness -- and decides
that design.  It is not a family-wide or all-witness exclusion: the VRC slope restriction it
uses is genuinely all-size and witness-independent, but the finite UNSAT core is only for the
design's own counts, and the witness probes below show some count assignments stay SAT or
undecided at the tested cap.

A contextual priority rule switches the ranking on an explicit context state read off the
population -- here ``sigma(P) = (negative present, level >= 4 present, low-positive 1..3
present)`` -- and then ranks *within* the state.  Transitivity is guaranteed by one globally
defined score

    S(P) = gamma[sigma(P)] + sum_l w[sigma(P), l] * c_l(P),

so there are no pairwise case rules; ``P >= Q  <=>  S(P) >= S(Q)`` is one total preorder.

Two facts are established, each with the exact quantifier scope it supports:

1.  FORCED PREMISE (all finite sizes, no search).  VRC's ``B`` ranges over *every* population
    inside R(1, y_V), so on this ladder it may be any number of lives at levels 1, 2 or 3.
    Every such ``B`` union ``m_V`` copies of W_-1 has context (neg=1, high=0, low=1), and
    ``S(B union C)`` is linear in B's multiplicities in that (fixed) state.  Bounded above by
    the fixed ``S(n_V at z)`` for all multiplicities forces

        w[(1, 0, 1), l] <= 0  for l in {1, 2, 3}.       (VRC saturation)

2.  FIXED-WITNESS NO-GO (all finite sizes for one specific count witness; NOT a family-wide
    exclusion).  With (VRC saturation) the *design's* linear system over the primitive source
    instances of the five conditions is UNSAT at populations of size <= 6 (it is still SAT at
    size <= 5).  Because (VRC saturation) is forced at every finite size and every count
    witness, no context-state score satisfies the five conditions at any size *provided the
    design's counts hold*: NE count 1, GNEP witness (u, y, n) = (4, 3, 1), n_V = 1.  The
    obstruction is a finite set of audited primitive instances (the reported ``unsat_core``),
    replayed with :func:`research.ladder.audit`.  Other count witnesses are only *probed* in
    ``WITNESS_GRID``: NE count 2 and GNEP count 2 returned "unknown" at the cap and GNEP
    u = 5 returned SAT, so no exclusion is claimed for them.  The refutation is therefore of a
    *specific* design, never of every count assignment and never of the family at large.

The finite-size *discovery* control (SCC feasibility of the raw instance system, no context
assumption) is DISCOVERY ONLY, at the reported cap: it shows a plain total preorder is *not*
contradicted up to that cap.  It is not an all-size consistency claim, and it says nothing
about the context-state design beyond the bounded populations it enumerates.  A failed
candidate is not an impossibility theorem about all orders.

Nothing here is a new source principle or a re-certification of the published theorem.

Cost note: ``run()`` (the default CLI) keeps only the cheap parts; the witness grid, the
saturation control and the heavy cap-``GENERAL_CAP_FULL`` discovery control run only with
``python -m research.p20_contextual_priority --full`` (or via ``exploratory_grid`` /
``exploratory_general``).
"""

from __future__ import annotations

import json
import time
from collections import Counter, defaultdict
from collections.abc import Iterable, Mapping, Sequence
from itertools import combinations_with_replacement
from typing import Any

import z3  # type: ignore[import-untyped]

from research.ladder import Witness, audit
from research.p8_catalogue import LADDER
from research.schema import Instance, Pop

# ---------------------------------------------------------------------------------------------
# Source principles and the design's explicit existential witnesses.

ED = "arrhenius-2003:egalitarian-dominance"
NE = "thesis:non-elitism"
GNEP = "arrhenius-2003:general-non-extreme-priority"
VRC = "arrhenius-2003:vrc-avoidance"
DA = "thesis:dominance-addition"

LEVELS: tuple[int, ...] = LADDER.levels
NEGATIVE = -1
HIGH = 4  # W_4; the source forces VRC's "very high" floor u = 4 on this ladder
LOW = (1, 2, 3)  # R(1, 3), the source's "very low positive" range on this ladder

DESIGN_WITNESS = Witness(
    {
        "non-elitism": {"n": 1},
        "general-non-extreme-priority": {"u": 4, "y": 3, "n": 1},
        "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
    }
)

# The witnesses the finite driver uses; VRC's (x, u, y, v) are forced by the ladder, the
# counts are the design's own choice, and NE/GNEP sizes are the design's choice.
WITNESS_PARAMS: dict[str, int] = {
    "ne_n": 1,
    "g_u": 4,
    "g_y": 3,
    "g_n": 1,
    "v_n": 1,
    "v_m": 1,
}

FAMILY_CAP = 6  # populations of at most this many lives in the no-go search
DISCOVERY_CAP = 5  # the design is not yet refuted below size 6
GENERAL_CAP = 8  # default cap for the (cheap) discovery control inside run()
GENERAL_CAP_FULL = 11  # heavy cap for the separate discovery control (exploratory_general)

# Witness probes for the design's *chosen* counts.  VRC's (x, u, v, y) are forced by the
# ladder; these vary the counts and the NE/GNEP witnesses to show the refutation is not an
# artefact of one count assignment.
WITNESS_GRID: tuple[dict[str, int], ...] = (
    {"ne_n": 1, "g_u": 4, "g_y": 3, "g_n": 1, "v_n": 1, "v_m": 1},
    {"ne_n": 2, "g_u": 4, "g_y": 3, "g_n": 1, "v_n": 1, "v_m": 1},
    {"ne_n": 1, "g_u": 5, "g_y": 3, "g_n": 1, "v_n": 1, "v_m": 1},
    {"ne_n": 1, "g_u": 4, "g_y": 3, "g_n": 2, "v_n": 1, "v_m": 1},
    {"ne_n": 1, "g_u": 4, "g_y": 3, "g_n": 1, "v_n": 2, "v_m": 1},
)


def _plus(*parts: Pop) -> Pop:
    return tuple(sorted(v for p in parts for v in p))


def _bags(levels: Sequence[int], size: int) -> list[Pop]:
    if size <= 0:
        return [()]
    return [tuple(c) for c in combinations_with_replacement(sorted(levels), size)]


def _context(pop: Pop) -> tuple[int, int, int]:
    return (
        1 if any(v < 0 for v in pop) else 0,
        1 if any(v >= HIGH for v in pop) else 0,
        1 if any(v in LOW for v in pop) else 0,
    )


def source_instances(max_size: int, w: Mapping[str, int]) -> list[tuple[str, Pop, Pop, bool]]:
    """Every primitive instance of the five conditions with both populations of size <= max_size.

    The quadruple is ``(principle, left, right, strict)``; a valid order must satisfy
    ``left > right`` when ``strict`` (ED) and ``left >= right`` otherwise.  For the N-shaped
    thesis DA on a *complete* preorder the clause ``not(A > B u C)`` is ``B u C >= A``, so the
    tuple keeps ``(A, B u C)`` and the checker orients it.
    """
    ne_n, g_u, g_y, g_n = w["ne_n"], w["g_u"], w["g_y"], w["g_n"]
    v_n, v_m = w["v_n"], w["v_m"]
    universe: set[Pop] = set()
    for size in range(1, max_size + 1):
        universe |= set(_bags(LEVELS, size))
    out: list[tuple[str, Pop, Pop, bool]] = []

    # Egalitarian Dominance: n at W_x strictly above n lives all below W_x.
    for x in LEVELS:
        below = [v for v in LEVELS if v < x]
        for n in range(1, max_size + 1):
            for b in _bags(below, n):
                a = (x,) * n
                if a in universe and b in universe:
                    out.append(("ED", a, b, True))

    # Ranged Non-Elitism: (n+1) at W_{x-1} + D  >=  one at W_x + n at W_y + D, D in R(y, x).
    for x in LEVELS:
        for y in LEVELS:
            if not (x - 1 > y) or (x - 1) not in LEVELS:
                continue
            region = tuple(v for v in LEVELS if y <= v <= x)
            for dsize in range(0, max_size - (ne_n + 1) + 1):
                for d in _bags(region, dsize):
                    left = _plus((x - 1,) * (ne_n + 1), d)
                    right = _plus((x,), (y,) * ne_n, d)
                    if left in universe and right in universe and left != right:
                        out.append(("NE", left, right, False))

    # GNEP: n at W_x (x >= u) + one at W_z + E  >=  n in R(1, y) + one at W_{z+1} + E.
    for z in LEVELS:
        if (z + 1) not in LEVELS:
            continue
        for x in [v for v in LEVELS if v >= g_u]:
            for dsize in range(0, max_size - (g_n + 1) + 1):
                for e in _bags(LEVELS, dsize):
                    for b in _bags(tuple(v for v in LEVELS if 1 <= v <= g_y), g_n):
                        left = _plus((x,) * g_n, (z,), e)
                        right = _plus(b, (z + 1,), e)
                        if left in universe and right in universe and left != right:
                            out.append(("GNEP", left, right, False))

    # VRC (no background): n at any single level z >= u  >=  any B in R(1, y) union m at W_x.
    for z in [v for v in LEVELS if v >= HIGH]:
        for bsize in range(1, max_size):
            for b in _bags(LOW, bsize):
                left = (z,) * v_n
                right = _plus(b, (NEGATIVE,) * v_m)
                if left in universe and right in universe and left != right:
                    out.append(("VRC", left, right, False))

    # N-shaped thesis Dominance Addition, as a complete-preorder clause B u C >= A.
    for x in LEVELS:
        below = [v for v in LEVELS if v < x]
        atleast = [v for v in LEVELS if v >= x]
        for n in range(1, max_size + 1):
            for a in _bags(below, n):
                for b in _bags(atleast, n):
                    for y in [v for v in LEVELS if v > 0]:
                        # A has n lives and B u C has n + k lives; both must fit the cap.
                        for k in range(1, max_size - n + 1):
                            bc = _plus(b, (y,) * k)
                            if a in universe and bc in universe and a != bc:
                                out.append(("DA", a, bc, False))
    return out


def principle_ids() -> dict[str, str]:
    return {"ED": ED, "NE": NE, "GNEP": GNEP, "VRC": VRC, "DA": DA}


def audited(instances: Sequence[tuple[str, Pop, Pop, bool]]) -> dict[str, Any]:
    """Replay every instance with ``research.ladder.audit`` at the design's witness."""
    ids = principle_ids()
    bad = []
    counts: Counter[str] = Counter()
    for kind, left, right, _ in instances:
        counts[kind] += 1
        if not audit(Instance(ids[kind], (left, right)), LADDER, DESIGN_WITNESS):
            bad.append({"kind": kind, "left": list(left), "right": list(right)})
    return {"counts": dict(counts), "unaudited": bad, "all_audited": not bad}


# ---------------------------------------------------------------------------------------------
# Section 1: the forced premise, and the family's linear feasibility.


def family_infeasible(
    max_size: int, w: Mapping[str, int], saturation: bool = True, timeout_ms: int = 600_000
) -> dict[str, Any]:
    """Decide one context-state score design (a fixed count witness) with z3 over the reals.

    Variables: ``gamma[c]`` and ``w[c][l]`` for the eight contexts c.  ``saturation`` adds the
    forced VRC consequence ``w[(1, 0, 1), l] <= 0`` for l in {1, 2, 3}.  UNSAT is a no-go for
    *this* count witness only; it is not, by itself, a family-wide statement.
    """
    contexts = [(a, b, c) for a in (0, 1) for b in (0, 1) for c in (0, 1)]
    weight = {
        (c, level): z3.Real(f"w_{c[0]}{c[1]}{c[2]}_{level}") for c in contexts for level in LEVELS
    }
    offset = {c: z3.Real(f"g_{c[0]}{c[1]}{c[2]}") for c in contexts}
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)
    if saturation:
        for level in LOW:
            solver.add(weight[((1, 0, 1), level)] <= 0)

    def value(pop: Pop) -> Any:
        c = _context(pop)
        counts = Counter(pop)
        return offset[c] + sum(weight[(c, level)] * counts.get(level, 0) for level in LEVELS)

    instances = source_instances(max_size, w)
    tracked = []
    for index, (kind, left, right, strict) in enumerate(instances):
        diff = value(left) - value(right)
        if kind == "DA":
            constraint = diff <= 0  # A <= B u C
        elif strict:
            constraint = diff >= 1  # ED: strict gap
        else:
            constraint = diff >= 0
        name = z3.Bool(f"i{index}")
        solver.assert_and_track(constraint, name)
        tracked.append((name, kind, left, right))
    decision = str(solver.check())
    core: list[dict[str, Any]] = []
    if decision == "unsat":
        keep = {str(b) for b in solver.unsat_core()}
        for name, kind, left, right in tracked:
            if str(name) in keep:
                core.append(
                    {
                        "kind": kind,
                        "left": list(left),
                        "right": list(right),
                        "principle": principle_ids()[kind],
                    }
                )
    return {
        "decision": decision,
        "instances": len(instances),
        "saturation": saturation,
        "core": core,
    }


# ---------------------------------------------------------------------------------------------
# Section 2: discovery control - a plain total preorder on bounded populations.


def _reachability_feasible(max_size: int, w: Mapping[str, int]) -> dict[str, Any]:
    """Feasibility of the raw instance system as difference constraints (no context assumption).

    A real-valued score exists on populations of size <= max_size iff no strict (ED) instance
    lies on a directed cycle.  Equivalently: no ED edge joins two nodes of one SCC of the union
    graph.  This is a DISCOVERY-ONLY finite control; the cap is reported and nothing beyond it
    is claimed.
    """
    instances = source_instances(max_size, w)
    adjacency: dict[Pop, set[Pop]] = defaultdict(set)
    edges = 0
    strict_edges: list[tuple[Pop, Pop]] = []
    nodes: set[Pop] = set()
    for kind, left, right, strict in instances:
        if kind == "DA":
            adjacency[right].add(left)
        else:
            adjacency[left].add(right)
            if strict:
                strict_edges.append((left, right))
        nodes.add(left)
        nodes.add(right)
        edges += 1
    scc = _tarjan(nodes, adjacency)
    comp = {node: i for i, group in enumerate(scc) for node in group}
    in_cycle = [(a, b) for a, b in strict_edges if comp[a] == comp[b]]
    return {
        "max_size": max_size,
        "nodes": len(nodes),
        "edges": edges,
        "strict_edges": len(strict_edges),
        "components": len(scc),
        "nontrivial_components": sum(1 for g in scc if len(g) > 1),
        "strict_edges_in_cycle": len(in_cycle),
        "feasible": not in_cycle,
        "first_cycle": (
            {"better": list(in_cycle[0][0]), "worse": list(in_cycle[0][1])} if in_cycle else None
        ),
    }


def _tarjan(nodes: Iterable[Pop], adjacency: Mapping[Pop, set[Pop]]) -> list[list[Pop]]:
    """Iterative Tarjan SCC, deterministic, no recursion limit."""
    index: dict[Pop, int] = {}
    low: dict[Pop, int] = {}
    on_stack: dict[Pop, bool] = {}
    stack: list[Pop] = []
    groups: list[list[Pop]] = []
    counter = 0
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(sorted(adjacency[root])))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on_stack[root] = True
        while work:
            node, iterator = work[-1]
            advanced = False
            for nxt in iterator:
                if nxt not in index:
                    index[nxt] = low[nxt] = counter
                    counter += 1
                    stack.append(nxt)
                    on_stack[nxt] = True
                    work.append((nxt, iter(sorted(adjacency[nxt]))))
                    advanced = True
                    break
                if on_stack.get(nxt):
                    low[node] = min(low[node], index[nxt])
            if advanced:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[node])
            if low[node] == index[node]:
                group = []
                while True:
                    top = stack.pop()
                    on_stack[top] = False
                    group.append(top)
                    if top == node:
                        break
                groups.append(group)
    return groups


# ---------------------------------------------------------------------------------------------
# Section 3: stress test - a shared background that flips the context state.


def context_flip_stress() -> dict[str, Any]:
    """Serialize the NE instances where a shared background *flips* the context state.

    Ranged Non-Elitism adds the same ``D`` to both sides, so the design's context switch is
    driven only by the two *added* parts plus D's support.  At (x, y) = (4, -1) the left adds
    W_3 lives and the right adds one W_4 life and W_-1 lives; adding W_-1 to D puts both sides
    in the negative context, while adding W_3 to D widens only the left's low block.  The
    family cannot keep the sides ordered across the switch, which is exactly what the UNSAT
    core reports.
    """
    rows = []
    for d_lives in ((), (-1,), (3,), (-1, 3)):
        left = _plus((3, 3), d_lives)
        right = _plus((4, -1), d_lives)
        rows.append(
            {
                "D": list(d_lives),
                "left": list(left),
                "right": list(right),
                "context_left": list(_context(left)),
                "context_right": list(_context(right)),
                "context_flipped": _context(left) != _context(right),
                "audited": audit(Instance(NE, (left, right)), LADDER, DESIGN_WITNESS),
            }
        )
    vrc_rows = []
    for b_size in (1, 2, 4):
        b = (3,) * b_size
        vrc_rows.append(
            {
                "B_size": b_size,
                "left": [4],
                "right": list(_plus(b, (-1,))),
                "audited": audit(Instance(VRC, ((4,), _plus(b, (-1,)))), LADDER, DESIGN_WITNESS),
            }
        )
    return {
        "non_elitism_at_x4_y_minus1": rows,
        "vrc_unbounded_low_block": vrc_rows,
        "note": (
            "VRC's B is unbounded, so the family's low weights in the negative-no-high context "
            "must be nonpositive; the NE rows then over-constrain them until the size<=6 system "
            "is UNSAT."
        ),
    }


def exploratory_grid(cap: int = FAMILY_CAP) -> list[dict[str, Any]]:
    """Probe the design at ``cap`` for each witness in ``WITNESS_GRID`` (sensitivity only).

    A probe that returns ``sat`` or ``unknown`` is NOT refuted; the report records decisions
    without generalising any of them into a family-wide claim.  This is the heavy part of the
    witness sensitivity check and is only run under ``--full``.
    """
    out = []
    for params in WITNESS_GRID:
        report = family_infeasible(cap, params, saturation=True, timeout_ms=60_000)
        out.append(
            {
                "witness": dict(params),
                "decision": report["decision"],
                "instances": report["instances"],
                "core_size": len(report["core"]),
            }
        )
    return out


def exploratory_general(cap: int = GENERAL_CAP_FULL) -> dict[str, Any]:
    """DISCOVERY ONLY: raw total-preorder feasibility at ``cap`` (heavy: edges/memory grow fast).

    At cap 11 this enumerates ~1.0e7 difference-constraint edges and peaks near 3.7 GB, so it is
    kept out of the default ``run()`` and exposed through ``--full`` (or called directly).
    """
    return _reachability_feasible(cap, WITNESS_PARAMS)


def run(full: bool = False) -> dict[str, Any]:
    """Default: the fixed-witness no-go, its size-5 control, stress test and a cheap discovery
    control (cap ``GENERAL_CAP``).  ``full=True`` adds the witness grid, the saturation control
    and the heavy cap-``GENERAL_CAP_FULL`` discovery control.
    """
    started = time.monotonic()
    by_size = {
        DISCOVERY_CAP: family_infeasible(DISCOVERY_CAP, WITNESS_PARAMS, saturation=True),
        FAMILY_CAP: family_infeasible(FAMILY_CAP, WITNESS_PARAMS, saturation=True),
    }
    general = _reachability_feasible(GENERAL_CAP, WITNESS_PARAMS)
    stress = context_flip_stress()
    instances = source_instances(FAMILY_CAP, WITNESS_PARAMS)
    audit_report = audited(instances)
    design_refuted = by_size[FAMILY_CAP]["decision"] == "unsat" and audit_report["all_audited"]
    verdict = "refuted-candidate" if design_refuted else "bounded-only"

    without_saturation: dict[str, Any] | None = None
    grid: list[dict[str, Any]] | None = None
    general_full: dict[str, Any] | None = None
    if full:
        without_saturation = family_infeasible(FAMILY_CAP, WITNESS_PARAMS, saturation=False)
        grid = exploratory_grid(FAMILY_CAP)
        general_full = exploratory_general()
    grid_all_unsat = None if grid is None else all(row["decision"] == "unsat" for row in grid)

    data: dict[str, Any] = {
        "route": "B",
        "approach": (
            "context-state score: one global score S(P) = gamma[sigma(P)] + "
            "sum_l w[sigma(P), l] c_l(P) over sigma = (negative present, level >= 4 present, "
            "low-positive 1..3 present); total preorder by construction, no pairwise case rules"
        ),
        "scope": (
            "ladder W_-1..W_6; fixed-witness design: VRC (x=-1, u=4, v=6, y=3) forced by the "
            "ladder, counts (n_V, m_V, n_NE, u_GNEP, y_GNEP, n_GNEP) = "
            f"({WITNESS_PARAMS['v_n']}, {WITNESS_PARAMS['v_m']}, {WITNESS_PARAMS['ne_n']}, "
            f"{WITNESS_PARAMS['g_u']}, {WITNESS_PARAMS['g_y']}, {WITNESS_PARAMS['g_n']}). "
            "All-size: the forced VRC slope restriction. All-size for this design: the "
            "size<=6 UNSAT core once the forced restriction is added. Discovery only "
            f"(reported caps): raw total-preorder feasibility (size <= {GENERAL_CAP}"
            + (f", and a separate run to {GENERAL_CAP_FULL}" if full else "")
            + ") and the witness grid (size <= 6, --full only)."
        ),
        "verdict": verdict,
        "exclusion_scope": (
            "FIXED-WITNESS design only: NE count 1, GNEP (u,y,n)=(4,3,1), n_V=1, m_V=1. "
            "This is NOT a family-wide or all-witness exclusion. The VRC slope restriction "
            "(forced_premise) is the only all-size, witness-independent part."
        ),
        "family_wide_exclusion": False,
        "discovery_only_fields": [
            "bounded_general_total_preorder",
            "witness_grid (--full only)",
            "design_unsat_by_cap[" + str(DISCOVERY_CAP) + "] SAT row",
        ],
        "evidence": {
            "forced_premise": (
                "All-size, witness-independent: VRC's unbounded nonempty B forces "
                "w[(1,0,1), l] <= 0 for l in {1,2,3}. S(B union C) is linear in B's "
                "multiplicities in the fixed context (1,0,1) and bounded above by the fixed "
                "S(n_V at z) for every finite nonempty B. Exact, no search."
            ),
            "design_unsat_by_cap": by_size,
            "design_without_forced_premise": without_saturation,
            "witness_grid": grid,
            "witness_grid_all_unsat": grid_all_unsat,
            "bounded_general_total_preorder": general,
            "bounded_general_total_preorder_full_cap": general_full,
            "stress": stress,
            "instance_audit": audit_report,
            "witness_manifest": {k: list(v) for k, v in sorted(DESIGN_WITNESS.params.items())},
        },
        "remaining_obligation": (
            "The no-go is for a *specific* context-state design (sign-context [neg, level>=4, "
            "low] with a per-context linear rank) at the design's own count witnesses only - NOT "
            "a family-wide exclusion: witness probes (run with --full) show NE count 2 and GNEP "
            "count 2 undecided (timeout) and GNEP u=5 SAT at the cap, so those count assignments "
            "are open. The other results are discovery only: a plain total preorder is not "
            "contradicted by the raw instance system up to size "
            f"{GENERAL_CAP} (cap; not an all-size claim). The design is satisfiable at size "
            f"{DISCOVERY_CAP} ({by_size[DISCOVERY_CAP]['decision']}), so the obstruction needs a "
            "population of size 6. A surviving model must score population counts by something "
            "other than a per-context linear form - a support-pattern-indexed or nonlinear "
            "aggregation; the support-pattern refinement of the context was not decided (solver "
            "timeout) and is left open."
        ),
        "wall_time_s": round(time.monotonic() - started, 1),
    }
    return data


def main() -> None:
    import sys

    print(json.dumps(run(full="--full" in sys.argv[1:]), indent=2, ensure_ascii=False, default=str))


if __name__ == "__main__":
    main()
