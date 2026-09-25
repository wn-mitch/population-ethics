"""Phase 23 corner probe: ranged thesis Non-Elitism + 2003 weak Dominance Addition.

This is the ``ranged-ne`` corner of ``research/p17_vrc_boundary.py:VARIANTS``: the
2003 condition set ED, GNEP, VRC with **thesis ranged** Non-Elitism and **2003**
Dominance Addition taken as its positive weak edge (``B u C >= A``, shape W), at
P21's exact witness.

Result: the corner is **consistent**. The reflexive/transitive closure of all
five primitive edge schemas is acyclic on every finite multiset over W_-1..W_6.
It also includes positive-bag-to-empty DA edges if A=B=empty is source-legal.
This does not follow from P21's both-weakened certificate: its quadratic
potential fails on VRC edges whose low bag B has at least two lives. Its
invariant I = #{t<=0} - #{t>=5} cannot exclude every 2003 weak-DA source:
the legal DA source (0,1) itself has I=1. Instead acyclicity uses the invariant

    Psi(P) = #{t < 0} - #{t >= 5}   (negative lives minus high lives)

which is >= 1 at every VRC image and non-decreasing along every edge whose source
still contains a negative life.  A 2003 weak-DA source is nonnegative by definition
(its "high" part sits above A and its addition C is strictly positive), so no DA
edge can follow a VRC edge, while VRC is the only size-increasing schema and DA
the only size-decreasing one. A directed cycle needs one of each, so none exists.

The argument holds for any convex chain with minimum W_-1 and all W_1..W_6,
including a one-sided infinite upper chain. Its size-preserving descent uses
P21's *integer* potential, not the quadratic finite-ladder potential. It does
not cover chains extending below W_-1: ranged NE may then lower Psi.

Nothing here mutates P21.  The bounded scans below are diagnostics only and are
labelled ``not_a_general_proof``.
"""

from __future__ import annotations

from collections import defaultdict, deque
from itertools import combinations_with_replacement
from typing import Any

import z3  # type: ignore[import-untyped]

from research.ladder import Ladder, Witness, audit, domain, instances_over, validate
from research.p17_vrc_boundary import DA_2003, ED, GNEP, NE_THESIS, VRC
from research.p18_vrc_certificate import verify_edge
from research.schema import Instance, Pop

CORNER = "ranged-ne"

# P21's frozen witness and ladder; reproduced verbatim, never mutated.
LADDER = Ladder(negative=1, positive=6)
WITNESS = Witness(
    {
        "non-elitism": {"n": 1},
        "general-non-extreme-priority": {"u": 5, "y": 3, "n": 1},
        "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
    }
)
PRINCIPLES = (ED, NE_THESIS, GNEP, VRC, DA_2003)

# Bounded diagnostics.  cap 5 already touches ~42k instances; keep the default cheap.
SCAN_CAP = 4
HIGH = 5  # GNEP's floor u = 5 is where H(P) starts counting.


def _neg(pop: Pop) -> int:
    return sum(1 for t in pop if t < 0)


def _high(pop: Pop) -> int:
    return sum(1 for t in pop if t >= HIGH)


def _psi(pop: Pop) -> int:
    return _neg(pop) - _high(pop)


# ---------------------------------------------------------------------------------------------
# Section 1: the symbolic acyclicity certificate (the model proof).


def _ne_psi_delta(x: int, n: int) -> int:
    """Psi(target) - Psi(source) for ranged NE with a negative life present.

    A negative life can only sit in the shared background D, which forces -1 in
    R(y, x), hence y = -1 on a chain whose minimum is -1.  The added parts are
    (x-1)^(n+1) -> x + (-1)^n: the negative count rises by n and the high count by
    [x >= 5] - (n+1)[x-1 >= 5].
    """
    return n - (int(x >= HIGH) - (n + 1) * int(x - 1 >= HIGH))


def _gnep_psi_delta(z: int) -> int:
    """Psi(target) - Psi(source) for GNEP with a negative life present.

    If z = -1 the one negative life becomes W_0 and the consumed high life
    offsets its loss. Otherwise the negative life is in the background E;
    the source has 1 + [z >= 5] high lives and the target has [z+1 >= 5].
    """
    if z == -1:
        return 0
    return 1 + int(z >= HIGH) - int(z + 1 >= HIGH)


def acyclicity_certificate() -> dict[str, Any]:
    """Prove the combined edge graph is acyclic, exhaustively over level parameters.

    P21's integer potential strictly decreases along size-preserving ED, NE,
    GNEP, empty-bag VRC and empty-addition DA edges. Only nonempty-bag VRC
    increases cardinality; only nonempty-addition DA decreases it. Every cycle
    containing either thus needs both. A VRC image has Psi=1, and Psi cannot
    decrease while a negative life remains. DA sources contain no negatives on
    this welfare chain, so DA cannot follow VRC. If A=B=empty is permitted,
    DA sends an all-positive C to the empty population; the empty population
    is a sink and cannot close a cycle.
    """
    # Every VRC image is B u (-1), even if B is empty; there is exactly one
    # negative life and no life at or above 5, independently of the source.
    vrc = WITNESS.get("vrc-avoidance")
    for size in range(4):
        for b in combinations_with_replacement(LADDER.range(1, vrc["y"]), size):
            image = tuple(sorted((*b, vrc["x"])))
            assert _neg(image) == 1 and _high(image) == 0 and _psi(image) == 1, (b, image)

    # Every 2003 weak-DA source B u C is nonnegative on a chain starting
    # at W_-1: B sits above A and C is positive (even when either is empty).
    da_instances = instances_over(domain(LADDER, SCAN_CAP), LADDER, WITNESS, (DA_2003,))
    assert all(_neg(inst.args[0]) == 0 for inst in da_instances)

    # Ranged NE with a negative life present: y = -1 forced; Psi never falls.
    ne_min = None
    for x in LADDER.levels:
        if not LADDER.has(x - 1):
            continue
        for y in LADDER.levels:
            if y >= x - 1:
                continue
            if y != -1:
                continue  # a negative life forces y = -1; the others are irrelevant
            for n in range(1, 6):
                d = _ne_psi_delta(x, n)
                assert d >= 0, (x, n, d)
                ne_min = d if ne_min is None else min(ne_min, d)
    assert ne_min == 0  # attained at x = 5, n = 1

    # GNEP with a negative life present.
    gnep_min = None
    for z in LADDER.levels:
        if not LADDER.has(z + 1):
            continue
        d = _gnep_psi_delta(z)
        assert d >= 0, (z, d)
        gnep_min = d if gnep_min is None else min(gnep_min, d)
    assert gnep_min == 0  # attained at z = -1 and z = 4

    # ED cannot start at a negative level: W_-1 has no lower relatum on
    # this chain. VRC starts at a positive singleton, and DA starts at a
    # nonnegative source. The possible empty target is a sink.
    # Quantify over every upper-chain level and every legal NE count; the
    # finite LADDER loops above are diagnostics, not the unbounded proof.
    x, n, z = z3.Ints("x n z")
    ne_delta = n - z3.If(x >= HIGH, 1, 0) + (n + 1) * z3.If(x - 1 >= HIGH, 1, 0)
    gnep_delta = z3.If(z == -1, 0, 1 + z3.If(z >= HIGH, 1, 0) - z3.If(z + 1 >= HIGH, 1, 0))
    ne_solver = z3.Solver()
    ne_solver.add(x >= 1, n >= 1, ne_delta < 0)
    gnep_solver = z3.Solver()
    gnep_solver.add(z >= -1, gnep_delta < 0)
    assert ne_solver.check() == z3.unsat
    assert gnep_solver.check() == z3.unsat
    return {
        "invariant": "Psi(P) = #{t<0} - #{t>=5}",
        "vrc_image_psi": 1,
        "da_source_nonnegative": True,
        "ne_min_delta_psi": ne_min,
        "unbounded_ne_delta_counterexample": "unsat for all x>=1, n>=1",
        "unbounded_gnep_delta_counterexample": "unsat for all z>=-1",
        "empty_source_clauses": "DA with A=B=empty sends positive C to empty; empty is a sink. VRC with B=empty and DA with C=empty are size-preserving and decrease P21's integer potential.",
        "gnep_min_delta_psi": gnep_min,
        "conclusion": (
            "Psi >= 1 after any VRC edge and is non-decreasing while a negative life "
            "remains, so the negative-live count never returns to zero; no 2003 weak-DA "
            "edge can follow a VRC edge, and no directed cycle can contain either"
        ),
        "domain": "every convex subchain {W_-1, ..., W_k} with k >= 6",
        "not_covering": "the bi-integer chain Z (NE at x=0 with y<=-2 lowers Psi)",
    }


# ---------------------------------------------------------------------------------------------
# Section 2: bounded diagnostics (explicitly not proofs).


def _edge_graph(cap: int) -> tuple[dict[Pop, set[Pop]], list[Any], list[Pop]]:
    pops = domain(LADDER, cap)
    instances = instances_over(pops, LADDER, WITNESS, PRINCIPLES)
    assert all(audit(inst, LADDER, WITNESS) for inst in instances)
    edges: dict[Pop, set[Pop]] = defaultdict(set)
    vrc_targets: list[Pop] = []
    for inst in instances:
        if inst.principle == VRC:
            vrc_targets.append(inst.args[1])
        if inst.shape in {"W", "S"}:
            edges[inst.args[0]].add(inst.args[1])
    # The reviewed source leaves B=empty (VRC), C=empty (DA), and
    # A=B=empty (DA) admissible. The ladder generator omits these; add
    # their graph edges explicitly rather than silently narrowing the model.
    present = set(pops)
    for high in LADDER.levels:
        if high >= WITNESS.get("vrc-avoidance")["u"] and (high,) in present:
            edges[(high,)].add((-1,))
            vrc_targets.append((-1,))
    for source in pops:
        if source and all(level > 0 for level in source):
            edges[source].add(())
        for target in pops:
            if target and len(target) == len(source) and min(source) > max(target):
                edges[source].add(target)
    return edges, instances, vrc_targets


def bounded_cycle_scan(cap: int = SCAN_CAP) -> dict[str, Any]:
    """Bounded diagnostic: no directed cycle among the five schemas up to ``cap`` lives."""
    edges, instances, _ = _edge_graph(cap)
    # Tarjan SCC over the deduplicated edge graph.
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
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) > 1 or comp[0] in edges.get(comp[0], ()):
                cyclic += 1

    for v in sorted(edges):
        if v not in index:
            strong(v)
    return {
        "not_a_general_proof": True,
        "domain": "all finite multisets on W_-1..W_6",
        "population_cap": cap,
        "instances_audited": len(instances),
        "edge_count": sum(len(rights) for rights in edges.values()),
        "cyclic_scc_count": cyclic,
    }


def bounded_da_reachability(cap: int = SCAN_CAP) -> dict[str, Any]:
    """Bounded diagnostic: no VRC image reaches any weak-DA source up to ``cap`` lives."""
    edges, instances, vrc_targets = _edge_graph(cap)
    da_sources = {()} | {pop for pop in domain(LADDER, cap) if all(level >= 0 for level in pop)}
    rev: dict[Pop, set[Pop]] = defaultdict(set)
    for left, rights in edges.items():
        for right in rights:
            rev[right].add(left)
    reach = set(da_sources)
    queue = deque(da_sources)
    while queue:
        node = queue.popleft()
        for pred in rev.get(node, ()):
            if pred not in reach:
                reach.add(pred)
                queue.append(pred)
    hits = [t for t in vrc_targets if t in reach]
    return {
        "not_a_general_proof": True,
        "domain": "all finite multisets on W_-1..W_6",
        "population_cap": cap,
        "vrc_targets_checked": len(vrc_targets),
        "vrc_targets_reaching_a_da_source": len(hits),
    }


# ---------------------------------------------------------------------------------------------
# Section 3: P21 proof devices insufficient here, checked on concrete source instances.


def failed_p21_devices() -> dict[str, Any]:
    """Concrete instances showing why P21's original two proof devices do not suffice.

    The finite quadratic potential can increase across a VRC edge that grows
    cardinality. P21's invariant I = #{t<=0} - #{t>=5} is >= 1 at a
    valid 2003 weak-DA source, so its protected region alone does not
    exclude a DA step after a VRC image. Psi does exclude it.
    """

    def phi(t: int) -> int:
        return 20 * t - t * t

    vrc_edge = Instance(VRC, ((4,), (3, 3, -1)))
    assert audit(vrc_edge, LADDER, WITNESS), vrc_edge
    phi_source = phi(4)
    phi_target = sum(phi(t) for t in (3, 3, -1))

    def invariant(pop: Pop) -> int:
        return sum(1 for t in pop if t <= 0) - sum(1 for t in pop if t >= 5)

    da_edge = Instance(DA_2003, ((0, 1), (-1,)))
    assert audit(da_edge, LADDER, WITNESS), da_edge
    da_i_source = invariant(da_edge.args[0])
    da_i_target = invariant(da_edge.args[1])
    assert da_i_source == 1 and _psi(da_edge.args[0]) == 0

    return {
        "potential": {
            "instance": {"principle": vrc_edge.principle, "args": list(vrc_edge.args)},
            "phi_source": phi_source,
            "phi_target": phi_target,
            "phi_decreases": phi_target < phi_source,
            "audited": True,
        },
        "invariant": {
            "instance": {"principle": da_edge.principle, "args": list(da_edge.args)},
            "i_source": da_i_source,
            "i_target": da_i_target,
            "i_excludes_da_source": da_i_source < 1,
            "psi_source": _psi(da_edge.args[0]),
            "audited": True,
        },
    }


# ---------------------------------------------------------------------------------------------
# Section 4: manifest replay of a concrete 2003 weak-DA edge at P21's witness.


def da_edge_replay() -> dict[str, Any]:
    """Replay the control's serialized 2003 weak-DA edge with P18's manifest verifier."""
    from research.p18_vrc_certificate import control_edges

    da_edge = control_edges()[-1]
    assert da_edge.principle == DA_2003
    problems = verify_edge(da_edge.record(), LADDER, WITNESS)
    return {
        "record": da_edge.record(),
        "verify_edge_problems": problems,
        "ladder_audit": audit(da_edge.instance, LADDER, WITNESS),
        "left": list(da_edge.left),
        "right": list(da_edge.right),
        "skipped_verify_edge_count": (
            "every generated instance is replayed by ladder.audit; verify_edge is applied to "
            "the one serialized control DA edge, not to every generated instance (those are "
            "recovered from populations, not from P18 serialized decompositions)"
        ),
    }


# ---------------------------------------------------------------------------------------------
# Section 5: the probe.


def probe() -> dict[str, Any]:
    for family in ("non-elitism", "general-non-extreme-priority", "vrc-avoidance"):
        validate(family, LADDER, WITNESS.get(family))

    cert = acyclicity_certificate()
    cycle = bounded_cycle_scan()
    reach = bounded_da_reachability()
    failed = failed_p21_devices()
    replay = da_edge_replay()

    return {
        "corner": CORNER,
        "status": "consistent",
        "witness": {key: dict(value) for key, value in WITNESS.params.items()},
        "model": {
            "relation": "reflexive/transitive closure of primitive ED, ranged NE, GNEP, VRC and 2003 weak-DA edges, including source-permitted empty-part clauses",
            "domain": "all finite multisets on W_-1..W_6, including the empty population",
            "extends_to": "every convex subchain {W_-1, ..., W_k} with k >= 6, also k unbounded above",
            "acyclicity_certificate": cert,
            "ed_strictness": "the closure is antisymmetric (acyclic), so an ED edge x^n -> B has no return path B ->* x^n and is genuinely strict",
            "empty_population": "DA with A=B=empty and positive C may require C >= empty; include those edges. Empty has no outgoing edges except reflexivity, so remains a sink.",
        },
        "diagnostics": [
            {
                **cycle,
                "label": "bounded directed-cycle scan",
            },
            {
                **reach,
                "label": "bounded VRC-image-to-DA-source reachability",
            },
            {
                "label": "P21 potential and I-invariant insufficient at concrete source instances",
                "not_a_general_proof": True,
                "domain": "W_-1..W_6 at the selected witness",
                "population_cap": 3,
                "potential": failed["potential"],
                "invariant": failed["invariant"],
            },
            {
                "label": "manifest replay of the control's 2003 weak-DA edge at P21's witness",
                "not_a_general_proof": True,
                "domain": "one audited 2003 DA source instance on W_-1..W_6",
                "population_cap": max(len(replay["left"]), len(replay["right"])),
                "replay": replay,
            },
        ],
        "obstruction": None,
        "routes": {
            "impossibility": {
                "evidence": "no audited cycle or VRC-image-to-DA-source path up to the stated caps; the corner is consistent, so no impossibility is sought",
                "conclusion": "not impossible on W_-1..W_6",
            },
            "all_size_model": {
                "evidence": "symbolic acyclicity certificate (level-parameter exhaustive) plus bounded no-cycle diagnostics",
                "remaining_gap": (
                    "the certificate needs a chain whose minimum level is -1; the "
                    "bi-integer chain Z is not covered because ranged NE at x = 0 with "
                    "y <= -2 lowers the negative-live count and Psi may fall"
                ),
            },
        },
    }


if __name__ == "__main__":
    import json

    print(json.dumps(probe(), indent=2, ensure_ascii=False))
