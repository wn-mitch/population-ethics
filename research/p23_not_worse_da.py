"""Phase 23 corner probe: 2003 unrestricted Non-Elitism with thesis not-worse Dominance Addition.

Corner ``"not-worse-da"`` of :data:`research.p17_vrc_boundary.VARIANTS` (index 2): 2003
Egalitarian Dominance, the **unrestricted** 2003 Non-Elitism (shared background ``D`` any
population), 2003 General Non-Extreme Priority, 2003 VRC avoidance, and the thesis not-worse
Dominance Addition -- the N-shaped clause ``not(A strictly better than B u C)``, never normalized
into a weak edge.  Completeness is assumed nowhere below.

At P21's witness (``research/p21_least_preorder.WITNESS``, imported read-only: Non-Elitism
``n = 1``; GNEP ``(u, y, n) = (5, 3, 1)``; VRC ``(x, u, v, y, n, m) = (-1, 4, 6, 3, 1, 1)``) on
the ladder ``W_-1..W_6``:

1.  P21's invariant device does not survive the unrestricted background.  ``(4, 4) + D ->
    (5, 1) + D`` with ``D = (-1)`` is a legal source instance of 2003 Non-Elitism -- the ranged
    reading forbids that background, as ``W_-1`` lies outside ``R(1, 5)``.  Under P21's
    ``I(P) = #{t <= 0} - #{t >= 5}`` the source has ``I = 1`` and the image ``I = 0``, while P21's
    ranged-support test returns ``True`` for the same edge.  That alone is *not* an impossibility:
    P21's size-preserving potential is background-independent and still decreases, so this is a
    failed proof device, not an audited contradiction.

2.  The least reflexive/transitive closure of the corner's primitive weak instances nevertheless
    violates thesis Dominance Addition there, and the **two-source obstruction lemma** turns that
    into a refutation from forced constraints alone: if a legal thesis-DA target ``T = B u C``
    (B one life at ``W_b``, C a nonempty perfectly equal positive bag) is reachable in that
    closure from two distinct singleton sources ``(W_a,)`` and ``(W_a',)`` with ``a < a' < b``,
    then no preorder satisfies the corner at that witness.  Proof: ``(W_a,) >= T`` and
    ``(W_a',) >= T`` are forced; the DA instance with ``A = (W_a',)`` demands ``not(A > T)``,
    which -- since ``A >= T`` is forced -- means ``T >= A``; transitivity gives
    ``(W_a,) >= (W_a',)``, contradicting the strict ED instance ``(W_a',) > (W_a,)``.  QED.

    At P21's witness the hypotheses hold with ``T = (W_6, W_1^7)``, sources ``(W_4,)`` and
    ``(W_5,)`` and 18-edge chains from each (19 distinct edges); every edge is replayed by
    :func:`research.p19_impossibility_not_worse_da._replay` (p18 ``verify_edge`` plus
    :func:`research.ladder.audit`), and the solver check over every primitive instance induced on
    the certificate relata is UNSAT without completeness.  Every frozen nonempty-bag primitive
    instance of a population of at most ten lives is enumerated, and a path to a width-``w``
    target never leaves populations of at most ``w`` lives, so no two-source target of width
    below eight exists there.

3.  Scope: item 2 refutes the corner at *one* fixed legal witness, not source-general.  The source
    quantifies over its own existential witnesses (Non-Elitism's ``n`` per level pair, GNEP's
    ``(u, y, n)``, VRC's ``(x, u, v, y, n, m)``), so a source-general contradiction must quantify
    over every legal witness, which is not done here; ``probe()`` reports **OPEN** with a
    reproducible fixed-witness refutation.  The ranged control isolates the cause: with thesis
    *ranged* Non-Elitism at the same witness and ladder no DA target is reachable at all, matching
    P21's all-size model for the both-weakened corner.  Only the forward per-population
    enumeration is new machinery -- no existing scanner recovers unrestricted Non-Elitism
    backgrounds (``ladder.instances_over`` needs the subbags of a whole universe, P19's pool is
    bounded to one focus); replay, source-instance generation and the decision reuse the
    P18/P19/P21 machinery and :class:`research.lab.Engine`.
"""

from __future__ import annotations

import json
import time
from collections import Counter, deque
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from itertools import combinations_with_replacement
from typing import Any

from research.lab import Engine, background
from research.ladder import Witness, audit, instances_over, validate
from research.p6_schema import core_constraints, name_of
from research.p17_vrc_boundary import DA_THESIS, ED, GNEP, NE_2003, VARIANTS, VRC
from research.p18_vrc_certificate import Edge
from research.p19_impossibility_not_worse_da import _replay as replay_edge
from research.p21_least_preorder import (
    LADDER,
    WITNESS,
    invariant_preserved,
    invariant_weight,
    potential,
)
from research.schema import Instance, Pop

CORNER = "not-worse-da"
PRINCIPLES: tuple[str, ...] = (ED, NE_2003, GNEP, VRC, DA_THESIS)
assert VARIANTS[2] == (CORNER, NE_2003, DA_THESIS), "corner ids moved in VARIANTS"
LEVELS = LADDER.levels


@dataclass(frozen=True)
class Schema:
    """One fixed legal witness: the three existential parameter mappings, unchanged."""

    ne: Mapping[str, int]
    gnep: Mapping[str, int]
    vrc: Mapping[str, int]

    @classmethod
    def of(cls, witness: Witness) -> Schema:
        return cls(
            witness.get("non-elitism"),
            witness.get("general-non-extreme-priority"),
            witness.get("vrc-avoidance"),
        )


DEFAULT = Schema.of(WITNESS)


# ---------------------------------------------------------------------------------------------
# Multisets and the forward per-population enumeration of primitive instances.


def _plus(*parts: Pop) -> Pop:
    return tuple(sorted(v for part in parts for v in part))


def _sub(pop: Pop, *remove: int) -> Pop | None:
    counts = Counter(pop)
    counts.subtract(Counter(remove))
    if any(v < 0 for v in counts.values()):
        return None
    return tuple(sorted(counts.elements()))


def _bags(levels: Sequence[int], size: int) -> list[Pop]:
    if size <= 0:
        return [()]
    return [tuple(c) for c in combinations_with_replacement(sorted(levels), size)]


def edges_from(pop: Pop, cap: int, schema: Schema, *, ranged: bool) -> list[tuple[Pop, Edge]]:
    """Every frozen nonempty-bag ED/NE/GNEP/VRC instance from ``pop`` up to ``cap`` lives.

    For one population, removing the added part leaves every legal shared background,
    including unrestricted 2003 Non-Elitism backgrounds of any size up to ``len(pop)``.
    The source-permitted empty VRC bag is not part of this frozen translation.
    """
    out: list[tuple[Pop, Edge]] = []
    counts = Counter(pop)
    n_ne, g_u, g_y, g_n = schema.ne["n"], schema.gnep["u"], schema.gnep["y"], schema.gnep["n"]
    v_x, v_u, v_v, v_y, v_n, v_m = (schema.vrc[key] for key in ("x", "u", "v", "y", "n", "m"))
    if len(set(pop)) == 1:  # Egalitarian Dominance: A = x^n strictly above n lives below W_x.
        x = pop[0]
        for target in _bags([v for v in LEVELS if v < x], len(pop)):
            if target != pop:
                out.append((target, Edge(ED, (x,) * len(pop), target, (), {})))
    for middle in LEVELS:  # Non-Elitism: (m, m) + D -> (m + 1, y) + D, m + 1 > y.
        if not LADDER.has(middle + 1) or counts[middle] < n_ne + 1:
            continue
        left = (middle,) * (n_ne + 1)
        shared = _sub(pop, *left)
        assert shared is not None  # Removing an available counted multiset cannot fail.
        for low in [v for v in LEVELS if v < middle]:
            if ranged and any(v not in LADDER.range(low, middle + 1) for v in shared):
                continue
            right = _plus((middle + 1,), (low,) * n_ne)
            witness = {"x": middle + 1, "y": low, "n": n_ne}
            out.append((_plus(shared, right), Edge(NE_2003, left, right, shared, witness)))
    for z in LEVELS:  # GNEP: h^n + z + E -> B_n + (z + 1) + E.
        if not LADDER.has(z + 1) or counts[z] < 1:
            continue
        for high in [v for v in LEVELS if v >= g_u]:
            left = _plus((high,) * g_n, (z,))
            shared = _sub(pop, *left)
            if shared is None:
                continue
            for low_bag in _bags(LADDER.range(1, g_y), g_n):
                right = _plus(low_bag, (z + 1,))
                witness = {"z": z, "u": g_u, "y": g_y, "n": g_n}
                out.append((_plus(shared, right), Edge(GNEP, left, right, shared, witness)))
    if len(pop) == v_n and len(set(pop)) == 1 and pop[0] >= v_u:
        for size in range(1, cap):
            for bag in _bags(LADDER.range(1, v_y), size):
                right = _plus(bag, (v_x,) * v_m)
                out.append((right, Edge(VRC, pop, right, (), dict(schema.vrc))))
    return [(target, edge) for target, edge in out if len(target) <= cap]


def _forward(
    source: Pop, cap: int, schema: Schema, *, ranged: bool
) -> dict[Pop, tuple[Pop, Edge] | None]:
    """Breadth-first closure; a node's value is its (predecessor, edge) on a shortest path."""
    parent: dict[Pop, tuple[Pop, Edge] | None] = {source: None}
    queue = deque([source])
    while queue:
        current = queue.popleft()
        for target, edge in edges_from(current, cap, schema, ranged=ranged):
            if target not in parent:
                parent[target] = (current, edge)
                queue.append(target)
    return parent


def scan(
    cap: int, schema: Schema, *, ranged: bool
) -> dict[int, dict[Pop, tuple[Pop, Edge] | None]]:
    """Shortest-path closures of every singleton source, one per level."""
    return {level: _forward((level,), cap, schema, ranged=ranged) for level in LEVELS}


def _path(parent: Mapping[Pop, tuple[Pop, Edge] | None], target: Pop) -> list[Edge]:
    steps: list[Edge] = []
    node: Pop = target
    while parent[node] is not None:
        previous, edge = parent[node]  # type: ignore[misc]
        steps.append(edge)
        node = previous
    return list(reversed(steps))


def _step(edge: Edge) -> dict[str, Any]:
    return {
        "principle": edge.principle,
        "shape": edge.shape,
        "left": list(edge.left),
        "right": list(edge.right),
        "background": list(edge.background),
        "witness": dict(edge.witness),
    }


def _dedup(*chains: Sequence[Edge]) -> list[Edge]:
    """Edges are unhashable (witness mappings), so dedupe on endpoints and background."""
    chosen: dict[tuple[Any, ...], Edge] = {}
    for chain in chains:
        for edge in chain:
            chosen.setdefault((edge.principle, edge.left, edge.right, edge.background), edge)
    return list(chosen.values())


# ---------------------------------------------------------------------------------------------
# Route A, step 1: the invariant-breaking legal instance.  A failed device, not impossibility.


def _ne_invariant(middle: int, low: int, n_ne: int) -> tuple[int, int]:
    """P21's invariant base and delta for the Non-Elitism edge at ``middle`` with low level ``low``."""
    base = (n_ne + 1) * invariant_weight(middle)
    return base, invariant_weight(middle + 1) + n_ne * invariant_weight(low) - base


def invariant_failure(schema: Schema = DEFAULT, witness: Witness = WITNESS) -> dict[str, Any]:
    """The shortest legal unrestricted-background Non-Elitism instance that breaks P21's invariant.

    P21 proves ``I(source) >= 1 => I(target) >= 1`` for ranged Non-Elitism.  An unrestricted
    background may contain the weight-``+1`` levels ``t <= 0`` (or the weight-``-1`` levels
    ``t >= 5``), which the ranged window cannot.  The size-preserving potential is unaffected.
    """
    n_ne = schema.ne["n"]
    edge = Edge(NE_2003, (4, 4), (5, 1), (-1,), {"x": 5, "y": 1, "n": n_ne})
    base, delta = _ne_invariant(4, 1, n_ne)
    failures = [
        [middle, low]
        for middle in LEVELS
        if LADDER.has(middle + 1)
        for low in LEVELS
        if low < middle and not invariant_preserved(*_ne_invariant(middle, low, n_ne), LEVELS)
    ]
    return {
        "kind": "failed proof device",
        "invariant": "#{t <= 0} - #{t >= 5}",
        "instance": edge.record(),
        "instance_audited": not replay_edge(edge),
        "source_I": sum(invariant_weight(v) for v in edge.left),
        "target_I": sum(invariant_weight(v) for v in edge.right),
        "invariant_preserved_on_full_support": invariant_preserved(base, delta, LEVELS),
        "invariant_preserved_on_p21_ranged_support": invariant_preserved(
            base, delta, LADDER.range(1, 5)
        ),
        "potential_still_decreases": 2 * potential(4) > potential(5) + potential(1),
        "failing_level_pairs_middle_low": failures,
        "why_not_impossibility": (
            "one legal instance with I(source) = 1 > I(target) = 0 refutes the invariant lemma "
            "only; the background-independent potential still decreases, and neither a strict "
            "cycle nor a DA violation follows from that instance alone"
        ),
        "not_a_general_proof": True,
        "domain": (
            "ladder W_-1..W_6, one fixed witness; every failing (middle, low) level pair is "
            "realizable with a background containing a weight-+1 or weight--1 level"
        ),
        "cap": "level pairs only; not a population-size cap",
    }


# ---------------------------------------------------------------------------------------------
# Route A, step 2: the refuting certificate and the induced-domain decision.


def _da_target_of(pop: Pop) -> tuple[int, int, int] | None:
    """``(b, c, k)`` when ``pop = (b, c^k)`` is a legal thesis-DA target, else ``None``.

    Such a target is a legal ``B u C`` for every DA source ``A = (a,)`` with ``a < b``: ``B`` is
    the single life at ``W_b`` -- the only split placing every B life above every A life -- and
    ``C`` is the perfectly equal positive bag ``W_c^k``.
    """
    counts = Counter(pop)
    for high in sorted(counts):
        rest = counts - Counter({high: 1})
        if rest and len(rest) == 1 and next(iter(rest)) > 0:
            return high, next(iter(rest)), sum(rest.values())
    return None


def _reachable_targets(parent: Mapping[Pop, Any], level: int) -> list[Pop]:
    return [target for target in parent if (info := _da_target_of(target)) and level < info[0]]


def _targets_table(parents: Mapping[int, Mapping[Pop, Any]]) -> dict[str, list[Pop]]:
    """Legal DA targets reachable from each singleton source (a source of size >= 2 cannot grow)."""
    return {
        str(level): sorted(_reachable_targets(parent, level), key=lambda pop: (len(pop), pop))
        for level, parent in parents.items()
        if _reachable_targets(parent, level)
    }


def _two_source_target(
    parents: Mapping[int, Mapping[Pop, Any]],
) -> tuple[Pop, int, int, int, list[int]] | None:
    """Smallest legal DA target reachable from two distinct singleton sources, if one exists."""
    best: tuple[Pop, int, int, int, list[int]] | None = None
    for target in {t for parent in parents.values() for t in parent}:
        info = _da_target_of(target)
        if info is None:
            continue
        high, low, copies = info
        sources = sorted(level for level in LEVELS if level < high and target in parents[level])
        if len(sources) >= 2 and (best is None or (len(target), target) < (len(best[0]), best[0])):
            best = (target, high, low, copies, sources)
    return best


def certificate(
    cap: int = 10,
    schema: Schema = DEFAULT,
    witness: Witness = WITNESS,
    parents: Mapping[int, Mapping[Pop, Any]] | None = None,
) -> dict[str, Any]:
    """The refutation certificate: one DA target reachable from two distinct singleton sources."""
    parents = scan(cap, schema, ranged=False) if parents is None else parents
    found = _two_source_target(parents)
    if found is None:
        raise RuntimeError(f"no two-source DA target found at population cap {cap}")
    target, high, low, copies, sources = found
    low_source, high_source = sources[0], sources[-1]
    da_instance = Instance(DA_THESIS, ((high_source,), target))
    ed_instance = Instance(ED, ((high_source,), (low_source,)))
    chains = {
        "low_source": _path(parents[low_source], target),
        "high_source": _path(parents[high_source], target),
    }
    edges = _dedup(*chains.values())
    problems = [
        {"record": edge.record(), "problems": replay_edge(edge)}
        for edge in edges
        if replay_edge(edge)
    ]
    return {
        "target": list(target),
        "target_decomposition": {"B": [high], "C": [low] * copies},
        "target_width": len(target),
        "sources": sources,
        "chains": {key: [_step(edge) for edge in chain] for key, chain in chains.items()},
        "dominance_addition_instance": {
            "principle": DA_THESIS,
            "shape": da_instance.shape,
            "args": [list(da_instance.args[0]), list(da_instance.args[1])],
        },
        "egalitarian_dominance_instance": {
            "principle": ED,
            "shape": ed_instance.shape,
            "args": [list(ed_instance.args[0]), list(ed_instance.args[1])],
        },
        "replay": {
            "edge_count": len(edges),
            "edge_problems": problems,
            "da_instance_audited": audit(da_instance, LADDER, witness),
            "ed_instance_audited": audit(ed_instance, LADDER, witness),
        },
        "all_edges_replayed_clean": not problems
        and audit(da_instance, LADDER, witness)
        and audit(ed_instance, LADDER, witness),
        "minimality": (
            f"every frozen nonempty-bag primitive instance from a population of at most {cap} "
            f"lives is enumerated, and a path to a target of width w never leaves populations "
            f"of at most w lives, so no two-source DA target of width below {len(target)} "
            f"exists at this witness"
        ),
        "argument": (
            f"any model has (W_{low_source},) >= T by transitivity over the low chain and "
            f"(W_{high_source},) >= T over the high chain; the DA instance A = (W_{high_source},), "
            f"B u C = T forces not(A > T), hence T >= (W_{high_source},) because A >= T is already "
            f"forced; transitivity gives (W_{low_source},) >= (W_{high_source},), contradicting "
            f"the strict ED instance (W_{high_source},) > (W_{low_source},)"
        ),
    }


def focused_decision(cert: Mapping[str, Any], cap: int = 10) -> dict[str, Any]:
    """Decide every primitive instance induced on the certificate relata, without completeness.

    The instance set is built two ways and cross-checked: this module's per-population enumeration
    (four edge principles) plus :func:`research.ladder.audit` over relata pairs for the N-shaped
    thesis DA instances, against :func:`research.ladder.instances_over` for the edge principles.
    """
    relata = {
        tuple(step[key])
        for steps in cert["chains"].values()
        for step in steps
        for key in ("left", "right")
    }
    for instance in (
        cert["dominance_addition_instance"]["args"],
        cert["egalitarian_dominance_instance"]["args"],
    ):
        relata |= {tuple(args) for args in instance}
    relata.discard(())
    instances = [
        edge.instance
        for pop in sorted(relata)
        for target, edge in edges_from(pop, cap, DEFAULT, ranged=False)
        if target in relata
    ]
    for left in sorted(relata):
        for right in sorted(relata):
            candidate = Instance(DA_THESIS, (left, right))
            if audit(candidate, LADDER, WITNESS):
                instances.append(candidate)
    generated = instances_over(sorted(relata), LADDER, WITNESS, (ED, NE_2003, GNEP, VRC))
    seen = set(instances)
    names = tuple(sorted({name_of(pop) for inst in instances for pop in inst.args}))
    hard = [
        *background(names)["reflexivity"],
        *background(names)["transitivity"],
        *core_constraints(instances, "p23-not-worse-da/induced"),
    ]
    result = Engine(names, hard, timeout_ms=120000).check()
    return {
        "relata": len(relata),
        "instances": len(instances),
        "decision_without_completeness": result.decision,
        "reason": result.reason,
        "generator_cross_check": {
            "ladder_instances_over": len(generated),
            "missing_from_enumeration": sum(1 for inst in generated if inst not in seen),
        },
        "scope": (
            f"every ED/NE-2003/GNEP/VRC/DA-thesis instance induced on the {len(relata)} "
            f"certificate relata (at most {cap} lives each)"
        ),
        "not_a_general_proof": True,
    }


# ---------------------------------------------------------------------------------------------
# Controls and census: the ranged reading at the same witness, and further legal witnesses.


def ranged_control(
    cap: int = 10,
    schema: Schema = DEFAULT,
    chain_low: Sequence[Edge] | None = None,
) -> dict[str, Any]:
    """Same witness and ladder with thesis ranged Non-Elitism: no DA target is reachable."""
    parents = scan(cap, schema, ranged=True)
    forbidden: dict[str, Any] | None = None
    for edge in chain_low or ():
        window = LADDER.range(edge.witness["y"], edge.witness["x"])
        if edge.principle == NE_2003 and any(v not in window for v in edge.background):
            forbidden = {
                **_step(edge),
                "ranged_window": list(window),
                "replay_problems": replay_edge(edge),
            }
            break
    return {
        "control_for": "the both-weakened corner (thesis ranged Non-Elitism) at the same witness",
        "non_elitism": "thesis ranged",
        "population_cap": cap,
        "reachable_da_targets": _targets_table(parents),
        "first_edge_the_ranged_reading_forbids": forbidden,
        "interpretation": (
            "with the ranged reading no DA target is reachable at all, so the corner's refutation "
            "is caused by the background-permitted Non-Elitism edges; this agrees with P21's "
            "all-size model for the both-weakened corner at the same witness"
        ),
        "not_a_general_proof": True,
        "domain": f"ladder W_-1..W_6, populations of at most {cap} lives, one fixed witness",
        "cap": f"populations of at most {cap} lives",
    }


def witness_census(cap: int = 8) -> dict[str, Any]:
    """A finite legal-witness grid: where the same two-source obstruction appears."""
    rows: list[dict[str, Any]] = []
    for label, params in CENSUS_WITNESSES:
        witness = Witness(params)
        try:
            for family, values in params.items():
                validate(family, LADDER, values)
        except ValueError:
            rows.append({"label": label, "legal_witness": False, "params": params})
            continue
        found = _two_source_target(scan(cap, Schema.of(witness), ranged=False))
        rows.append(
            {
                "label": label,
                "legal_witness": True,
                "params": {family: dict(values) for family, values in params.items()},
                "two_source_obstruction": found is not None,
                "smallest_target": list(found[0]) if found else None,
                "sources": found[4] if found else None,
            }
        )
    return {
        "witness_count": len(rows),
        "rows": rows,
        "not_a_general_proof": True,
        "domain": f"ladder W_-1..W_6, populations of at most {cap} lives, {len(rows)} witnesses",
        "cap": f"{len(rows)} validated witnesses, populations of at most {cap} lives",
    }


CENSUS_WITNESSES: tuple[tuple[str, dict[str, Mapping[str, int]]], ...] = (
    (
        "p21-witness",
        {
            "non-elitism": {"n": 1},
            "general-non-extreme-priority": {"u": 5, "y": 3, "n": 1},
            "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
        },
    ),
    (
        "p17-p18-p20-witness",
        {
            "non-elitism": {"n": 1},
            "general-non-extreme-priority": {"u": 4, "y": 3, "n": 1},
            "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
        },
    ),
    (
        "ne-n2",
        {
            "non-elitism": {"n": 2},
            "general-non-extreme-priority": {"u": 5, "y": 3, "n": 1},
            "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
        },
    ),
    (
        "gnep-n2",
        {
            "non-elitism": {"n": 1},
            "general-non-extreme-priority": {"u": 5, "y": 3, "n": 2},
            "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
        },
    ),
    (
        "vrc-m2",
        {
            "non-elitism": {"n": 1},
            "general-non-extreme-priority": {"u": 5, "y": 3, "n": 1},
            "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 2},
        },
    ),
    (
        "vrc-n2",
        {
            "non-elitism": {"n": 1},
            "general-non-extreme-priority": {"u": 5, "y": 3, "n": 1},
            "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 2, "m": 1},
        },
    ),
)


# ---------------------------------------------------------------------------------------------
# Contract entry points.


def probe(cap: int = 10, census_cap: int = 8) -> dict[str, Any]:
    """The corner's contract payload: status, witness, diagnostics, obstruction and both routes."""
    parents = scan(cap, DEFAULT, ranged=False)
    cert = certificate(cap, parents=parents)
    low_source, high_source = cert["sources"][0], cert["sources"][-1]
    chain_low = _path(parents[low_source], tuple(cert["target"]))
    control = ranged_control(cap, chain_low=chain_low)
    invariant = invariant_failure()
    targets = _targets_table(parents)
    scope = f"ladder W_-1..W_6, populations of at most {cap} lives, one fixed witness"
    return {
        "corner": CORNER,
        "status": "open",
        "status_reason": (
            "refuted at one fixed legal witness by an audited primitive certificate, but no "
            "source-general contradiction over every legal witness and no all-size model is "
            "established here"
        ),
        "principles": list(PRINCIPLES),
        "witness": {
            "ladder": [min(LEVELS), max(LEVELS)],
            "params": {family: dict(values) for family, values in WITNESS.params.items()},
            "source": "research/p21_least_preorder.WITNESS (read-only)",
        },
        "diagnostics": [
            {"name": "p21-invariant-breaking instance", **invariant},
            {
                "name": "least-closure DA targets (2003 unrestricted Non-Elitism)",
                "reachable_da_targets": targets,
                "not_a_general_proof": True,
                "domain": scope,
                "cap": f"populations of at most {cap} lives",
            },
            {"name": "thesis ranged Non-Elitism control", **control},
            {"name": "witness census", **witness_census(census_cap)},
        ],
        "best_failed_lemma": {
            "name": "p21 invariant preservation under unrestricted Non-Elitism",
            "statement": (
                "I(P) = #{t <= 0} - #{t >= 5} satisfies I(source) >= 1 => I(target) >= 1 along "
                "every primitive edge"
            ),
            "status": "false for 2003 Non-Elitism",
            "counterexample": invariant["instance"],
            "counterexample_audited": invariant["instance_audited"],
            "countersource_I": invariant["source_I"],
            "countertarget_I": invariant["target_I"],
            "kept_true_by_the_ranged_reading": invariant[
                "invariant_preserved_on_p21_ranged_support"
            ],
            "what_it_does_not_prove": invariant["why_not_impossibility"],
            "not_a_general_proof": True,
            "domain": invariant["domain"],
            "cap": invariant["cap"],
        },
        "obstruction": {
            "kind": "fixed-witness contradiction from the two-source obstruction lemma",
            "target": cert["target"],
            "target_decomposition": cert["target_decomposition"],
            "sources": cert["sources"],
            "dominance_addition_instance": cert["dominance_addition_instance"],
            "egalitarian_dominance_instance": cert["egalitarian_dominance_instance"],
            "chains": cert["chains"],
            "minimality": cert["minimality"],
            "all_edges_replayed_clean": cert["all_edges_replayed_clean"],
            "replay": cert["replay"],
            "argument": cert["argument"],
            "induced_domain_check": focused_decision(cert, cap),
            "not_a_general_proof": True,
            "domain": scope,
            "cap": f"populations of at most {cap} lives",
        },
        "routes": {
            "impossibility": {
                "route": "arbitrary-witness primitive chain with symbolic count/level dependencies",
                "proved": (
                    "at the fixed legal witness of research/p21_least_preorder.WITNESS the corner "
                    "is inconsistent: one audited thesis-DA target is reachable from two singleton "
                    f"sources, forcing (W_{low_source},) >= (W_{high_source},) against the strict "
                    "ED instance"
                ),
                "evidence": (
                    "obstruction.chains: the two audited weak chains plus the DA instance with "
                    f"A = (W_{high_source},) and the strict ED instance (W_{high_source},) > "
                    f"(W_{low_source},)"
                ),
                "remaining_gap": (
                    "source-general impossibility is not claimed: the source's existential "
                    "witnesses (Non-Elitism's n per level pair, GNEP's (u, y, n), VRC's "
                    "(x, u, v, y, n, m)) are fixed here, so only this witness is refuted; the "
                    "witness census samples further witnesses without quantifying over them"
                ),
            },
            "model": {
                "route": "all-size model on a stated full domain",
                "least_closure_is_a_model": False,
                "why": (
                    "the least reflexive/transitive closure of the primitive weak instances "
                    "already reaches a legal DA target from a legal singleton source, so the least "
                    "closure violates thesis DA; combining the DA-forced reverse comparison with "
                    "the target's second source chain then yields a comparison that the strict "
                    "Egalitarian Dominance instance forbids"
                ),
                "reachable_da_targets": "diagnostics[1].reachable_da_targets",
                "remaining_gap": (
                    "no all-size model at this witness; the model route is untested for other "
                    "legal witnesses, where the corner may still be satisfiable"
                ),
                "not_a_general_proof": True,
                "domain": scope,
                "cap": f"populations of at most {cap} lives",
            },
        },
        "controls": {
            "p21_read_only": (
                "research/p21_least_preorder is imported read-only; its witness, ladder, "
                "certificates and both ledger ids are unchanged"
            ),
            "ranged_reading": control["interpretation"],
            "original_2003_control": (
                "the published 2003 control stays the source-general impossibility of the "
                "unweakened conjunction (arrhenius-2003:theorem, P18 result); this module changes "
                "neither its witness nor its certificate"
            ),
        },
        "not_a_general_proof": True,
    }


def run(cap: int = 10) -> dict[str, Any]:
    return probe(cap=cap)


def main() -> None:
    started = time.monotonic()
    data = probe()
    data["wall_time_s"] = round(time.monotonic() - started, 1)
    print(json.dumps(data, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
