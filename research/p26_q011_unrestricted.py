"""Phase 26: a source-general two-source certificate for Q-011's remaining corner.

Corner ``"not-worse-da"`` of :data:`research.p17_vrc_boundary.VARIANTS` (index 2):
2003 Egalitarian Dominance, the **unrestricted** 2003 Non-Elitism, 2003 General
Non-Extreme Priority, 2003 VRC avoidance, and the thesis not-worse Dominance
Addition (the N-shaped clause ``not(A strictly better than B u C)``).  P23 refuted
this corner at one fixed witness; P25 repaired the scanner and bounded the search.
This module closes the construction gap with an explicit primitive chain for
**every** legal witness, so the corner is inconsistent for every legal existential
witness on a convex level domain containing ``W_0``.

The concrete control witnesses, the symbolic count obligations, the finite
diagnostics and the priority/collision note live in
:mod:`research.p26_q011_controls`; this module holds the witness type, the legality
check, the construction, the per-witness certificate and the contract entry points.

The construction
-----------------
Fix a legal witness.  Write ``x < 0`` for VRC's negative level, ``u`` / ``y`` / ``n``
/ ``m`` for VRC's high floor / low-range top / high count / negative count, and, for
each carrier level ``z = x, x+1, ..., 0``, write ``(u_z, y_z, n_z)`` for GNEP's
existential triple at ``z``.  Put

    b  = max(u + 2, u_x, ..., u_0)          (above VRC's floor and every GNEP floor)
    N_j = n(j+1, 1) + 1   for j = 3..b-1    (the NE existential at pair (j+1, 1))
    M  = prod_j N_j
    H  = n + m * sum_z n_z
    K  = M * H

``b >= 4`` because GNEP needs ``u_z > y_z >= 3``.  Both ``(W_u)^n`` and ``(W_{u+1})^n``
are VRC sources.  From either one:

1.  **VRC** sends it to ``(W_3)^K u (W_x)^m``: one application, ``B = (W_3)^K`` inside
    ``R(1, y)`` because ``y >= 3``, ``C = (W_x)^m`` at the negative level, no background.
2.  **Non-Elitism**, for ``j = 3..b-1``: consume groups of ``N_j`` lives at ``W_j`` and
    emit one life at ``W_{j+1}`` plus ``n(j+1, 1)`` lives at ``W_1``, all other lives
    (including the ``m`` negatives) in the shared background ``D``, which 2003
    Non-Elitism allows to be *any* population.  The pool at ``W_j`` holds
    ``L_j = (prod_{i>=j} N_i) * H`` lives, so ``N_j | L_j`` exactly and the level is
    emptied; afterwards the population is ``(W_b)^H u (W_1)^{K-H} u (W_x)^m``.
3.  **GNEP**, one negative carrier at a time, for ``z = x..0``: with ``n_z`` lives at
    ``W_b`` as fuel (legal since ``b >= u_z``) and the low bag ``(W_1)^{n_z}`` inside
    ``R(1, y_z)``, lift the carrier from ``W_z`` to ``W_{z+1}``.  Total fuel
    ``m * sum_z n_z = H - n``, leaving exactly ``n`` lives at ``W_b``.

The two sources reach the same ``T = (W_b)^n u (W_1)^k`` with ``k = K + m - n >= 2``.

The contradiction
-----------------
``T`` is a legal thesis-DA target for ``A_high = (W_{u+1})^n``: ``B = (W_b)^n`` has the
same size, every ``A_high`` life is below ``W_b`` (``b >= u + 2``), and
``C = (W_1)^k`` is nonempty, perfectly equal and positive.  Both ``A_low = (W_u)^n``
and ``A_high`` reach ``T``, so any model has ``A_low >= T`` and ``A_high >= T``.  The
thesis-DA instance with ``A = A_high`` then forces ``not(A_high > T)``; since
``A_high >= T`` is already forced this means ``T >= A_high``, and transitivity gives
``A_low >= A_high``.  But Egalitarian Dominance gives the strict instance
``A_high > A_low`` (same size, every ``A_low`` life below ``W_{u+1}``).  Contradiction.
No completeness is used; strict preference is the macro
``weak(a, b) and not weak(b, a)``.

Scope, and what is *not* claimed here
-------------------------------------
*  Domain.  The chain names the levels ``x..0``, ``1``, ``3..b``, ``u``, ``u+1``.
   On a convex level domain containing ``W_0`` the witness's own legality already
   supplies every one of them: VRC's range needs ``u, u+1, u+2`` and its low range
   needs ``1, 2, 3``, ``u >= 4`` because ``u > y >= 3`` so ``b >= 6`` and ``3..b``
   is the interval between two levels of the domain, and ``x..0`` is the interval
   between VRC's negative level and ``W_0``.  On the frozen ``W_-1..W_6`` ladder
   that gives ``b = 6`` for every legal witness; on the integer chain ``b`` is
   finite for every witness because only the finitely many carriers ``x..0`` are
   used.  A non-convex or ``W_0``-free domain lies outside the ledger's level
   translation and is not claimed here.
*  Quantifiers.  NE's ``n`` is used at the *pair-dependent* existential
   ``n(j+1, 1)`` and GNEP's triple at the *carrier-dependent* ``z``, matching the
   sources; nothing here assumes the frozen uniform translation, and the frozen
   uniform witnesses are a special case.
*  Empty branches.  ``B = empty`` inside VRC, ``C = empty`` or ``A = B = empty``
   inside thesis Dominance Addition are *not* used; the certificate lives entirely
   inside the frozen nonempty-bag / nonempty-addition translation, so it is valid
   for the source too (the source keeps every instance the frozen translation keeps).
*  Priority.  The conclusion is **not novel**: ``not(A_high >= T)`` is the
   weak-Dominance-Addition conclusion recorded in the 2016 reconstruction
   (``thomas-2016-reconstructing``, p. 10) after its Theorem 5, whose General
   Non-Elitism is the unrestricted-background 2003 Non-Elitism and whose other
   ingredients are the same four conditions; that conclusion is the negation of
   2003 VRC avoidance's own ``A >= B u C`` for the same populations.  The corner's
   impossibility is therefore source-known and this module claims no priority.  See
   :func:`research.p26_q011_controls.priority_note` for the exact overlap.
"""

from __future__ import annotations

import json
import math
import time
from collections import Counter
from collections.abc import Mapping
from dataclasses import dataclass, replace
from typing import Any

from research.lab import Engine, LedgerEntry, background, record, write_result
from research.ladder import FORM, Witness, audit
from research.p6_schema import core_constraints, name_of
from research.p17_vrc_boundary import DA_THESIS, ED, GNEP, NE_2003, VARIANTS, VRC
from research.p18_vrc_certificate import Edge, verify_edge
from research.p19_impossibility_not_worse_da import _replay as replay_edge
from research.p21_least_preorder import LADDER
from research.schema import Instance, Pop

CORNER = "not-worse-da"
PRINCIPLES: tuple[str, ...] = (ED, NE_2003, GNEP, VRC, DA_THESIS)
assert VARIANTS[2] == (CORNER, NE_2003, DA_THESIS), "corner ids moved in VARIANTS"
LEVELS = LADDER.levels
DOMAIN = f"levels {min(LEVELS)}..{max(LEVELS)} on the frozen ladder; every finite population"

# The full ``_replay`` (record replay plus endpoint-to-decomposition search plus audit) runs for
# the smallest certificates only; every certificate is replayed with the independent p18 record
# verifier and the independent ``ladder.audit`` at every edge regardless.
FULL_REPLAY_MAX_TARGET = 32


# ---------------------------------------------------------------------------------------------
# Witnesses and legality.  The source's Non-Elitism n depends on (x, y) and GNEP's triple on z;
# the frozen translation fixes one value each, so both are represented here.


@dataclass(frozen=True)
class CornerWitness:
    """One existential witness of the corner, with the source's own dependencies."""

    label: str
    ne: Mapping[tuple[int, int], int]
    gnep: Mapping[int, tuple[int, int, int]]
    vrc: Mapping[str, int]
    frozen: Mapping[str, Mapping[str, int]] | None = None

    def ne_at(self, x: int, y: int) -> int:
        return self.ne[(x, y)]

    def gnep_at(self, z: int) -> tuple[int, int, int]:
        return self.gnep[z]

    @classmethod
    def uniform(cls, label: str, params: Mapping[str, Mapping[str, int]]) -> CornerWitness:
        """The frozen uniform translation of one p23 census row."""
        ne_n = params["non-elitism"]["n"]
        g = params["general-non-extreme-priority"]
        ne = {(x, y): ne_n for x in LEVELS for y in LEVELS if LADDER.has(x - 1) and x - 1 > y}
        gnep = {z: (g["u"], g["y"], g["n"]) for z in LEVELS if LADDER.has(z + 1)}
        return cls(
            label,
            ne,
            gnep,
            dict(params["vrc-avoidance"]),
            {key: dict(value) for key, value in params.items()},
        )


def _is_range(lo: int, hi: int) -> bool:
    return lo < hi and len(LADDER.range(lo, hi)) >= 3 and LADDER.has(lo) and LADDER.has(hi)


def legality(w: CornerWitness) -> list[str]:
    """Every premise ``research.ladder.validate`` imposes, kept per pair and per carrier."""
    problems: list[str] = []
    for (x, y), n in w.ne.items():
        if not (LADDER.has(x - 1) and x - 1 > y):
            problems.append(f"NE pair ({x}, {y}) is not a source instance")
        if n < 1:
            problems.append(f"NE n({x}, {y}) = {n} is not positive")
    for z, (u, y, n) in w.gnep.items():
        if not (LADDER.has(z + 1) and LADDER.has(z)):
            problems.append(f"GNEP carrier z = {z} is off the ladder")
        if not _is_range(1, y):
            problems.append(f"GNEP R(1, {y}) at z = {z} is not a range")
        if not (LADDER.has(u) and u > 0 and u > y):
            problems.append(f"GNEP floor u = {u} at z = {z} is not above R(1, {y})")
        if n < 1:
            problems.append(f"GNEP n at z = {z} is not positive")
    v = w.vrc
    if not (LADDER.has(v["x"]) and v["x"] < 0):
        problems.append("VRC x is not a negative level")
    if not (_is_range(v["u"], v["v"]) and v["u"] > 0):
        problems.append("VRC R(u, v) is not a positive range")
    if not (_is_range(1, v["y"]) and v["u"] > v["y"]):
        problems.append("VRC R(1, y) is not a range below R(u, v)")
    if not (v["n"] > 0 and v["m"] > 0):
        problems.append("VRC n and m must be positive")
    return problems


# ---------------------------------------------------------------------------------------------
# The construction.


@dataclass(frozen=True)
class Construction:
    """The count data of one witness's chain, before any population is built."""

    b: int
    carriers: tuple[int, ...]  # x .. 0
    ne_counts: Mapping[int, int]  # j -> n(j+1, 1)
    step_sizes: Mapping[int, int]  # j -> N_j = n(j+1,1)+1
    gnep_counts: Mapping[int, int]  # z -> n_z
    vrc_floor: int  # u, VRC's high floor
    product: int  # M
    fuel: int  # H
    reservoir: int  # K
    vrc_n: int
    vrc_m: int

    @property
    def level_one_pile(self) -> int:
        return self.reservoir + self.vrc_m - self.vrc_n


def construction(w: CornerWitness) -> Construction:
    """The count data of the chain for one witness: b, M, H, K and the step sizes."""
    vrc = w.vrc
    carriers = tuple(range(vrc["x"], 1))  # x .. 0
    high = max(vrc["u"] + 2, *(w.gnep_at(z)[0] for z in carriers))
    ne_counts = {j: w.ne_at(j + 1, 1) for j in range(3, high)}
    step_sizes = {j: n + 1 for j, n in ne_counts.items()}
    gnep_counts = {z: w.gnep_at(z)[2] for z in carriers}
    product = math.prod(step_sizes.values())
    fuel = vrc["n"] + vrc["m"] * sum(gnep_counts.values())
    return Construction(
        b=high,
        carriers=carriers,
        ne_counts=ne_counts,
        step_sizes=step_sizes,
        gnep_counts=gnep_counts,
        vrc_floor=vrc["u"],
        product=product,
        fuel=fuel,
        reservoir=product * fuel,
        vrc_n=vrc["n"],
        vrc_m=vrc["m"],
    )


def _plus(*parts: Pop) -> Pop:
    return tuple(sorted(v for part in parts for v in part))


def _minus(pop: Pop, part: Pop) -> Pop:
    counts = Counter(pop)
    counts.subtract(Counter(part))
    if any(v < 0 for v in counts.values()):
        raise AssertionError("construction removed lives that are not present")
    return tuple(sorted(counts.elements()))


def _source(w: CornerWitness, low: bool) -> Pop:
    level = w.vrc["u"] + (0 if low else 1)
    return (level,) * w.vrc["n"]


def chain(w: CornerWitness, c: Construction, low: bool) -> tuple[list[Edge], Pop]:
    """The full primitive chain from one VRC source to the common target."""
    vrc = w.vrc
    edges: list[Edge] = []
    reservoir = _plus((3,) * c.reservoir, (vrc["x"],) * vrc["m"])
    edges.append(Edge(VRC, _source(w, low), reservoir, (), dict(vrc)))
    current = reservoir
    for j in sorted(c.step_sizes):
        n, step = c.ne_counts[j], c.step_sizes[j]
        while Counter(current)[j] >= step:
            left_part = (j,) * step
            right_part = _plus((j + 1,), (1,) * n)
            shared = _minus(current, left_part)
            edges.append(Edge(NE_2003, left_part, right_part, shared, {"x": j + 1, "y": 1, "n": n}))
            current = _plus(shared, right_part)
    for _ in range(vrc["m"]):
        for z in c.carriers:
            u, y, n = w.gnep_at(z)
            left_part = _plus((c.b,) * n, (z,))
            right_part = _plus((1,) * n, (z + 1,))
            shared = _minus(current, left_part)
            edges.append(
                Edge(GNEP, left_part, right_part, shared, {"z": z, "u": u, "y": y, "n": n})
            )
            current = _plus(shared, right_part)
    return edges, current


def _level_counts(c: Construction) -> dict[str, int]:
    return {
        "target_width": c.reservoir + c.vrc_m,
        "levels_at_b": c.vrc_n,
        "levels_at_1": c.level_one_pile,
        "negatives_at_x": c.vrc_m,
        "level_one_pile_before_gnep": c.reservoir - c.fuel,
        "gnep_fuel": c.fuel - c.vrc_n,
    }


# ---------------------------------------------------------------------------------------------
# Verification.  Independent of the constructor: p18 record replay plus ``ladder.audit``.


def _checker(edge: Edge) -> Witness:
    family = {
        "non-elitism-any": "non-elitism",
        "general-non-extreme-priority": "general-non-extreme-priority",
        "vrc-avoidance": "vrc-avoidance",
    }.get(FORM[edge.principle])
    if family is None:
        return Witness({})
    fields = {
        "non-elitism": ("n",),
        "general-non-extreme-priority": ("u", "y", "n"),
        "vrc-avoidance": ("x", "u", "v", "y", "n", "m"),
    }[family]
    return Witness({family: {key: edge.witness[key] for key in fields}})


def _edge_problems(edge: Edge) -> list[str]:
    problems = [
        f"record: {problem}"
        for problem in verify_edge(edge.record(), ladder=LADDER, witness=_checker(edge))
    ]
    if not audit(edge.instance, LADDER, _checker(edge)):
        problems.append("ladder.audit rejected the instance")
    return problems


def _decision(instances: list[Instance]) -> dict[str, Any]:
    names = tuple(sorted({name_of(pop) for inst in instances for pop in inst.args}))
    hard = [
        *background(names)["reflexivity"],
        *background(names)["transitivity"],
        *core_constraints(instances, "p26-q011-unrestricted/v1"),
    ]
    checked = Engine(names, hard, timeout_ms=180000).check()
    return {
        "decision_without_completeness": checked.decision,
        "reason": checked.reason,
        "relata": len(names),
        "instances": len(instances),
    }


def certificate(w: CornerWitness) -> dict[str, Any]:
    """One witness's certificate: both chains, every edge replayed, the induced theory decided."""
    problems = legality(w)
    if problems:
        return {"witness": w.label, "legal": False, "problems": problems}
    c = construction(w)
    low_edges, low_target = chain(w, c, low=True)
    high_edges, high_target = chain(w, c, low=False)
    if low_target != high_target:
        raise AssertionError("the two sources did not reach one common target")
    target = low_target
    if Counter(target)[c.b] != c.vrc_n:
        raise AssertionError("construction did not leave exactly n_v lives at the top level")
    high, low = _source(w, low=False), _source(w, low=True)
    da = Instance(DA_THESIS, (high, target))
    ed = Instance(ED, (high, low))
    unique = list(
        {
            (e.principle, e.left, e.right, e.background): e for e in (*low_edges, *high_edges)
        }.values()
    )
    edge_problems = []
    for edge in unique:
        found = _edge_problems(edge)
        if found:
            edge_problems.append(
                {
                    "principle": edge.principle,
                    "left": list(edge.left),
                    "right": list(edge.right),
                    "problems": found,
                }
            )
    da_ok, ed_ok = audit(da, LADDER, Witness({})), audit(ed, LADDER, Witness({}))
    replay = replay_edge if len(target) <= FULL_REPLAY_MAX_TARGET else None
    full_replay = (
        [{"principle": e.principle, "problems": p} for e in unique if (p := replay(e))]
        if replay is not None
        else None
    )
    decision = _decision([*(e.instance for e in unique), da, ed])
    return {
        "witness": w.label,
        "legal": True,
        "source_dependent_quantifiers": (
            "NE at pair-dependent n(j+1, 1); GNEP at carrier-dependent (u_z, y_z, n_z); VRC fixed"
        ),
        "params": {
            "ne_pairs_used": {f"({j + 1}, 1)": n for j, n in sorted(c.ne_counts.items())},
            "gnep_carriers": {str(z): list(w.gnep_at(z)) for z in c.carriers},
            "vrc": dict(w.vrc),
        },
        "construction": {
            "b": c.b,
            "step_sizes": {str(j): n for j, n in sorted(c.step_sizes.items())},
            "product_M": c.product,
            "fuel_H": c.fuel,
            "reservoir_K": c.reservoir,
            **_level_counts(c),
        },
        "target": list(target),
        "target_decomposition": {
            "A_low": list(low),
            "A_high": list(high),
            "B": [c.b] * c.vrc_n,
            "C_level": 1,
            "C_size": c.level_one_pile,
        },
        "edges": {
            "distinct": len(unique),
            "per_chain": {"low": len(low_edges), "high": len(high_edges)},
            "problems": edge_problems,
            "all_replayed_and_audited": not edge_problems,
            "full_p19_replay_used": replay is not None,
            "full_p19_replay_problems": full_replay,
        },
        "instances": {
            "dominance_addition_audited": da_ok,
            "egalitarian_dominance_audited": ed_ok,
            **decision,
        },
        "finite_certificate": True,
        "not_a_general_proof": False,
        "general_scope": (
            "the count identities hold for every positive witness parameter (see "
            "symbolic_obligations), so this witness is one instantiation of a schema covering "
            "every legal witness on a convex domain containing W_0"
        ),
    }


# ---------------------------------------------------------------------------------------------
# Contract entry points.


def run() -> dict[str, Any]:
    from research import p26_q011_controls as controls

    obligations = controls.count_obligations()
    rows = [certificate(w) for w in controls.WITNESSES]
    illegal = [row for row in rows if not row["legal"]]
    if illegal:
        raise AssertionError(f"illegal witness rows: {illegal}")
    failures = [
        row
        for row in rows
        if row["edges"]["problems"]
        or not row["instances"]["dominance_addition_audited"]
        or not row["instances"]["egalitarian_dominance_audited"]
        or row["instances"]["decision_without_completeness"] != "unsat"
    ]
    if failures:
        raise AssertionError(f"certificate failed at {[row['witness'] for row in failures]}")
    if not (
        obligations["all_identities_refuted"]
        and obligations["all_phases_nonempty"]
        and obligations["fuel_identity_refuted"]
        and obligations["fuel_positive_refuted"]
        and obligations["target_width_refuted"]
    ):
        raise AssertionError("a symbolic count obligation did not close")
    cross = {
        w.label: check
        for w in controls.WITNESSES
        if (check := controls.generator_cross_check(w)) is not None
    }
    if any(not check["agrees"] for check in cross.values()):
        raise AssertionError("a construction edge is absent from the repaired P23 scanner")
    return {
        "corner": CORNER,
        "principles": list(PRINCIPLES),
        "status": "inconsistent for every legal witness (impossible); priority collides",
        "q011_verdict": {
            "corner": CORNER,
            "verdict": "impossible",
            "scope": (
                "every legal existential witness on a convex level domain containing W_0, so in "
                "particular on the frozen W_-1..W_6 ladder (b = 6 for every witness legal there) "
                "and on the integer chain (b finite for every witness)"
            ),
            "settles": (
                "Q-011's remaining corner, unrestricted 2003 Non-Elitism with thesis not-worse "
                "Dominance Addition"
            ),
            "priority": (
                "collides (source-known: the 2016 reconstruction thomas-2016-reconstructing p. 10; "
                "arrhenius-2003-vrc Theorem 5)"
            ),
            "caveats": [
                "the source-permitted empty branches are untouched and no claim is made about them",
                "a non-convex or W_0-free level domain lies outside the translation",
                "no novelty or priority claim is made",
            ],
            "not_a_general_proof": False,
        },
        "status_reason": (
            "an explicit primitive chain is written for an arbitrary legal witness: the two VRC "
            "sources (W_u)^n and (W_{u+1})^n both reach T = (W_b)^n u (W_1)^k, which is a legal "
            "thesis-DA target for (W_{u+1})^n, so DA forces T >= (W_{u+1})^n and transitivity "
            "contradicts the strict ED instance (W_{u+1})^n > (W_u)^n"
        ),
        "domain": DOMAIN,
        "domain_caveat": (
            "the chain names levels x..0, 1, 3..b, u, u+1. Legality of the witness supplies "
            "every named level on a convex domain containing W_0: VRC's range needs u, u+1, u+2, "
            "its low range needs 1, 2, 3, u >= 4 forces b >= 6, and x..0 is the interval from "
            "VRC's negative level to W_0. On the frozen W_-1..W_6 ladder b = 6 for every legal "
            "witness; on the integer chain b is finite for every witness. A non-convex or "
            "W_0-free domain is outside the ledger's level translation and is not claimed here"
        ),
        "witness_quantifiers": {
            "NE": (
                "exists n(x, y) > 0 per pair, used at n(j+1, 1); the frozen uniform n is a "
                "special case"
            ),
            "GNEP": "exists (u_z, y_z, n_z) > 0 per carrier z, used at z = x..0",
            "VRC": "exists (x, u, v, y, n, m); a single fixed witness",
            "coverage": "the construction is a function of the witness, not of one witness",
        },
        "symbolic_obligations": obligations,
        "proof_obligations": controls.proof_obligations(),
        "lemma": controls.lemma(),
        "refuted_candidates": controls.refuted_candidates(),
        "certificates": rows,
        "generator_cross_check": cross,
        "diagnostics": {
            "p25_bounded_absence": controls.p25_bounded_absence_control(),
            "empty_branches": controls.empty_branch_note(),
        },
        "priority": controls.priority_note(),
        "not_a_general_proof": False,
    }


def main() -> None:
    started = time.monotonic()
    result = run()
    path = write_result(
        "p26_q011_unrestricted",
        result,
        {"wall_time_s": round(time.monotonic() - started, 1)},
    )
    artifact = str(path.relative_to(path.parent.parent.parent))
    theorem = LedgerEntry(
        candidate_id="P26-source-general-two-source-chain",
        hypothesis="Unrestricted 2003 NE with thesis not-worse DA is impossible at every legal witness.",
        motivation="P25's bounded absences left the arbitrary-witness contradiction unproved.",
        exact_formal_change="None: the proof uses only reviewed nonempty source instances.",
        scope="every legal witness on a convex indexed chain containing W_0",
        search_method="arbitrary-witness count construction, P18 replay, independent ladder audit and exact preorder decision",
        result="two VRC sources reach one thesis-DA target at every legal witness; thesis DA and strict ED contradict without completeness",
        evidence_type="symbolic all-witness proof and eight independently audited instantiations",
        checked=True,
        minimal="no proof-size or premise minimality claim",
        interpretation="Unrestricted NE raises an arbitrarily large VRC low bag while retaining the negative background.",
        next_experiment="study off-chain fidelity separately; this impossibility is source-known",
        result_scope="source-general impossibility on indexed chains, not arbitrary off-chain quasi-orders",
        formalization_tier="agent-cross-read source clauses, with pair-dependent NE and carrier-dependent GNEP witnesses",
        witness_conditions="arbitrary legal VRC counts and ranges, NE n(x,y), GNEP (u_z,y_z,n_z)",
        novelty_status="source-known; exact 2016 reconstruction collision",
        status="confirmed",
        artifacts=[artifact],
    )
    record(
        [
            theorem,
            replace(
                theorem,
                candidate_id="P26-ne-n2-least-preorder-refutation",
                hypothesis="The ne-n2 least primitive preorder satisfies thesis DA at every population size.",
                scope="fixed ne-n2 witness on W_-1..W_6; one finite certificate of width 82",
                result="refuted: both W_4 and W_5 reach one legal thesis-DA target at width 82; the induced theory is UNSAT",
                evidence_type="finite audited counterexample to a universal model candidate",
                result_scope="one fixed-witness refutation, not a new source-general theorem",
                interpretation="Cap-eight and cap-ten absences are compatible with a wider contradiction.",
                next_experiment="none for this refuted fixed-witness candidate",
                status="refuted",
            ),
        ]
    )
    print(
        json.dumps(
            {
                "result": artifact,
                "status": result["status"],
                "witnesses": len(result["certificates"]),
                "claim": "impossible (source-known)",
            }
        )
    )


if __name__ == "__main__":
    main()
