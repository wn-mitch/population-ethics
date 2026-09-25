"""Phase 26 controls: the concrete witness catalogue, the count obligations and the diagnostics.

Companion of :mod:`research.p26_q011_unrestricted`, which holds the witness type, the
legality check, the source-general two-source construction and the per-witness
certificate.  This module owns the concrete witnesses the construction is instantiated
at, the symbolic integer obligations that make the construction a schema rather than
one example, the finite diagnostics (including the correction of P25's bounded
absence), and the priority/collision note.

Priority.  The corner's derived comparison ``not(A_high >= T)`` is the
weak-Dominance-Addition conclusion recorded in the 2016 reconstruction
(``thomas-2016-reconstructing``, p. 10) after its Theorem 5: its General Non-Elitism
is the unrestricted-background 2003 Non-Elitism (p. 7, "for any population R"), it
uses the same Egalitarian Dominance, GNEP and Dominance Addition ingredients, and its
conclusion is the negation of 2003 VRC avoidance's own ``A >= B u C`` once the low bag
is the uniform ``W_3`` bag (``3`` lies in ``R(1, y)`` because ``y >= 3``), the negative
level is VRC's ``x``, the high level is at or above VRC's floor, and the sizes are
matched.  The corner's impossibility is therefore source-known: this phase supplies an
independent, machine-replayed certificate, not a priority claim.
"""

from __future__ import annotations

import functools
import operator
from collections.abc import Iterable
from typing import Any

import z3  # type: ignore[import-untyped]

from research.ladder import Witness, audit
from research.p17_vrc_boundary import NE_2003
from research.p18_vrc_certificate import Edge
from research.p21_least_preorder import LADDER
from research.p23_not_worse_da import CENSUS_WITNESSES, Schema, edges_from
from research.p26_q011_unrestricted import (
    LEVELS,
    CornerWitness,
    chain,
    construction,
)

# ---------------------------------------------------------------------------------------------
# The witness catalogue.  The six frozen p23 census rows, whose Non-Elitism n is uniform and
# whose GNEP triple is uniform in z, plus two witnesses that exercise the source's own
# dependencies: a per-pair NE count with unequal step sizes, and a GNEP floor that varies by
# carrier level.

P23_WITNESSES: tuple[CornerWitness, ...] = tuple(
    CornerWitness.uniform(label, params) for label, params in CENSUS_WITNESSES
)


def _dependent_witnesses() -> tuple[CornerWitness, ...]:
    """Witnesses whose NE count depends on the level pair and GNEP's triple on z."""
    carriers = [z for z in LEVELS if LADDER.has(z + 1)]
    ne = {
        (x, y): 1 + ((x + y) % 3) for x in LEVELS for y in LEVELS if LADDER.has(x - 1) and x - 1 > y
    }
    gnep_a = {z: (4 + ((z + 1) % 2), 3, 1 + ((z + 1) % 2)) for z in carriers}
    gnep_b = {z: (6 if z == -1 else 4, 3, 1) for z in carriers}
    return (
        CornerWitness(
            "dependent-ne-gnep", ne, gnep_a, {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1}
        ),
        CornerWitness(
            "high-gnep-floor",
            {pair: 1 for pair in ne},
            gnep_b,
            {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
        ),
    )


WITNESSES: tuple[CornerWitness, ...] = (*P23_WITNESSES, *_dependent_witnesses())


# ---------------------------------------------------------------------------------------------
# Symbolic obligations.  Exact integer identities over arbitrary positive witness parameters.


def _product(terms: Iterable[z3.ArithRef]) -> z3.ArithRef:
    return functools.reduce(operator.mul, terms, z3.IntVal(1))


def count_obligations(max_depth: int = 5) -> dict[str, Any]:
    """Machine-check the count identities for arbitrary positive witness parameters.

    (D) depth: for symbolic ``N_1..N_d >= 2`` and ``H >= 1``, the pool
        ``L_i = (prod_{j>=i} N_j) * H`` satisfies ``L_i * (prod_{j<i} N_j) = (prod_j N_j) * H``
        and ``L_i >= N_i``; the level-``i`` phase is therefore exact and nonempty.
    (F) fuel: ``H = n + m * S`` with ``S >= 1`` makes ``H - n`` exactly the consumed count
        ``m * S``, which is positive.
    (T) target: ``K = M * H`` with ``M >= 1`` and ``K >= H`` gives ``k = K + m - n >= 2``.
    """
    rows: list[dict[str, Any]] = []
    for depth in range(1, max_depth + 1):
        sizes = z3.Ints(" ".join(f"N_{i}" for i in range(depth)))
        fuel = z3.Int(f"H_{depth}")
        solver = z3.Solver()
        for size in sizes:
            solver.add(size >= 2)
        solver.add(fuel >= 1)
        total = _product(sizes)
        reservoir = total * fuel
        for i in range(depth):
            prefix, suffix = _product(sizes[:i]), _product(sizes[i:])
            pool = suffix * fuel
            solver.push()
            solver.add(pool * prefix != reservoir)  # the identity to refute
            identity = solver.check()
            solver.pop()
            solver.push()
            solver.add(pool < sizes[i])  # the phase must be nonempty
            nonempty = solver.check()
            solver.pop()
            rows.append(
                {
                    "depth": depth,
                    "index": i,
                    "identity_refuted": identity == z3.unsat,
                    "identity_status": str(identity),
                    "nonempty_refuted": nonempty == z3.unsat,
                    "nonempty_status": str(nonempty),
                }
            )
    fuel_solver = z3.Solver()
    n_v, m_v, spread, fuel = z3.Ints("n_v m_v S H")
    fuel_solver.add(n_v >= 1, m_v >= 1, spread >= 1)
    consumed = m_v * spread
    fuel_solver.add(fuel == n_v + consumed)
    fuel_solver.push()
    fuel_solver.add(fuel - n_v - consumed != 0)  # the fuel identity
    fuel_identity = fuel_solver.check()
    fuel_solver.pop()
    fuel_solver.push()
    fuel_solver.add(consumed < 1)  # the GNEP phase is nonempty
    fuel_positive = fuel_solver.check()
    fuel_solver.pop()
    target_solver = z3.Solver()
    k, reservoir_s, n_v_s, m_v_s, spread_s, fuel_s = z3.Ints("k K n_v m_v S H")
    target_solver.add(n_v_s >= 1, m_v_s >= 1, spread_s >= 1)
    target_solver.add(fuel_s == n_v_s + m_v_s * spread_s)
    target_solver.add(reservoir_s >= fuel_s)  # M >= 1 gives K >= H
    target_solver.add(k == reservoir_s + m_v_s - n_v_s, k < 2)
    target_check = target_solver.check()
    return {
        "divisibility_and_nonemptiness": rows,
        "all_identities_refuted": all(r["identity_refuted"] for r in rows),
        "all_phases_nonempty": all(r["nonempty_refuted"] for r in rows),
        "fuel_identity_refuted": fuel_identity == z3.unsat,
        "fuel_identity_status": str(fuel_identity),
        "fuel_positive_refuted": fuel_positive == z3.unsat,
        "fuel_positive_status": str(fuel_positive),
        "target_width_refuted": target_check == z3.unsat,
        "target_width_status": str(target_check),
        "depth_checked": max_depth,
        "general_depth_argument": (
            "prod_{j<i} N_j * prod_{j>=i} N_j = prod_j N_j by associativity and commutativity "
            "of integer multiplication for every depth, so the per-depth checks above discharge "
            "the identity for all d and the loop instances are exactly the symbolic ones"
        ),
        "not_a_general_proof": False,
    }


# ---------------------------------------------------------------------------------------------
# Diagnostics.


def generator_cross_check(w: CornerWitness) -> dict[str, Any] | None:
    """Check every construction edge against P23's repaired forward scanner, when uniform."""
    if w.frozen is None:
        return None
    c = construction(w)
    schema = Schema.of(Witness(w.frozen))
    missing: list[dict[str, Any]] = []
    checked = 0
    for low in (True, False):
        edges, _ = chain(w, c, low=low)
        for edge in edges:
            cap = max(len(edge.left), len(edge.right))
            generated = edges_from(edge.left, cap, schema, ranged=False)
            checked += 1
            if not any(
                target == edge.right and candidate.principle == edge.principle
                for target, candidate in generated
            ):
                missing.append(
                    {
                        "principle": edge.principle,
                        "left": list(edge.left),
                        "right": list(edge.right),
                    }
                )
    return {
        "edges_checked": checked,
        "missing_from_p23_scanner": missing,
        "agrees": not missing,
        "cap": "per-edge: the edge's own largest endpoint, so no edge is cap-truncated",
    }


def p25_bounded_absence_control() -> dict[str, Any]:
    """P25 recorded no singleton DA target at ne-n2 for caps 8 and 10; show why."""
    ne_n2 = next(w for w in WITNESSES if w.label == "ne-n2")
    c = construction(ne_n2)
    return {
        "witness": "ne-n2",
        "p25_caps": [8, 10],
        "p25_result": "no equal-size two-source target at either cap",
        "constructed_target_width": c.reservoir + c.vrc_m,
        "constructed_reservoir_K": c.reservoir,
        "interpretation": (
            "the cap-eight and cap-ten absences were genuine absences *below the cap*; the "
            "constructed target is far wider, so absence at a cap is not evidence for a model "
            "and the P25 bounded rows stay diagnostics"
        ),
        "not_a_general_proof": True,
    }


def empty_branch_note() -> dict[str, Any]:
    """The source-permitted empty clauses stay outside this certificate and unclaimed."""
    return {
        "source_permitted_empty_branches": [
            "VRC low bag B = empty",
            "thesis DA C = empty",
            "thesis DA A = B = empty",
        ],
        "status": (
            "not used and not needed by the certificate: every instance here has a nonempty VRC "
            "low bag, a nonempty, perfectly equal positive DA addition C, and nonempty A, so the "
            "result holds inside the frozen translation and therefore for the source, which keeps "
            "those instances as well; the empty branches remain a separate review-first fidelity "
            "question and no claim is made about them"
        ),
    }


def priority_note() -> dict[str, Any]:
    """The exact prior-work overlap, recorded without a novelty claim."""
    return {
        "verdict": "collides / source-known",
        "sources": [
            "thomas-2016-reconstructing, printed p. 10, remark after Theorem 5",
            "arrhenius-2003-vrc, Theorem 5 (the fifth impossibility theorem, pp. 176-177)",
        ],
        "overlap": (
            "the 2016 reconstruction's Theorem 5 uses Egalitarian Dominance, its General "
            "Non-Elitism (p. 7, 'for any population R', i.e. the unrestricted 2003 background), "
            "GNEP and Dominance Addition; its remark after the theorem states that with the "
            "weaker not-worse Dominance Addition the valid conclusion is that n[A] is not at "
            "least as good as m[z] u N[3]"
        ),
        "why_it_contradicts_the_corner": (
            "that conclusion is not(A_high >= B u C) for a uniform W_3 low bag, which is the "
            "negation of 2003 VRC avoidance's own A >= B u C once the low bag is that uniform W_3 "
            "bag (3 lies in R(1, y) because y >= 3), the negative level is VRC's x, the high level "
            "is at or above VRC's floor u, and the sizes are matched"
        ),
        "consequence": (
            "Q-011's remaining corner is impossible and the impossibility is essentially "
            "published; the module's contribution is an independent, machine-replayed "
            "per-witness certificate and the exact count identities, not priority"
        ),
        "not_a_priority_claim": True,
    }


def lemma() -> dict[str, Any]:
    """The exact lemma this phase proves, with its derivation written out."""
    return {
        "name": "source-general two-source primitive chain",
        "statement": (
            "For every legal corner witness W on a convex level domain containing W_0, the five "
            "corner principles have no model: the VRC sources (W_u)^n and (W_{u+1})^n both reach "
            "T = (W_b)^n u (W_1)^k with k >= 2, which is a legal thesis-Dominance-Addition target "
            "for (W_{u+1})^n."
        ),
        "derivation": [
            "A_low = (W_u)^n and A_high = (W_{u+1})^n are both legal VRC sources: n lives, one level, at or above VRC's floor u.",
            "VRC sends each of them to (W_3)^K u (W_x)^m with K = M * H, because the low bag may be any subpopulation of R(1, y) and 3 lies in R(1, y) as y >= 3.",
            "For j = 3..b-1 the pool at W_j holds L_j = (prod_{i>=j} N_i) * H lives with N_j = n(j+1,1)+1, so N_j | L_j and the NE instance at pair (j+1, 1) empties W_j while emitting one life at W_{j+1} and n(j+1,1) lives at W_1; 2003 NE allows the arbitrary shared background, which carries the negatives.",
            "After the NE phases the population is (W_b)^H u (W_1)^{K-H} u (W_x)^m.",
            "For each of the m negative carriers and each z = x..0, GNEP with n_z lives at W_b as fuel (legal because b >= u_z) and low bag (W_1)^{n_z} in R(1, y_z) lifts the carrier from W_z to W_{z+1}; total fuel m * sum_z n_z = H - n, so exactly n lives remain at W_b.",
            "Both sources therefore reach T = (W_b)^n u (W_1)^k, k = K + m - n >= 2.",
            "T is a legal thesis-DA target: B = (W_b)^n has the same size as A_high, every A_high life is below W_b because b >= u + 2, and C = (W_1)^k is nonempty, perfectly equal and positive.",
            "A_low and A_high both reach T, so any model has A_low >= T and A_high >= T; the DA instance with A = A_high forces not(A_high > T), which with A_high >= T gives T >= A_high, hence A_low >= A_high by transitivity.",
            "The strict ED instance A_high > A_low is legal (equal size, every life of A_low below W_{u+1}). Contradiction.",
        ],
        "uses_completeness": False,
        "uses": [
            "transitivity",
            "the definition of strict preference as weak(a, b) and not weak(b, a)",
            "classical propositional logic",
        ],
        "not_a_general_proof": False,
    }


def proof_obligations() -> dict[str, Any]:
    """Discharged versus open, so the promotion gate is auditable from the result alone."""
    return {
        "discharged": [
            "O1 divisibility and nonemptiness: every level pool L_j is exactly divisible by its "
            "step size N_j and every phase runs at least once (z3 over symbolic N_j >= 2, H >= 1, "
            "depths 1..5; the identity is depth-independent by associativity of integer products)",
            "O2 level bookkeeping: after the NE phases only levels b, 1 and x are occupied, with H "
            "lives at b and K - H drops at W_1 (asserted from the built populations per witness)",
            "O3 fuel: the GNEP phases consume exactly m * sum_z n_z = H - n lives at W_b, leaving n",
            "O4 target width: k = K + m - n >= 2 for every positive witness parameter (z3)",
            "O5 VRC source legality at both levels u and u+1, with the low bag inside R(1, y)",
            "O6 NE pair (j+1, 1) legality at the pair-dependent existential, with drop level 1 < j",
            "O7 GNEP carrier (z, z+1) legality with b >= u_z and the low bag inside R(1, y_z)",
            "O8 thesis-DA target and strict-ED instance legality, independently confirmed by "
            "research.ladder.audit at every witness",
            "O9 closure: the finite theory induced on the certificate relata is UNSAT with no "
            "completeness assumption at every witness (research.lab.Engine)",
        ],
        "open": [
            "the source-permitted empty branches (VRC low bag empty, thesis-DA C empty, thesis-DA "
            "A = B = empty) are untouched; the certificate never uses them, so no claim is made "
            "about a variant that adopts them",
            "a non-convex or W_0-free level domain lies outside the ledger's level translation; "
            "the construction is not defined there and no claim is made about it",
            "priority/novelty is not a proof obligation; the conclusion collides with the 2016 "
            "reconstruction (thomas-2016-reconstructing p. 10) and arrhenius-2003-vrc Theorem 5, "
            "so the module makes no novelty claim",
        ],
    }


def refuted_candidates() -> list[dict[str, Any]]:
    """Universal-route candidates that the certificate refutes, each with its witness."""
    ne_one = Witness({"non-elitism": {"n": 1}})
    invariant_edge = Edge(NE_2003, (4, 4), (5, 1), (-1,), {"x": 5, "y": 1, "n": 1})
    ne_n2 = next(w for w in WITNESSES if w.label == "ne-n2")
    c = construction(ne_n2)
    vrc_edge = chain(ne_n2, c, low=True)[0][0]
    return [
        {
            "candidate": "the P25 ne-n2 least-preorder candidate is a model of the corner",
            "verdict": "refuted",
            "counterexample": (
                f"the ne-n2 certificate reaches T = (W_6) u (W_1)^{c.level_one_pile} of width "
                f"{c.reservoir + c.vrc_m} from both (W_4) and (W_5); DA plus strict ED make that "
                "theory UNSAT, so the least primitive closure at ne-n2 violates thesis DA and "
                "cannot be completed to a preorder"
            ),
            "audited_by": (
                "certificates[ne-n2].instances.decision_without_completeness == 'unsat' and "
                "certificates[ne-n2].edges.all_replayed_and_audited"
            ),
        },
        {
            "candidate": "absence of a DA target below a population cap is evidence for a model",
            "verdict": "refuted",
            "counterexample": (
                "the same witness's constructed target has width 82 while P25 scanned caps 8 and "
                "10; a bounded absence below the cap is not a model, and this target is above it"
            ),
            "audited_by": "diagnostics.p25_bounded_absence plus the ne-n2 certificate",
        },
        {
            "candidate": "the level-sum measure M(P) = sum of levels is non-increasing along every "
            "weak edge of the corner",
            "verdict": "refuted",
            "counterexample": (
                "VRC's own instance used by the certificate carries A_low to the reservoir with "
                f"level sum {sum(vrc_edge.left)} -> {sum(vrc_edge.right)}; VRC's low bag is "
                "unbounded in size, so the unweighted level sum rises and cannot be the missing "
                "potential"
            ),
            "audited_by": "certificates[ne-n2].edges (the replayed VRC edge)",
        },
        {
            "candidate": "the P21 score I(P) = #{t <= 0} - #{t >= 5} is preserved by the corner's "
            "unrestricted Non-Elitism",
            "verdict": "refuted",
            "counterexample": (
                "the legal instance (-1, 4, 4) >= (-1, 1, 5) at pair (5, 1) drops the score from "
                "1 to 0"
            ),
            "instance_audited": audit(invariant_edge.instance, LADDER, ne_one),
            "record": invariant_edge.record(),
        },
    ]
