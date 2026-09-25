"""Phase 20 (Q-011 route B): nonlinear cardinality-normalized and level-separable saturating
orders are excluded on the ladder W_-1 … W_6.

Q-011 asks whether the 2003 VRC impossibility survives two weakenings: Non-Elitism restricted to
the thesis's ranged background ``D subset R(y, x)``, and Dominance Addition replaced by the
thesis's not-worse, single-positive-level-C form.  Phase 19 excluded *translation-invariant*
(lexicographic-linear) orders and left the model route unresolved, concluding that any surviving
model "must be background-dependent".  This phase attacks the two natural background-dependent
families a survivor would have to live in and *excludes both*, for every finite population size
on the ladder and for every admissible choice of the source's own existential witnesses.

**Family S — level-separable count potentials.**
An order ``P ⪰ Q iff S(P) ≥ S(Q)`` with ``S(P) = Σ_v ψ_v(n_v(P))`` where ``ψ_v(0) = 0`` for
every level and ``ψ_0(k) ≥ 0`` for every ``k`` (the neutral anchor: adding neutral lives never
lowers the score).  The potentials at the other levels are arbitrary real functions on ℕ with
value 0 at 0 — capped, concave, convex, linear, or even decreasing — so the family covers
saturating "quota" orders, the natural sub-family of *nondecreasing* count potentials (all capped
potentials, nondecreasing concave/convex potentials, and additive level-weightings with
nonnegative coefficients), and also orders that penalise negative lives or shape any selected
level arbitrarily.  Potentials see only the multiplicity of each level, so a common background is
*not* cancelled once any ``ψ_v`` is nonlinear (a capped ``ψ_v`` makes adding a background change
the marginal value of every further life).  What the family does **not** cover: additive
weightings with a *negative* neutral coefficient (those are translation-invariant and are
excluded separately in research/p19_vrc_translation_invariant.py), and orders that are not
level-separable at all.

THEOREM 1 (all sizes, on W_-1 … W_6).  No member of family S satisfies
``Egalitarian Dominance + ranged Non-Elitism + VRC avoidance``; a fortiori none satisfies any of
the three weakened 2003 sets (each contains these three conditions).

Proof, with the exact witness dependence.  Only the neutral anchor ``ψ_0 ≥ 0`` is used; the
potentials ψ_1 … ψ_6 need not be monotone.
  (1) ED at ``(x, 0)``: ED's instance ``k@W_x`` vs ``k@W_0`` (``x ≥ 1``) is the instance
      ``ladder.instances_over`` generates for ED with background ``∅`` (the ED form has no
      background), and ``research.ladder.audit`` re-derives its decomposition; ED forces
      ``ψ_x(k) > ψ_0(k) ≥ 0``.  Hence ``ψ_x(k) > 0`` for all ``x ≥ 1, k ≥ 1``.
  (2) ranged NE at ``(x, y) = (4, 2)`` with background ``D = J@W_3`` (legal: ``3 ∈ R(2, 4)``).
      The consequent ``C ∪ D ⪰ A ∪ B ∪ D`` separates as
      ``ψ_3(J + n + 1) - ψ_3(J) ≥ ψ_4(1) + ψ_2(n) =: c(n) > 0`` for **every** ``J ≥ 0``, where
      ``n ≥ 1`` is the model's own NE witness.  By (1), ``c(n) > 0`` for every ``n``.
      Iterating the one-step growth gives ``ψ_3(J0 + m·(n+1)) ≥ ψ_3(J0) + m·c(n)``, so ``ψ_3`` is
      unbounded above.
  (3) VRC avoidance with its own witness ``(x < 0, u, v, y, n_V, m_V)``.  On this ladder the
      witness levels are forced: ``R(1, y)`` needs three levels so ``y ≥ 3``; ``R(u, v)`` needs
      three levels so ``u ≤ 4``; ``u > y`` forces ``u = 4, y = 3, v = 6`` and ``x = -1`` is the
      only negative level (``forced_vrc_levels`` enumerates the whole legal level space and finds
      exactly this tuple).  Taking ``B = J@W_3`` inside ``R(1, 3)`` gives
      ``ψ_3(J) ≤ ψ_4(n_V) - ψ_{-1}(m_V) =: B`` for every ``J ≥ 1``: ``ψ_3`` is bounded above.
  (4) Steps (2) and (3) contradict: pick ``m`` with ``m·c(n) > B``; then
      ``B ≥ ψ_3(m(n+1)) ≥ ψ_3(0) + m·c(n) = m·c(n) > B``.
The argument is uniform in the model's witnesses: any ``n ≥ 1`` (step 2) and any ``n_V, m_V ≥ 1``
(step 3) yield the same clash, and the VRC *levels* are forced by the ladder.  ``separable_scan``
replays the three derived facts for concrete potentials, exhibits the smallest audited NE
instance at which a capped/power/quota potential fails, and reports ``m`` and ``J*`` of the
contradiction; no finite search is used as evidence for the theorem.

**Family N — cardinality-normalized (size-normalized) orders, i.e. densities.**
An order ``P ⪰ Q iff F(W(P), |P|) ≥ F(W(Q), |Q|)`` with ``W(P) = Σ_{v ∈ P} h(v)`` for a strictly
increasing ``h`` and ``F`` strictly increasing in its first argument (so comparisons at a fixed
size are comparisons of total welfare, while size may be normalised, penalised or saturated
arbitrarily).  This family contains the average ``W/|P|``, every power density ``W/|P|^θ``, every
critical-level total ``W - c|P|``, and every "density plus size term" order.

THEOREM 2 (all sizes, on W_-1 … W_6).  No member of family N satisfies
``thesis Dominance Addition + VRC avoidance``; a fortiori none satisfies any of the three
weakened 2003 sets.

Proof, with the exact witness dependence (all witnesses are the model's own).
  Let the VRC witness be ``(x0 < 0, u, v, y, n_V, m_V)``; as in (3) the ladder forces
  ``x0 = -1, u = 4, v = 6, y = 3``.  Write ``Υ := F(n_V·h(4), n_V)`` — the score of the VRC
  high population ``n_V@W_4``.
  (a) thesis DA instance ``A = n_V@W_u``, ``B = n_V@W_{u+1}``, ``C = k@W_1`` (``k ≥ 1``;
      ``u + 1 = 5`` is a ladder level, ``C`` is perfectly equal at a positive level, and every
      A-life is below ``W_5`` while every B-life is at it).  Its consequent ``B ∪ C ⪰ A`` reads
      ``F(n_V·h(5) + k·h(1), n_V + k) ≥ Υ``.
  (b) VRC instance with the *same* size ``N := n_V + k``: ``A_V = n_V@W_4``, ``B_V = J@W_3``
      (``J := N - m_V ≥ 1``, legal inside ``R(1, 3)``), ``C_V = m_V@W_{-1}``.  Its consequent
      ``A_V ⪰ B_V ∪ C_V`` reads ``Υ ≥ F(J·h(3) + m_V·h(-1), N)``.
  (c) Choose ``k`` so that the DA-side total welfare is strictly smaller than the VRC-side one:
      ``n_V·h(5) + k·h(1) < (n_V + k - m_V)·h(3) + m_V·h(-1)``.  Since ``h(1) < h(3)`` the left
      minus right side is affine in ``k`` with negative slope and is negative for all large ``k``.
      ``F(·, N)`` is strictly increasing, so (c) gives ``F(DA side) < F(VRC side)``.
  (d) Chaining (a)–(c): ``Υ ≤ F(DA side) < F(VRC side) ≤ Υ`` — a contradiction.
  The dependence is exactly this: DA's ``A`` is the VRC witness population itself, DA's ``C`` is
  the smallest positive level, and the DA-side added block ``n_V@W_5 + k@W_1`` is driven, by
  choosing ``k`` from the VRC witness's ``(y, m_V, x0)``, strictly below the VRC-side block
  ``J@W_3 + m_V@W_-1`` at the shared size ``N``.  ``size_normalized_chain`` builds both audited
  instances, computes the three scores exactly, and asserts that they cannot satisfy DA, VRC and
  strict monotonicity together; ``chain_family_scan`` replays it over a spread of ``h`` and ``F``
  (average, density powers, logarithmic, exponential, affine, saturating, critical-level).

**What is *not* claimed.**  These are family exclusions, not a source-general impossibility: an
order outside both families (for example one that couples levels beyond a total-welfare/size
summary, or a lexicographic or support-based rule) is not touched here — lexicographic-linear
orders are excluded separately in ``research/p19_vrc_translation_invariant.py``.  No positive
model of a weakened set was found, and the finite z3 run in ``reduced_system_search`` is
discovery only and reports its cap.  Nothing here changes the source readings, the source
checker, or any ledger/results artefact.
"""

from __future__ import annotations

import json
import math
from collections import Counter
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

from research.ladder import Witness, audit, validate
from research.p8_catalogue import LADDER
from research.p17_vrc_boundary import DA_THESIS, ED, NE_THESIS, VRC
from research.schema import Instance, Pop

LADDER_LEVELS: tuple[int, ...] = LADDER.levels

# The VRC witness's own level parameters are forced on this ladder (three levels in R(1, y),
# three in R(u, v), u > y, and one negative level).
VRC_X = -1
VRC_U = 4
VRC_V = 6
VRC_Y = 3


def _plus(*parts: Pop) -> Pop:
    return tuple(sorted(v for part in parts for v in part))


def _fmt(pop: Pop) -> str:
    counts = Counter(pop)
    if not counts:
        return "empty"
    return "{" + ", ".join(f"W_{level}^{count}" for level, count in sorted(counts.items())) + "}"


# =============================================================================================
# Theorem 1: level-separable count potentials.


@dataclass(frozen=True)
class SeparableOrder:
    """``P ⪰ Q iff S(P) ≥ S(Q)`` with ``S(P) = Σ_v psi[v](n_v(P))``.

    Required of ``psi``: ``psi[v](0) = 0`` for every level and ``psi[0](k) >= 0`` for every k
    (the neutral anchor used by Theorem 1).  No monotonicity is required at the other levels; the
    scan's candidates instantiate the natural nondecreasing sub-family.  ``formula`` is a short
    human-readable description used in the report.
    """

    name: str
    psi: Mapping[int, Callable[[int], Fraction]]
    formula: str
    note: str = ""

    def score(self, population: Pop) -> Fraction:
        counts = Counter(population)
        return sum((self.psi[v](n) for v, n in counts.items()), Fraction(0))


def _scaled(
    weights: Mapping[int, Fraction], shape: Callable[[int], Fraction]
) -> dict[int, Callable[[int], Fraction]]:
    def scaled(v: int) -> Callable[[int], Fraction]:
        weight = weights[v]

        def psi(t: int) -> Fraction:
            return Fraction(0) if t == 0 else weight * shape(t)

        return psi

    return {v: scaled(v) for v in LADDER_LEVELS}


def level_weights(kind: str = "power") -> dict[int, Fraction]:
    """A strictly increasing positive weight per level; the level order is the only one used."""
    if kind == "power":
        return {v: Fraction(2) ** v for v in LADDER_LEVELS}
    if kind == "linear":
        return {v: Fraction(v + 2) for v in LADDER_LEVELS}
    raise ValueError(kind)


def capped_order(cap: int, kind: str = "power", name: str | None = None) -> SeparableOrder:
    """Saturating/capped count potentials: ``ψ_v(t) = w_v · min(t, cap)``."""
    weights = level_weights(kind)

    def shape(t: int) -> Fraction:
        return Fraction(min(t, cap))

    psi = _scaled(weights, shape)
    return SeparableOrder(
        name or f"capped count potentials (cap={cap}, weights={kind})",
        psi,
        f"S(P) = Σ_v w_v · min(n_v(P), {cap}),  w_v = {kind} level weights",
        "Nonlinear (hence background-sensitive) and saturating: a level's value stops growing.",
    )


def power_order(exponent: Fraction, kind: str = "power", name: str | None = None) -> SeparableOrder:
    """Concave count potentials ``ψ_v(t) = w_v · t^exponent`` (0 < exponent < 1)."""
    weights = level_weights(kind)

    def shape(t: int) -> Fraction:
        # A rational surrogate for t^exponent (exponent = 1/2): floor-based rational upper bound.
        value = float(t) ** float(exponent)
        return Fraction(math.floor(value * 10**6), 10**6)

    psi = _scaled(weights, shape)
    return SeparableOrder(
        name or f"concave count potentials (exponent={exponent}, weights={kind})",
        psi,
        f"S(P) = Σ_v w_v · n_v(P)^{exponent},  w_v = {kind} level weights",
        "Sublinear growth: marginal value of further lives at a level shrinks.",
    )


def quota_order(cap: int, kind: str = "power", name: str | None = None) -> SeparableOrder:
    """A 'quota' order: the count at each level is capped and additionally penalised past it."""
    weights = level_weights(kind)

    def shape(t: int, M: int = cap) -> Fraction:
        return Fraction(min(t, M)) - Fraction(max(0, t - M), 8)

    psi = _scaled(weights, shape)
    return SeparableOrder(
        name or f"capped-with-penalty count potentials (cap={cap}, weights={kind})",
        psi,
        f"S(P) = Σ_v w_v · (min(n_v, {cap}) - max(0, n_v - {cap})/8)",
        "Saturating and then *decreasing* marginals, still nondecreasing overall.",
    )


def additive_order(kind: str = "power", name: str | None = None) -> SeparableOrder:
    """The additive (uncapped) level-weighting: ``ψ_v(t) = w_v · t``.

    Included as the *linear* extreme of the family: it is background-insensitive (and separately
    excluded by the translation-invariant argument in phase 19), and it fails VRC on the witness
    bound rather than the NE step inequality.
    """
    weights = level_weights(kind)
    psi = _scaled(weights, lambda t: Fraction(t))
    return SeparableOrder(
        name or f"additive level weights (weights={kind})",
        psi,
        f"S(P) = Σ_v w_v · n_v(P),  w_v = {kind} level weights",
        "Linear in every count: a common background cancels exactly, so VRC's unbounded B bites.",
    )


def negative_sensitive_order(cap: int = 6, name: str | None = None) -> SeparableOrder:
    """A member that only the broad family admits: ψ_{-1} is *decreasing*.

    ``ψ_{-1}(t) = -3t`` (so a negative life lowers the score) while ψ_0 … ψ_6 are capped.  The
    neutral anchor ψ_0 ≥ 0 still holds, which is all Theorem 1 uses; this candidate shows the
    exclusion is not restricted to potentials that are monotone at every level.
    """
    weights = level_weights("power")

    def shape(t: int) -> Fraction:
        return Fraction(min(t, cap))

    def decreasing(t: int) -> Fraction:
        return Fraction(-3 * t)

    psi = _scaled(weights, shape)
    psi[VRC_X] = decreasing
    return SeparableOrder(
        name or f"arbitrary ψ_-1 (=-3t) with capped ψ_0..ψ_6 (cap={cap})",
        psi,
        f"ψ_-1(t) = -3t (decreasing), ψ_v(t) = w_v · min(t, {cap}) for v >= 0",
        "Covers orders that penalise negative lives arbitrarily; still refuted by ED+NE+VRC.",
    )


def separable_candidates() -> tuple[SeparableOrder, ...]:
    return (
        additive_order(),
        capped_order(4),
        capped_order(8, kind="linear"),
        quota_order(3),
        power_order(Fraction(1, 2)),
        negative_sensitive_order(),
    )


def _ne_step_failure(order: SeparableOrder, n: int, cap: int) -> int | None:
    """First J with ``ψ_3(J+n+1) − ψ_3(J) < c(n)``, or None if none within the cap."""
    psi = order.psi
    c = psi[4](1) + psi[2](n)
    for J in range(0, cap + 1):
        if psi[3](J + n + 1) - psi[3](J) < c:
            return J
    return None


def _vrc_exceedance(
    order: SeparableOrder, n_v: int, m_v: int, cap: int
) -> tuple[Fraction, int | None]:
    """VRC bound ``B = ψ_4(n_V) − ψ_−1(m_V)`` and the first J with ``ψ_3(J) > B``."""
    psi = order.psi
    bound = psi[VRC_U](n_v) - psi[VRC_X](m_v)
    for J in range(1, cap + 1):
        if psi[3](J) > bound:
            return bound, J
    return bound, None


def separable_obstruction(
    order: SeparableOrder, cap: int = 4000, witness_scan: int = 32
) -> dict[str, Any]:
    """Replay Theorem 1's three derived claims for one concrete potential family.

    Claim (i)   ED: ``ψ_x(k) > ψ_0(k) ≥ 0`` for x ≥ 1, hence ``c(n) = ψ_4(1) + ψ_2(n) > 0``.
    Claim (ii)  ranged NE at (4, 2) with background ``J@W_3``: the step inequality
                ``ψ_3(J+n+1) − ψ_3(J) ≥ c(n)`` for **every** J ≥ 0 (hence ``ψ_3`` unbounded).
    Claim (iii) VRC with ``B = J@W_3``: ``ψ_3(J) ≤ ψ_4(n_V) − ψ_−1(m_V) =: B`` for every J ≥ 1.

    The three cannot coexist: if (ii) holds at ``0, n+1, …, m(n+1)`` then
    ``ψ_3(J*) ≥ ψ_3(0) + m·c(n)`` for ``J* = m(n+1)``, and choosing ``m`` with
    ``ψ_3(0) + m·c(n) > B`` contradicts (iii) at ``J*``.  The scan below reports, for each
    candidate, the *most favourable* witness choices (the ``n`` whose step inequality survives
    longest and the ``(n_V, m_V)`` that maximises the VRC bound) together with the audited source
    instance at which the candidate still breaks a claim.
    """
    psi = order.psi
    ed_audited = {
        f"ED k@W_{level} vs k@W_0 (k=1)": audit(ed_instance(level, 1), LADDER, Witness({}))
        for level in (1, 2, 3, 4)
    }

    per_n: dict[str, Any] = {}
    best_n: int | None = None
    best_prefix = -1
    for n in range(1, witness_scan + 1):
        failure = _ne_step_failure(order, n, cap)
        prefix = cap if failure is None else failure
        per_n[str(n)] = {
            "c(n)": str(psi[4](1) + psi[2](n)),
            "first_step_failure_J": failure,
        }
        if prefix > best_prefix:
            best_prefix, best_n = prefix, n
    assert best_n is not None

    c = psi[4](1) + psi[2](best_n)
    bound, bound_j = None, None
    best_pair = (1, 1)
    for n_v in (1, 2, 4):
        for m_v in (1, 2):
            candidate_bound, exceed = _vrc_exceedance(order, n_v, m_v, cap)
            if bound is None or candidate_bound > bound:
                bound, bound_j, best_pair = candidate_bound, exceed, (n_v, m_v)
    assert bound is not None

    step_failure = _ne_step_failure(order, best_n, cap)
    if step_failure is not None:
        inst = ne_instance(4, 2, best_n, step_failure)
        first: dict[str, Any] = {
            "claim": "ranged Non-Elitism (claim ii)",
            "witness": {"non-elitism": {"n": best_n}},
            "J": step_failure,
            "instance": f"{_fmt(inst.args[0])}  vs  {_fmt(inst.args[1])}",
            "audited": audit(inst, LADDER, Witness({"non-elitism": {"n": best_n}})),
            "why": (
                f"ψ_3({step_failure + best_n + 1}) − ψ_3({step_failure}) = "
                f"{psi[3](step_failure + best_n + 1) - psi[3](step_failure)} < c({best_n}) = {c}"
            ),
        }
    elif bound_j is not None:
        n_v, m_v = best_pair
        pair, witness = vrc_instance(n_v, m_v, bound_j)
        first = {
            "claim": "VRC avoidance (claim iii)",
            "witness": dict(witness.params["vrc-avoidance"]),
            "J": bound_j,
            "instance": f"{_fmt(pair.args[0])}  vs  {_fmt(pair.args[1])}",
            "audited": audit(pair, LADDER, witness),
            "why": f"ψ_3({bound_j}) = {psi[3](bound_j)} > B = {bound}",
        }
    else:
        first = {
            "claim": "none within cap",
            "witness": None,
            "J": None,
            "instance": None,
            "audited": None,
            "why": (
                f"claims (ii) and (iii) both hold up to J = {cap} for the scanned witnesses; the "
                "all-size proof still closes because ψ_3 cannot be both unbounded and bounded"
            ),
        }

    joint: dict[str, Any] = {
        "c(n)": str(c),
        "c_strictly_positive": bool(c > 0),
        "B": str(bound),
        "statement": (
            "(i)+(ii)+(iii) are jointly unsatisfiable: VRC bounds ψ_3 above by B while the NE step "
            "repeated m times gives ψ_3(m(n+1)) ≥ ψ_3(0) + m·c(n) > B for large m"
        ),
    }
    if c > 0:
        m_needed = max(1, math.floor(float(bound - psi[3](0)) / float(c)) + 1)
        j_star = m_needed * (best_n + 1)
        joint.update(
            {
                "m": m_needed,
                "J_star": j_star,
                "iteration_lower_bound": str(psi[3](0) + m_needed * c),
                "exceeds_B": psi[3](0) + m_needed * c > bound,
                "within_cap": j_star <= cap,
            }
        )

    return {
        "candidate": order.name,
        "formula": order.formula,
        "nonlinear_note": order.note,
        "ed_positivity_audited": ed_audited,
        "best_ne_witness_n": best_n,
        "ne_step_failure_by_witness": per_n,
        "vrc_bound_B": str(bound),
        "vrc_bound_sizes": {"n_V": best_pair[0], "m_V": best_pair[1]},
        "psi3_first_exceeding_B": bound_j,
        "first_audited_failure": first,
        "joint_unsatisfiability": joint,
        "cap": cap,
        "scope": (
            "arithmetic replay of the proved all-size argument; the cap and the witness scan bound "
            "only the reporting, and each refuted candidate is refuted by one audited source "
            "instance at a stated witness choice"
        ),
    }


def separable_scan() -> dict[str, Any]:
    rows = [separable_obstruction(order) for order in separable_candidates()]
    return {
        "theorem": (
            "No S in family S satisfies ED + ranged NE + VRC avoidance on W_-1..W_6: ED makes "
            "psi_x(k) > 0 (x >= 1); ranged NE at (4,2) with background J@W_3 forces "
            "psi_3(J+n+1) - psi_3(J) >= c(n) > 0 for every J, so psi_3 is unbounded; VRC with "
            "B = J@W_3 forces psi_3(J) <= psi_4(n_V) - psi_-1(m_V) for every J."
        ),
        "family": (
            "S(P) = Σ_v psi_v(n_v(P)) with psi_v(0) = 0 for every level and psi_0(k) >= 0 for "
            "every k (neutral anchor); potentials at the other levels are arbitrary, including "
            "decreasing ones.  The natural nondecreasing sub-family (capped, quota, nondecreasing "
            "concave/convex, additive with nonnegative coefficients) is what the rows instantiate."
        ),
        "not_in_family": (
            "additive weightings with a negative neutral coefficient psi_0 < 0 (translation-"
            "invariant; excluded separately in research/p19_vrc_translation_invariant.py) and "
            "orders not representable by a level-separable score"
        ),
        "all_witness_reasoning": (
            "The NE witness n >= 1 is the model's own choice and c(n) = psi_4(1) + psi_2(n) > 0 "
            "for every n (ED forces psi_4(1) > psi_0(1) and psi_2(n) > psi_0(n), and the neutral "
            "anchor gives psi_0 >= 0, with no monotonicity needed for psi_1..psi_6); the VRC sizes "
            "n_V, m_V >= 1 are the model's own choice and B is finite for every choice; the VRC "
            "levels are forced to (x,u,v,y) = (-1,4,6,3) by the ladder. Whatever witnesses a "
            "member of the family picks, either its psi_3 fails to grow by c(n) at some audited "
            "NE instance or it exceeds B at some audited VRC instance."
        ),
        "audited_instances": {
            "ed": "k@W_x vs k@W_0 for x in 1..4, every k via the family's monotonicity",
            "ne": "(n+1)@W_3 + J@W_3  vs  W_4 + n@W_2 + J@W_3, for every J >= 0",
            "vrc": "n_V@W_4  vs  J@W_3 + m_V@W_-1, for every J >= 1",
        },
        "no_finite_sat_inference": (
            "no row claims consistency from a bounded run: the family is refuted by the proved "
            "impossibility of (i)+(ii)+(iii) together"
        ),
        "rows": rows,
    }


# --- audited source instances used by Theorem 1


def ed_instance(x: int, k: int) -> Instance:
    """ED: ``k`` lives at ``W_x`` against ``k`` lives at the neutral level W_0 (below W_x)."""
    return Instance(ED, ((x,) * k, (0,) * k))


def ne_instance(x: int, y: int, n: int, J: int) -> Instance:
    """Ranged NE at ``(x, y)`` with background ``D = J lives at W_{x-1}``.

    ``left = C ⊎ D`` with ``C = (n+1) lives at W_{x-1}``;
    ``right = A ⊎ B ⊎ D`` with ``A = one W_x`` and ``B = n lives at W_y``.
    """
    left = _plus((x - 1,) * (n + 1), (x - 1,) * J)
    right = _plus((x,), (y,) * n, (x - 1,) * J)
    return Instance(NE_THESIS, (left, right))


def vrc_instance(n_v: int, m_v: int, J: int) -> tuple[Instance, Witness]:
    """VRC with ``B = J lives at W_3`` (legal in ``R(1, 3)``) and ``C = m_v lives at W_{-1}``."""
    left = (VRC_U,) * n_v
    right = _plus((VRC_Y,) * J, (VRC_X,) * m_v)
    witness = Witness(
        {
            "vrc-avoidance": {
                "x": VRC_X,
                "u": VRC_U,
                "v": VRC_V,
                "y": VRC_Y,
                "n": n_v,
                "m": m_v,
            }
        }
    )
    return Instance(VRC, (left, right)), witness


def forced_vrc_levels(ladder: Any = LADDER) -> list[tuple[int, int, int, int]]:
    """Every level quadruple ``(x, u, v, y)`` admissible for VRC on this ladder."""
    legal: list[tuple[int, int, int, int]] = []
    for x in ladder.levels:
        for u in ladder.levels:
            for v in ladder.levels:
                for y in ladder.levels:
                    params = {"x": x, "u": u, "v": v, "y": y, "n": 1, "m": 1}
                    try:
                        validate("vrc-avoidance", ladder, params)
                    except ValueError:
                        continue
                    legal.append((x, u, v, y))
    return legal


# =============================================================================================
# Theorem 2: cardinality-normalized (size-normalized) orders.


@dataclass(frozen=True)
class SizeNormalizedOrder:
    """``P ⪰ Q iff F(W(P), |P|) ≥ F(W(Q), |Q|)`` with ``W(P) = Σ_{v ∈ P} h(v)``."""

    name: str
    h: Callable[[int], Fraction]
    F: Callable[[Fraction, int], Fraction]
    formula: str
    note: str = ""

    def score(self, population: Pop) -> Fraction:
        return self.F(sum((self.h(v) for v in population), Fraction(0)), len(population))


def size_normalized_candidates() -> tuple[SizeNormalizedOrder, ...]:
    def ident(v: int) -> Fraction:
        return Fraction(v)

    def exp_h(v: int) -> Fraction:
        return Fraction(2) ** v - 1

    def log_h(v: int) -> Fraction:
        return Fraction(math.copysign(math.log1p(abs(v)), v)).limit_denominator(10**6) * 10

    def avg(u: Fraction, n: int) -> Fraction:
        return u / n

    def density2(u: Fraction, n: int) -> Fraction:
        return u / (n * n)

    def critical(u: Fraction, n: int) -> Fraction:
        return u - 3 * n

    def logd(u: Fraction, n: int) -> Fraction:
        return u / n - Fraction(math.log(n)).limit_denominator(10**6)

    def saturating(u: Fraction, n: int) -> Fraction:
        return (u / n) / (1 + Fraction(abs(u), n * n))

    def exp_size(u: Fraction, n: int) -> Fraction:
        return u * (1 - Fraction(1, 2 ** min(n, 40)))

    return (
        SizeNormalizedOrder("average (density)", ident, avg, "P ⪰ Q iff W(P)/|P| ≥ W(Q)/|Q|"),
        SizeNormalizedOrder("power density W/|P|²", ident, density2, "W/|P|² ≥ W'/|Q|²"),
        SizeNormalizedOrder(
            "critical-level total W - 3|P|", ident, critical, "W - 3|P| ≥ W' - 3|Q|"
        ),
        SizeNormalizedOrder("density with log size penalty", ident, logd, "W/|P| - log|P|"),
        SizeNormalizedOrder("saturating density", ident, saturating, "(W/|P|)/(1 + |W|/|P|²)"),
        SizeNormalizedOrder("size-boosted total", ident, exp_size, "W·(1 - 2^-min(|P|,40))"),
        SizeNormalizedOrder("exponential level weights, average", exp_h, avg, "Σ(2^v - 1)/|P|"),
        SizeNormalizedOrder(
            "logarithmic level weights, average",
            log_h,
            avg,
            "Σ h(v)/|P| with h(v) = 10·sign(v)·log(1+|v|)",
        ),
    )


def da_thesis_instance(n_v: int, k: int) -> Instance:
    """thesis DA: ``A = n_V@W_4``, ``B = n_V@W_5``, ``C = k@W_1`` (perfectly equal, positive)."""
    A = (VRC_U,) * n_v
    B = (VRC_U + 1,) * n_v
    C = (1,) * k
    return Instance(DA_THESIS, (A, _plus(B, C)))


def size_normalized_chain(
    order: SizeNormalizedOrder, n_v: int = 1, m_v: int = 1, cap: int = 400
) -> dict[str, Any]:
    """Build Theorem 2's two audited instances and test the three-way contradiction.

    The chain is: ``Υ ≤ F(DA side) < F(VRC side) ≤ Υ`` where ``Υ = F(n_V·h(4), n_V)``.
    DA, VRC and strict monotonicity cannot all hold; the report names the violated link.
    """
    x, y, x0 = VRC_U + 1, VRC_Y, VRC_X
    found: tuple[int, Fraction, Fraction, int] | None = None
    for k in range(1, cap + 1):
        J = n_v + k - m_v
        if J < 1:
            continue
        da_side = n_v * order.h(x) + k * order.h(1)
        vrc_side = J * order.h(y) + m_v * order.h(x0)
        if da_side < vrc_side:
            found = (k, da_side, vrc_side, J)
            break
    if found is None:
        return {
            "candidate": order.name,
            "closed": False,
            "cap": cap,
            "reason": "no k <= cap makes the DA side strictly smaller than the VRC side",
        }

    k_found, w_da_side, w_vrc_side, J_found = found
    N = n_v + k_found
    upsilon = order.F(n_v * order.h(VRC_U), n_v)
    da_value = order.F(w_da_side, N)
    vrc_value = order.F(w_vrc_side, N)
    monotone = da_value < vrc_value  # strict increase in total welfare at fixed size N
    da_holds = da_value >= upsilon
    vrc_holds = vrc_value <= upsilon
    # audit both source instances
    da_audited = audit(da_thesis_instance(n_v, k_found), LADDER, Witness({"non-elitism": {"n": 1}}))
    vrc_pair, vrc_witness = vrc_instance(n_v, m_v, J_found)
    vrc_audited = audit(vrc_pair, LADDER, vrc_witness)
    # The k-inequality is affine in k with slope h(1) - h(y) < 0, so it holds for all large k
    # independently of n_V and m_V; the reported k is the smallest one, found by bounded search.
    slope = order.h(1) - order.h(VRC_Y)
    constant = n_v * order.h(VRC_U + 1) - (n_v - m_v) * order.h(VRC_Y) - m_v * order.h(VRC_X)
    return {
        "candidate": order.name,
        "formula": order.formula,
        "witness": {"n_V": n_v, "m_V": m_v, "J": J_found, "k": k_found, "N": N},
        "DA_instance": [_fmt(p) for p in da_thesis_instance(n_v, k_found).args],
        "VRC_instance": [_fmt(p) for p in vrc_pair.args],
        "audited": {"DA": da_audited, "VRC": vrc_audited},
        "witness_value_upsilon": str(upsilon),
        "DA_value": str(da_value),
        "VRC_value": str(vrc_value),
        "strict_monotonicity": (
            f"same size N={N}; DA side total welfare {w_da_side} < VRC side total welfare "
            f"{w_vrc_side}, so F(DA side) < F(VRC side)"
        ),
        "forces": {"DA_needs": "F(DA side) >= Υ", "VRC_needs": "F(VRC side) <= Υ"},
        "general_k_exists": {
            "slope_of_RHS_minus_LHS_in_k": str(-slope),
            "slope_positive": bool(slope < 0),
            "constant_term": str(constant),
            "argument": (
                "n_V·h(5) + k·h(1) - [(n_V+k-m_V)·h(3) + m_V·h(-1)] = constant + k·(h(1)-h(3)); "
                "h(1) < h(3) because h is strictly increasing and 1 < 3, so the difference is "
                "negative for every k above a threshold that depends only on n_V and m_V"
            ),
        },
        "violated_link": (
            "DA" if not da_holds else ("VRC" if not vrc_holds else "none (impossible)")
        ),
        "all_three_hold": bool(da_holds and vrc_holds and monotone),
        "closed": not (da_holds and vrc_holds and monotone),
        "cap": cap,
        "scope": "exact arithmetic on the audited instances; the cap bounds only the k search",
    }


def chain_family_scan(cap: int = 400) -> dict[str, Any]:
    rows = [
        size_normalized_chain(order, n_v, m_v, cap)
        for order in size_normalized_candidates()
        for n_v, m_v in ((1, 1), (2, 3), (3, 1), (4, 5))
    ]
    return {
        "theorem": (
            "No order P ⪰ Q iff F(W(P),|P|) ≥ F(W(Q),|Q|), with h strictly increasing and F "
            "strictly increasing in total welfare, satisfies thesis DA + VRC avoidance on "
            "W_-1..W_6: DA's A is the VRC witness population, and choosing k from the VRC "
            "witness's own (y, m_V, x0) drives the DA side strictly below the VRC side at a "
            "shared size, so Υ ≤ F(DA side) < F(VRC side) ≤ Υ."
        ),
        "forced_witness_levels": [list(t) for t in forced_vrc_levels()],
        "legal_witness_level_count": len(forced_vrc_levels()),
        "first_level_available_x": VRC_U + 1,
        "witness_dependence_dag": [
            "VRC witness levels are forced to (x,u,v,y) = (-1,4,6,3) on this ladder",
            "DA's A population is the VRC witness population n_V@W_4",
            "DA's C is k lives at W_1, the lowest positive level",
            "DA's B is n_V lives at W_5 = W_{u+1}, one level above DA's threshold",
            "k is chosen from the VRC witness's own (y, m_V, x0) so that the DA side sits strictly "
            "below the VRC side at the shared size N",
        ],
        "all_witness_reasoning": (
            "The chain closes for every n_V >= 1 and m_V >= 1: the required k exists by the slope "
            "argument recorded in each row's general_k_exists, so no admissible witness assignment "
            "escapes; the VRC levels cannot be chosen differently on this ladder."
        ),
        "no_finite_sat_inference": (
            "the k search is bounded only for reporting the smallest witness; solvability for all "
            "large k is the affine slope argument, and the exclusion is the strict cycle"
        ),
        "rows": rows,
    }


def reduced_system_search(cap: int = 8, timeout_ms: int = 60_000) -> dict[str, Any]:
    """Discovery only: solve family N's reduced constraint system for one choice of h.

    Variables ``F[u, N]`` for ``1 <= N <= cap`` and ``-N <= u <= 6N``; constraints are strict
    increase in ``u`` at fixed ``N`` (the family's own property, not a source instance), the
    extremal thesis-DA inequalities ``F[n·x + k·y, n+k] >= F[n(x-1), n]`` for every ``n + k <= cap``,
    and the VRC endpoint bounds ``F[3N - 4m_V, N] <= F[4n_V, n_V]`` with h the identity.

    *Every* population pair encoded below is first replayed through ``ladder.audit`` with the
    source readings' own decompositions; instances that fail the audit are dropped and reported,
    so the decision is taken over audited source instances plus the family's monotonicity.  The
    result is still discovery only: the cap truncates it and it is never used as evidence.
    """
    import z3  # type: ignore[import-untyped]

    n_v, m_v = 1, 1
    F = {(u, N): z3.Int(f"F_{u}_{N}") for N in range(1, cap + 1) for u in range(-N, 6 * N + 1)}
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)
    for N in range(1, cap + 1):
        for u in range(-N, 6 * N):
            solver.assert_and_track(F[(u + 1, N)] >= F[(u, N)] + 1, f"mono({u},{N})")
    da_checked = 0
    da_rejected: list[str] = []
    for n in range(1, cap + 1):
        for k in range(1, cap + 1 - n):
            N = n + k
            for x in range(0, 7):
                for y in range(1, 7):
                    # The source instance behind this inequality: A = n@W_(x-1),
                    # B = n@W_x, C = k@W_y, consequent not(A ≻ B ∪ C).
                    pair = (
                        ((x - 1,) * n),
                        tuple(sorted((x,) * n + (y,) * k)),
                    )
                    if not audit(Instance(DA_THESIS, pair), LADDER, Witness({})):
                        da_rejected.append(f"x={x},y={y},n={n},k={k}")
                        continue
                    da_checked += 1
                    solver.assert_and_track(
                        F[(n * x + k * y, N)] >= F[(n * (x - 1), n)],
                        f"DA(n={n},k={k},x={x},y={y})",
                    )
    vrc_checked = 0
    vrc_rejected: list[str] = []
    for N in range(m_v + 1, cap + 1):
        u = 3 * N - 4 * m_v
        if u < -N:
            continue
        vrc_pair, vrc_witness = vrc_instance(n_v, m_v, N - m_v)
        if not audit(vrc_pair, LADDER, vrc_witness):
            vrc_rejected.append(f"N={N}")
            continue
        vrc_checked += 1
        solver.assert_and_track(F[(u, N)] <= F[(4 * n_v, n_v)], f"VRC(N={N})")
    decision = str(solver.check())
    core = sorted(str(c) for c in solver.unsat_core()) if decision == "unsat" else []
    return {
        "cap": cap,
        "h": "identity",
        "witness_sizes": {"n_V": n_v, "m_V": m_v},
        "audited_da_instances_encoded": da_checked,
        "rejected_da_instances": da_rejected[:8],
        "rejected_da_instance_count": len(da_rejected),
        "audited_vrc_instances_encoded": vrc_checked,
        "rejected_vrc_instances": vrc_rejected[:8],
        "decision": decision,
        "unsat_core": core,
        "scope": (
            "discovery only: truncated system (cap), one h, fixed witness sizes; every encoded "
            "instance is ladder-audited source content, but the decision is not evidence"
        ),
    }


# =============================================================================================
# Report.


def run() -> dict[str, Any]:
    separable = separable_scan()
    normalized = chain_family_scan()
    discovery = reduced_system_search(cap=8)
    rows_ok = all(row["closed"] for row in normalized["rows"])
    return {
        "route": "B (positive-model route: nonlinear cardinality-normalized / level-separable saturating orders)",
        "approach": (
            "Two families a background-dependent survivor of the weakened 2003 sets could live in "
            "are reduced to exact witness-dependent inequalities and excluded: (S) level-separable "
            "count potentials S(P) = Σ_v ψ_v(n_v(P)); (N) size-normalized orders "
            "P ⪰ Q iff F(Σ_v h(v), |P|) ≥ F(Σ_v h(v), |Q|)."
        ),
        "scope": (
            "ladder W_-1..W_6 (research/p8_catalogue.LADDER), every finite population size, every "
            "admissible choice of the model's own existential witnesses; source instances audited "
            "with research/ladder.audit; no source reading or checker is altered"
        ),
        "verdict": "proved",
        "evidence": {
            "theorem_1_level_separable": separable,
            "theorem_2_cardinality_normalized": normalized,
            "discovery_search": discovery,
            "audit_machinery": (
                "research.ladder.audit re-derives each instance's decomposition from its "
                "populations alone; every NE/VRC/DA/ED instance used here is audited in "
                "separable_obstruction and size_normalized_chain"
            ),
            "consistency_of_report": rows_ok,
            "no_finite_sat_used_as_consistency": (
                "reduced_system_search is labelled discovery, reports its cap, and audits every "
                "population pair it encodes (its rejected-instance lists are reported and dropped "
                "before solving); the theorems are the symbolic arguments in the theorem strings"
            ),
        },
        "remaining_obligation": (
            "A positive model of a weakened 2003 set must lie outside both excluded families: it "
            "must couple levels beyond a total-welfare/size summary (family N) and beyond per-level "
            "counts (family S), and it must not be a translation-invariant lexicographic-linear "
            "order (research/p19_vrc_translation_invariant.py). No such model was found here, and "
            "the exclusion of these two families is not a source-general impossibility."
        ),
    }


def main() -> None:
    print(json.dumps(run(), indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
