"""Route B component check: no translation-invariant order satisfies Q-011's weakened set.

Q-011's three weakened variants replace 2003 Non-Elitism by the thesis's ranged form and/or 2003
Dominance Addition by the thesis's not-worse, single-level-C form. This module decides one
structural question about the model route: can any *translation-invariant* axiology satisfy the
weakest variant {Egalitarian Dominance, ranged Non-Elitism, GNEP, VRC avoidance, thesis Dominance
Addition} on the ladder W_−1 … W_6?

Translation-invariant total preorders on level-count vectors are exactly the lexicographic orders
given by a basis of linear functionals (the standard ordered-abelian-group fact), so additive
orders and lexicographic-linear count-first orders are covered, but background-sensitive tie-breaks
are not.
The module answers it by writing down, for the first functional ``phi_1``, the conditions each
source condition *forces* on its coefficients, and asking z3 for a non-zero solution.

Every constraint below is a NECESSARY condition on ``phi_1``, so a joint UNSAT is a valid
exclusion; the direction matters and no strengthening of a premise is used:

* Egalitarian Dominance is a strict requirement, so ``phi_1`` only has to not point the wrong way:
  ``k`` lives at ``W_x`` against ``k`` lives strictly below forces ``a[x] >= a[l]`` for ``l < x``.
* VRC avoidance's ``B`` is unconstrained in size (corpus/readings.toml, ``vrc-avoidance``: "N(B) is
  unconstrained, so B may be arbitrarily large"), so ``phi_1(e_w) <= 0`` on ``R(1, y_V)``; its
  added group is exactly ``m_V`` lives at the negative level and its high population exactly ``n_V``
  lives at every level ``z >= u_V``.
* thesis Dominance Addition's ``C`` is a single positive level of any size, so ``phi_1(e_y) >= 0``
  for every positive ``y``.
* GNEP's ``B`` has EXACTLY ``n(z)`` lives ("N(A)=N(B)=n"), so only the worst such ``B`` enters; the
  requirement is ``n*phi_1(e_x) + phi_1(e_z) - phi_1(e_{z+1}) - n*max{phi_1(e_w) : w in R(1,y(z))}
  >= 0`` for every ``x >= u(z)``, with ``(u, y, n)`` chosen per ``z`` and ``n >= 1``.
* ranged Non-Elitism requires some ``n >= 1`` with
  ``n(a[x-1] - a[y]) + a[x-1] - a[x] >= 0``. For an integer slope this means:
  positive slope (eventually), zero slope with nonnegative intercept, or negative slope with
  the inequality already true at ``n=1``.

The coefficient contradiction also has a short direct proof. DA makes every positive coefficient
nonnegative. VRC's arbitrarily large low-positive bag makes coefficients 1, 2 and 3 nonpositive,
so those three vanish. NE at (x,y)=(4,1),(5,1),(6,1) successively makes coefficients 4, 5
and 6 nonpositive, hence zero. ED puts the neutral coefficient at most zero and the negative
one at most the neutral coefficient. GNEP at z=0 puts the neutral coefficient at least zero;
GNEP at z=-1 puts the negative coefficient at least the neutral one. Thus every coefficient
vanishes, contradicting a nonzero first functional, regardless of the existential witness sizes.

Scope: the result is ladder-relative and excludes lexicographic-linear, translation-invariant
relations. It is NOT a proof that no axiology satisfies the weakened set: a surviving model
would have to be background-dependent. The control run shows that the necessary-coefficient
system becomes satisfiable when VRC avoidance's size-unconstrained B premise is removed.
"""

from __future__ import annotations

import z3  # type: ignore[import-untyped]

from research.p8_catalogue import LADDER

LEVELS: tuple[int, ...] = LADDER.levels
POSITIVE: tuple[int, ...] = tuple(level for level in LEVELS if level > 0)


def _coefficients(tag: str) -> dict[int, z3.ArithRef]:
    return {level: z3.Int(f"a_{tag}_{level}") for level in LEVELS}


def first_functional_system(vrc_unbounded_b: bool = True, timeout_ms: int = 300_000) -> z3.Solver:
    """The necessary conditions on the first functional of a translation-invariant order."""
    tag = "ub" if vrc_unbounded_b else "bounded"
    a = _coefficients(tag)
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    solver.add(z3.Or(*[a[level] != 0 for level in LEVELS]))

    # VRC avoidance: witnesses are the axiology's own; x_V = -1 is the ladder's only negative level.
    u_v, y_v = z3.Ints(f"u_v_{tag} y_v_{tag}")
    n_v, m_v = z3.Ints(f"n_v_{tag} m_v_{tag}")
    solver.add(u_v >= 4, u_v <= 6, y_v >= 3, y_v < u_v, n_v >= 1, m_v >= 1)
    if vrc_unbounded_b:
        for level in LEVELS:
            solver.add(z3.Implies(level >= 1, z3.Implies(level <= y_v, a[level] <= 0)))
    for z in range(2, 7):
        solver.add(z3.Implies(z >= u_v, n_v * a[z] - m_v * a[-1] >= 0))

    # thesis Dominance Addition: one positive level of arbitrary size.
    for level in POSITIVE:
        solver.add(a[level] >= 0)

    # GNEP: B has exactly n lives, so only its worst case of size n enters the requirement.
    for z in range(-1, 6):
        branches = []
        for u in (4, 5, 6):
            for y in range(3, u):
                n = z3.Int(f"n_{tag}_{z}_{u}_{y}")
                worst = z3.Int(f"w_{tag}_{z}_{u}_{y}")
                branches.append(
                    z3.And(
                        n >= 1,
                        *[worst >= a[level] for level in range(1, y + 1)],
                        *[n * a[x] + a[z] - a[z + 1] - n * worst >= 0 for x in LEVELS if x >= u],
                    )
                )
        solver.add(z3.Or(*branches))

    # Ranged Non-Elitism: the n>=1 linear inequality has an integer solution exactly
    # when a positive slope eventually wins, a zero slope has nonnegative intercept,
    # or a negative slope already works at n=1.
    for x in LEVELS:
        for y in LEVELS:
            if x - 1 > y:
                slope = a[x - 1] - a[y]
                intercept = a[x - 1] - a[x]
                solver.add(
                    z3.Or(
                        slope > 0,
                        z3.And(slope == 0, intercept >= 0),
                        z3.And(slope < 0, slope + intercept >= 0),
                    )
                )

    # Egalitarian Dominance, necessary form.
    for x in LEVELS:
        for lower in LEVELS:
            if lower < x:
                solver.add(a[x] >= a[lower])
    return solver


def decide(vrc_unbounded_b: bool = True) -> str:
    """'unsat' excludes the translation-invariant class; 'sat' would exhibit a coefficient vector."""
    return str(first_functional_system(vrc_unbounded_b=vrc_unbounded_b).check())


def main() -> None:
    excluded = decide(vrc_unbounded_b=True)
    control = decide(vrc_unbounded_b=False)
    if excluded != "unsat":
        raise AssertionError(f"expected the translation-invariant class to be excluded: {excluded}")
    if control != "sat":
        raise AssertionError(f"expected the control without VRC's unbounded B to be sat: {control}")
    print(
        "No translation-invariant order satisfies {Egalitarian Dominance, ranged Non-Elitism, "
        "GNEP, VRC avoidance, thesis Dominance Addition} on the ladder: the necessary coefficient "
        "system for its first functional is UNSAT. Without VRC avoidance's size-unconstrained B the "
        "same necessary system is SAT; that control is not a model. Scope: ladder-relative, and "
        "it excludes the translation-invariant class only; a surviving model must be "
        "background-dependent."
    )


if __name__ == "__main__":
    main()
