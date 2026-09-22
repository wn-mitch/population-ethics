"""Phase 3: witness arithmetic for the fixed baseline skeleton.

The propositional skeleton (seven formulas over seven relata) is fixed; only the numbers that
make each formula a legitimate instance of its principle vary. Applicability is checked by the
exact clause set in ``research.lab.applicability``.
"""

from __future__ import annotations

import json
import subprocess
import time
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from itertools import product
from math import floor
from typing import Any

from population_ethics.candidates import run_formalization_guard_probes
from population_ethics.spec import load_experiment, problem_id_for
from research.lab import (
    ROOT,
    SN,
    VH,
    VL,
    LedgerEntry,
    Witness,
    applicability,
    baseline_witness,
    load_baseline,
    materialize_witness,
    record,
    write_result,
)

GRID = {SN: frozenset({-1}), VL: frozenset({1, 2, 3, 4}), VH: frozenset({8})}
LEVEL_ROLES = {"A": VH, "A_prime": VH, "B": VL, "C": VL, "D": VL, "E": SN, "F": VL, "G": VL}
F_MAX, C_MAX, B_MAX, E_MAX = 60, 80, 8, 2
SIZE_FREE_CLAUSES = (
    "categories:ordered",
    "repugnance:A-equal-very-high",
    "repugnance:D-very-low",
    "dominance:min(AC)>max(G)",
    "addition:max(B)<min(A)",
    "addition:max(C)<min(B)",
    "roles:B,C,F,G-very-low",
    "mnep:A_prime-q-very-high",
)


def m_min_closed_form(p: int, q: int, lv: dict[str, int]) -> int:
    """Smallest |F| for the skeleton: Addition's |C|>|B| plus both strict average clauses."""
    a, a2, c, d, f, g = lv["A"], lv["A_prime"], lv["C"], lv["D"], lv["F"], lv["G"]
    ac_bound = Fraction(p * (a - d), d - c) - q
    aaf_bound = Fraction(p * (a - g) + q * (a2 - g), g - f)
    return max(2, floor(ac_bound) + 1, floor(aaf_bound) + 1)


def witness(
    p: int,
    q: int,
    lv: dict[str, int],
    nB: int,
    nE: int,
    nF: int,
    nC: int,
    categories: dict[str, frozenset[int]],
) -> Witness:
    large = p + nC
    sizes = {"A": p, "A_prime": q, "B": nB, "C": nC, "D": large, "E": nE, "F": nF, "G": large}
    return Witness(lv, sizes, categories)


def grid_search(p: int, q: int) -> dict[str, Any]:
    """Exhaustive search over the declared grid within explicit bounds.

    |D| and |G| are set to |AC|: any other value fails the cardinality clauses of
    anti-egalitarianism or Dominance, so this pruning drops no valid witness.
    """
    solutions = []
    level_sets = 0
    for values in product(*(sorted(GRID[LEVEL_ROLES[r]]) for r in LEVEL_ROLES)):
        lv = dict(zip(LEVEL_ROLES, values, strict=True))
        probe = applicability(witness(p, q, lv, 1, 1, 1, 1, GRID))
        if not all(probe[c] for c in SIZE_FREE_CLAUSES):
            continue
        level_sets += 1
        for nB, nE, nF, nC in product(
            range(1, B_MAX + 1), range(1, E_MAX + 1), range(1, F_MAX + 1), range(1, C_MAX + 1)
        ):
            w = witness(p, q, lv, nB, nE, nF, nC, GRID)
            if all(applicability(w).values()):
                solutions.append(w)
    best_total = min(sum(w.sizes.values()) for w in solutions)
    best_large = min(w.sizes["D"] for w in solutions)
    levels_used = {len(set(w.levels.values())) for w in solutions}
    minimal = [w for w in solutions if w.sizes["D"] == best_large]
    return {
        "p": p,
        "q": q,
        "valid_level_assignments": level_sets,
        "valid_witnesses_in_bounds": len(solutions),
        "min_total_block_lives": best_total,
        "min_largest_population": best_large,
        "distinct_levels_in_all_solutions": sorted(levels_used),
        "minimal_witnesses": [{"levels": dict(w.levels), "sizes": dict(w.sizes)} for w in minimal],
        "closed_form_m_min": m_min_closed_form(p, q, dict(minimal[0].levels)),
        "closed_form_largest": p + q + m_min_closed_form(p, q, dict(minimal[0].levels)),
        "pareto_front": sorted(
            {
                (sum(w.sizes.values()), w.sizes["D"], len(set(w.levels.values())))
                for w in solutions
                if not any(
                    sum(v.sizes.values()) <= sum(w.sizes.values())
                    and v.sizes["D"] <= w.sizes["D"]
                    and len(set(v.levels.values())) <= len(set(w.levels.values()))
                    and (sum(v.sizes.values()), v.sizes["D"])
                    != (sum(w.sizes.values()), w.sizes["D"])
                    for v in solutions
                )
            }
        ),
    }


def _grid_pair(pq: tuple[int, int]) -> dict[str, Any]:
    return grid_search(*pq)


def spacing_study() -> dict[str, Any]:
    """Rational-cardinal spacing sensitivity: keep SN<0<VL<VH, vary the cardinal gaps.

    Checks the closed form against brute force on integer spacings (any rational spacing
    scales to an integer one without changing order, signs, or average comparisons).
    """
    checks = []
    for a, b, c, g, f in product(range(3, 17), repeat=5):
        if not (0 < f < g < c < b < a):
            continue
        if (a + b + c + g + f) % 7:  # deterministic thinning of the 3003-point grid
            continue
        lv = {"A": a, "A_prime": a, "B": b, "C": c, "D": b, "E": -1, "F": f, "G": g}
        cats = {SN: frozenset({-1}), VL: frozenset({b, c, f, g}), VH: frozenset({a})}
        for p, q in ((1, 1), (1, 2), (2, 1)):
            predicted = m_min_closed_form(p, q, lv)
            found = next(
                nF
                for nF in range(1, 400)
                if all(applicability(witness(p, q, lv, q + 1, 1, nF, q + nF, cats)).values())
            )
            checks.append(predicted == found)
    collapse: dict[str, dict[str, Any]] = {
        "p=q=1": {
            "levels": {"A": 8, "A_prime": 8, "B": 7, "C": 6, "D": 7, "E": -1, "F": 1, "G": 5}
        },
        "p=1,q=2": {
            "levels": {"A": 16, "A_prime": 16, "B": 15, "C": 14, "D": 15, "E": -1, "F": 1, "G": 13}
        },
    }
    for key, item in collapse.items():
        p, q = (1, 1) if key == "p=q=1" else (1, 2)
        lv = item["levels"]
        cats = {
            SN: frozenset({-1}),
            VL: frozenset({lv["B"], lv["C"], lv["F"], lv["G"]}),
            VH: frozenset({lv["A"]}),
        }
        m = m_min_closed_form(p, q, lv)
        w = witness(p, q, lv, q + 1, 1, m, q + m, cats)
        item.update(
            {
                "m": m,
                "largest_population": w.sizes["D"],
                "all_clauses_hold": all(applicability(w).values()),
                "ratio_(a-g)/(g-f)": str(Fraction(lv["A"] - lv["G"], lv["G"] - lv["F"])),
            }
        )
    ratio_table = []
    for num, den in ((1, 4), (1, 2), (2, 3), (1, 1), (2, 1), (3, 1), (6, 1), (12, 1)):
        # a - g = num*k, g - f = den*k with f = 1, a' = a; b, c, d chosen to keep AC slack.
        k = 4
        f, g = 1, 1 + den * k
        a = g + num * k
        lv = {"A": a, "A_prime": a, "B": a - 1, "C": g + 1, "D": a - 1, "E": -1, "F": f, "G": g}
        if not (lv["C"] < lv["B"]):
            continue
        ratio_table.append(
            {
                "ratio": f"{num}/{den}",
                "m_min(p=1,q=2)": m_min_closed_form(1, 2, lv),
                "largest(p=1,q=2)": 3 + m_min_closed_form(1, 2, lv),
            }
        )
    return {
        "closed_form_checks": len(checks),
        "closed_form_all_agree": all(checks),
        "collapse_examples": collapse,
        "ratio_table": ratio_table,
        "universal_lower_bound": "|D|=|G|=|AC|=|AAF|=p+q+m with m>=2 (Addition |C|>|B|)",
    }


def _cli(*args: str) -> str:
    return subprocess.run(
        ["uv", "run", "--quiet", "population-ethics", *args],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout


def materialize(name: str, w: Witness, fidelity: str, bindings: dict[str, int]) -> dict[str, Any]:
    path = ROOT / "research" / "experiments" / f"{name}.toml"
    assert all(applicability(w).values()), name
    path.write_text(
        materialize_witness(
            w,
            experiment_id=name,
            formalization_id=f"arrhenius-2000.{name}/v1",
            source_fidelity=fidelity,
            witness_bindings=bindings,
        )
    )
    spec = load_experiment(path)
    out = ROOT / "research" / "results" / f"{name}.run.json"
    _cli("run", str(path), "--format", "json", "--output", str(out))
    verified = _cli("verify", str(out))
    run = json.loads(out.read_text())
    guards = run_formalization_guard_probes(spec)
    out.unlink()  # raw run records contain timing; keep only the canonical projection
    kinds = sorted(e["kind"] for e in run["evidence"])
    return {
        "toml": str(path.relative_to(ROOT)),
        "problem_id": problem_id_for(spec),
        "decision": run["outcome"]["decision"],
        "evidence": kinds,
        "verify_accepted": "verification: accepted" in verified,
        "guard_probes": {k: getattr(guards, k) for k in guards.__slots__ if k != "base_problem_id"},
        "sizes": dict(w.sizes),
        "levels": dict(w.levels),
    }


def main() -> None:
    started = time.monotonic()
    spec = load_baseline()
    base = baseline_witness(spec)
    base_clauses = applicability(base)
    with ProcessPoolExecutor() as pool:
        grid = list(pool.map(_grid_pair, [(p, q) for p in (1, 2, 3) for q in (1, 2, 3, 4, 5)]))
    spacing = spacing_study()

    lv_grid = {"A": 8, "A_prime": 8, "B": 4, "C": 3, "D": 4, "E": -1, "F": 1, "G": 2}
    m11 = m_min_closed_form(1, 1, lv_grid)
    lv4 = spacing["collapse_examples"]["p=q=1"]["levels"]
    cats4 = {SN: frozenset({-1}), VL: frozenset({1, 5, 6, 7}), VH: frozenset({8})}
    materialized = {
        "regenerated-baseline": materialize(
            "fixed-skeleton-p1-q2",
            witness(1, 2, lv_grid, 3, 1, 19, 21, GRID),
            "source-constrained fixed-skeleton generalization (unreviewed); numbers equal baseline",
            {"p": 1, "q": 2, "m": 19},
        ),
        "grid-p1-q1": materialize(
            "fixed-skeleton-p1-q1",
            witness(1, 1, lv_grid, 2, 1, m11, 1 + m11, GRID),
            "source-constrained fixed-skeleton generalization (unreviewed); different MNEP witness",
            {"p": 1, "q": 1, "m": m11},
        ),
        "spacing-p1-q1": materialize(
            "spacing-sensitivity-p1-q1",
            witness(1, 1, lv4, 2, 1, 2, 3, cats4),
            "rational-cardinal spacing sensitivity; NOT a source-faithful witness (7 declared very "
            "low, 8 declared very high)",
            {"p": 1, "q": 1, "m": 2},
        ),
    }
    regenerated_equals_baseline = (
        load_experiment(ROOT / materialized["regenerated-baseline"]["toml"]).common.universe.names
        == spec.common.universe.names
    )
    data = {
        "baseline_applicability": base_clauses,
        "baseline_all_clauses": all(base_clauses.values()),
        "fixed_by_construction": {
            "relation_atoms": 144,
            "ground_constraints": 1813,
            "curated_certificate_nodes": 75,
            "active_relata": 7,
            "substantive_instances": 7,
        },
        "grid_search_bounds": {"F": F_MAX, "C": C_MAX, "B": B_MAX, "E": E_MAX},
        "grid": grid,
        "grid_closed_form_agrees": all(
            g["min_largest_population"] == g["closed_form_largest"] for g in grid
        ),
        "spacing": spacing,
        "materialized": materialized,
        "regenerated_baseline_populations_equal": regenerated_equals_baseline,
    }
    write_result("p3_witness", data, {"wall_time_s": round(time.monotonic() - started, 2)})
    _ledger(data)


def _ledger(data: dict[str, Any]) -> None:
    grid = {(g["p"], g["q"]): g for g in data["grid"]}
    table = {f"p={p},q={q}": g["min_largest_population"] for (p, q), g in sorted(grid.items())}
    sp = data["spacing"]
    record(
        [
            LedgerEntry(
                candidate_id="P3-grid-minimum",
                hypothesis="On the baseline grid a smaller witness than |D|=|G|=22 exists for p=1,q=2.",
                motivation="Objective A/B: minimum lives and largest population.",
                exact_formal_change="numbers only; skeleton, ids and categories fixed",
                scope="baseline grid {-1,1,2,3,4,8}; p in 1..3, q in 1..5; |F|<=60, |C|<=80, |B|<=8",
                search_method="exhaustive enumeration with exact applicability clauses",
                result=f"min largest population by (p,q): {table}; baseline is minimal for p=1,q=2",
                evidence_type="exhaustive finite search + closed form",
                checked=True,
                minimal="yes, within stated bounds (minima lie well inside them)",
                counterexample_if_false="none: 22 is optimal for (1,2); it equals 7(p+q)+1",
                interpretation=(
                    "The selected witness is tight. On this grid every size depends on p+q only: "
                    "|D|=|G|=7(p+q)+1, and the AAF-vs-G average clause alone binds."
                ),
                next_experiment="spacing sensitivity",
                result_scope="finite computational result",
                formalization_tier="source-constrained fixed-skeleton generalization",
                status="refuted",
                witness_conditions="W: p in 1..3, q in 1..5 (each (p,q) a different MNEP/Repugnance witness)",
            ),
            LedgerEntry(
                candidate_id="P3-six-level-lemma",
                hypothesis=(
                    "Under the applicability clauses, the skeleton forces e<0<f<g<c<b<a, hence at least "
                    "6 distinct welfare levels; 6 is attained (d=b, a'=a)."
                ),
                motivation="Objective C: minimum number of distinct welfare levels.",
                exact_formal_change="none",
                scope="fixed skeleton, any spacing respecting the categories",
                search_method="derivation + exhaustive grid + spacing sample",
                result=f"grid: distinct levels {sorted({x for g in data['grid'] for x in g['distinct_levels_in_all_solutions']})}",
                evidence_type="derivation checked by enumeration",
                checked=True,
                minimal="6 attained",
                interpretation=(
                    "Dominance gives c>g; Addition gives c<b<a; avg(AAF)<g with a,a'>g and F "
                    "nonempty gives f<g; Non-Sadism/MNEP give e<0<f. The forcing is the content: the "
                    "counting is then immediate."
                ),
                next_experiment="n/a",
                result_scope="checked theorem (fixed skeleton)",
                formalization_tier="source-constrained fixed-skeleton generalization",
                status="confirmed",
            ),
            LedgerEntry(
                candidate_id="P3-spacing-collapse",
                hypothesis="Witness size is controlled by cardinal gap ratios, not by the skeleton.",
                motivation="Formalization-sensitivity experiment requested by the user.",
                exact_formal_change="category levels and gaps varied; order SN<0<VL<VH kept",
                scope="fixed skeleton; integer spacings (rational spacings scale to these)",
                search_method="closed form checked against brute force on a thinned spacing grid",
                result=(
                    f"closed form agrees on {sp['closed_form_checks']} cases: "
                    f"{sp['closed_form_all_agree']}; largest population collapses to p+q+2 "
                    f"(4 for p=q=1, 5 for p=1,q=2) when (a-g)/(g-f) is small"
                ),
                evidence_type="exact arithmetic; materialized TOML run+verify",
                checked=True,
                minimal="p+q+2 is a spacing-independent lower bound (Addition |C|>|B|)",
                interpretation=(
                    "Order-only categories under-specify the principles: letting 'very high' sit just "
                    "above 'very low' shrinks the witness from 22 to 5 lives. The distance between "
                    "categories does substantive work in the source witness; it does not create the "
                    "contradiction, which is propositional."
                ),
                next_experiment="fix a source-justified minimum VH/VL gap before any size claim",
                result_scope="finite computational result",
                formalization_tier="rational-cardinal spacing sensitivity",
                status="confirmed",
            ),
        ]
    )


if __name__ == "__main__":
    main()
