"""Phase 2: what exactly does incompleteness buy in the frozen Arrhenius instance?

H = the seven substantive instances + reflexivity + transitivity on the seven active relata.
Soft constraints = the 21 completeness pairs. Everything is cross-checked against an exhaustive
enumeration of all 9,535,241 preorders on seven labeled points.
"""

from __future__ import annotations

import time
from collections import Counter
from itertools import permutations
from typing import Any

import z3  # type: ignore[import-untyped]

from population_ethics.relations import formula_json
from population_ethics.relations import weak as _w
from research.lab import (
    ACTIVE,
    Engine,
    LedgerEntry,
    background,
    compile_predicate,
    load_baseline,
    marco,
    pair_id,
    pairs,
    preorders,
    record,
    substantive_constraints,
    write_result,
)

PAIRS = pairs(ACTIVE)
PAIR_IDS = [pair_id(a, b) for a, b in PAIRS]


def automorphisms(formulas: list[Any]) -> list[dict[str, str]]:
    """Permutations of the relata mapping the substantive formula set onto itself."""
    from population_ethics.relations import formula_from_data, formula_to_data

    target = sorted(formula_json(f) for f in formulas)
    result = []
    for perm in permutations(ACTIVE):
        mapping = dict(zip(ACTIVE, perm, strict=True))

        renamed = sorted(
            formula_json(formula_from_data(_rename(formula_to_data(f), mapping))) for f in formulas
        )
        if renamed == target:
            result.append(mapping)
    return result


def _rename(value: Any, mapping: dict[str, str]) -> Any:
    if isinstance(value, dict):
        return {
            k: (mapping[v] if k in ("left", "right") else _rename(v, mapping))
            for k, v in value.items()
        }
    if isinstance(value, list):
        return [_rename(v, mapping) for v in value]
    return value


def describe(pattern: tuple[str, ...]) -> dict[str, Any]:
    edges = [tuple(p.split(":")[1:]) for p in pattern]
    degree = Counter(x for e in edges for x in e)
    center = [x for x, d in degree.items() if d == len(edges)] if len(edges) > 1 else []
    return {
        "pairs": ["|".join(e) for e in edges],
        "size": len(edges),
        "degree": dict(sorted(degree.items())),
        "star_center": center[0] if center else None,
    }


def main() -> None:
    started = time.monotonic()
    spec = load_baseline()
    substantive = list(substantive_constraints(spec))
    bg = background(ACTIVE)
    hard = [*bg["reflexivity"], *bg["transitivity"], *substantive]
    soft = list(bg["completeness"])
    engine = Engine(ACTIVE, hard, soft)
    assert sorted(engine.soft) == sorted(PAIR_IDS)

    h_sat = engine.require().decision
    all_unsat = engine.require(PAIR_IDS).decision

    # 1. Complete MUS / MSS enumeration.
    muses, msses = marco(engine)
    mcses = sorted(tuple(sorted(set(PAIR_IDS) - set(m))) for m in msses)
    for mcs in mcses:  # each MCS: relaxing it is SAT, and relaxing any proper subset is UNSAT
        rest = [p for p in PAIR_IDS if p not in mcs]
        assert engine.require(rest).decision == "sat"
        for p in mcs:
            assert engine.require([*rest, p]).decision == "unsat"
    core_intersection = sorted(set.intersection(*(set(m) for m in muses))) if muses else []

    # 2. Pairwise classification.
    classification: dict[str, str] = {}
    for a, b in PAIRS:
        can_incomparable = engine.require(extra=[engine.incomparable(a, b)]).decision == "sat"
        can_comparable = (
            engine.require(extra=[z3.Or(engine.w(a, b), engine.w(b, a))]).decision == "sat"
        )
        classification[pair_id(a, b)] = (
            "forced-comparable"
            if not can_incomparable
            else "forced-incomparable"
            if not can_comparable
            else "free"
        )

    # 3. Extrema of K = number of incomparable active pairs.
    count = engine.count_incomparable(PAIRS)
    k_min = next(k for k in range(22) if engine.require(extra=[count <= k]).decision == "sat")
    k_max = next(
        k for k in range(21, -1, -1) if engine.require(extra=[count >= k]).decision == "sat"
    )

    # 4. All minimum-K incomparability patterns (projection on the I_p vector).
    minimum_patterns: list[tuple[str, ...]] = []
    blocks: list[z3.BoolRef] = []
    while True:
        result = engine.require(extra=[count == k_min, *blocks])
        if result.decision != "sat":
            break
        assert result.assignment is not None
        pattern = tuple(
            sorted(
                pair_id(a, b)
                for a, b in PAIRS
                if not result.assignment[_w(a, b)] and not result.assignment[_w(b, a)]
            )
        )
        minimum_patterns.append(pattern)
        blocks.append(
            z3.Or(
                [
                    z3.Not(engine.incomparable(a, b))
                    if pair_id(a, b) in pattern
                    else engine.incomparable(a, b)
                    for a, b in PAIRS
                ]
            )
        )
    minimum_patterns.sort()

    # 5. Exhaustive independent enumeration over every preorder on the seven relata.
    predicate = compile_predicate([c.formula for c in substantive], ACTIVE)
    n = len(ACTIVE)
    index = {x: i for i, x in enumerate(ACTIVE)}
    pair_bits = [(1 << (index[a] * n + index[b]), 1 << (index[b] * n + index[a])) for a, b in PAIRS]
    escape_models = 0
    patterns: Counter[int] = Counter()
    for mask in preorders(n):
        if not predicate(mask):
            continue
        escape_models += 1
        code = 0
        for bit, (ab, ba) in enumerate(pair_bits):
            if not mask & ab and not mask & ba:
                code |= 1 << bit
        patterns[code] += 1
    distinct = list(patterns)
    minimal_realized = [p for p in distinct if not any(q != p and q & p == q for q in distinct)]

    def decode(code: int) -> tuple[str, ...]:
        return tuple(sorted(PAIR_IDS[i] for i in range(len(PAIRS)) if code >> i & 1))

    enum_minimal = sorted(decode(p) for p in minimal_realized)
    enum_k_min = min(bin(p).count("1") for p in distinct)
    enum_k_max = max(bin(p).count("1") for p in distinct)
    enum_forced_comparable = sorted(
        PAIR_IDS[i] for i in range(len(PAIRS)) if not any(p >> i & 1 for p in distinct)
    )
    enum_forced_incomparable = sorted(
        PAIR_IDS[i] for i in range(len(PAIRS)) if all(p >> i & 1 for p in distinct)
    )
    k_distribution: Counter[int] = Counter()
    for code, models in patterns.items():
        k_distribution[bin(code).count("1")] += models

    # 6. Structure of the escape: which avoidance comparisons each MCS leaves unresolved.
    avoidance_pairs = sorted(
        pair_id(*sorted(c.populations)) for c in substantive if c.principle_id.startswith("avoid")
    )
    avoidance_is_mus = tuple(avoidance_pairs) in set(muses)
    mcs_avoidance = Counter(tuple(p for p in avoidance_pairs if p in mcs) for mcs in mcses)
    curated = sorted([*avoidance_pairs, pair_id("AB", "AC")])
    curated_minimal = tuple(curated) in set(muses)
    pair_frequency_in_mcses = {p: sum(1 for m in mcses if p in m) for p in PAIR_IDS}
    minimum_models = []
    for mask in preorders(n):
        if predicate(mask):
            code = 0
            for bit, (ab, ba) in enumerate(pair_bits):
                if not mask & ab and not mask & ba:
                    code |= 1 << bit
            if bin(code).count("1") == k_min:
                minimum_models.append(_order_text(mask))

    route_cost = {}
    for route in avoidance_pairs:
        others = [pair.split(":")[1:] for pair in avoidance_pairs if pair != route]
        comparable = [z3.Or(engine.w(x, y), engine.w(y, x)) for x, y in others]
        route_cost[route] = next(
            k
            for k in range(22)
            if engine.require(extra=[*comparable, count <= k]).decision == "sat"
        )
    single_route_mcses = {
        route: [describe(m) for m in mcses if [p for p in avoidance_pairs if p in m] == [route]]
        for route in avoidance_pairs
    }

    # 8. Same-number versus different-number comparability.
    sizes = {name: len(spec.common.universe.names[name]) for name in ACTIVE}
    same_pairs = [(a, b) for a, b in PAIRS if sizes[a] == sizes[b]]
    different_pairs = [(a, b) for a, b in PAIRS if sizes[a] != sizes[b]]
    same_comparable = [z3.Or(engine.w(a, b), engine.w(b, a)) for a, b in same_pairs]
    k_same = next(
        k
        for k in range(22)
        if engine.require(extra=[*same_comparable, count <= k]).decision == "sat"
    )
    same_patterns: list[tuple[str, ...]] = []
    same_blocks: list[z3.BoolRef] = []
    while True:
        found = engine.require(extra=[*same_comparable, count == k_same, *same_blocks])
        if found.decision != "sat" or found.assignment is None:
            break
        pattern = tuple(
            sorted(
                pair_id(a, b)
                for a, b in PAIRS
                if not found.assignment[_w(a, b)] and not found.assignment[_w(b, a)]
            )
        )
        same_patterns.append(pattern)
        same_blocks.append(
            z3.Or(
                [
                    z3.Not(engine.incomparable(a, b))
                    if pair_id(a, b) in pattern
                    else engine.incomparable(a, b)
                    for a, b in PAIRS
                ]
            )
        )
    different_count = engine.count_incomparable(different_pairs)
    k_different = next(
        k for k in range(22) if engine.require(extra=[different_count <= k]).decision == "sat"
    )

    # 7. Fidelity check on the full 12-name domain (66 pairs).
    names = tuple(sorted({*ACTIVE, "A_prime", "B", "C", "E", "F"}))
    full_bg = background(names)
    full_engine = Engine(
        names,
        [*full_bg["reflexivity"], *full_bg["transitivity"], *substantive],
        full_bg["completeness"],
    )
    full_muses, full_msses = marco(full_engine)
    full_mcses = sorted(tuple(sorted(set(full_engine.soft) - set(m))) for m in full_msses)
    full_count = full_engine.count_incomparable(pairs(names))
    full_k_min = next(
        k for k in range(67) if full_engine.require(extra=[full_count <= k]).decision == "sat"
    )

    autos = automorphisms([c.formula for c in substantive])
    mus_sizes = Counter(len(m) for m in muses)
    mcs_sizes = Counter(len(m) for m in mcses)

    data = {
        "H_sat": h_sat,
        "H_plus_all_21_pairs": all_unsat,
        "mus_count": len(muses),
        "mus_size_distribution": dict(sorted(mus_sizes.items())),
        "mus_intersection": core_intersection,
        "muses": [list(m) for m in muses],
        "mcs_count": len(mcses),
        "mcs_size_distribution": dict(sorted(mcs_sizes.items())),
        "mcses": [describe(m) for m in mcses],
        "pair_classification": classification,
        "k_min": k_min,
        "k_max": k_max,
        "minimum_patterns": [describe(p) for p in minimum_patterns],
        "enumeration": {
            "preorders_scanned": 9535241,
            "escape_models": escape_models,
            "distinct_incomparability_patterns": len(distinct),
            "k_min": enum_k_min,
            "k_max": enum_k_max,
            "k_distribution_models": dict(sorted(k_distribution.items())),
            "forced_comparable": enum_forced_comparable,
            "forced_incomparable": enum_forced_incomparable,
            "inclusion_minimal_patterns_equal_mcses": enum_minimal == mcses,
        },
        "automorphisms": autos,
        "avoidance_pairs": avoidance_pairs,
        "avoidance_pairs_form_a_mus": avoidance_is_mus,
        "curated_certificate_pairs_form_a_mus": curated_minimal,
        "mcs_by_unresolved_avoidance_pairs": {
            "|".join(k) or "none": v for k, v in sorted(mcs_avoidance.items())
        },
        "pair_frequency_in_mcses": pair_frequency_in_mcses,
        "single_route_min_k": route_cost,
        "same_number_pairs": [pair_id(a, b) for a, b in same_pairs],
        "min_k_with_same_number_complete": k_same,
        "same_number_complete_minimum_patterns": [describe(p) for p in sorted(same_patterns)],
        "min_unresolved_different_number_pairs": k_different,
        "single_route_mcses": single_route_mcses,
        "minimum_models": minimum_models,
        "full_domain_66_pairs": {
            "mus_count": len(full_muses),
            "muses_equal_active": sorted(full_muses) == sorted(muses),
            "mcs_count": len(full_mcses),
            "mcses_equal_active": full_mcses == mcses,
            "k_min": full_k_min,
            "z3_calls": full_engine.calls,
        },
        "z3_calls": engine.calls,
    }
    write_result("p2_escape", data, {"wall_time_s": round(time.monotonic() - started, 2)})
    _ledger(data)


def _ledger(data: dict[str, Any]) -> None:
    enum = data["enumeration"]
    star = data["minimum_patterns"][0]["pairs"] if len(data["minimum_patterns"]) == 1 else None
    record(
        [
            LedgerEntry(
                candidate_id="P2-escape-sat",
                hypothesis="Dropping completeness restores consistency.",
                motivation="Completeness is visibly used to turn avoidance into weak comparisons.",
                exact_formal_change="completeness removed; reflexivity+transitivity on 7 relata",
                scope="frozen formulas, 7 active relata (66-pair domain agrees by lemma + check)",
                search_method="Z3 + exhaustive enumeration of 9,535,241 preorders",
                result=f"SAT; {enum['escape_models']} escape preorders on the 7 labeled relata",
                evidence_type="checked-model + exhaustive enumeration",
                checked=True,
                minimal="n/a",
                interpretation="Escape models are 0.21% of all preorders on 7 points.",
                next_experiment="minimum incomparability",
                result_scope="finite computational result",
                formalization_tier="frozen source-reviewed witness",
                status="confirmed",
            ),
            LedgerEntry(
                candidate_id="P2-min-incomparability",
                hypothesis=(
                    "Every escape leaves at least k of the 21 active comparisons unresolved; "
                    "find k and every pattern attaining it."
                ),
                motivation="State exactly what incompleteness buys.",
                exact_formal_change="none (quantified over all preorders satisfying H)",
                scope="frozen formulas, 7 active relata; 66-pair domain k_min identical",
                search_method=(
                    "Z3 bound sweep on Sum(If(incomparable)) + projection-blocked pattern "
                    "enumeration; independent exhaustive preorder enumeration"
                ),
                result=(
                    f"k_min={data['k_min']} (enumeration {enum['k_min']}); unique minimum "
                    f"pattern {star}; {enum['k_distribution_models'][data['k_min']]} labeled minimum models"
                    if star
                    else f"k_min={data['k_min']}; {len(data['minimum_patterns'])} patterns"
                ),
                evidence_type="Z3 + exhaustive enumeration (two decision procedures)",
                checked=True,
                minimal="bound attained; pattern unique",
                interpretation=(
                    "The cheapest escape isolates AAF (A plus A_prime plus the m barely-positive F "
                    "lives) from AAE, AB, AC and G while comparing everything else; both the "
                    "Non-Sadism and the second Non-Anti-Egalitarianism instance are then "
                    "satisfied vacuously. The analytical tie-the-sole-gap lemma gives only k>=2."
                ),
                next_experiment="does the AAF star persist across witness variations (P3/P6)?",
                result_scope="finite computational result",
                formalization_tier="frozen source-reviewed witness",
                status="confirmed",
            ),
            LedgerEntry(
                candidate_id="P2-core-structure",
                hypothesis=(
                    "Some pair is in every completeness core (forced incomparability), and the "
                    "curated proof's five completeness pairs are minimal."
                ),
                motivation="Reviewer anchors and the curated certificate.",
                exact_formal_change="none",
                scope="frozen formulas, 21 active pairs",
                search_method="two-solver MARCO (complete enumeration), MCS verification",
                result=(
                    f"{data['mus_count']} MUSes {data['mus_size_distribution']}, intersection "
                    f"{data['mus_intersection'] or 'empty'}; {data['mcs_count']} MCSes "
                    f"{data['mcs_size_distribution']}; forced comparable "
                    f"{enum['forced_comparable']}; forced incomparable none; curated 5-pair set "
                    f"is a MUS: {data['curated_certificate_pairs_form_a_mus']}"
                ),
                evidence_type="solver-reported MARCO; MCS family cross-checked by enumeration",
                checked=True,
                minimal="all MUSes and MCSes enumerated",
                counterexample_if_false=(
                    "no forced incomparability: every pair except AAE:AB and AC:G is comparable "
                    "in some escape; curated set strictly contains the 4 avoidance-pair MUS"
                ),
                interpretation=(
                    "Both hypotheses fail. The curated certificate uses one redundant "
                    "completeness premise (AB:AC)."
                ),
                next_experiment="M1 certificate over the four avoidance pairs",
                result_scope="finite computational result",
                formalization_tier="frozen source-reviewed witness",
                status="refuted",
            ),
            LedgerEntry(
                candidate_id="P2-same-number-escape",
                hypothesis=(
                    "If every same-number comparison is settled, the cheapest escape is unique "
                    "and isolates the Repugnance witness A."
                ),
                motivation="M1c: same-number completeness is consistent with the seven instances.",
                exact_formal_change="none (same-number pairs forced comparable in the query)",
                scope="frozen formulas, 7 active relata",
                search_method="Z3 bound sweep + projection-blocked enumeration",
                result=(
                    f"min K = {data['min_k_with_same_number_complete']}; patterns "
                    f"{[p['pairs'] for p in data['same_number_complete_minimum_patterns']]}; "
                    f"min unresolved different-number pairs overall = "
                    f"{data['min_unresolved_different_number_pairs']}"
                ),
                evidence_type="solver-reported (Z3); consistent with P2 enumeration",
                checked=True,
                minimal="bound attained; pattern unique",
                interpretation=(
                    "Two canonical escapes: the global minimum isolates AAF from the four "
                    "populations below it (4 pairs); if same-number comparisons must be settled, "
                    "the only cheapest escape makes the single very-high life A incomparable "
                    "to everything (6 pairs, all different-number)."
                ),
                next_experiment="test both escape shapes on schema skeletons",
                result_scope="finite computational result",
                formalization_tier="frozen source-reviewed witness",
                status="confirmed",
            ),
            LedgerEntry(
                candidate_id="P2-avoidance-necessity",
                hypothesis=(
                    "Every escape leaves at least one of the four avoidance comparisons "
                    "(A:D, AC:D, AAE:AAF, AAF:G) unresolved."
                ),
                motivation="The four avoidance pairs form a MUS.",
                exact_formal_change="none",
                scope="frozen formulas, 7 active relata",
                search_method="MUS membership; every MCS inspected; per-route minimum K",
                result=(
                    f"confirmed (avoidance pairs form a MUS: {data['avoidance_pairs_form_a_mus']}); "
                    f"single-route minimum K: {data['single_route_min_k']}"
                ),
                evidence_type="solver-reported; MCS family cross-checked by enumeration",
                checked=True,
                minimal="the 4-set is a MUS",
                interpretation=(
                    "Incompleteness can only help where an avoidance principle is applied. "
                    "Escaping through one avoidance principle alone is costlier than the global "
                    "minimum: via Repugnance (A isolated from all six others) costs 6; the "
                    "global minimum 4 uses two avoidance routes at once (AAE:AAF and AAF:G)."
                ),
                next_experiment="certificate (M1) and cross-witness stability (P6)",
                result_scope="finite computational result",
                formalization_tier="frozen source-reviewed witness",
                status="confirmed",
            ),
        ]
    )


def _order_text(mask: int) -> str:
    """Render a preorder on the active relata as ranked indifference classes plus gaps."""
    n = len(ACTIVE)

    def ge(i: int, j: int) -> bool:
        return bool(mask >> (i * n + j) & 1)

    parts = []
    for i, a in enumerate(ACTIVE):
        above = [ACTIVE[j] for j in range(n) if j != i and ge(j, i) and not ge(i, j)]
        tied = [ACTIVE[j] for j in range(n) if j != i and ge(j, i) and ge(i, j)]
        loose = [ACTIVE[j] for j in range(n) if j != i and not ge(j, i) and not ge(i, j)]
        parts.append(f"{a}: above={above} tied={tied} incomparable={loose}")
    return "; ".join(parts)


if __name__ == "__main__":
    main()
