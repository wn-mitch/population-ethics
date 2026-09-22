"""Phase 1: principle and instance frontier of the frozen baseline."""

from __future__ import annotations

import time
from typing import Any

from population_ethics.relations import weak
from population_ethics.search import FrontierResult, scan_frontier
from population_ethics.solver import solve_groups
from population_ethics.spec import CheckedModelEvidence, SolverReportEvidence
from research.lab import (
    ACTIVE,
    LedgerEntry,
    assignment_to_mask,
    background,
    compile_predicate,
    dpll_check,
    is_preorder,
    load_baseline,
    mask_to_assignment,
    record,
    substantive_constraints,
    total_preorders,
    write_result,
)


def _summarize(result: FrontierResult) -> dict[str, Any]:
    nodes = result.nodes
    decisions = {node.index: node.decision for node in nodes}
    width = len(result.dimensions)
    edges = [
        (node.index, node.index | (1 << bit))
        for node in nodes
        for bit in range(width)
        if not node.index & (1 << bit)
        and decisions[node.index] == "sat"
        and decisions[node.index | (1 << bit)] == "unsat"
    ]
    return {
        "unit": result.unit,
        "dimensions": [d.id for d in result.dimensions],
        "subsets": len(nodes),
        "sat": sum(1 for n in nodes if n.decision == "sat"),
        "unsat": sum(1 for n in nodes if n.decision == "unsat"),
        "unknown": sum(1 for n in nodes if n.decision == "unknown"),
        "minimal_unsat": [
            list(n.selected_units) for n in nodes if n.boundary_kind == "minimal-unsat"
        ],
        "maximal_sat": [list(n.selected_units) for n in nodes if n.boundary_kind == "maximal-sat"],
        "unresolved_boundary": [
            list(n.selected_units) for n in nodes if n.boundary_kind.startswith("unresolved")
        ],
        "sat_to_unsat_edges": len(edges),
        "solver_calls": result.solver_calls,
    }


def main() -> None:
    started = time.monotonic()
    spec = load_baseline()
    policy = spec.common.resource_policy
    principle = scan_frontier(spec, unit="principle")
    instance = scan_frontier(spec, unit="instance")
    summary = {"principle": _summarize(principle), "instance": _summarize(instance)}

    # Ground minimisation of each principle-level MUS (fixed background included).
    mus_cores = []
    for units in summary["principle"]["minimal_unsat"]:
        solved = solve_groups(spec.groups, (*spec.fixed_group_ids, *units), policy)
        report = solved.evidence[0]
        assert isinstance(report, SolverReportEvidence)
        mus_cores.append(
            {
                "groups": units,
                "grounded_core": list(report.grounded_core),
                "minimality": report.minimality,
                "trace": list(report.trace),
                "note": "one deletion-minimal core in id order, not the unique core",
            }
        )

    # Representative checked model of each maximal SAT set, independently rechecked.
    names = tuple(sorted(spec.common.role_bindings.values()) + ["AB", "AC", "AAF", "AAE"])
    names = tuple(sorted(set(names)))
    substantive = substantive_constraints(spec)
    models = []
    for units in summary["principle"]["maximal_sat"]:
        solved = solve_groups(spec.groups, (*spec.fixed_group_ids, *units), policy)
        evidence = solved.evidence[0]
        assert isinstance(evidence, CheckedModelEvidence)
        mask = assignment_to_mask(evidence.assignment, names)
        dropped = sorted(set(spec.candidate_group_ids) - set(units))
        complete = all(
            (mask >> (i * len(names) + j)) & 1 or (mask >> (j * len(names) + i)) & 1
            for i in range(len(names))
            for j in range(len(names))
        )
        # Restriction to the active relata satisfies the restricted theory.
        restricted = {
            a: v for a, v in evidence.assignment.items() if a.left in ACTIVE and a.right in ACTIVE
        }
        active_mask = assignment_to_mask(restricted, ACTIVE)
        kept = [c.formula for c in substantive if c.principle_id not in set(_principles(dropped))]
        models.append(
            {
                "dropped_group": dropped,
                "independent_preorder_check": is_preorder(mask, len(names)),
                "complete": bool(complete),
                "restriction_satisfies_active_theory": is_preorder(active_mask, len(ACTIVE))
                and compile_predicate(kept, ACTIVE)(active_mask),
                "active_strict_order": _describe(active_mask),
            }
        )

    # Active-relata reduction: exhaustive check over all 47,293 complete preorders on 7 points,
    # and an independent DPLL refutation over the 7-relata ground theory.
    full_predicate = compile_predicate([c.formula for c in substantive], ACTIVE)
    complete_models = sum(1 for mask in total_preorders(len(ACTIVE)) if full_predicate(mask))
    bg = background(ACTIVE)
    dpll_formulas = [c.formula for group in bg.values() for c in group] + [
        c.formula for c in substantive
    ]
    dpll_decision, _ = dpll_check(dpll_formulas)

    # Extension direction: a 7-relata model with the five inert names added as one universal
    # top class satisfies the 12-name background (checked on each maximal-SAT restriction).
    extension_ok = []
    for units in summary["principle"]["maximal_sat"]:
        solved = solve_groups(spec.groups, (*spec.fixed_group_ids, *units), policy)
        evidence = solved.evidence[0]
        assert isinstance(evidence, CheckedModelEvidence)
        restricted = {
            a: v for a, v in evidence.assignment.items() if a.left in ACTIVE and a.right in ACTIVE
        }
        extended = dict(restricted)
        inert = [n for n in names if n not in ACTIVE]
        for x in names:
            for y in names:
                if x in inert or y in inert:
                    extended[weak(x, y)] = x in inert
        mask = assignment_to_mask(extended, names)
        extension_ok.append(is_preorder(mask, len(names)))

    data = {
        "frontier": summary,
        "mus_ground_cores": mus_cores,
        "maximal_sat_models": models,
        "active_reduction": {
            "active_relata": list(ACTIVE),
            "complete_preorders_checked": 47293,
            "complete_preorders_satisfying_all_seven_instances": complete_models,
            "dpll_decision_on_active_ground_theory": dpll_decision,
            "universal_top_extension_is_preorder": extension_ok,
        },
    }
    write_result("p1_frontier", data, {"wall_time_s": round(time.monotonic() - started, 2)})
    p = summary["principle"]
    i = summary["instance"]
    record(
        [
            LedgerEntry(
                candidate_id="P1-frontier",
                hypothesis="Every candidate group, and every instance, is necessary for UNSAT.",
                motivation="Characterize the known frontier before proposing anything new.",
                exact_formal_change="none (subset scans of the frozen spec)",
                scope="selected finite witness; background fixed",
                search_method="scan_frontier principle (2^7) and instance (2^8) power sets",
                result=(
                    f"principle: {len(p['minimal_unsat'])} MUS {p['minimal_unsat']}, "
                    f"{len(p['maximal_sat'])} maximal SAT; instance: {len(i['minimal_unsat'])} MUS, "
                    f"{len(i['maximal_sat'])} maximal SAT; unknown={p['unknown'] + i['unknown']}"
                ),
                evidence_type="solver-reported frontier; checked models for maximal SAT sets",
                checked=True,
                minimal="the unique MUS is the full set at both levels",
                interpretation=(
                    "The selected instance is irreducibly inconsistent relative to reflexivity "
                    "and transitivity: dropping any one group or instance restores consistency. "
                    "This is not logical independence of the principles, and the completeness "
                    "group contains many redundant ground pairs (see P2)."
                ),
                next_experiment="P2 completeness escape at pair granularity",
                result_scope="finite computational result",
                formalization_tier="frozen source-reviewed witness",
                status="confirmed",
            ),
            LedgerEntry(
                candidate_id="P1-active-reduction",
                hypothesis=(
                    "The five populations B, C, E, F, A_prime are inert: the theory restricted "
                    "to the seven active relata has the same SAT/UNSAT status and the same "
                    "completeness cores."
                ),
                motivation="Shrink the search space from 66 to 21 pairs soundly.",
                exact_formal_change="background principles restricted to 7 relata",
                scope="frozen formulas",
                search_method=(
                    "restriction/extension lemma; exhaustive check of 47,293 complete preorders; "
                    "DPLL refutation; universal-top extension check on maximal-SAT models"
                ),
                result=(
                    f"{complete_models} of 47,293 complete preorders satisfy all seven "
                    f"instances; DPLL={dpll_decision}; extensions preorder={all(extension_ok)}"
                ),
                evidence_type="exhaustive enumeration + independent DPLL",
                checked=True,
                minimal="n/a",
                interpretation="Phase 2 may work over 21 pairs; 66-pair results follow by lemma.",
                next_experiment="P2",
                result_scope="finite computational result",
                formalization_tier="frozen source-reviewed witness",
                status="confirmed",
            ),
        ]
    )


PRINCIPLE_OF_GROUP = {
    "repugnance-avoidance": "avoid-repugnance",
    "anti-egalitarianism-avoidance": "avoid-anti-egalitarianism",
    "sadism-avoidance": "avoid-sadism",
    "minimal-non-extreme-priority": "minimal-non-extreme-priority",
    "dominance": "dominance",
    "addition": "addition",
}


def _principles(groups: list[str]) -> list[str]:
    return [PRINCIPLE_OF_GROUP[g] for g in groups if g in PRINCIPLE_OF_GROUP]


def _describe(mask: int) -> list[str]:
    assignment = mask_to_assignment(mask, ACTIVE)
    out = []
    for i, a in enumerate(ACTIVE):
        for j, b in enumerate(ACTIVE):
            if i < j:
                ab, ba = assignment[weak(a, b)], assignment[weak(b, a)]
                rel = "~" if ab and ba else ">" if ab else "<" if ba else "||"
                out.append(f"{a} {rel} {b}")
    return out


if __name__ == "__main__":
    main()
