"""P25: conditional equal-size DA obstruction and bounded Q-011 controls.

The primitive scanner uses the frozen nonempty VRC bag and nonempty thesis DA
translation. A path's absence at a cap is not an all-size model or a theorem.
"""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Mapping
from dataclasses import replace
from typing import Any

import z3  # type: ignore[import-untyped]

from research.lab import Engine, LedgerEntry, background, record, write_result
from research.ladder import Witness, audit, validate
from research.p6_schema import core_constraints, name_of
from research.p17_vrc_boundary import DA_THESIS, ED
from research.p18_vrc_certificate import Edge
from research.p19_impossibility_not_worse_da import _replay as replay_edge
from research.p21_least_preorder import LADDER
from research.p23_not_worse_da import (
    CENSUS_WITNESSES,
    PRINCIPLES,
    Schema,
    _forward,
    _path,
    _step,
    certificate,
)
from research.schema import Instance, Pop

CONTROLS = frozenset({"ne-n2", "vrc-m2", "vrc-n2"})
CAPS = (8, 10)


def _da_targets(pop: Pop, size: int) -> list[tuple[int, int, int]]:
    """All B=W_b^size, C=W_c^k decompositions of a frozen thesis-DA target."""
    counts = Counter(pop)
    out = []
    for high, copies in counts.items():
        if copies < size:
            continue
        rest = counts - Counter({high: size})
        if rest and len(rest) == 1:
            low, count = next(iter(rest.items()))
            if low > 0:
                out.append((high, low, count))
    return out


def _found(
    parents: Mapping[int, Mapping[Pop, tuple[Pop, Edge] | None]], size: int
) -> tuple[Pop, int, int, int, int, int] | None:
    """Smallest common legal target for two equal-size source populations."""
    best: tuple[Pop, int, int, int, int, int] | None = None
    for target in set().union(*(set(seen) for seen in parents.values())):
        for high, low, count in _da_targets(target, size):
            sources = [
                level for level in LADDER.levels if level < high and target in parents[level]
            ]
            if len(sources) < 2:
                continue
            candidate = target, high, low, count, sources[0], sources[-1]
            if best is None or (len(target), target, high) < (len(best[0]), best[0], best[1]):
                best = candidate
    return best


def _decision(edges: list[Edge], da: Instance, ed: Instance) -> str:
    instances = [*(edge.instance for edge in edges), da, ed]
    names = tuple(sorted({name_of(pop) for instance in instances for pop in instance.args}))
    clauses = [
        *background(names)["reflexivity"],
        *background(names)["transitivity"],
        *core_constraints(instances, "p25-equal-size-diagnostic"),
    ]
    return Engine(names, clauses, timeout_ms=120000).require().decision


def _case(label: str, witness: Witness, size: int, cap: int) -> dict[str, Any]:
    schema = Schema.of(witness)
    parents = {
        level: _forward((level,) * size, cap, schema, ranged=False) for level in LADDER.levels
    }
    found = _found(parents, size)
    result: dict[str, Any] = {
        "witness": label,
        "params": {key: dict(value) for key, value in witness.params.items()},
        "ladder": [min(LADDER.levels), max(LADDER.levels)],
        "source_size": size,
        "population_cap": cap,
        "found_path": found is not None,
        "not_a_general_proof": True,
    }
    if found is None:
        result["bounded_absence"] = (
            "No equal-size two-source DA target in the scanned primitive closure."
        )
        return result
    target, high, low, count, low_level, high_level = found
    source_low, source_high = (low_level,) * size, (high_level,) * size
    chains = {
        "low": _path(parents[low_level], target),
        "high": _path(parents[high_level], target),
    }
    edges = list(
        {
            (edge.principle, edge.left, edge.right, edge.background): edge
            for chain in chains.values()
            for edge in chain
        }.values()
    )
    problems = [
        {
            "edge": _step(edge),
            "replay": replay_edge(edge),
            "audit": audit(edge.instance, LADDER, witness),
        }
        for edge in edges
        if replay_edge(edge) or not audit(edge.instance, LADDER, witness)
    ]
    da = Instance(DA_THESIS, (source_high, target))
    ed = Instance(ED, (source_high, source_low))
    da_ok, ed_ok = audit(da, LADDER, witness), audit(ed, LADDER, witness)
    if problems or not da_ok or not ed_ok:
        raise AssertionError(f"invalid {label} source path: {problems}; DA={da_ok}; ED={ed_ok}")
    decision = _decision(edges, da, ed)
    if decision != "unsat":
        raise AssertionError(f"two-source conditional obstruction did not close: {decision}")
    result["certificate"] = {
        "target": list(target),
        "decomposition": {"B": [high] * size, "C": [low] * count},
        "sources": [list(source_low), list(source_high)],
        "paths": {key: [_step(edge) for edge in path] for key, path in chains.items()},
        "edge_count": len(edges),
        "all_edges_replayed_and_audited": not problems,
        "da_audited": da_ok,
        "ed_audited": ed_ok,
        "decision_without_completeness": decision,
    }
    return result


def _least_preorder_control() -> dict[str, Any]:
    """Independent symbolic cycle check; DA reachability remains an open obligation."""
    witness = Witness(dict(CENSUS_WITNESSES[2][1]))
    schema = Schema.of(witness)
    previous, current, gap, high_gap = z3.Reals("p25_previous current gap high_gap")
    solver = z3.Solver()
    # P21's strictly decreasing positive adjacent gains F(t+1)-F(t):
    # NE n=2 costs 2(F(m)-F(y)) while gaining F(m+1)-F(m).
    solver.add(previous > current, current > 0, gap >= previous, current - 2 * gap >= 0)
    if solver.check() != z3.unsat:
        raise AssertionError("ne-n2 can fail to lower the potential")
    solver = z3.Solver()
    solver.add(high_gap > 2, current < 2, high_gap - current <= 0)
    if solver.check() != z3.unsat:
        raise AssertionError("GNEP can fail to lower the potential")

    integer, real, boolean = z3.IntSort(), z3.RealSort(), z3.BoolSort()
    reach = z3.Function("p25_reach", integer, real, integer, real, boolean, boolean)
    bad = z3.Function("p25_return_cycle", boolean)
    fp = z3.Fixedpoint()
    fp.set(engine="spacer")
    fp.register_relation(reach, bad)
    start_size, size, next_size = z3.Ints("p25_start_size size next_size")
    start_score, score, next_score, gain = z3.Reals("p25_start_score score next_score gain")
    moved = z3.Bool("p25_moved")
    fp.declare_var(start_size, size, next_size, start_score, score, next_score, gain, moved)
    fp.rule(
        reach(start_size, start_score, start_size, start_score, False),
        start_size >= 1,
    )
    fp.rule(
        reach(start_size, start_score, size, score - gain, True),
        [reach(start_size, start_score, size, score, moved), gain > 0],
    )
    fp.rule(
        reach(start_size, start_score, next_size, next_score, True),
        [reach(start_size, start_score, size, score, moved), next_size > size],
    )
    fp.rule(
        bad(),
        [
            reach(start_size, start_score, size, score, moved),
            size == start_size,
            moved,
            score >= start_score,
        ],
    )
    if fp.query(bad()) != z3.unsat:
        raise AssertionError("positive-size VRC growth can return to an ED source")

    parents = {level: _forward((level,), 10, schema, ranged=False) for level in LADDER.levels}
    reachable_da = sum(
        any(level < high for high, _, _ in _da_targets(target, 1))
        for level, seen in parents.items()
        for target in seen
    )
    return {
        "universal_acyclicity": (
            "Same-size ED, unrestricted NE n=2 and GNEP n=1 strictly lower P21's "
            "positive-gain potential; nonempty VRC n=1 strictly grows size; "
            "SMT inequalities and Spacer finite-path induction exclude strict cycles."
        ),
        "bounded_reachable_singleton_da_targets": reachable_da,
        "population_cap": 10,
        "missing_model_obligation": (
            "No all-size invariant excludes every DA-forbidden return from every "
            "source, especially arbitrarily large VRC bags; acyclicity alone "
            "does not establish thesis DA."
        ),
        "not_a_general_proof": True,
    }


def run() -> dict[str, Any]:
    assert PRINCIPLES == (
        "arrhenius-2003:egalitarian-dominance",
        "arrhenius-2003:non-elitism",
        "arrhenius-2003:general-non-extreme-priority",
        "arrhenius-2003:vrc-avoidance",
        DA_THESIS,
    )
    p21 = CENSUS_WITNESSES[0]
    chosen = [p21, *(row for row in CENSUS_WITNESSES if row[0] in CONTROLS)]
    rows: list[dict[str, Any]] = []
    for label, params in chosen:
        witness = Witness(params)
        for family, values in params.items():
            validate(family, LADDER, values)
        sizes = tuple(dict.fromkeys((1, params["vrc-avoidance"]["n"])))
        for cap in CAPS:
            rows.extend(_case(label, witness, size, cap) for size in sizes)
    control = certificate(cap=8)
    if not control["all_edges_replayed_clean"] or control["target"] != [1] * 7 + [6]:
        raise AssertionError("the fixed-witness P23 singleton regression changed")
    da_good = Instance(DA_THESIS, ((3, 3), (1, 1, 6, 6)))
    da_mixed = Instance(DA_THESIS, ((3, 3), (1, 2, 6, 6)))
    if not audit(da_good, LADDER, Witness({})) or audit(da_mixed, LADDER, Witness({})):
        raise AssertionError(
            "thesis DA equal positive C decomposition is not independently audited"
        )
    return {
        "status": "superseded by P26",
        "principles": list(PRINCIPLES),
        "translation": "frozen nonempty VRC low bag and nonempty thesis DA addition",
        "conditional_lemma": (
            "For every r>=1, a<a'<b, c>0 and k>=1, paths from W_a^r and "
            "W_a'^r to T=W_b^r union W_c^k force A_low>=T and A_high>=T. "
            "Thesis DA forbids A_high>T, so T>=A_high; then A_low>=A_high "
            "contradicts strict ED A_high>A_low. No completeness is used."
        ),
        "p23_singleton_control": {"target": control["target"], "replayed": True},
        "da_target_audit": {"equal_C": True, "mixed_C_rejected": True},
        "bounded_rows": rows,
        "ne_n2_least_preorder_control": _least_preorder_control(),
        "p23_census_correction": (
            "P23's prior ledger ID is retained. Its GNEP n>1 edges had used only "
            "one high life and one low life; VRC n>1 had accepted mixed high "
            "sources. The regenerated P23 artifact now enumerates exact counts "
            "and perfectly equal sources. At cap eight the corrected gnep-n2 "
            "row reports bounded absence, alongside ne-n2, vrc-m2 and vrc-n2. "
            "Prior paths from the invalid generator are not evidence."
        ),
        "universal_routes": {
            "not_a_general_proof": True,
            "impossibility": (
                "P25's fixed-witness scanner did not derive an arbitrary-witness chain. "
                "P26 later constructs that chain for every legal witness."
            ),
            "least_preorder_ne_n2": (
                "P25 proved acyclicity but not DA compliance; P26 refutes DA compliance "
                "with an audited width-82 target."
            ),
        },
        "source_empty_branches": "VRC B=empty and thesis DA C=empty or A=B=empty remain separate fidelity questions, not scanner edges.",
        "not_a_general_proof": True,
    }


def main() -> None:
    result = run()
    path = write_result("p25_q011_frontier", result, {})
    artifact = str(path.relative_to(path.parent.parent.parent))
    base = LedgerEntry(
        candidate_id="P25-equal-size-two-source-lemma",
        hypothesis="Two equal-size primitive paths into one thesis-DA target refute a fixed witness.",
        motivation="The P23 scanner miscounted GNEP high lives and admitted mixed VRC high sources.",
        exact_formal_change="None: corrected enumeration of the frozen nonempty-bag translation.",
        scope="indexed W_-1..W_6, legal control witnesses and population caps 8 and 10",
        search_method="forward primitive closure, P18/P19 replay, independent ladder audit and exact preorder decision",
        result="proved conditionally for every r>=1; P23 r=1 control replayed; no all-witness path claim",
        evidence_type="conditional proof and independently audited bounded source-instance controls",
        checked=True,
        minimal="no source-general minimality claim",
        interpretation="DA's N shape becomes a reverse comparison only after the high forward path.",
        next_experiment="derive both paths for arbitrary legal existential witnesses",
        result_scope="conditional all-r obstruction plus finite fixed-witness diagnostics",
        formalization_tier="agent-cross-read frozen source translation, explicitly excluding empty branches",
        witness_conditions="P21, ne-n2, vrc-m2, vrc-n2 legal census witnesses",
        novelty_status="no priority claim; exact collision check incomplete",
        status="confirmed",
        artifacts=[artifact],
    )
    record(
        [
            base,
            replace(
                base,
                candidate_id="P25-p23-scanner-correction",
                hypothesis="P23's forward GNEP and VRC edges exactly enumerate the frozen source instances.",
                result="prior n>1 generator false: repaired counts and uniform VRC source, independently cross-checked against all tiny instances; corrected cap-eight gnep-n2 obstruction absent",
                result_scope="corrected frozen scanner and cap-eight P23 census",
                interpretation="P23 historical ledger IDs stand, but prior invalid paths are superseded by regenerated diagnostics.",
                next_experiment="review source-permitted empty branches only after a separate formalization decision",
            ),
            replace(
                base,
                candidate_id="P25-q011-bounded-witness-routes",
                hypothesis="The equal-size lemma forces a contradiction for every legal Q-011 witness.",
                result="P25 supplies finite witness/cap controls only; P26 later proves the every-witness contradiction",
                result_scope="three selected legal witnesses at caps eight and ten; universal resolution in P26",
                interpretation="Bounded missing paths do not establish a model; P26 constructs larger paths.",
                next_experiment="source-general proof supplied by P26",
                status="confirmed",
            ),
            replace(
                base,
                candidate_id="P25-ne-n2-least-preorder-candidate",
                hypothesis="The least ED/NE/GNEP/VRC preorder at ne-n2 satisfies thesis DA for all finite profiles.",
                result="refuted by P26: ne-n2 primitive closure is acyclic, but at width 82 both ED sources reach one forbidden DA target",
                search_method="P25 symbolic potential and bounded DA scan; P26 independent audited width-82 target",
                evidence_type="all-finite-path acyclicity plus later finite DA counterexample",
                result_scope="ne-n2 fixed-witness candidate refuted by P26",
                interpretation="Acyclicity and bounded absence do not establish thesis DA compliance.",
                next_experiment="none for this refuted candidate",
                status="refuted",
                artifacts=[artifact, "research/results/p26_q011_unrestricted.json"],
            ),
        ]
    )
    print(
        json.dumps(
            {"result": artifact, "rows": len(result["bounded_rows"]), "status": result["status"]}
        )
    )


if __name__ == "__main__":
    main()
