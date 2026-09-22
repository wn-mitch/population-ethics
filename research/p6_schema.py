"""Phase 6: schema-level skeleton search under ``arrhenius-2000.schema/v0-unreviewed``.

For each grid and fixed witness W = (p, q), increase the bound N on lives per population until
the instance set over D_N is UNSAT (complete branch, rank encoding). UNSAT at N transfers to
every N' > N because D_N ⊆ D_N' and the instance sets are nested (checked). Minimized cores are
canonicalized as colored hypergraphs and re-verified with the atom encoding (production CLI),
the independent preorder enumerator, and the per-instance applicability audit.
"""

from __future__ import annotations

import json
import subprocess
import time
from collections import Counter
from fractions import Fraction
from typing import Any

from population_ethics.principles import GroundConstraint
from population_ethics.relations import Formula, Implies, Not, strict, weak
from research.known import known_ground, novelty_rank
from research.lab import (
    ROOT,
    Engine,
    LedgerEntry,
    background,
    compile_predicate,
    ground,
    marco,
    pairs,
    record,
    toml_value,
    total_preorders,
    write_result,
)
from research.schema import (
    BASELINE_SKELETON,
    SCHEMA_ID,
    Grid,
    Instance,
    Pop,
    RankEngine,
    canonical_skeleton,
    check_instance,
    domain,
    holds,
    instances,
)

GRIDS = {
    "baseline": Grid(
        "baseline", (-1, 1, 2, 3, 4, 8), frozenset({8}), frozenset({1, 2, 3, 4}), frozenset({-1})
    ),
    "relaxed": Grid(
        "relaxed", (-1, 1, 5, 6, 7, 8), frozenset({8}), frozenset({1, 5, 6, 7}), frozenset({-1})
    ),
    # Same very-low levels as "relaxed", very-high raised to 14 so that the MNEP bundle's
    # average ((q*14 - 1)/(q+1) >= 6.5) sits above every very-low level that has a higher
    # very-low level: the MNEP/Dominance/Non-Anti-Egalitarianism triangle cannot fire. The
    # baseline skeleton needs 9 lives here (closed form), so any UNSAT at N <= 8 is a new skeleton.
    "gapped": Grid(
        "gapped", (-1, 1, 5, 6, 7, 14), frozenset({14}), frozenset({1, 5, 6, 7}), frozenset({-1})
    ),
}
RUNS = [
    ("baseline", 1, 1, 8),
    ("baseline", 1, 2, 8),
    ("relaxed", 1, 1, 6),
    ("relaxed", 1, 2, 6),
    # Falsification test of the triangle closed form: predicted to fire for q=3, not for q=4.
    ("relaxed", 1, 3, 6),
    ("relaxed", 1, 4, 6),
    ("gapped", 1, 1, 8),
    ("gapped", 1, 2, 8),
]
DIVERSIFY_CAP = 12


def name_of(pop: Pop) -> str:
    return "P_" + "_".join(("m" + str(-v)) if v < 0 else str(v) for v in pop)


def formula_of(inst: Instance) -> Formula:
    x = [name_of(p) for p in inst.args]
    if inst.shape == "S":
        return strict(x[0], x[1])
    if inst.shape == "N":
        return Not(strict(x[0], x[1]))
    if inst.shape == "W":
        return weak(x[0], x[1])
    return Implies(strict(x[0], x[1]), weak(x[1], x[2]))


def core_constraints(
    core: list[Instance], formalization_id: str = SCHEMA_ID
) -> list[GroundConstraint]:
    return [
        ground(
            f"{inst.principle}:{i}",
            inst.principle,
            formula_of(inst),
            formalization_id,
            f"{inst.principle} instance over {[name_of(p) for p in inst.args]}",
        )
        for i, inst in enumerate(core)
    ]


def materialize(
    tag: str,
    grid: Grid,
    core: list[Instance],
    p: int,
    q: int,
    n: int,
    *,
    source_ids: tuple[str, ...] = ("arrhenius-2000",),
    formalization_id: str = SCHEMA_ID,
    source_fidelity: str = "unreviewed schema generalization; solver-discovered proof skeleton",
    claim_kind: str = "bounded-search",
    bindings: dict[str, int] | None = None,
    completeness_candidate: bool = True,
) -> str:
    relata = sorted({x for inst in core for x in inst.args})
    names = [name_of(x) for x in relata]
    lines = [
        'schema = "population-ethics.experiment/v2"',
        f"id = {toml_value(tag)}",
        'kind = "compatibility"',
        f"claim_kind = {toml_value(claim_kind)}",
        f"source_fidelity = {toml_value(source_fidelity)}",
        f"source_ids = {toml_value(list(source_ids))}",
        f"formalization_id = {toml_value(formalization_id + '/' + tag)}",
        'fixed_groups = ["reflexivity", "transitivity"]',
        "candidate_groups = "
        + toml_value(
            [
                *(["completeness"] if completeness_candidate else []),
                *sorted({inst.principle for inst in core}),
            ]
        ),
        "",
        "[resource_policy]",
        "max_populations = 100",
        "max_expanded_lives = 5000",
        "max_relation_atoms = 1000",
        "max_ground_constraints = 5000",
        "max_subsets = 256",
        "timeout_ms = 0",
        "",
        "[domain]",
        'mode = "explicit"',
    ]
    for pop, nm in zip(relata, names, strict=True):
        lines += [
            "",
            "[[domain.populations]]",
            f"name = {toml_value(nm)}",
            f"values = {toml_value(list(pop))}",
        ]
    lines += [
        "",
        "[categories]",
        f"slightly_negative = {toml_value(sorted(grid.slightly_negative))}",
        f"very_low_positive = {toml_value(sorted(grid.very_low))}",
        f"very_high_positive = {toml_value(sorted(grid.very_high))}",
        "",
        "[witness_bindings]",
        *(
            f"{k} = {v}"
            for k, v in (
                bindings if bindings is not None else {"p": p, "q": q, "max_lives": n}
            ).items()
        ),
    ]
    for group in (
        "reflexivity",
        "transitivity",
        *(["completeness"] if completeness_candidate else []),
    ):
        lines += [
            "",
            "[[groups]]",
            f"id = {toml_value(group)}",
            f"principle_id = {toml_value(group)}",
            f"compiler = {toml_value(group)}",
            f"populations = {toml_value(names)}",
        ]
    by_principle: dict[str, list[GroundConstraint]] = {}
    for c in core_constraints(core, formalization_id):
        by_principle.setdefault(c.principle_id, []).append(c)
    from population_ethics.relations import formula_to_data

    for principle, items in sorted(by_principle.items()):
        lines += [
            "",
            "[[groups]]",
            f"id = {toml_value(principle)}",
            f"principle_id = {toml_value(principle)}",
        ]
        for c in items:
            lines += [
                "",
                "[[groups.constraints]]",
                f"id = {toml_value(c.id)}",
                f"formula = {toml_value(formula_to_data(c.formula))}",
                f"populations = {toml_value(list(c.populations))}",
                f"formalization_id = {toml_value(formalization_id)}",
                f"explanation = {toml_value(c.explanation)}",
            ]
    path = ROOT / "research" / "experiments" / f"{tag}.toml"
    path.write_text("\n".join(lines) + "\n")
    return str(path.relative_to(ROOT))


def _cli(*args: str) -> str:
    return subprocess.run(
        ["uv", "run", "--quiet", "population-ethics", *args],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout


def verify_core(
    tag: str, grid: Grid, core: list[Instance], p: int, q: int, n: int
) -> dict[str, Any]:
    relata = sorted({x for inst in core for x in inst.args})
    names = tuple(sorted(name_of(x) for x in relata))
    toml = materialize(tag, grid, core, p, q, n)
    out = ROOT / "research" / "results" / f"{tag}.run.json"
    _cli("run", toml, "--format", "json", "--output", str(out))
    verified = _cli("verify", str(out))
    decision = json.loads(out.read_text())["outcome"]["decision"]
    out.unlink()
    formulas = [c.formula for c in core_constraints(core)]
    enumerated = None
    if len(names) <= 8:
        predicate = compile_predicate(formulas, names)
        enumerated = sum(1 for m in total_preorders(len(names)) if predicate(m))
    # Incomplete branch (atom encoding): minimum number of unresolved pairs among the relata.
    bg = background(names)
    engine = Engine(
        names,
        [*bg["reflexivity"], *bg["transitivity"], *core_constraints(core)],
        bg["completeness"],
    )
    escape = engine.require().decision
    k_min = None
    minimum_patterns: list[list[str]] = []
    if escape == "sat":
        count = engine.count_incomparable(pairs(names))
        k_min = next(
            k
            for k in range(len(pairs(names)) + 1)
            if engine.require(extra=[count <= k]).decision == "sat"
        )
        import z3  # type: ignore[import-untyped]

        blocks: list[Any] = []
        while len(minimum_patterns) < 50:
            r = engine.require(extra=[count == k_min, *blocks])
            if r.decision != "sat" or r.assignment is None:
                break
            pat = [
                f"{a}|{b}"
                for a, b in pairs(names)
                if not r.assignment[weak(a, b)] and not r.assignment[weak(b, a)]
            ]
            minimum_patterns.append(pat)
            blocks.append(
                z3.Or(
                    [
                        z3.Not(engine.incomparable(a, b))
                        if f"{a}|{b}" in pat
                        else engine.incomparable(a, b)
                        for a, b in pairs(names)
                    ]
                )
            )
    muses, _ = marco(engine) if len(names) <= 8 else ([], [])
    return {
        "toml": toml,
        "cli_decision": decision,
        "cli_verify_accepted": "verification: accepted" in verified,
        "relata": len(names),
        "complete_preorders_satisfying_core": enumerated,
        "all_instances_pass_applicability_audit": all(check_instance(i, grid, p, q) for i in core),
        "escape_without_completeness": escape,
        "escape_k_min": k_min,
        "escape_minimum_patterns": minimum_patterns,
        "completeness_mus_sizes": dict(sorted(Counter(len(m) for m in muses).items())),
    }


def describe(core: list[Instance]) -> list[str]:
    return [f"{i.principle}({', '.join(name_of(x) for x in i.args)})" for i in core]


def run_config(grid_name: str, p: int, q: int, n_max: int) -> dict[str, Any]:
    grid = GRIDS[grid_name]
    steps = []
    previous: set[Instance] | None = None
    for n in range(2, n_max + 1):
        t0 = time.monotonic()
        insts = list(instances(grid, n, p, q))
        current = set(insts)
        nested = previous is None or previous <= current
        previous = current
        pops = domain(grid, n)
        engine = RankEngine(pops, insts)
        decision, core, ranks = engine.check(list(range(len(insts))))
        print("  N", n, decision, len(insts), flush=True)
        step: dict[str, Any] = {
            "N": n,
            "populations": len(pops),
            "instances": len(insts),
            "by_principle": dict(sorted(Counter(i.principle for i in insts).items())),
            "nested_in_next": nested,
            "decision": decision,
        }
        if decision == "sat":
            assert ranks is not None
            step["model_checked_all_instances"] = all(holds(i, ranks) for i in insts)
            step["seconds"] = round(time.monotonic() - t0, 1)
            steps.append(step)
            continue
        first = engine.minimize(core)
        cores = [first]
        frontier = [first]
        seen = {tuple(first)}
        while frontier and len(cores) < DIVERSIFY_CAP:
            base = frontier.pop(0)
            for banned in base:
                if len(cores) >= DIVERSIFY_CAP:
                    break
                enabled = [j for j in range(len(insts)) if j != banned]
                d2, c2, _ = engine.check(enabled)
                if d2 != "unsat":
                    continue
                m2 = engine.minimize(c2)
                if tuple(m2) not in seen:
                    seen.add(tuple(m2))
                    cores.append(m2)
                    frontier.append(m2)
        skeletons: dict[tuple[object, ...], dict[str, Any]] = {}
        baseline_logical = canonical_skeleton(BASELINE_SKELETON, principle_colors=False)
        baseline_semantic = canonical_skeleton(BASELINE_SKELETON, principle_colors=True)
        for c in cores:
            core_insts = [insts[j] for j in c]
            logical = canonical_skeleton(core_insts, principle_colors=False)
            semantic = canonical_skeleton(core_insts, principle_colors=True)
            entry = skeletons.setdefault(
                semantic,
                {
                    "instances": len(core_insts),
                    "relata": len({x for i in core_insts for x in i.args}),
                    "canonical_form_exact": semantic[0] != "inexact-color-refinement",
                    "principles": dict(sorted(Counter(i.principle for i in core_insts).items())),
                    "logically_isomorphic_to_baseline": logical == baseline_logical,
                    "semantically_isomorphic_to_baseline": semantic == baseline_semantic,
                    "largest_population": max(len(x) for i in core_insts for x in i.args),
                    "total_distinct_lives": sum(
                        len(x) for x in {x for i in core_insts for x in i.args}
                    ),
                    "example": describe(core_insts),
                    "core": [
                        {"principle": i.principle, "args": [list(x) for x in i.args]}
                        for i in core_insts
                    ],
                    "known_ground": known_ground(core_insts),
                    "occurrences": 0,
                    "_core": core_insts,
                },
            )
            entry["occurrences"] += 1
        # Cores isomorphic to a catalogued skeleton go last so verification targets new ground.
        ranked = sorted(skeletons.values(), key=novelty_rank)
        for k, s in enumerate(ranked[:3]):
            tag = f"schema-{grid_name}-p{p}q{q}-N{n}-skeleton{k}"
            s["verification"] = verify_core(tag, grid, s["_core"], p, q, n)
        for s in ranked:
            del s["_core"]
        step.update(
            {
                "cores_found": len(cores),
                "coverage": f"diversified search, cap {DIVERSIFY_CAP}; not all MUSes",
                "distinct_semantic_skeletons": len(ranked),
                "distinct_logical_skeletons": len(
                    {
                        (s["relata"], s["instances"], s["logically_isomorphic_to_baseline"])
                        for s in ranked
                    }
                ),
                "skeletons": ranked,
                "seconds": round(time.monotonic() - t0, 1),
            }
        )
        steps.append(step)
        break
    first_unsat = next((s["N"] for s in steps if s["decision"] == "unsat"), None)
    return {
        "grid": grid_name,
        "p": p,
        "q": q,
        "N_max": n_max,
        "smallest_unsat_N": first_unsat,
        "steps": steps,
    }


def main() -> None:
    started = time.monotonic()
    results = []
    for cfg in RUNS:
        print("run", cfg, flush=True)
        results.append(run_config(*cfg))
        (ROOT / "research" / "results" / "p6_schema.partial.json").write_text(
            json.dumps(results, default=str)
        )
    data = {
        "schema": SCHEMA_ID,
        "grids": {
            k: {
                "levels": list(g.levels),
                "very_high": sorted(g.very_high),
                "very_low": sorted(g.very_low),
                "slightly_negative": sorted(g.slightly_negative),
            }
            for k, g in GRIDS.items()
        },
        "transfer": (
            "UNSAT over D_N refutes v0 schema + W(p,q) (universal instances over D_N are "
            "consequences of the unrestricted v0 schema; W is fixed inside D_N). It does "
            "not refute Arrhenius's principles, nor v0 with other witnesses."
        ),
        "runs": results,
        "baseline_skeleton_logical": str(
            canonical_skeleton(BASELINE_SKELETON, principle_colors=False)
        ),
    }
    timings = {
        f"{r['grid']}-p{r['p']}q{r['q']}-N{step['N']}": step.pop("seconds")
        for r in results
        for step in r["steps"]
    }
    write_result(
        "p6_schema",
        data,
        {"wall_time_s": round(time.monotonic() - started, 2), "step_seconds": timings},
    )
    (ROOT / "research" / "results" / "p6_schema.partial.json").unlink(missing_ok=True)
    _ledger(data)
    print(json.dumps([{k: v for k, v in r.items() if k != "steps"} for r in results]))
    for r in results:
        for s in r["steps"]:
            print(
                r["grid"], r["p"], r["q"], s["N"], s["decision"], s["instances"], s.get("seconds")
            )
            for sk in s.get("skeletons", [])[:5]:
                print(
                    "   ",
                    sk["instances"],
                    sk["relata"],
                    sk["principles"],
                    sk["logically_isomorphic_to_baseline"],
                    sk["largest_population"],
                    sk.get("verification", {}).get("cli_decision"),
                    sk.get("verification", {}).get("escape_k_min"),
                )
                print("      ", sk["example"])


def triangle_fires(grid: Grid, q: int) -> bool:
    """Closed-form firing condition of the MNEP/Dominance/Non-Anti-Egalitarianism triangle.

    With empty MNEP background the bundle is q very-high lives plus one slightly negative life;
    the triangle needs a very-low level c with some very-low level above it and
    (q * min VH + min SN) / (q + 1) < c.
    """
    below_top = sorted(grid.very_low)[:-1]
    if not below_top:
        return False
    bundle = Fraction(q * min(grid.very_high) + min(grid.slightly_negative), q + 1)
    return bundle < max(below_top)


def _ledger(data: dict[str, Any]) -> None:
    entries = []
    for run in data["runs"]:
        grid = GRIDS[run["grid"]]
        steps = run["steps"]
        last = steps[-1]
        tier = (
            "unreviewed schema generalization"
            if run["grid"] == "baseline"
            else "unreviewed schema generalization + rational-cardinal spacing sensitivity"
        )
        predicted = triangle_fires(grid, run["q"])
        if run["smallest_unsat_N"] is None:
            result = (
                f"SAT for every N <= {run['N_max']} ({last['populations']} populations, "
                f"{last['instances']} instances at N={last['N']}); every SAT rank model checked "
                "against all instances"
            )
            status = "confirmed"
        else:
            skeletons = last["skeletons"]
            result = (
                f"smallest UNSAT N = {run['smallest_unsat_N']}; {last['cores_found']} cores, "
                f"{len(skeletons)} distinct skeletons; smallest: {skeletons[0]['example']} "
                f"(CLI {skeletons[0]['verification']['cli_decision']}, enumerator models "
                f"{skeletons[0]['verification']['complete_preorders_satisfying_core']})"
            )
            status = "confirmed"
        entries.append(
            LedgerEntry(
                candidate_id=f"P6-{run['grid']}-p{run['p']}q{run['q']}",
                hypothesis=(
                    f"Under v0 schema + W(p={run['p']}, q={run['q']}) on the {run['grid']} grid a "
                    f"contradiction exists among populations of at most {run['N_max']} lives."
                ),
                motivation="Search for proof skeletons other than the baseline's.",
                exact_formal_change=f"{SCHEMA_ID}: universal instances over D_N; W fixed",
                scope=f"levels {list(grid.levels)}; N <= {run['N_max']}",
                search_method="rank encoding (complete branch), nested D_N, core minimization",
                result=result + f"; triangle closed form predicts firing: {predicted}",
                evidence_type="Z3 rank encoding; UNSAT cores re-verified by CLI atom encoding "
                "and exhaustive enumeration",
                checked=True,
                minimal="cores deletion-minimal; skeleton search capped (not all MUSes)",
                interpretation=(
                    "No skeleton smaller than the known one in this range."
                    if run["smallest_unsat_N"] is None
                    else "Triangle skeleton: MNEP bundle ⪰ (q+1)·b ≻ (q+1)·c and "
                    "¬(bundle ≻ (q+1)·c), fired by close category spacing."
                ),
                next_experiment="raise N; add a source-justified VH/VL gap to the schema",
                result_scope="finite computational result",
                formalization_tier=tier,
                status=status,
                witness_conditions=f"W: A = {run['p']} life at {max(grid.very_high)}; MNEP n = {run['q']}",
                completion_status="complete for the stated N range; skeleton list capped",
            )
        )
    for run in data["runs"]:
        last = run["steps"][-1]
        if last["decision"] != "unsat":
            continue
        for k, sk in enumerate(last["skeletons"]):
            known = sk.get("known_ground", {})
            if (
                sk["instances"] <= 3
                or sk["logically_isomorphic_to_baseline"]
                or known.get("exact_known")
            ):
                continue
            v = sk.get("verification")
            entries.append(
                LedgerEntry(
                    candidate_id=f"P6-skeleton-{run['grid']}-p{run['p']}q{run['q']}-{k}",
                    hypothesis="A v0 proof skeleton not isomorphic to the baseline skeleton exists.",
                    motivation="Search for non-isomorphic minimal comparison graphs.",
                    exact_formal_change=f"{SCHEMA_ID}; solver-discovered core",
                    scope=f"{run['grid']} grid, N={last['N']}, W(p={run['p']}, q={run['q']})",
                    search_method="rank-encoded core, deletion-minimized; colored-hypergraph canonical form",
                    result=(
                        f"{sk['instances']} instances over {sk['relata']} relata "
                        f"({sk['principles']}); largest population {sk['largest_population']}; "
                        + (
                            f"CLI {v['cli_decision']}, enumerator models "
                            f"{v['complete_preorders_satisfying_core']}, completeness MUS sizes "
                            f"{v['completeness_mus_sizes']}, escape k_min {v['escape_k_min']}"
                            if v
                            else "not re-verified (ranked below top 3)"
                        )
                        + f"; core: {sk['example']}"
                        + (
                            f"; known ground {known['per_known']}, uncovered by published "
                            f"skeletons: {known['uncovered_by_published']}"
                            if known
                            else ""
                        )
                    ),
                    evidence_type="Z3 rank encoding + CLI atom encoding + exhaustive enumeration"
                    if v
                    else "Z3 rank encoding",
                    checked=bool(v),
                    minimal="deletion-minimal core",
                    interpretation="See REPORT.md R6.",
                    next_experiment="human fidelity review of Addition with a negative life in the lower group and MNEP on a nonempty background",
                    result_scope="finite computational result",
                    formalization_tier="solver-discovered proof skeleton (unreviewed schema)",
                    status="confirmed",
                    witness_conditions=f"W: A = {run['p']} life at the VH level; MNEP n = {run['q']}",
                )
            )
    record(entries)


if __name__ == "__main__":
    import sys

    if "--ledger-only" in sys.argv:
        _ledger(
            json.loads((ROOT / "research" / "results" / "p6_schema.json").read_text())["result"]
        )
    else:
        main()
