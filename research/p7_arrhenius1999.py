"""Phase 7: Arrhenius (1999) as a second frozen problem, and known-ground classification.

The 1999 theorem is frozen as ``arrhenius-1999.selected-witness/v1`` (``corpus/sources.toml``):
witnesses p = q = 1, r = 5 on the gapped grid, so its populations are the ones R6 reuses.
Its five conditions are all at-least-as-good except Egalitarian Dominance, and no completeness
is assumed. The phase checks the contradiction three ways, finds its transitivity cores,
tests the transitivity weakenings used in Phase 4, and classifies the baseline and R6 against
the known-skeleton catalogue in ``research/known.py``.
"""

from __future__ import annotations

import json
import time
from collections import Counter
from typing import Any

from population_ethics.principles import GroundConstraint
from research.known import CATALOGUE, known_ground
from research.lab import (
    ROOT,
    Engine,
    LedgerEntry,
    background,
    compile_predicate,
    dpll_check,
    marco,
    preorders,
    record,
    write_result,
)
from research.p4_mutations import acyclicity, quasi_transitivity, suzumura
from research.p6_schema import GRIDS, _cli, core_constraints, materialize, name_of, verify_core
from research.schema import (
    BASELINE_SKELETON,
    Grid,
    Instance,
    Pop,
    RankEngine,
    check_instance,
    domain,
)

FORMALIZATION_ID = "arrhenius-1999.selected-witness/v1"
GRID = GRIDS["gapped"]
P, Q, R = 1, 1, 5
VLP1, VLP2, VLP3 = 1, 5, 7
VH = max(GRID.very_high)
SN = min(GRID.slightly_negative)


def _pop(*parts: tuple[int, int]) -> Pop:
    return tuple(sorted(v for v, n in parts for _ in range(n)))


# Source names (p. 17) for the five populations the proof compares.
POPULATIONS: dict[str, Pop] = {
    "AAE": _pop((VH, P + Q), (SN, 1)),  # A_p ∪ A'_q ∪ E_1
    "AB": _pop((VH, P), (VLP3, Q + 1)),  # A_p ∪ B_{q+1}
    "BC": _pop((VLP3, Q + 1 + P + R - 1)),  # B_{q+1} ∪ C_{p+r-1}
    "G": _pop((VLP2, P + Q + R)),  # G_{p+q+r}
    "AAF": _pop((VH, P + Q), (VLP1, R)),  # A_p ∪ A'_q ∪ F_r
}

CORE = [
    Instance(
        "arrhenius-1999:minimal-non-extreme-priority", (POPULATIONS["AAE"], POPULATIONS["AB"])
    ),
    Instance("arrhenius-1999:quality-addition", (POPULATIONS["AB"], POPULATIONS["BC"])),
    Instance("arrhenius-1999:egalitarian-dominance", (POPULATIONS["BC"], POPULATIONS["G"])),
    Instance("arrhenius-1999:minimal-inequality-aversion", (POPULATIONS["G"], POPULATIONS["AAF"])),
    Instance("arrhenius-1999:non-sadism", (POPULATIONS["AAF"], POPULATIONS["AAE"])),
]

# R6 as found on the gapped grid by Phase 6 (REPORT.md R6).
R6_CORE = [
    Instance("dominance", (_pop((7, 7)), _pop((6, 7)))),
    Instance("dominance", (_pop((6, 7)), _pop((5, 7)))),
    Instance("non-anti-egalitarianism", (_pop((1, 5), (14, 2)), _pop((5, 7)))),
    Instance("non-repugnance", (_pop((7, 7)), _pop((14, 1)))),
    Instance("non-sadism", (_pop((-1, 1), (14, 2)), _pop((1, 5), (14, 2)))),
    Instance("mnep", (_pop((-1, 1), (14, 2)), _pop((7, 2), (14, 1)))),
    Instance("mnep", (_pop((-1, 1), (6, 5), (14, 1)), _pop((6, 7)))),
    Instance("addition", (_pop((14, 1)), _pop((7, 2), (14, 1)), _pop((-1, 1), (6, 5), (14, 1)))),
]


def audit(inst: Instance, grid: Grid) -> bool:
    """Re-derive each 1999 condition's applicability from the populations (pp. 15–17).

    Existential witnesses are the declared A_p (p lives at the very-high level), MNEP n = q, and
    MIA m = r. MNEP and Non-Sadism reuse the v0 decomposition checks, whose side conditions
    match the 1999 wording; Non-Sadism's arguments are in positive order here.
    """
    x, y = (Counter(a) for a in inst.args)
    name = inst.principle.removeprefix("arrhenius-1999:")
    if name == "minimal-non-extreme-priority":
        return check_instance(Instance("mnep", inst.args), grid, P, Q)
    if name == "non-sadism":
        return check_instance(Instance("non-sadism", (inst.args[1], inst.args[0])), grid, P, Q)
    if name == "egalitarian-dominance":
        a, b = inst.args
        return len(a) == len(b) and len(set(a)) == 1 and min(a) > max(b)
    if name == "quality-addition":
        background = x & y
        added, lowered = x - background, y - background
        return (
            added == Counter({VH: P})
            and bool(lowered)
            and all(v in grid.very_low for v in lowered.elements())
        )
    if name == "minimal-inequality-aversion":
        c, mixed = inst.args
        levels = sorted(set(mixed))
        if len(c) != len(mixed) or len(set(c)) != 1 or len(levels) != 2:
            return False
        low, high = levels
        return y[low] == R and y[high] < R and c[0] > low
    return False


def _principle_constraints() -> list[GroundConstraint]:
    return core_constraints(CORE, FORMALIZATION_ID)


def _names() -> tuple[str, ...]:
    return tuple(sorted(name_of(p) for p in POPULATIONS.values()))


def _decide(hard: list[GroundConstraint], names: tuple[str, ...]) -> str:
    z = Engine(names, hard).require().decision
    d, _ = dpll_check([c.formula for c in hard])
    if z != d:
        raise AssertionError(f"Z3 {z} disagrees with DPLL {d}")
    return z


def frozen_problem() -> dict[str, Any]:
    names = _names()
    bg = background(names)
    principles = _principle_constraints()
    tag = "arrhenius-1999-p1q1r5"
    toml = materialize(
        tag,
        GRID,
        CORE,
        P,
        Q,
        max(len(p) for p in POPULATIONS.values()),
        source_ids=("arrhenius-1999",),
        formalization_id=FORMALIZATION_ID,
        source_fidelity="selected finite witness instance; not the unrestricted theorem",
        claim_kind="bounded-proof-instance",
        bindings={"p": P, "q": Q, "r": R},
        completeness_candidate=False,
    )
    out = ROOT / "research" / "results" / f"{tag}.run.json"
    _cli("run", toml, "--format", "json", "--output", str(out))
    verified = _cli("verify", str(out))
    run_record = json.loads(out.read_text())
    cli_decision = run_record["outcome"]["decision"]
    out.unlink()

    predicate = compile_predicate([c.formula for c in principles], names)
    satisfying_preorders = sum(1 for m in preorders(len(names)) if predicate(m))

    hard = [*bg["reflexivity"], *bg["transitivity"], *principles]
    by_principle = {}
    for c in principles:
        by_principle[c.principle_id] = _decide([x for x in hard if x.id != c.id], names)

    # Transitivity cores: principles hard, transitivity instances soft.
    t_engine = Engine(names, [*bg["reflexivity"], *principles], bg["transitivity"])
    t_muses, _ = marco(t_engine)

    weakenings = {}
    for label, relation in (
        ("quasi-transitivity", quasi_transitivity(names)),
        ("strict acyclicity", acyclicity(names)),
        ("suzumura consistency", suzumura(names)),
    ):
        for with_completeness in (False, True):
            extra = bg["completeness"] if with_completeness else ()
            key = f"{label}{' + completeness' if with_completeness else ''}"
            weakenings[key] = _decide([*bg["reflexivity"], *relation, *principles, *extra], names)

    return {
        "formalization_id": FORMALIZATION_ID,
        "witness": {"p": P, "q": Q, "r": R, "grid": GRID.name},
        "populations": {k: list(v) for k, v in POPULATIONS.items()},
        "toml": toml,
        "all_instances_pass_applicability_audit": all(audit(i, GRID) for i in CORE),
        "decision_without_completeness": _decide(hard, names),
        "cli_decision": cli_decision,
        "problem_id": run_record["problem_id"],
        "cli_verify_accepted": "verification: accepted" in verified,
        "preorders_checked": sum(1 for _ in preorders(len(names))),
        "preorders_satisfying_principles": satisfying_preorders,
        "drop_one_principle": by_principle,
        "transitivity_mus_sizes": dict(sorted(Counter(len(m) for m in t_muses).items())),
        "transitivity_minimum_cores": [
            list(m) for m in t_muses if len(m) == min(map(len, t_muses))
        ],
        "weakenings": weakenings,
    }


def classifications() -> dict[str, Any]:
    r6_pops = sorted({x for inst in R6_CORE for x in inst.args})
    r6_audit = all(check_instance(i, GRID, 1, 1) for i in R6_CORE)
    rank = RankEngine(domain(GRID, 7), R6_CORE)
    r6_decision, _, _ = rank.check(list(range(len(R6_CORE))))
    literature = [k for k in CATALOGUE if k.id != "arrhenius-2000-ep"]
    # Phase 6 now ranks R6 last as known ground, so its CLI evidence is produced here.
    r6_verification = verify_core("r6-gapped-p1q1", GRID, R6_CORE, 1, 1, 7)
    return {
        "catalogue": {k.id: {"sources": list(k.sources), "edges": len(k.edges)} for k in CATALOGUE},
        "arrhenius-1999 frozen core": known_ground(CORE),
        "arrhenius-2000 baseline vs the rest of the catalogue": known_ground(
            BASELINE_SKELETON, literature
        ),
        "R6 core": {
            "relata": len(r6_pops),
            "applicability_audit": r6_audit,
            "rank_engine_decision": r6_decision,
            "verification": r6_verification,
            **known_ground(R6_CORE),
        },
    }


def main() -> None:
    started = time.monotonic()
    data = {"frozen": frozen_problem(), "known_ground": classifications()}
    write_result("p7_arrhenius1999", data, {"wall_time_s": round(time.monotonic() - started, 2)})
    _ledger(data)
    print(json.dumps(data, indent=2, ensure_ascii=False))


def _ledger(data: dict[str, Any]) -> None:
    f = data["frozen"]
    kg = data["known_ground"]
    r6 = kg["R6 core"]
    base = kg["arrhenius-2000 baseline vs the rest of the catalogue"]
    record(
        [
            LedgerEntry(
                candidate_id="P7-arrhenius-1999-baseline",
                hypothesis="The frozen 1999 witness is inconsistent with a preorder, without completeness.",
                motivation="Freeze Arrhenius's completeness-free theorem as a second reference problem.",
                exact_formal_change=f"{FORMALIZATION_ID}: five instances, reflexivity + transitivity",
                scope="5 relata; p = q = 1, r = 5 on the gapped grid",
                search_method="Z3 + DPLL; exhaustive preorder enumeration; production CLI",
                result=(
                    f"{f['decision_without_completeness']}; CLI {f['cli_decision']} "
                    f"(verify accepted: {f['cli_verify_accepted']}); "
                    f"{f['preorders_satisfying_principles']} of {f['preorders_checked']} preorders satisfy "
                    f"the instances; dropping any one principle: {sorted(set(f['drop_one_principle'].values()))}; "
                    f"transitivity MUS sizes {f['transitivity_mus_sizes']}; weakenings {f['weakenings']}"
                ),
                evidence_type="Z3, DPLL, enumeration, CLI",
                checked=True,
                minimal="principle set minimal (each drop is SAT); transitivity MUSes enumerated",
                interpretation=(
                    "Reproduction of a published theorem. Suzumura consistency alone yields the "
                    "contradiction, because the proof is one weak cycle closed by one strict link."
                ),
                next_experiment="use as the reference skeleton for known-ground filtering",
                result_scope="finite computational result",
                formalization_tier="frozen agent-read witness (not human-reviewed)",
                status="confirmed",
                novelty_status="not-applicable (reproduction)",
                witness_conditions="p = q = 1, r = 5; levels vlp1 = 1, vlp2 = 5, vlp3 = 7, VH = 14, SN = −1",
                parent_problem_id=f["problem_id"],
            ),
            LedgerEntry(
                candidate_id="P7-known-ground-baseline-2000",
                hypothesis="The E&P 2000 witness skeleton contains the 1999 skeleton minus one edge.",
                motivation="Measure how much of the 2000 proof the 1999 proof already contains.",
                exact_formal_change="role-labeled embedding, complete-branch normalization",
                scope="BASELINE_SKELETON against the catalogue without itself",
                search_method="maximum partial hypergraph embedding (research/known.py)",
                result=f"per known skeleton {base['per_known']}; uncovered by published: {base['uncovered_by_published']}",
                evidence_type="exhaustive branch-and-bound embedding",
                checked=True,
                minimal="maximum embedding",
                interpretation=(
                    "The 2000 proof is the 1999 cycle with Quality Addition replaced by a derived "
                    "AB ⪰ AC link (Addition, Repugnance avoidance, Non-Anti-Egalitarianism, and a "
                    "completeness case split)."
                ),
                next_experiment="check the reading against the 1999 p. 12 remark on the 1998 mimeo",
                result_scope="finite computational result",
                formalization_tier="role correspondence (project judgment)",
                status="confirmed",
                novelty_status="likely known in substance (same author, 1999 p. 12)",
            ),
            LedgerEntry(
                candidate_id="P7-known-ground-R6",
                hypothesis="R6 is a known skeleton plus a closing link.",
                motivation="Separate R6's new steps from its published frame.",
                exact_formal_change="role-labeled embedding, complete-branch normalization",
                scope="R6 core on the gapped grid, W(p=1, q=1)",
                search_method="maximum partial hypergraph embedding (research/known.py)",
                result=(
                    f"audit {r6['applicability_audit']}, rank engine {r6['rank_engine_decision']}; "
                    f"per known skeleton {r6['per_known']}; uncovered by published: "
                    f"{r6['uncovered_by_published']}"
                ),
                evidence_type="exhaustive branch-and-bound embedding",
                checked=True,
                minimal="maximum embedding",
                interpretation="Only R6's closing link is outside the published skeletons.",
                next_experiment="fidelity review of the closing link's Addition instance",
                result_scope="finite computational result",
                formalization_tier="role correspondence (project judgment)",
                status="confirmed",
                novelty_status="partial collision; closing link not found in literature",
                witness_conditions="W: A = 1 life at 14; MNEP n = 1",
            ),
        ]
    )


if __name__ == "__main__":
    main()
