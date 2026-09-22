"""Phase 4: controlled mutations from the frozen catalogue ``research/mutations.toml``.

Every mutation is decided twice (Z3 ``Engine`` and the pure-Python ``dpll_check``). Where the
theory is UNSAT and the proof is short, a natural-deduction certificate is assembled and
checked with the production ``check_proof`` (script level; ``verify`` does not see it).
"""

from __future__ import annotations

import hashlib
import json
import time
import tomllib
from itertools import permutations
from typing import Any

import z3  # type: ignore[import-untyped]

from population_ethics.principles import GroundConstraint
from population_ethics.proofs import (
    CHECKER_VERSION,
    ProofCertificate,
    check_proof,
    proof_certificate_to_data,
)
from population_ethics.relations import (
    FALSE,
    Formula,
    Implies,
    Not,
    conjunction,
    formula_json,
    strict,
    weak,
)
from research.lab import (
    ACTIVE,
    ROOT,
    Engine,
    LedgerEntry,
    ProofBuilder,
    background,
    dpll_check,
    ground,
    load_baseline,
    pair_id,
    pairs,
    record,
    substantive_constraints,
    write_result,
)

CATALOGUE = ROOT / "research" / "mutations.toml"
SIZES = {"A": 1, "AB": 4, "AAE": 4, "AC": 22, "AAF": 22, "D": 22, "G": 22}
AVOIDANCE = {  # avoidance constraint id -> (left, right) of the avoided strict comparison
    "avoid-repugnance:D-not-strict-A": ("D", "A"),
    "avoid-anti-egalitarianism:AC-not-strict-D": ("AC", "D"),
    "avoid-anti-egalitarianism:AAF-not-strict-G": ("AAF", "G"),
    "avoid-sadism:AAE-not-strict-AAF": ("AAE", "AAF"),
}
AVOID_PAIRS = sorted(pair_id(*v) for v in AVOIDANCE.values())
MID = "research.mutation/v1"


def strict_part(x: str, y: str) -> Formula:
    return strict(x, y)


def simple_cycles(nodes: tuple[str, ...]) -> list[tuple[str, ...]]:
    """Every directed simple cycle of length >= 2, each once (rotation fixed at its minimum)."""
    out = []
    for k in range(2, len(nodes) + 1):
        for perm in permutations(nodes, k):
            if perm[0] == min(perm):
                out.append(perm)
    return out


class Theory:
    """A named ground theory over the active relata."""

    def __init__(self, spec_constraints: dict[str, GroundConstraint]) -> None:
        self.base = spec_constraints
        bg = background(ACTIVE)
        self.reflexivity = list(bg["reflexivity"])
        self.transitivity = list(bg["transitivity"])
        self.completeness = {c.id: c for c in bg["completeness"]}

    def completeness_on(self, pair_ids: list[str]) -> list[GroundConstraint]:
        return [self.completeness[p] for p in sorted(pair_ids)]


def replaced(constraint: GroundConstraint, formula: Formula, tag: str) -> GroundConstraint:
    return ground(
        f"{constraint.id}~{tag}",
        constraint.principle_id,
        formula,
        MID,
        f"{constraint.explanation} [mutated: {tag}]",
    )


def quasi_transitivity() -> list[GroundConstraint]:
    return [
        ground(
            f"quasi-transitivity:{x}:{y}:{z}",
            "quasi-transitivity",
            Implies(conjunction(strict(x, y), strict(y, z)), strict(x, z)),
            MID,
            "Strict preference is transitive.",
        )
        for x in ACTIVE
        for y in ACTIVE
        for z in ACTIVE
        if len({x, y, z}) == 3
    ]


def acyclicity() -> list[GroundConstraint]:
    return [
        ground(
            "acyclic:" + ":".join(c),
            "acyclicity",
            Not(conjunction(*(strict(c[i], c[(i + 1) % len(c)]) for i in range(len(c))))),
            MID,
            "No cycle of strict preferences.",
        )
        for c in simple_cycles(ACTIVE)
    ]


def suzumura() -> list[GroundConstraint]:
    out = []
    for c in simple_cycles(ACTIVE):
        k = len(c)
        for s in range(k):  # the edge c[s] -> c[s+1] is the strict one, the rest weak
            edges = [
                strict(c[i], c[(i + 1) % k]) if i == s else weak(c[i], c[(i + 1) % k])
                for i in range(k)
            ]
            out.append(
                ground(
                    "suzumura:" + ":".join(c) + f"@{s}",
                    "suzumura",
                    Not(conjunction(*edges)),
                    MID,
                    "No weak cycle containing a strict edge.",
                )
            )
    return out


def decide(hard: list[GroundConstraint]) -> dict[str, Any]:
    engine = Engine(ACTIVE, hard)
    z = engine.require().decision
    d, _ = dpll_check([c.formula for c in hard])
    if z != d:
        raise AssertionError(f"Z3 {z} disagrees with DPLL {d}")
    return {"decision": z, "independent_dpll": d, "hard_constraints": len(hard)}


def theory_id(hard: list[GroundConstraint]) -> str:
    return hashlib.sha256(
        json.dumps(sorted(formula_json(c.formula) for c in hard)).encode()
    ).hexdigest()


def chain_certificate(
    hard: list[GroundConstraint], reverse: dict[str, str], addition_id: str, weak_addition: bool
) -> dict[str, Any]:
    certificate, declared = build_chain_certificate(hard, reverse, addition_id, weak_addition)
    result = check_proof(certificate, declared, expected_problem_id=certificate.problem_id)
    return {
        "checker": CHECKER_VERSION,
        "theory_id": certificate.problem_id,
        "nodes": len(certificate.nodes),
        "declared_premises_used": list(result.declared_premises),
        "certificate_sha256": hashlib.sha256(
            json.dumps(proof_certificate_to_data(certificate), sort_keys=True).encode()
        ).hexdigest(),
        "checked_by": "research/p4_mutations.py via population_ethics.proofs.check_proof",
    }


def build_chain_certificate(
    hard: list[GroundConstraint], reverse: dict[str, str], addition_id: str, weak_addition: bool
) -> tuple[ProofCertificate, dict[str, GroundConstraint]]:
    """Certificate for the four-avoidance chain proof.

    ``reverse`` maps each avoidance constraint id either to the id of its completeness premise
    ("completeness route") or to "positive" when the avoidance premise already states the
    reverse weak comparison (M2).
    """
    declared = {c.id: c for c in hard}
    b = ProofBuilder()
    trans = {c.id: c for c in hard if c.id.startswith("transitivity:")}
    derived: dict[tuple[str, str], str] = {}
    for avoidance_id, (left, right) in AVOIDANCE.items():
        prefix = f"{right}-over-{left}"
        if reverse[avoidance_id] == "positive":
            derived[(right, left)] = b.premise(prefix, declared[f"{avoidance_id}~positive"])
        else:
            derived[(right, left)] = b.reverse_from_avoidance(
                prefix, declared[reverse[avoidance_id]], declared[avoidance_id], left, right
            )
    derived[("AAE", "AB")] = b.premise("AAE-over-AB", declared["minimal-priority:AAE-weak-AB"])
    dom = b.premise("AC-strict-G", declared["dominance:AC-strict-G"])
    derived[("AC", "G")] = b.add("AC-over-G", weak("AC", "G"), "conjunction-elimination", (dom,))
    not_g_ac = b.add("not-G-over-AC", Not(weak("G", "AC")), "conjunction-elimination", (dom,))

    def chain(x: str, y: str, z: str) -> str:
        node = b.transitive(
            f"{x}-over-{z}.via-{y}",
            trans[f"transitivity:{x}:{y}:{z}"],
            derived[(x, y)],
            derived[(y, z)],
            x,
            z,
        )
        derived[(x, z)] = node
        return node

    chain("A", "D", "AC")
    chain("G", "AAF", "AAE")
    chain("G", "AAE", "AB")
    chain("A", "AC", "G")
    chain("A", "G", "AB")
    # Reductio on AB ⪰ A: it would give G ⪰ A ⪰ AC, against Dominance.
    h = b.hypothesis("hyp.AB-over-A", weak("AB", "A"))
    derived[("AB", "A")] = h
    g_a = b.transitive(
        "G-over-A.hyp", trans["transitivity:G:AB:A"], derived[("G", "AB")], h, "G", "A"
    )
    g_ac = b.transitive(
        "G-over-AC.hyp", trans["transitivity:G:A:AC"], g_a, derived[("A", "AC")], "G", "AC"
    )
    false1 = b.add("hyp.AB-over-A.false", FALSE, "contradiction", (g_ac, not_g_ac))
    not_ab_a = b.add(
        "not-AB-over-A", Not(weak("AB", "A")), "negation-introduction", (false1,), discharged=(h,)
    )
    a_strict_ab = b.add(
        "A-strict-AB",
        strict("A", "AB"),
        "conjunction-introduction",
        (derived[("A", "AB")], not_ab_a),
    )
    add = b.premise("addition", declared[addition_id])
    consequence = b.add(
        "by-addition",
        declared[addition_id].formula.consequent,  # type: ignore[union-attr]
        "implication-elimination",
        (add, a_strict_ab),
    )
    if not weak_addition:
        derived[("AB", "AC")] = consequence
        final = chain("G", "AB", "AC")
        root = b.add("contradiction", FALSE, "contradiction", (final, not_g_ac))
    else:
        # Consequent is ¬(AC ≻ AB). Derive AC ≻ AB: AC ⪰ G ⪰ AB, and AB ⪰ AC would give G ⪰ AC.
        ac_ab = chain("AC", "G", "AB")
        h2 = b.hypothesis("hyp.AB-over-AC", weak("AB", "AC"))
        g_ac2 = b.transitive(
            "G-over-AC.hyp2", trans["transitivity:G:AB:AC"], derived[("G", "AB")], h2, "G", "AC"
        )
        false2 = b.add("hyp.AB-over-AC.false", FALSE, "contradiction", (g_ac2, not_g_ac))
        not_ab_ac = b.add(
            "not-AB-over-AC",
            Not(weak("AB", "AC")),
            "negation-introduction",
            (false2,),
            discharged=(h2,),
        )
        ac_strict = b.add(
            "AC-strict-AB", strict("AC", "AB"), "conjunction-introduction", (ac_ab, not_ab_ac)
        )
        root = b.add("contradiction", FALSE, "contradiction", (ac_strict, consequence))
    return b.certificate(theory_id(hard), root), declared


def main() -> None:
    started = time.monotonic()
    catalogue = tomllib.loads(CATALOGUE.read_text())
    spec = load_baseline()
    sub = {c.id: c for c in substantive_constraints(spec)}
    T = Theory(sub)
    base = [*T.reflexivity, *T.transitivity]
    subs = list(sub.values())
    all_pairs = [pair_id(a, b) for a, b in pairs(ACTIVE)]
    same = [pair_id(a, b) for a, b in pairs(ACTIVE) if SIZES[a] == SIZES[b]]
    different = [p for p in all_pairs if p not in same]
    curated = [*AVOID_PAIRS, pair_id("AB", "AC")]
    positive = {
        cid: replaced(sub[cid], weak(right, left), "positive")
        for cid, (left, right) in AVOIDANCE.items()
    }
    weak_add = replaced(
        sub["addition:A-AB-implies-AB-AC"],
        Implies(strict("A", "AB"), Not(strict("AC", "AB"))),
        "weak-consequent",
    )
    weak_mnep = replaced(sub["minimal-priority:AAE-weak-AB"], Not(strict("AB", "AAE")), "not-worse")
    weak_dom = replaced(sub["dominance:AC-strict-G"], weak("AC", "G"), "weak")

    results: dict[str, Any] = {}
    certificates: dict[str, Any] = {}

    def run(key: str, hard: list[GroundConstraint]) -> dict[str, Any]:
        outcome = decide(hard)
        results[key] = outcome
        return outcome

    m1 = [*base, *subs, *T.completeness_on(AVOID_PAIRS)]
    run("M1-local-completeness-avoidance", m1)
    certificates["M1-local-completeness-avoidance"] = chain_certificate(
        m1,
        {cid: pair_id(*AVOIDANCE[cid]) for cid in AVOIDANCE},
        "addition:A-AB-implies-AB-AC",
        weak_addition=False,
    )
    run("M1b-curated-completeness", [*base, *subs, *T.completeness_on(curated)])
    run("M1c-same-number-completeness", [*base, *subs, *T.completeness_on(same)])
    run("M1d-different-number-completeness", [*base, *subs, *T.completeness_on(different)])

    m2 = [*base, *(c for c in subs if c.id not in AVOIDANCE), *positive.values()]
    run("M2-reverse-weak-avoidance-all", m2)
    certificates["M2-reverse-weak-avoidance-all"] = chain_certificate(
        m2,
        {cid: "positive" for cid in AVOIDANCE},
        "addition:A-AB-implies-AB-AC",
        weak_addition=False,
    )
    single = {}
    for cid in AVOIDANCE:
        others = [pair_id(*AVOIDANCE[o]) for o in AVOIDANCE if o != cid]
        hard = [*base, *(c for c in subs if c.id != cid), positive[cid], *T.completeness_on(others)]
        single[cid] = decide(hard)
        # Without the three remaining completeness pairs:
        single[cid + " (no completeness)"] = decide(
            [*base, *(c for c in subs if c.id != cid), positive[cid]]
        )
    results["M2s-reverse-weak-avoidance-single"] = single

    # M3: minimum-cardinality transitivity cores (implicit hitting sets), full completeness and M1.
    m3 = {}
    for label, completeness in (("full-completeness", all_pairs), ("M1-completeness", AVOID_PAIRS)):
        engine = Engine(
            ACTIVE, [*T.reflexivity, *subs, *T.completeness_on(completeness)], T.transitivity
        )
        k, minimum_sets = minimum_cores(engine)
        m3[label] = {
            "min_transitivity_instances": k,
            "count_minimum_cores": len(minimum_sets),
            "minimum_cores": minimum_sets,
        }
    results["M3-transitivity-minimum"] = m3

    for label, completeness in (("full", all_pairs), ("M1", AVOID_PAIRS), ("none", [])):
        run(
            f"M3q-quasi-transitivity/{label}",
            [*T.reflexivity, *quasi_transitivity(), *subs, *T.completeness_on(completeness)],
        )
        run(
            f"M3a-acyclicity/{label}",
            [*T.reflexivity, *acyclicity(), *subs, *T.completeness_on(completeness)],
        )
        run(
            f"M3s-suzumura/{label}",
            [*T.reflexivity, *suzumura(), *subs, *T.completeness_on(completeness)],
        )

    run(
        "M4-weak-dominance",
        [
            *base,
            *(c for c in subs if c.id != weak_dom.id.split("~")[0]),
            weak_dom,
            *T.completeness_on(all_pairs),
        ],
    )
    no_add = [c for c in subs if c.id != "addition:A-AB-implies-AB-AC"]
    run(
        "M5-weak-addition-consequent/full",
        [*base, *no_add, weak_add, *T.completeness_on(all_pairs)],
    )
    run(
        "M5-weak-addition-consequent/M1",
        [*base, *no_add, weak_add, *T.completeness_on(AVOID_PAIRS)],
    )
    run("M5-weak-addition-consequent/none", [*base, *no_add, weak_add])
    no_mnep = [c for c in subs if c.id != "minimal-priority:AAE-weak-AB"]
    run("M6-weak-mnep/full", [*base, *no_mnep, weak_mnep, *T.completeness_on(all_pairs)])
    run("M6-weak-mnep/M1", [*base, *no_mnep, weak_mnep, *T.completeness_on(AVOID_PAIRS)])
    run(
        "M6-weak-mnep/M1+AAE:AB",
        [*base, *no_mnep, weak_mnep, *T.completeness_on([*AVOID_PAIRS, pair_id("AAE", "AB")])],
    )

    c1 = [*base, *no_add, weak_add, *T.completeness_on(AVOID_PAIRS)]
    run("C1-combined-weakening", c1)
    certificates["C1-combined-weakening"] = chain_certificate(
        c1, {cid: pair_id(*AVOIDANCE[cid]) for cid in AVOIDANCE}, weak_add.id, weak_addition=True
    )
    # Local irreducibility of C1: each further single catalogue step from C1.
    steps = {
        "drop one avoidance completeness pair": [
            decide(
                [*base, *no_add, weak_add, *T.completeness_on([p for p in AVOID_PAIRS if p != q])]
            )
            for q in AVOID_PAIRS
        ],
        "quasi-transitivity instead of transitivity": decide(
            [
                *T.reflexivity,
                *quasi_transitivity(),
                *no_add,
                weak_add,
                *T.completeness_on(AVOID_PAIRS),
            ]
        ),
        "suzumura instead of transitivity": decide(
            [*T.reflexivity, *suzumura(), *no_add, weak_add, *T.completeness_on(AVOID_PAIRS)]
        ),
        "weak MNEP": decide(
            [
                *base,
                *(c for c in no_add if c.id != "minimal-priority:AAE-weak-AB"),
                weak_mnep,
                weak_add,
                *T.completeness_on(AVOID_PAIRS),
            ]
        ),
        "weak Dominance": decide(
            [
                *base,
                *(c for c in no_add if c.id != "dominance:AC-strict-G"),
                weak_dom,
                weak_add,
                *T.completeness_on(AVOID_PAIRS),
            ]
        ),
        "drop reflexivity": decide(
            [*T.transitivity, *no_add, weak_add, *T.completeness_on(AVOID_PAIRS)]
        ),
    }
    results["C1-local-irreducibility"] = steps

    data = {
        "catalogue_version": catalogue["version"],
        "catalogue_ids": [m["id"] for m in catalogue["mutation"]],
        "same_number_pairs": same,
        "results": results,
        "certificates": certificates,
    }
    write_result("p4_mutations", data, {"wall_time_s": round(time.monotonic() - started, 2)})
    _ledger(data)


def _ledger(data: dict[str, Any]) -> None:
    r = data["results"]
    c = data["certificates"]

    def d(key: str) -> str:
        return str(r[key]["decision"])

    common = {
        "scope": "frozen formulas on the 7 active relata (inert names by the P1 lemma)",
        "evidence_type": "Z3 + independent DPLL",
        "checked": True,
        "result_scope": "finite computational result",
        "formalization_tier": "logical mutation",
    }
    record(
        [
            LedgerEntry(
                candidate_id="M1-local-completeness-avoidance",
                hypothesis="Completeness on the four avoidance pairs alone suffices for UNSAT.",
                motivation="Phase 2 MUS; the curated proof's AB:AC reductio looked redundant.",
                exact_formal_change="global completeness -> completeness on A:D, AC:D, AAE:AAF, AAF:G",
                search_method="Z3 + DPLL + natural-deduction certificate (check_proof)",
                result=f"{d('M1-local-completeness-avoidance')}; certificate "
                f"{c['M1-local-completeness-avoidance']['nodes']} nodes (curated: 75 nodes, 5 pairs)",
                minimal="the 4-pair set is a MUS (P2); certificate uses 8 transitivity instances (minimum 7)",
                interpretation=(
                    "Strictly weaker sufficient assumption: only the comparisons the avoidance "
                    "principles speak about need to be settled. The AB:AC case split is unnecessary: "
                    "A⪰AB follows by transitivity and ¬(AB⪰A) by negation introduction."
                ),
                next_experiment="C1",
                status="confirmed",
                **common,  # type: ignore[arg-type]
            ),
            LedgerEntry(
                candidate_id="M1c-same-number-completeness",
                hypothesis="Same-number completeness (comparability only between equal-size populations) suffices.",
                motivation="A recognized restriction: same-number comparisons are uncontroversial.",
                exact_formal_change="completeness only between populations of equal size",
                search_method="Z3 + DPLL",
                result=f"same-number: {d('M1c-same-number-completeness')}; different-number only: "
                f"{d('M1d-different-number-completeness')}",
                minimal="n/a",
                counterexample_if_false="SAT model under same-number completeness (Z3 + DPLL agree)",
                interpretation=(
                    "The contradiction is driven by different-number comparability. With only "
                    "same-number comparisons settled the seven instances are consistent; with only "
                    "different-number comparisons settled they are not."
                ),
                next_experiment="minimum number of different-number incomparabilities (P5)",
                status="refuted",
                **common,  # type: ignore[arg-type]
            ),
            LedgerEntry(
                candidate_id="M2-reverse-weak-avoidance",
                hypothesis="With avoidance in positive form (Y⪰X), no completeness is needed.",
                motivation="Positive form differs from ¬(X≻Y) only without completeness (a strengthening).",
                exact_formal_change="each ¬(X≻Y) -> Y⪰X; completeness removed",
                search_method="Z3 + DPLL + certificate",
                result=f"all four: {d('M2-reverse-weak-avoidance-all')} with no completeness; certificate "
                f"{c['M2-reverse-weak-avoidance-all']['nodes']} nodes; single positive avoidance + "
                "other three pairs: UNSAT for each; single positive avoidance alone: SAT for each",
                minimal="each positive avoidance substitutes for exactly its own completeness pair",
                interpretation=(
                    "Completeness does exactly one job in this proof: it converts each 'not better' "
                    "avoidance into 'at least as good'. A strengthening, not a weakening."
                ),
                next_experiment="n/a",
                status="confirmed",
                **common,  # type: ignore[arg-type]
            ),
            LedgerEntry(
                candidate_id="M3-transitivity",
                hypothesis="The contradiction needs only a handful of transitivity instances; recognized weakenings of transitivity escape.",
                motivation="Replace a global principle by the exact local instances used.",
                exact_formal_change="transitivity -> minimum instance sets; quasi-transitivity; strict acyclicity; Suzumura",
                search_method="implicit-hitting-set minimum cores; Z3 + DPLL for each weakening",
                result=(
                    f"min transitivity instances: {r['M3-transitivity-minimum']['full-completeness']['min_transitivity_instances']} "
                    f"under full completeness ({r['M3-transitivity-minimum']['full-completeness']['count_minimum_cores']} minimum cores), "
                    f"{r['M3-transitivity-minimum']['M1-completeness']['min_transitivity_instances']} under M1 "
                    f"({r['M3-transitivity-minimum']['M1-completeness']['count_minimum_cores']} cores); quasi-transitivity: "
                    f"{d('M3q-quasi-transitivity/full')}; acyclicity: {d('M3a-acyclicity/full')}; Suzumura: "
                    f"{d('M3s-suzumura/full')} (full completeness), {d('M3s-suzumura/M1')} (M1)"
                ),
                minimal="minimum-cardinality cores enumerated completely",
                interpretation=(
                    "Completeness and transitivity trade off: settling more comparisons shortens the "
                    "transitive chains needed. Quasi-transitivity and acyclicity escape even with full "
                    "completeness: the proof needs transitivity of weak preference (indifference "
                    "chains), not only of strict preference. Suzumura consistency equals transitivity "
                    "under completeness and escapes under M1."
                ),
                next_experiment="n/a",
                status="confirmed",
                **common,  # type: ignore[arg-type]
            ),
            LedgerEntry(
                candidate_id="M4-M6-premise-weakenings",
                hypothesis="Weak Dominance escapes; weakened Addition and MNEP consequents survive where comparability is available.",
                motivation="Catalogue M4–M6.",
                exact_formal_change="AC≻G -> AC⪰G; Addition consequent -> ¬(AC≻AB); MNEP -> ¬(AB≻AAE)",
                search_method="Z3 + DPLL",
                result=(
                    f"weak Dominance: {d('M4-weak-dominance')}; weak Addition: full {d('M5-weak-addition-consequent/full')}, "
                    f"M1 {d('M5-weak-addition-consequent/M1')}, none {d('M5-weak-addition-consequent/none')}; "
                    f"weak MNEP: full {d('M6-weak-mnep/full')}, M1 {d('M6-weak-mnep/M1')}, "
                    f"M1+AAE:AB {d('M6-weak-mnep/M1+AAE:AB')}"
                ),
                minimal="n/a",
                interpretation=(
                    "Strict Dominance is the only strict premise and is indispensable. The Addition "
                    "consequent can be weakened to 'not better' at no cost. Weakening MNEP costs "
                    "exactly one extra comparability, AAE:AB."
                ),
                next_experiment="C1",
                status="confirmed",
                **common,  # type: ignore[arg-type]
            ),
            LedgerEntry(
                candidate_id="C1-combined-weakening",
                hypothesis="M1 + weak Addition consequent is UNSAT and locally irreducible in the catalogue.",
                motivation="Combine surviving single-step weakenings.",
                exact_formal_change="completeness on 4 avoidance pairs; Addition consequent ¬(AC≻AB)",
                search_method="Z3 + DPLL + certificate; every further single catalogue step tested",
                result=(
                    f"{d('C1-combined-weakening')}; certificate {c['C1-combined-weakening']['nodes']} nodes; "
                    "dropping any avoidance pair: SAT (all 4); quasi-transitivity: SAT; Suzumura: SAT; "
                    "weak MNEP: SAT; weak Dominance: SAT; dropping reflexivity: UNSAT (reflexivity unused)"
                ),
                minimal="locally irreducible relative to catalogue v1, except that reflexivity is idle",
                interpretation=(
                    "Candidate strengthened finite statement: no transitive relation on these seven "
                    "populations satisfies the seven instances (Addition in 'not better' form) while "
                    "settling the four avoidance comparisons. Reflexivity plays no role."
                ),
                next_experiment="check whether the same weakening holds for schema-level skeletons (P6)",
                status="confirmed",
                **common,  # type: ignore[arg-type]
            ),
        ]
    )


def minimum_cores(engine: Engine, cap: int = 500) -> tuple[int, list[list[str]]]:
    """All minimum-cardinality UNSAT subsets of ``engine.soft`` by implicit hitting sets.

    A map solver holds one clause per correction set found so far (complement of a grown
    maximal SAT set). The smallest hitting set is a lower bound on the minimum core size; when
    a smallest hitting set is UNSAT it is a minimum core. Selectors never enter the engine.
    """
    ids = sorted(engine.soft)
    sel = {cid: z3.Bool(f"h_{i}") for i, cid in enumerate(ids)}
    total = z3.Sum([z3.If(v, 1, 0) for v in sel.values()])
    mapper = z3.Solver()
    k = 0
    cores: list[list[str]] = []
    while len(cores) < cap:
        while mapper.check(total <= k) != z3.sat:
            k += 1
            if cores:  # no hitting set of the minimum size is left
                return k - 1, sorted(cores)
        model = mapper.model()
        chosen = [c for c in ids if z3.is_true(model.eval(sel[c], model_completion=True))]
        if engine.require(chosen).decision == "unsat":
            cores.append(sorted(chosen))
            mapper.add(z3.Or([z3.Not(sel[c]) for c in chosen]))
        else:
            grown = set(engine.grow(chosen))
            mapper.add(z3.Or([sel[c] for c in ids if c not in grown] or [z3.BoolVal(False)]))
    raise RuntimeError("minimum-core enumeration exceeded its cap")


if __name__ == "__main__":
    main()
