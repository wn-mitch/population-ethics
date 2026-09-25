"""Phase 23: independent probes of the two singly weakened 2003 VRC corners.

Original impossibility belongs to the published 2003 theorem. The both-weakened
integer-chain model is P21. A fixed-witness or bounded diagnostic for either
remaining corner is not an all-witness impossibility or a full-domain model.
"""

from __future__ import annotations

import json
from typing import Any

from research.lab import LedgerEntry, record, write_result
from research.p17_vrc_boundary import VARIANTS
from research.p18_vrc_certificate import compact_closure, control_edges
from research.p23_not_worse_da import probe as not_worse_probe
from research.p23_ranged_ne import probe as ranged_probe


def run() -> dict[str, Any]:
    labels = [label for label, _, _ in VARIANTS]
    assert labels == ["original", "ranged-ne", "not-worse-da", "both-weakened"]
    primitive = [edge.instance for edge in control_edges()]
    original = compact_closure(primitive, "p23-original-control/v1")
    assert original["decision_without_completeness"] == "unsat" and original["path_ok"]
    ranged = ranged_probe()
    not_worse = not_worse_probe()
    assert ranged["corner"] == labels[1] and not_worse["corner"] == labels[2]
    assert ranged["status"] in {"open", "consistent", "impossible"}
    assert not_worse["status"] in {"open", "consistent", "impossible"}
    return {
        "quantifiers": "One legal witness plus every source instance on the stated domain proves consistency; impossibility requires an audited contradiction for every valid existential witness. Finite caps and chosen-witness cycles decide neither.",
        "variants": [
            {
                "label": label,
                "non_elitism": ne,
                "dominance_addition": da,
                "status": (
                    "source-general impossible (published 2003 theorem)"
                    if label == "original"
                    else "all-size model on one indexed integer welfare chain (P21)"
                    if label == "both-weakened"
                    else ranged["status"]
                    if label == "ranged-ne"
                    else not_worse["status"]
                ),
            }
            for label, ne, da in VARIANTS
        ],
        "original_fixed_witness_control": {
            "primitive_edges": len(primitive),
            "decision": original["decision_without_completeness"],
            "witness_scope": "P18 selected witness only; published theorem supplies source-general claim",
        },
        "both_weakened_control": "P21-integer-chain-both-weakened: one legal uniform witness, every finite population profile and every path; P21 unchanged.",
        "single_weakening_probes": [ranged, not_worse],
    }


def main() -> None:
    data = run()
    path = write_result("p23_vrc_corners", data, {})
    record(
        [
            LedgerEntry(
                candidate_id="P23-vrc-corner-probes",
                hypothesis="Classify both singly weakened 2003 conjunctions without conflating their existential witnesses.",
                motivation="P21 proves the both-weakened corner; chosen-witness cycles do not quantify over every legal witness.",
                exact_formal_change="None; use the four variants keyed by research/p17_vrc_boundary.py:VARIANTS.",
                scope="original and both-weakened controls plus a ranged-NE model and a not-worse-DA selected-witness contradiction",
                search_method="audited primitive controls, universal one-sided-chain invariant, independent finite selected-witness route",
                result="ranged-NE is consistent on one full welfare chain; not-worse-DA remains source-general open",
                evidence_type="all-size graph proof, audited source-instance probes, published original theorem and P21 unbounded model",
                checked=True,
                minimal="no minimal source-general impossibility claim",
                interpretation="Positive 2003 DA is modeled with thesis ranged NE; N-shaped DA with 2003 unrestricted NE remains open.",
                next_experiment="seek a not-worse-DA all-size model at another legal witness or an arbitrary-witness primitive cycle",
                result_scope="source-general existence of a ranged-NE model; selected-witness not-worse-DA diagnostic",
                formalization_tier="agent-cross-read source clauses with exact invariant proof and audited finite instances",
                witness_conditions="NE n=1, GNEP (u,y,n)=(5,3,1), VRC (x,u,v,y,n,m)=(-1,4,6,3,1,1)",
                novelty_status="no priority claim; targeted literature comparison incomplete",
                status="confirmed",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            ),
            LedgerEntry(
                candidate_id="P23-ranged-ne-all-size-model",
                hypothesis="The 2003 conjunction remains satisfiable when only Non-Elitism is weakened to the thesis ranged-background form.",
                motivation="Positive 2003 Dominance Addition adds decreasing-cardinality edges absent from P21's generator.",
                exact_formal_change="Replace only 2003 Non-Elitism by thesis ranged Non-Elitism; keep positive weak 2003 DA, ED, GNEP and VRC.",
                scope="all finite population profiles over each chain {W_-1,...,W_k}, k>=6 or k unbounded above, including empty",
                search_method="closure of all source primitives; integer potential for size-preserving edges, Psi invariant excluding VRC-to-DA paths; universal level SMT checks",
                result="partial-order model at one legal witness for the ranged-NE corner; no claim for the bi-infinite chain or richer quasi-orders",
                evidence_type="symbolic all-size path and invariant proof; independently audited bounded source controls",
                checked=True,
                minimal="no minimal welfare domain, witness or relation claim",
                interpretation="The original 2003 impossibility does not survive replacing only unrestricted NE with ranged NE on this permitted chain.",
                next_experiment="test whether the full integer chain or off-chain domains admit an extension",
                result_scope="checked full-domain consistency theorem on one source-permitted one-sided welfare chain",
                formalization_tier="agent-cross-read 2003/thesis clauses with source-permitted empty cases checked",
                witness_conditions="NE n=1; GNEP (u,y,n)=(5,3,1); VRC (x,u,v,y,n,m)=(-1,4,6,3,1,1)",
                novelty_status="not claimed; literature comparison incomplete",
                status="confirmed",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            ),
            LedgerEntry(
                candidate_id="P23-not-worse-da-fixed-witness-obstruction",
                hypothesis="2003 unrestricted Non-Elitism with thesis N-shaped Dominance Addition is inconsistent at P21's legal witness.",
                motivation="P21's background-restricted invariant does not apply to unrestricted NE.",
                exact_formal_change="Replace only 2003 positive DA by thesis N-shaped DA; retain unrestricted 2003 NE.",
                scope="one legal P21 witness on W_-1..W_6; source-general conjunction remains open",
                search_method="shortest bounded primitive paths to a common DA target; independently replay each edge and decide induced clauses without completeness",
                result="audited contradiction at one fixed witness; NE n=2 and other witnesses remain undecided",
                evidence_type="primitive-edge manifest replay and ladder audit with focused solver contradiction",
                checked=True,
                minimal="no witness-general minimality claim",
                interpretation="The failed P21 invariant and this fixed-witness obstruction do not quantify over all source existential witnesses.",
                next_experiment="derive a parameterized all-witness chain or find a different full-domain model",
                result_scope="checked chosen-witness contradiction, unrestricted condition-set status open",
                formalization_tier="agent-cross-read 2003/thesis source clauses, audited selected witness",
                witness_conditions="NE n=1; GNEP (u,y,n)=(5,3,1); VRC (x,u,v,y,n,m)=(-1,4,6,3,1,1)",
                novelty_status="not claimed; P20 already found a different selected-witness contradiction",
                status="open",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            ),
        ]
    )
    print(json.dumps({"result": str(path), "variants": data["variants"]}, indent=2))


if __name__ == "__main__":
    main()
