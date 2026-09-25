"""Domain restriction of P21 and source-fidelity limits of two off-chain probes.

A relation satisfying universal source clauses on all finite integer-chain
profiles still satisfies them on every convex subchain containing its witness
ranges. Restrict the *full-chain relation*, rather than recomputing a closure
using only edges within the smaller domain: external intermediate populations
may matter to reachability. This makes no claim about an extra welfare level.
"""

from __future__ import annotations

import json
from typing import Any

from research.lab import LedgerEntry, record, write_result
from research.ladder import Ladder, audit, domain, instances_over, validate
from research.p20_contextual_priority import DA, ED, GNEP, NE, VRC
from research.p21_least_preorder import WITNESS, integer_certificate
from research.readings import require_reviewed

PRINCIPLES = (ED, NE, GNEP, VRC, DA)


def restriction_certificate() -> dict[str, Any]:
    """Pull back P21's relation along inclusion of a witness-containing subchain."""
    require_reviewed(PRINCIPLES)
    chain = integer_certificate()
    assert chain["machine_certificate"]["all_finite_path_lengths_checked"]
    examples = []
    for negative, positive in ((1, 6), (3, 9)):
        ladder = Ladder(negative=negative, positive=positive)
        for family in WITNESS.params:
            validate(family, ladder, WITNESS.get(family))
        insts = instances_over(domain(ladder, 2), ladder, WITNESS, PRINCIPLES)
        assert all(audit(inst, ladder, WITNESS) for inst in insts)
        examples.append(
            {
                "indexed_levels": [min(ladder.levels), max(ladder.levels)],
                "max_lives_diagnostic": 2,
                "independently_audited_instances": len(insts),
                "not_a_general_proof": True,
            }
        )
    return {
        "theorem": (
            "For every convex J subset of Z containing all W_-1,...,W_6, restrict P21's "
            "full-chain relation to every finite population profile over J, including empty. "
            "The resulting relation remains reflexive and transitive, retains every source "
            "universal W/S/N obligation on J, and preserves strict ED comparisons."
        ),
        "proof": (
            "Every source instance over J is already a source instance on Z at the same legal "
            "witness: the range and successor levels remain indexed and the witness ranges are "
            "present. A restriction of a reflexive/transitive relation stays reflexive/transitive. "
            "If ED was strict on Z, restricting cannot add a reverse comparison. Empty clauses "
            "remain satisfied, because the empty profile belongs to both universes."
        ),
        "quantifiers": "one fixed legal P21 witness; all finite profiles over each stated J; all source instances and arbitrary finite paths, not a finite cap",
        "domain_types": [
            "arbitrarily long finite intervals containing W_-1..W_6",
            "one-sided infinite integer intervals containing W_-1..W_6",
            "the full bi-infinite indexed integer chain",
            "order-isomorphic relabelings preserving successor, sign and witness ranges",
        ],
        "full_chain_certificate": {
            "all_finite_path_lengths_checked": chain["machine_certificate"][
                "all_finite_path_lengths_checked"
            ],
            "gain_bounds_verified": chain["gain_bounds_verified_for_every_positive_real_q"],
        },
        "finite_controls": examples,
        "scope_limit": "No claim about arbitrary welfare quasi-orders with off-chain levels or every satisfying axiology.",
    }


def extension_probes() -> list[dict[str, Any]]:
    """Exactly two proposed additions, without inventing missing comparability clauses."""
    return [
        {
            "probe": "inserted-level-between-W_4-and-W_5",
            "placement": "new level strictly between the existing indexed W_4 and W_5",
            "source_issue": (
                "The reviewed definitions call W_i and W_(i+1) consecutive, with no intervening "
                "welfare level. Holding the old indexes fixed makes the proposed ordering "
                "incompatible with that reading. Reindexing changes NE/GNEP successor instances "
                "and the witness threshold u=5; the reviewed source does not prescribe such a "
                "reindexing for an extra level."
            ),
            "status": "source-fidelity unresolved; fixed-index version violates consecutive-level premise",
            "primitive_closure_search": "not run: no source-authorized instance set for the insertion",
            "not_a_general_proof": True,
        },
        {
            "probe": "level-incomparable-with-every-W_i",
            "placement": "one extra welfare level incomparable to every indexed level",
            "source_issue": (
                "The life quasi-order admits incommensurable levels and the W_i select one "
                "chain. Exact indexed ranges exclude the off-chain level, but the informal "
                "higher/lower clauses refer to welfare comparison, and GNEP's 'any' shared "
                "background includes it. The reviewed source does not settle whether an "
                "unindexed level belongs to the universal welfare-level quantifiers or which "
                "mixed-profile comparisons survive translation from informal to exact clauses. "
                "Assigning it a numeric index or a private comparison rule would change the "
                "reviewed source interpretation."
            ),
            "status": "source-fidelity unresolved; off-chain axiology extension unproved",
            "primitive_closure_search": "not run: the full mixed-profile instance set is not source-determined",
            "not_a_general_proof": True,
        },
    ]


def run() -> dict[str, Any]:
    probes = extension_probes()
    assert [item["probe"] for item in probes] == [
        "inserted-level-between-W_4-and-W_5",
        "level-incomparable-with-every-W_i",
    ]
    return {
        "convex_restriction": restriction_certificate(),
        "off_chain_falsification_probes": probes,
        "source_level_status": (
            "exact finite complete-preorder W/S/I branch-cycle converse; fixed-witness "
            "fork-free source graph-cycle converse; original 2003 conjunction impossible; "
            "P21 both-weakened integer-chain model; P23 ranged-NE one-sided-chain model; "
            "unrestricted-NE plus thesis DA and off-chain extensions remain open"
        ),
        "forbidden_substructure_limit": "No all-witness source forbidden-substructure or representation iff follows from the abstract shape theorem.",
    }


def main() -> None:
    data = run()
    path = write_result("p24_domain_boundary", data, {})
    record(
        [
            LedgerEntry(
                candidate_id="P24-convex-chain-restriction",
                hypothesis="The P21 both-weakened integer-chain model restricts to every witness-containing convex subchain.",
                motivation="One whole-chain model already satisfies all universal source instances, and its witness ranges survive subchain restriction.",
                exact_formal_change="None; restrict the full P21 relation and its domain, without recomputing its primitive closure.",
                scope="every convex J subset of Z containing W_-1 through W_6; all finite profiles including empty",
                search_method="universal source-instance inclusion and preservation of quasi-order/strict comparisons under restriction; P21 machine proof control",
                result="all-size model over arbitrarily long finite, one-sided infinite and full bi-infinite indexed intervals",
                evidence_type="logical restriction theorem grounded in P21 exact full-chain path certificate",
                checked=True,
                minimal="no converse or domain-minimality claim",
                interpretation="Restriction proves existence on more indexed domains, not extensions to unindexed welfare levels.",
                next_experiment="resolve how reviewed source clauses apply to an added level before any off-chain promotion",
                result_scope="checked domain-restriction corollary of P21",
                formalization_tier="agent-cross-read thesis and 2003 clauses; P21 full integer chain",
                witness_conditions="P21 NE n=1; GNEP (u,y,n)=(5,3,1); VRC (x,u,v,y,n,m)=(-1,4,6,3,1,1)",
                novelty_status="elementary restriction corollary; no priority claim",
                status="confirmed",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            ),
            LedgerEntry(
                candidate_id="P24-off-chain-fidelity-probes",
                hypothesis="P21 or P23 relations may extend to an inserted or incomparable additional welfare level.",
                motivation="Indexed-chain existence cannot establish a model on every richer welfare quasi-order.",
                exact_formal_change="No new source principle or invented comparability convention; two proposed domain changes are probes only.",
                scope="one level inserted between W_4 and W_5; separately one level incomparable with all W_i",
                search_method="cross-read thesis/2003 definitions and quantifier scope against each proposed extension",
                result="fixed-index insertion conflicts with consecutiveness; treatment of unindexed incomparable lives remains source-fidelity open",
                evidence_type="reviewed-source ambiguity, not a finite SAT/UNSAT model search",
                checked=False,
                minimal="no claimed obstruction or model",
                interpretation="Without a source-authorized full mixed-profile instance set, neither probe supports a welfare-order iff.",
                next_experiment="obtain a new independent source reading clarifying indexing and mixed off-chain antecedents",
                result_scope="open source-fidelity question about two off-chain probes",
                formalization_tier="reviewed primary-source definitions D-014/D-023; no new generator",
                witness_conditions="P21's witness considered conditionally; extra level not assigned a private index",
                novelty_status="no mathematical priority claim",
                status="open",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            ),
        ]
    )
    print(
        json.dumps(
            {
                "result": str(path),
                "probes": [p["probe"] for p in data["off_chain_falsification_probes"]],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
