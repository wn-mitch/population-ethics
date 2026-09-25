"""Phase 22: exact branch-cycle certificates for finite complete-preorder shapes.

For a complete preorder represented by integer ranks, I(a,b,c) holds exactly when
r(b) >= r(a) or r(b) >= r(c). Pick one of these weak edges for each fork. In a
fixed branch, SCCs can be contracted iff no strict edge lies within an SCC;
the condensation is a DAG, and a longest strict-weighted path gives integer
ranks. If a branch fails, a strict edge and a return path give a simple strict
cycle. Exhausting the finitely many branches is necessary and sufficient.

This decision theorem is about finite abstract shapes under completeness, not
about source principles over incomplete population preorders or quantification
over the source's existential witnesses.
"""

from __future__ import annotations

import json
from typing import Any

from research.census import (
    ShapeEdge,
    is_fork_motif,
    minimal_cores,
    rank_certificate,
    rank_sat,
    verify_rank_certificate,
)
from research.lab import LedgerEntry, record, write_result

EXAMPLES: dict[str, tuple[int, tuple[ShapeEdge, ...]]] = {
    "weak_two_cycle": (2, (("W", (0, 1)), ("W", (1, 0)))),
    "strict_two_cycle": (2, (("S", (0, 1)), ("W", (1, 0)))),
    "one_fork": (3, (("I", (0, 1, 2)), ("S", (0, 1)), ("S", (2, 1)))),
    "two_forks": (
        4,
        (("I", (3, 1, 2)), ("I", (0, 3, 2)), ("S", (0, 1)), ("W", (2, 0))),
    ),
}


def certify_example(n: int, edges: tuple[ShapeEdge, ...]) -> dict[str, Any]:
    certificate = rank_certificate(n, edges)
    assert verify_rank_certificate(n, edges, certificate)
    assert (certificate["decision"] == "sat") == rank_sat(n, edges)
    deletion = [
        rank_certificate(n, edges[:i] + edges[i + 1 :])["decision"] for i in range(len(edges))
    ]
    return {
        "relata": n,
        "edges": [[shape, list(args)] for shape, args in edges],
        "certificate": certificate,
        "deletions": deletion,
    }


def run() -> dict[str, Any]:
    examples = {name: certify_example(*spec) for name, spec in EXAMPLES.items()}
    assert examples["weak_two_cycle"]["certificate"]["decision"] == "sat"
    assert examples["strict_two_cycle"]["certificate"]["decision"] == "unsat"
    assert examples["one_fork"]["certificate"]["decision"] == "unsat"
    assert examples["one_fork"]["deletions"] == ["sat"] * 3
    assert examples["two_forks"]["certificate"]["decision"] == "unsat"
    assert examples["two_forks"]["deletions"] == ["sat"] * 4
    bound = 4
    cores = minimal_cores(bound, max_forks=2)
    fork_counts: dict[int, int] = {}
    for core in cores.minimal:
        forks = sum(shape == "I" for shape, _ in core[1])
        fork_counts[forks] = fork_counts.get(forks, 0) + 1
    return {
        "theorem": "Finite W/S/I under a complete preorder is satisfiable iff one fork-branch assignment has no strict directed cycle; otherwise one simple strict cycle per assignment is a complete obstruction certificate.",
        "proof": "Completeness changes each negated strict antecedent to a weak reverse edge. Choosing a true disjunct in each I gives one W/S branch. Every strict cycle contradicts rank inequalities. If none exists, SCC contraction has only weak internal edges and the DAG longest strict-weighted path assigns integer ranks; it satisfies every edge. Conversely every model chooses at least one true disjunct for each fork, so all-branch strict cycles exclude every model.",
        "examples": examples,
        "minimal_core_census": {
            "max_edges": bound,
            "max_forks": 2,
            "fork_counts": fork_counts,
            "all_one_fork_cases_match_motif": all(
                is_fork_motif(core)
                for core in cores.minimal
                if sum(shape == "I" for shape, _ in core[1]) == 1
            ),
            "not_a_general_proof": True,
        },
        "one_fork_theorem": "Every deletion-minimal UNSAT set with one I(a,b,c) consists of the fork and the union of two simple strict paths a to b and c to b. Removing the fork leaves a SAT W/S graph; each refuting branch cycle must use its added weak edge, and removing that edge leaves the requisite strict path. Any base edge outside both paths could be deleted while preserving both cycles, contradicting minimality. Paths may overlap or coincide when a=c. The path-union form alone does not imply minimality.",
        "two_fork_control": "The four-edge two-fork example is deletion-minimal UNSAT; it has no one-fork UNSAT subcore and requires all four branch cycles.",
        "multiple_fork_compression": "Open: the branch-cycle certificate decides any finite input without a finite parameterized motif-family theorem.",
        "source_scope": "No source-level existential-witness or unrestricted welfare-domain conclusion follows.",
    }


def main() -> None:
    data = run()
    path = write_result("p22_shape_classification", data, {})
    record(
        [
            LedgerEntry(
                candidate_id="P22-complete-shape-branch-cycles",
                hypothesis="Finite W/S/I shapes under complete preorders admit an exact satisfiability and obstruction classification.",
                motivation="A bounded motif census does not classify graphs with arbitrary numbers of forks or vertices.",
                exact_formal_change="None; W and S are rank comparisons, I is the implication from strict preference to weak preference under completeness.",
                scope="arbitrary finite distinct abstract relata and finite W/S/I multisets under a complete preorder",
                search_method="exhaust fork assignments; SCC contraction and weighted longest paths; simple strict-cycle replay per branch",
                result="exact decision and obstruction converse; bounded core census only, not a finite motif-family classification",
                evidence_type="general graph proof and independently replayed SAT/UNSAT certificates",
                checked=True,
                minimal="the displayed one-fork core is deletion-minimal; no motif-family minimality claim",
                interpretation="The source's incomplete quasi-order and existential witnesses require a separate lift.",
                next_experiment="classify realizable fixed-witness source cycles, keeping multi-fork motif compression open",
                result_scope="checked finite abstract-shape theorem",
                formalization_tier="abstract complete-preorder shape calculus; not a source principle",
                witness_conditions="no source witnesses; one fork choice per abstract I edge",
                novelty_status="standard difference-constraint/SCC criterion; no priority claim",
                status="confirmed",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            )
        ]
    )
    print(json.dumps({"result": str(path), "examples": data["examples"]}, indent=2))


if __name__ == "__main__":
    main()
