"""Phase 13: the bounce theorem. Egalitarian Dominance, Quantity and Restricted Quality Addition
are jointly inconsistent.

Statement. No quasi-ordering satisfies Egalitarian Dominance, Quantity, and Restricted Quality
Addition (2009 Lemma 3's derived condition). Indeed it suffices that some n lives at one level
W_x are at least as good as every population in R(1, y) with at least m lives.

Proof. Let Restricted Quality Addition's witness give n lives at W_x (x > y ≥ 3) and a size
threshold m, and write A for n lives at W_x. Quantity is ∀n ∃m' > n: m' lives at W_j ⪰ n lives
at W_{j+1}; write q_j(s) for its witness.
1. Straight chain: s_0 = q_1(q_2(… q_{x−1}(n))) lives at W_1 ⪰ … ⪰ A, by Quantity once per
   level.
2. Bounce: for any size s at W_1 with s at W_1 ⪰ A, the population q_1(s) at W_1 satisfies
   q_1(s) at W_1 ⪰ s at W_2 (Quantity) ≻ s at W_1 (Egalitarian Dominance) ⪰ A. So
   S_{k+1} = q_1(S_k), starting from S_0 = s_0, gives S_k at W_1 ≻ A for every k ≥ 1.
3. q_1(s) > s, so the S_k grow without bound; pick k with S_k ≥ m. Since W_1 lies in R(1, y),
   Restricted Quality Addition (background ∅) gives A ⪰ S_k at W_1, contradicting step 2.
Transitivity is used; completeness is not. Every witness choice is covered, because step 2 only
needs Quantity's own witness at W_1 and step 3 only needs the sizes to be unbounded.

Corollary. With 2009 Lemma 2 (GNEP ⇒ δ) and Lemma 3 (Weak Quality Addition ∧ δ ⇒ Restricted
Quality Addition), {Egalitarian Dominance, GNEP, Quantity, 2009 Weak Quality Addition} is
inconsistent, for Weak Quality Addition in Thornley's repaired form (its negative level and
number fixed before the background; Thornley 2022 fn. 7). Arrhenius's own derivation of Lemma 3
has an error (Thomas 2018 fn. 4). The ladder encodes the repaired form, so the possibility map's
gap of that name is explained under that reading.

Literature (corpus/literature.toml, collision P13): under full comparability the theorem is
thesis Theorem 1 plus Appendix B; the completeness-free bounce was not found.

This phase freezes one instance (m = 5, Quantity's witness m' = n + 1), verifies it like
Phase 8, and records the result.
"""

from __future__ import annotations

import json
import time
from typing import Any

from research.lab import ROOT, LedgerEntry, background, record, write_result
from research.ladder import Ladder, Witness, audit
from research.p6_schema import _cli, core_constraints, materialize, name_of
from research.p8_catalogue import CLI_GRID, Frozen, _decide, _pop

LADDER = Ladder(negative=1, positive=6)
WITNESS = Witness(
    {"quantity": {"step": 1}, "restricted-quality-addition": {"x": 4, "y": 3, "n": 1, "m": 5}}
)
BOUNCE = Frozen(
    "project-bounce-restricted-quality",
    "project",
    "research/p13_bounce.py",
    {
        "S0": _pop((1, 4)),
        "C2": _pop((2, 3)),
        "C3": _pop((3, 2)),
        "A": _pop((4, 1)),
        "S1": _pop((1, 5)),
        "B2": _pop((2, 4)),
    },
    (
        ("thesis:quantity", "S0", "C2"),
        ("thesis:quantity", "C2", "C3"),
        ("thesis:quantity", "C3", "A"),
        ("arrhenius-2009:restricted-quality-addition", "A", "S1"),
        ("thesis:quantity", "S1", "B2"),
        ("thesis:egalitarian-dominance", "B2", "S0"),
    ),
    "Straight Quantity chain from 4 lives at W_1 to A, one bounce (5 at W_1 ⪰ 4 at W_2 ≻ 4 at W_1), "
    "closed by Restricted Quality Addition with threshold m = 5.",
)


def main() -> None:
    started = time.monotonic()
    core = BOUNCE.instances()
    names = tuple(sorted(name_of(p) for p in BOUNCE.populations.values()))
    bg = background(names)
    constraints = core_constraints(core, f"{BOUNCE.id}.selected-witness/v1")
    hard = [*bg["reflexivity"], *bg["transitivity"], *constraints]
    drop = {
        p: _decide([c for c in hard if c.principle_id != p], names)
        for p in sorted({c.principle_id for c in constraints})
    }
    tag = f"{BOUNCE.id}-ladder-1-6"
    toml = materialize(
        tag,
        CLI_GRID,
        core,
        1,
        1,
        max(len(p) for p in BOUNCE.populations.values()),
        source_ids=("arrhenius-2009-one-more", "arrhenius-2000-thesis"),
        formalization_id=f"{BOUNCE.id}.selected-witness/v1",
        source_fidelity="project theorem instance; conditions read from the sources",
        claim_kind="bounded-proof-instance",
        bindings={"ladder_negative": LADDER.negative, "ladder_positive": LADDER.positive},
        completeness_candidate=False,
    )
    out = ROOT / "research" / "results" / f"{tag}.run.json"
    _cli("run", toml, "--format", "json", "--output", str(out))
    verified = _cli("verify", str(out))
    run_record = json.loads(out.read_text())
    out.unlink()
    data: dict[str, Any] = {
        "populations": {k: list(v) for k, v in BOUNCE.populations.items()},
        "core": [list(e) for e in BOUNCE.core],
        "audit": all(audit(i, LADDER, WITNESS) for i in core),
        "decision_without_completeness": _decide(hard, names),
        "drop_one_principle": drop,
        "cli_decision": run_record["outcome"]["decision"],
        "cli_verify_accepted": "verification: accepted" in verified,
        "problem_id": run_record["problem_id"],
        "toml": toml,
    }
    write_result("p13_bounce", data, {"wall_time_s": round(time.monotonic() - started, 1)})
    ok = (
        data["audit"]
        and data["decision_without_completeness"] == "unsat"
        and data["cli_decision"] == "unsat"
        and data["cli_verify_accepted"]
        and all(v == "sat" for v in drop.values())
    )
    record(
        [
            LedgerEntry(
                candidate_id="P13-bounce-theorem",
                hypothesis="Egalitarian Dominance, Quantity and Restricted Quality Addition are jointly inconsistent; hence so are Egalitarian Dominance, GNEP, Quantity and 2009 Weak Quality Addition.",
                motivation="An open gap of the possibility map (Q-010) resisted every model; the resistance pointed to a proof.",
                exact_formal_change="parametric proof in research/p13_bounce.py; one frozen instance on W_-1..W_6",
                scope="all witnesses (proof); the instance is checked mechanically",
                search_method="hand proof + Z3/DPLL + production CLI on the instance",
                result=f"instance: {data['decision_without_completeness']} without completeness; CLI {data['cli_decision']}; drop-one {drop}; audit {'pass' if data['audit'] else 'FAIL'}",
                evidence_type="written proof + checked instance",
                checked=ok,
                minimal="principle-minimal on the instance",
                interpretation="Theorem 1 survives weakening Quality to a size-restricted quality condition, because an Egalitarian Dominance bounce inside the Quantity chain makes the low population arbitrarily large. The corollary is a 4-condition impossibility from the 2009 conditions without Non-Elitism or Weak Non-Sadism.",
                next_experiment="literature check; look for the bounce in other open gaps",
                result_scope="checked theorem",
                formalization_tier="written proof over cross-read conditions",
                witness_conditions="proof covers every witness; instance uses research/p13_bounce.py WITNESS",
                novelty_status="partial collision (see corpus collision P13)",
                status="confirmed" if ok else "refuted",
            )
        ]
    )
    print(json.dumps({k: v for k, v in data.items() if k != "toml"}, indent=1))


if __name__ == "__main__":
    main()
