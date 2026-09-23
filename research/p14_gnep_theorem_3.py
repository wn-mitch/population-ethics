"""Phase 14: Thesis Theorem 3 with GNEP in place of NEP.

Statement. No quasi-ordering satisfies Egalitarian Dominance, Inequality Aversion, General
Non-Extreme Priority, Weak Non-Sadism and Weak Quality Addition, in the thesis form or the
2009 form. Non-Sadism implies Weak Non-Sadism, so the Non-Sadism variants follow.

Proof. Write the witnesses as: Weak Quality Addition's a lives at a very high level (and, in
the 2009 form, its m_W lives at the negative level W_q); GNEP's n_G lives at levels at or above
W_u and its very low range R(1, y), y ≥ 3; Weak Non-Sadism's e lives at the negative level W_x.
Let W_h be a level at or above both very high levels. The cycle raises every negative life to
W_3 one level at a time with GNEP, which needs s = Σ (3 − level) steps over the e + m_W
negative lives, each paid for by n_G lives at W_h.
1. Let N = a + s·n_G, let Inequality Aversion's witness for N be M > N, and let G be N + M
   lives at W_2. Inequality Aversion (x = W_h, y = W_2, z = W_1): G ⪰ N at W_h ∪ M at W_1.
2. Weak Non-Sadism, background N at W_h: replace the M lives at W_1 by e lives at W_x.
3. Weak Quality Addition, background the other s·n_G lives at W_h and the negatives: replace
   a lives at W_h by C lives at W_3 (with m_W lives at W_q in the 2009 form), where
   |C| = a + M − e − m_W. M > N ≥ a + e + m_W, so |C| > 2a.
4. s GNEP steps, each with the rest as background: n_G lives at W_h and one life at W_z become
   n_G lives at W_3 and one life at W_{z+1}. Every life now lies at W_3, and the count never
   changed, so the population is N + M lives at W_3.
5. Egalitarian Dominance: N + M lives at W_3 ≻ G. With steps 1–4 this is a strict cycle.
Transitivity is used; completeness is not. The construction covers every witness choice:
steps 1 and 3 absorb any Inequality Aversion witness, and W_h exists because both very high
levels are levels of the ladder. It needs no level above W_h. It uses GNEP directly rather
than Condition δ or 2009 Lemma 3, whose derivation has an error (Thomas 2018 fn. 4); the 2009
form needs Weak Quality Addition's negative level and number fixed before the background,
which is Thornley's repaired form and the ladder's encoding.

``cycle`` builds the construction for any witness; tests audit it over a grid of witnesses.
This phase freezes one instance per form and verifies it like Phase 8.
"""

from __future__ import annotations

import json
import time
from collections import Counter
from collections.abc import Mapping
from typing import Any

from research.lab import ROOT, LedgerEntry, background, record, write_result
from research.ladder import Ladder, Witness, audit, larger
from research.p6_schema import _cli, core_constraints, materialize, name_of
from research.p8_catalogue import CLI_GRID, Frozen, _decide
from research.schema import Pop

LADDER = Ladder(negative=1, positive=6)
ED = "thesis:egalitarian-dominance"
IA = "thesis:inequality-aversion"
GNEP = "thesis:general-non-extreme-priority"
WNS = "thesis:weak-non-sadism"
WQA = {"thesis": "thesis:weak-quality-addition", "2009": "arrhenius-2009:weak-quality-addition"}
WITNESS = Witness(
    {
        "inequality-aversion": {"step": 1},
        "general-non-extreme-priority": {"u": 4, "y": 3, "n": 1},
        "weak-non-sadism": {"x": -1, "n": 1},
        "weak-quality-addition": {"x": 4, "w": 6, "y": 3, "n": 1},
        "weak-quality-addition-negative": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
    }
)


def _pop(c: Counter[int]) -> Pop:
    return tuple(sorted(c.elements()))


def cycle(form: str, ladder: Ladder, w: Witness) -> list[tuple[str, Pop, Pop]]:
    """The proof's cycle as (principle, left, right) steps, for any witness; the last step is
    the strict Egalitarian Dominance link back to the first population."""
    g, ns = w.get("general-non-extreme-priority"), w.get("weak-non-sadism")
    if form == "thesis":
        q: Mapping[str, int] = w.get("weak-quality-addition")
        a, high, negs = q["n"], q["x"], {ns["x"]: ns["n"]}
    else:
        q = w.get("weak-quality-addition-negative")
        a, high, negs = q["n"], q["u"], Counter({ns["x"]: ns["n"]}) + Counter({q["x"]: q["m"]})
    h = max(high, g["u"])
    steps = sum((3 - lvl) * k for lvl, k in negs.items())
    n = a + steps * g["n"]
    m = larger(w.get("inequality-aversion"), n)
    out: list[tuple[str, Pop, Pop]] = []
    pop = Counter({2: n + m})
    start = _pop(pop)

    def move(principle: str, remove: Counter[int], add: Counter[int]) -> None:
        nonlocal pop
        before = _pop(pop)
        assert not remove - pop, (principle, remove, pop)
        pop = pop - remove + add
        out.append((principle, before, _pop(pop)))

    move(IA, Counter({2: n + m}), Counter({h: n, 1: m}))
    move(WNS, Counter({1: m}), Counter({ns["x"]: ns["n"]}))
    c = a + m - ns["n"] - (q["m"] if form == "2009" else 0)
    added = Counter({3: c}) + (Counter({q["x"]: q["m"]}) if form == "2009" else Counter())
    move(WQA[form], Counter({h: a}), added)
    for lvl in sorted(negs):
        for _ in range(negs[lvl]):
            for z in range(lvl, 3):
                move(
                    GNEP,
                    Counter({h: g["n"]}) + Counter({z: 1}),
                    Counter({3: g["n"]}) + Counter({z + 1: 1}),
                )
    assert pop == Counter({3: n + m}), pop
    out.append((ED, _pop(pop), start))
    return out


def frozen(form: str) -> Frozen:
    steps = cycle(form, LADDER, WITNESS)
    names = {p: f"P{i}" for i, (_, p, _) in enumerate(steps)}
    return Frozen(
        f"project-gnep-theorem-3-{form}",
        "project",
        "research/p14_gnep_theorem_3.py",
        {v: k for k, v in names.items()},
        tuple((pr, names[left], names[right]) for pr, left, right in steps),
        f"Theorem 3's cycle with GNEP raising each negative life to W_3 ({form} Weak Quality "
        "Addition).",
    )


def verify(f: Frozen, tag: str) -> dict[str, Any]:
    core = f.instances()
    names = tuple(sorted(name_of(p) for p in f.populations.values()))
    bg = background(names)
    constraints = core_constraints(core, f"{f.id}.selected-witness/v1")
    hard = [*bg["reflexivity"], *bg["transitivity"], *constraints]
    drop = {
        p: _decide([c for c in hard if c.principle_id != p], names)
        for p in sorted({c.principle_id for c in constraints})
    }
    toml = materialize(
        tag,
        CLI_GRID,
        core,
        1,
        1,
        max(len(p) for p in f.populations.values()),
        source_ids=("arrhenius-2000-thesis", "arrhenius-2009-one-more"),
        formalization_id=f"{f.id}.selected-witness/v1",
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
    return {
        "populations": {k: list(v) for k, v in f.populations.items()},
        "core": [list(e) for e in f.core],
        "audit": all(audit(i, LADDER, WITNESS) for i in core),
        "decision_without_completeness": _decide(hard, names),
        "drop_one_principle": drop,
        "cli_decision": run_record["outcome"]["decision"],
        "cli_verify_accepted": "verification: accepted" in verified,
        "problem_id": run_record["problem_id"],
    }


def main() -> None:
    started = time.monotonic()
    data = {form: verify(frozen(form), f"project-gnep-theorem-3-{form}-ladder-1-6") for form in WQA}
    write_result("p14_gnep_theorem_3", data, {"wall_time_s": round(time.monotonic() - started, 1)})
    ok = all(
        d["audit"]
        and d["decision_without_completeness"] == "unsat"
        and d["cli_decision"] == "unsat"
        and d["cli_verify_accepted"]
        and all(v == "sat" for v in d["drop_one_principle"].values())
        for d in data.values()
    )
    sizes = {form: len(d["core"]) for form, d in data.items()}
    record(
        [
            LedgerEntry(
                candidate_id="P14-gnep-theorem-3",
                hypothesis="Egalitarian Dominance, Inequality Aversion, GNEP, Weak Non-Sadism and Weak Quality Addition (thesis or 2009 form) are jointly inconsistent.",
                motivation="Four gaps of the possibility map resisted every model and differ from thesis Theorem 3 only by GNEP for NEP.",
                exact_formal_change="parametric proof in research/p14_gnep_theorem_3.py; one frozen instance per form on W_-1..W_6",
                scope="all witnesses (proof); the instances are checked mechanically",
                search_method="hand proof + constructive cycle builder audited over a witness grid + Z3/DPLL + production CLI on the instances",
                result=f"cycle lengths {sizes}; "
                + "; ".join(
                    f"{form}: {d['decision_without_completeness']} without completeness, CLI {d['cli_decision']}, drop-one {sorted(set(d['drop_one_principle'].values()))}, audit {'pass' if d['audit'] else 'FAIL'}"
                    for form, d in data.items()
                ),
                evidence_type="written proof + checked instances",
                checked=ok,
                minimal="principle-minimal on the instances",
                interpretation="GNEP can stand in for NEP in Theorem 3 by raising every negative life one level at a time; the inequality-aversion step supplies enough lives to absorb any witness. The 2009 form needs neither Condition δ nor 2009 Lemma 3. With Non-Sadism for Weak Non-Sadism this also explains the Non-Sadism gaps.",
                next_experiment="literature check; the Dominance Addition gaps",
                result_scope="checked theorem",
                formalization_tier="written proof over cross-read conditions",
                witness_conditions="proof covers every witness; instances use research/p14_gnep_theorem_3.py WITNESS",
                novelty_status="unchecked",
                status="confirmed" if ok else "refuted",
            )
        ]
    )
    print(json.dumps(data, indent=1))


if __name__ == "__main__":
    main()
