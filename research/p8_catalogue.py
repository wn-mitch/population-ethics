"""Phase 8: freeze the remaining Arrhenius theorems as witnessed cores for the catalogue.

Each theorem's proof (corpus/readings.toml, ``proof_steps``) is instantiated on the ladder
W_−1, W_1 … W_6 with the smallest witnesses its quantifiers allow: ranges R(1, 3) and R(4, 6),
n = p = m = 1, and each "m > n" existential at m = n + 1. Theorem 4, the 2003 theorem and the 2009
theorem are frozen at the level of their final lemma (thesis Lemma 5.3, the 2003 main proof,
2009 Lemma 4), whose edges include the derived Conditions β and δ and Restricted Quality
Addition; the lemmas that derive those conditions are edge realizations, not skeleton edges.

For each frozen core the phase checks, without completeness (no theorem here assumes it):
- every instance passes the independent ladder audit;
- the core is inconsistent with a preorder (Z3 and DPLL agree) and through the production CLI;
- dropping any one principle restores consistency;
- how much of it the pre-existing catalogue already covers.
"""

from __future__ import annotations

import json
import time
from dataclasses import dataclass
from typing import Any

from research.known import CATALOGUE, known_ground
from research.lab import ROOT, Engine, LedgerEntry, background, dpll_check, record, write_result
from research.ladder import Ladder, Witness, audit
from research.p6_schema import _cli, core_constraints, materialize, name_of
from research.schema import Grid, Instance, Pop

LADDER = Ladder(negative=1, positive=6)
WITNESS = Witness(
    {
        "quantity": {"step": 1},
        "quality": {"u": 4, "v": 6, "y": 3, "n": 1},
        "inequality-aversion": {"step": 1},
        "non-extreme-priority": {"x": 4, "y": -1, "z": 3, "n": 1},
        "weak-quality-addition": {"x": 4, "w": 6, "y": 3, "n": 1},
        "weak-non-sadism": {"x": -1, "n": 1},
        "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
        "condition-beta": {"step": 1},
        "condition-delta": {"u": 4, "y": 3, "n": 1},
        "restricted-quality-addition": {"x": 4, "y": 3, "n": 1, "m": 1},
    }
)
# Categories for the CLI record only: R(4, 6) very high, R(1, 3) very low, W_−1 negative.
CLI_GRID = Grid(
    "ladder-1-6", LADDER.levels, frozenset({4, 5, 6}), frozenset({1, 2, 3}), frozenset({-1})
)


def _pop(*parts: tuple[int, int]) -> Pop:
    return tuple(sorted(level for level, count in parts for _ in range(count)))


@dataclass(frozen=True)
class Frozen:
    id: str
    work: str
    statement: str  # reading id of the theorem or lemma frozen here
    populations: dict[str, Pop]
    core: tuple[tuple[str, str, str], ...]  # (principle, left name, right name)
    note: str

    def instances(self) -> list[Instance]:
        return [Instance(p, (self.populations[x], self.populations[y])) for p, x, y in self.core]


# Thesis Theorem 1 (p. 157): A_1 = n_1 at W_u, Quantity down to A_4 at W_1, B at W_y.
THEOREM_1 = Frozen(
    "arrhenius-thesis-theorem-1",
    "arrhenius-2000-thesis",
    "thesis:theorem-1",
    {
        "A1": _pop((4, 1)),
        "A2": _pop((3, 2)),
        "A3": _pop((2, 3)),
        "A4": _pop((1, 4)),
        "B": _pop((3, 4)),
    },
    (
        ("thesis:quantity", "A2", "A1"),
        ("thesis:quantity", "A3", "A2"),
        ("thesis:quantity", "A4", "A3"),
        ("thesis:egalitarian-dominance", "B", "A4"),
        ("thesis:quality", "A1", "B"),
    ),
    "Quantity chain one level at a time from W_u to W_1, closed by Egalitarian Dominance and Quality.",
)

# Thesis Theorem 2 (pp. 159–161).
THEOREM_2 = Frozen(
    "arrhenius-thesis-theorem-2",
    "arrhenius-2000-thesis",
    "thesis:theorem-2",
    {
        "A": _pop((4, 1)),
        "B": _pop((3, 3)),
        "C": _pop((2, 3)),
        "E∪D": _pop((6, 1), (1, 2)),
    },
    (
        ("thesis:inequality-aversion", "C", "E∪D"),
        ("thesis:dominance-addition", "A", "E∪D"),
        ("thesis:egalitarian-dominance", "B", "C"),
        ("thesis:quality", "A", "B"),
    ),
    "A ⪰ B ≻ C ⪰ E∪D gives A ≻ E∪D against Dominance Addition's ¬(A ≻ E∪D).",
)

# Thesis Theorem 3 (pp. 163–165), the 1999 skeleton with the thesis conditions.
THEOREM_3 = Frozen(
    "arrhenius-thesis-theorem-3",
    "arrhenius-2000-thesis",
    "thesis:theorem-3",
    {
        "A∪H∪E": _pop((4, 2), (-1, 1)),
        "A∪B": _pop((4, 1), (3, 2)),
        "G": _pop((2, 5)),
        "A∪H∪F": _pop((4, 2), (1, 3)),
        "B∪C": _pop((3, 5)),
    },
    (
        ("thesis:non-extreme-priority", "A∪H∪E", "A∪B"),
        ("thesis:inequality-aversion", "G", "A∪H∪F"),
        ("thesis:non-sadism", "A∪H∪F", "A∪H∪E"),
        ("thesis:weak-quality-addition", "A∪B", "B∪C"),
        ("thesis:egalitarian-dominance", "B∪C", "G"),
    ),
    "One weak cycle through NEP, Weak Quality Addition, Inequality Aversion and Non-Sadism, "
    "closed by Egalitarian Dominance.",
)

# Thesis Lemma 5.3 (pp. 177–180), the final step of Theorem 4. I = ∅ at these witnesses.
THEOREM_4 = Frozen(
    "arrhenius-thesis-theorem-4",
    "arrhenius-2000-thesis",
    "thesis:lemma-5.3",
    {
        "A∪H∪E": _pop((4, 2), (-1, 1)),
        "A∪B1∪B2": _pop((4, 1), (3, 2)),
        "G∪I": _pop((2, 5)),
        "A∪H∪F∪I": _pop((4, 2), (1, 3)),
        "B1∪B2∪C": _pop((3, 5)),
    },
    (
        ("thesis:condition-delta", "A∪H∪E", "A∪B1∪B2"),
        ("thesis:condition-beta", "G∪I", "A∪H∪F∪I"),
        ("thesis:weak-non-sadism", "A∪H∪F∪I", "A∪H∪E"),
        ("thesis:weak-quality-addition", "A∪B1∪B2", "B1∪B2∪C"),
        ("thesis:egalitarian-dominance", "B1∪B2∪C", "G∪I"),
    ),
    "Theorem 3's cycle with Condition δ (from GNEP, Lemma 5.2) for NEP, Condition β (from "
    "Non-Elitism, Lemma 5.1) for Inequality Aversion, and Weak Non-Sadism.",
)

# Arrhenius 2003 (p. 173).
THEOREM_2003 = Frozen(
    "arrhenius-2003-vrc",
    "arrhenius-2003-vrc",
    "arrhenius-2003:theorem",
    {
        "A1": _pop((4, 1)),
        "A2": _pop((5, 1)),
        "A3∪B1∪C1∪D1": _pop((6, 1), (1, 4), (3, 1)),
        "A3∪B2∪C1∪D2": _pop((6, 2), (1, 3), (-1, 1)),
        "A4∪B3∪C2∪D2": _pop((3, 5), (-1, 1)),
    },
    (
        ("arrhenius-2003:egalitarian-dominance", "A2", "A1"),
        ("arrhenius-2003:dominance-addition", "A3∪B1∪C1∪D1", "A2"),
        ("arrhenius-2003:condition-delta", "A3∪B2∪C1∪D2", "A3∪B1∪C1∪D1"),
        ("arrhenius-2003:condition-beta", "A4∪B3∪C2∪D2", "A3∪B2∪C1∪D2"),
        ("arrhenius-2003:vrc-avoidance", "A1", "A4∪B3∪C2∪D2"),
    ),
    "A1 ≺ A2 ⪯ … ⪯ A4∪B3∪C2∪D2 ⪯ A1: one strict Egalitarian Dominance link, then Dominance "
    "Addition, δ, β, closed by VRC avoidance.",
)

# Arrhenius 2009 Lemma 4 (pp. 33–36), the final step of the 2009/2011 theorem; I = ∅.
THEOREM_2009 = Frozen(
    "arrhenius-2009-one-more",
    "arrhenius-2009-one-more",
    "arrhenius-2009:lemma-4",
    {
        "A∪H∪E": _pop((4, 2), (-1, 1)),
        "A∪B1∪B2": _pop((4, 1), (3, 2)),
        "G∪I": _pop((2, 5)),
        "A∪H∪F∪I": _pop((4, 2), (1, 3)),
        "B1∪B2∪C": _pop((3, 5)),
    },
    (
        ("arrhenius-2009:condition-delta", "A∪H∪E", "A∪B1∪B2"),
        ("arrhenius-2009:condition-beta", "G∪I", "A∪H∪F∪I"),
        ("arrhenius-2009:weak-non-sadism", "A∪H∪F∪I", "A∪H∪E"),
        ("arrhenius-2009:restricted-quality-addition", "A∪B1∪B2", "B1∪B2∪C"),
        ("arrhenius-2009:egalitarian-dominance", "B1∪B2∪C", "G∪I"),
    ),
    "Lemma 5.3's cycle with Restricted Quality Addition (from Weak Quality Addition and δ, "
    "Lemma 3) in the quality place.",
)

FROZEN = (THEOREM_1, THEOREM_2, THEOREM_3, THEOREM_4, THEOREM_2003, THEOREM_2009)


def _decide(hard: list[Any], names: tuple[str, ...]) -> str:
    z = Engine(names, hard).require().decision
    d, _ = dpll_check([c.formula for c in hard])
    if z != d:
        raise AssertionError(f"Z3 {z} disagrees with DPLL {d}")
    return z


def check(frozen: Frozen) -> dict[str, Any]:
    core = frozen.instances()
    names = tuple(sorted(name_of(p) for p in frozen.populations.values()))
    if len(set(names)) != len(frozen.populations):
        raise ValueError(f"{frozen.id}: two names denote the same population")
    bg = background(names)
    constraints = core_constraints(core, f"{frozen.id}.selected-witness/v1")
    hard = [*bg["reflexivity"], *bg["transitivity"], *constraints]
    drop = {
        principle: _decide([c for c in hard if c.principle_id != principle], names)
        for principle in sorted({c.principle_id for c in constraints})
    }
    tag = f"{frozen.id}-ladder-1-6"
    toml = materialize(
        tag,
        CLI_GRID,
        core,
        1,
        1,
        max(len(p) for p in frozen.populations.values()),
        source_ids=(frozen.work,),
        formalization_id=f"{frozen.id}.selected-witness/v1",
        source_fidelity="selected finite witness instance; not the unrestricted theorem",
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
        "work": frozen.work,
        "statement": frozen.statement,
        "populations": {k: list(v) for k, v in frozen.populations.items()},
        "core": [list(e) for e in frozen.core],
        "audit": {
            f"{p}:{x}->{y}": audit(i, LADDER, WITNESS)
            for (p, x, y), i in zip(frozen.core, core, strict=True)
        },
        "decision_without_completeness": _decide(hard, names),
        "drop_one_principle": drop,
        "cli_decision": run_record["outcome"]["decision"],
        "cli_verify_accepted": "verification: accepted" in verified,
        "problem_id": run_record["problem_id"],
        "toml": toml,
        "known_ground_before": known_ground(core, [k for k in CATALOGUE if k.id != frozen.id]),
    }


def main() -> None:
    started = time.monotonic()
    data = {
        "ladder": {"negative": LADDER.negative, "positive": LADDER.positive},
        "witness": {k: dict(v) for k, v in WITNESS.params.items()},
    }
    data["frozen"] = {f.id: check(f) for f in FROZEN}
    write_result("p8_catalogue", data, {"wall_time_s": round(time.monotonic() - started, 2)})
    _ledger(data)
    print(json.dumps(data, indent=2, ensure_ascii=False))


def _ledger(data: dict[str, Any]) -> None:
    entries = []
    for key, r in data["frozen"].items():
        ok = (
            all(r["audit"].values())
            and r["decision_without_completeness"] == "unsat"
            and r["cli_decision"] == "unsat"
            and r["cli_verify_accepted"]
            and all(v == "sat" for v in r["drop_one_principle"].values())
        )
        frozen = next(f for f in FROZEN if f.id == key)
        entries.append(
            LedgerEntry(
                candidate_id=f"P8-{key}",
                hypothesis=f"The frozen witness of {r['statement']} is inconsistent with a preorder, "
                "needs every principle, and needs no completeness.",
                motivation="Catalogue the remaining Arrhenius theorems as known ground.",
                exact_formal_change=f"{key}.selected-witness/v1 on ladder W_-1, W_1..W_6",
                scope="frozen witness; not the unrestricted theorem",
                search_method="Z3 + DPLL (atom encoding) and the production CLI run/verify",
                result=(
                    f"{r['decision_without_completeness']} without completeness; CLI "
                    f"{r['cli_decision']}; drop-one: {r['drop_one_principle']}; "
                    f"audit {'pass' if all(r['audit'].values()) else 'FAIL'}. {frozen.note}"
                ),
                evidence_type="solver decision + CLI verification",
                checked=ok,
                minimal="principle-minimal (dropping any principle is SAT)" if ok else "no",
                counterexample_if_false="n/a",
                generalization_status="not generalized",
                novelty_status="not-applicable (reproduction)",
                interpretation="Reproduces a published theorem; known ground.",
                next_experiment="catalogue in research/known.py",
                result_scope="finite computational result",
                formalization_tier="frozen agent-cross-read witness",
                witness_conditions="ladder W_-1, W_1..W_6; research/p8_catalogue.py WITNESS",
                completion_status="complete",
                status="confirmed" if ok else "refuted",
            )
        )
    record(entries)


if __name__ == "__main__":
    main()
