"""Phase 15: conditional headroom construction for Dominance Addition.

For every valid GNEP and 2009 Weak Quality Addition witness on a ladder containing
``W_{h+1}``, where ``h = max(GNEP.u, WQA.u)``, the construction below gives a
cycle using Weak Quality Addition, GNEP, Egalitarian Dominance, Inequality Aversion,
and Dominance Addition.  It uses only reflexivity and transitivity, never
completeness.  The thesis closing instance is the N-form ``not (A ≻ B∪C)``;
it is not a weak-edge orientation, unlike the 2003 closing instance.
"""

from __future__ import annotations

import json
import time
from collections import Counter
from collections.abc import Mapping
from typing import Any

from research.lab import ROOT, LedgerEntry, background, record, write_result
from research.ladder import Ladder, Witness, audit, larger, validate
from research.p6_schema import _cli, core_constraints, materialize, name_of
from research.p8_catalogue import CLI_GRID, Frozen, _decide
from research.schema import Instance, Pop

LADDER = Ladder(negative=2, positive=7)
ED = "thesis:egalitarian-dominance"
IA = "thesis:inequality-aversion"
GNEP = "thesis:general-non-extreme-priority"
WQA_2009 = "arrhenius-2009:weak-quality-addition"
DA_THESIS = "thesis:dominance-addition"
DA_2003 = "arrhenius-2003:dominance-addition"

WITNESS = Witness(
    {
        "inequality-aversion": {"step": 1},
        "general-non-extreme-priority": {"u": 6, "y": 3, "n": 1},
        "weak-quality-addition-negative": {
            "x": -2,
            "u": 4,
            "v": 6,
            "y": 3,
            "n": 1,
            "m": 1,
        },
    }
)


def _pop(c: Counter[int]) -> Pop:
    return tuple(sorted(c.elements()))


def cycle(form: str, ladder: Ladder, witness: Witness) -> list[Instance]:
    """Build the consecutive headroom cycle for one valid witness."""
    if form not in {"thesis", "2003"}:
        raise ValueError(f"unknown dominance-addition form {form}")
    g = witness.get("general-non-extreme-priority")
    q: Mapping[str, int] = witness.get("weak-quality-addition-negative")
    ia = witness.get("inequality-aversion")
    validate("general-non-extreme-priority", ladder, g)
    validate("weak-quality-addition-negative", ladder, q)
    validate("inequality-aversion", ladder, ia)

    h = max(g["u"], q["u"])
    if not ladder.has(h + 1):
        raise ValueError(f"dominance-addition headroom requires W_{h + 1}")

    n_g = g["n"]
    a = q["n"]
    m_w = q["m"]
    q_neg = q["x"]
    H = n_g * m_w * (3 - q_neg)
    N = a + H
    M = larger(ia, N)
    C = a + M - m_w
    K = N + M
    pop = Counter({h: N})
    out: list[Instance] = []

    def move(principle: str, remove: Counter[int], add: Counter[int]) -> None:
        nonlocal pop
        before = _pop(pop)
        assert not remove - pop, (principle, remove, pop)
        pop = pop - remove + add
        out.append(Instance(principle, (before, _pop(pop))))

    move(
        WQA_2009,
        Counter({h: a}) + Counter({h: H}),
        Counter({h: H}) + Counter({3: C}) + Counter({q_neg: m_w}),
    )
    for z in range(q_neg, 3):
        for _ in range(m_w):
            move(
                GNEP,
                Counter({h: n_g}) + Counter({z: 1}),
                Counter({3: n_g}) + Counter({z + 1: 1}),
            )
    assert pop == Counter({3: K}), pop
    move(ED, Counter({3: K}), Counter({2: K}))
    move(
        IA,
        Counter({2: K}),
        Counter({h + 1: N}) + Counter({1: M}),
    )
    if form == "2003":
        move(
            DA_2003,
            Counter({h + 1: N}) + Counter({1: M}),
            Counter({h: N}),
        )
    else:
        # Thesis Dominance Addition is N-shaped: ¬(N at W_h ≻ B∪C).
        before = _pop(pop)
        remove = Counter({h + 1: N}) + Counter({1: M})
        add = Counter({h: N})
        assert not remove - pop, (DA_THESIS, remove, pop)
        pop = pop - remove + add
        out.append(Instance(DA_THESIS, (_pop(pop), before)))
    if form == "2003":
        assert out[-1].args[1] == out[0].args[0]
    return out


def frozen(form: str) -> Frozen:
    steps = cycle(form, LADDER, WITNESS)
    names: dict[Pop, str] = {}
    for i, inst in enumerate(steps):
        names.setdefault(inst.args[0], f"P{i}")
    next_name = len(names)
    for inst in steps:
        for pop in inst.args:
            if pop not in names:
                names[pop] = f"P{next_name}"
                next_name += 1
    if len(names) != len(set(names.values())):
        raise ValueError(f"{form}: two distinct populations share a name")
    return Frozen(
        f"project-p15-dominance-addition-{form}",
        "project",
        "research/p15_dominance_addition.py",
        {name: pop for pop, name in names.items()},
        tuple((inst.principle, names[inst.args[0]], names[inst.args[1]]) for inst in steps),
        f"Conditional headroom cycle for {form} Dominance Addition; completeness is unused.",
    )


def verify(f: Frozen, tag: str) -> dict[str, Any]:
    core = f.instances()
    names = tuple(sorted(name_of(pop) for pop in f.populations.values()))
    if len(names) != len(f.populations):
        raise ValueError(f"{f.id}: two names denote the same population")
    bg = background(names)
    formalization_id = f"{f.id}.selected-witness/v1"
    constraints = core_constraints(core, formalization_id)
    hard = [*bg["reflexivity"], *bg["transitivity"], *constraints]
    drop = {
        principle: _decide([c for c in hard if c.principle_id != principle], names)
        for principle in sorted({c.principle_id for c in constraints})
    }
    toml = materialize(
        tag,
        CLI_GRID,
        core,
        1,
        1,
        max(len(pop) for pop in f.populations.values()),
        source_ids=("arrhenius-2000-thesis", "arrhenius-2003-vrc", "arrhenius-2009-one-more"),
        formalization_id=formalization_id,
        source_fidelity="conditional headroom construction; checked selected witnesses only",
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
        "populations": {name: list(pop) for name, pop in f.populations.items()},
        "core": [[inst.principle, list(inst.args[0]), list(inst.args[1])] for inst in core],
        "audit": all(audit(inst, LADDER, WITNESS) for inst in core),
        "decision_without_completeness": _decide(hard, names),
        "drop_one_principle": drop,
        "cli_decision": run_record["outcome"]["decision"],
        "cli_verify_accepted": "verification: accepted" in verified,
        "problem_id": run_record["problem_id"],
    }


def main() -> None:
    started = time.monotonic()
    data = {
        form: verify(frozen(form), f"project-p15-dominance-addition-{form}-ladder-2-7")
        for form in ("thesis", "2003")
    }
    write_result(
        "p15_dominance_addition",
        {
            "ladder": {"negative": LADDER.negative, "positive": LADDER.positive},
            "witness": {family: dict(params) for family, params in WITNESS.params.items()},
            "forms": data,
        },
        {"wall_time_s": round(time.monotonic() - started, 1)},
    )
    ok = all(
        result["audit"]
        and result["decision_without_completeness"] == "unsat"
        and result["cli_decision"] == "unsat"
        and result["cli_verify_accepted"]
        for result in data.values()
    )
    sizes = {form: len(result["core"]) for form, result in data.items()}
    record(
        [
            LedgerEntry(
                candidate_id="P15-headroom-dominance-addition",
                hypothesis=(
                    "Conditionally, every valid GNEP and 2009 Weak Quality Addition witness "
                    "with W_{h+1} present, h = max(GNEP u, 2009 WQA high level), makes "
                    "Egalitarian Dominance, Inequality Aversion, GNEP, 2009 Weak Quality "
                    "Addition and Dominance Addition inconsistent."
                ),
                motivation="Q-013 asks whether Dominance Addition can close the GNEP headroom cycle.",
                exact_formal_change=(
                    "mechanized conditional headroom cycle in research/p15_dominance_addition.py; "
                    "two selected instances on W_-2..W_7"
                ),
                scope="all valid witnesses satisfying the explicit W_{h+1} headroom condition; finite instances checked mechanically",
                search_method=(
                    "constructive population-counter proof audited over a bounded witness grid + "
                    "Z3/DPLL + production CLI on two selected finite instances"
                ),
                result=(
                    f"cycle lengths {sizes}; "
                    + "; ".join(
                        f"{form}: {result['decision_without_completeness']} without completeness, "
                        f"CLI {result['cli_decision']}, drop-one {result['drop_one_principle']}, "
                        f"audit {'pass' if result['audit'] else 'FAIL'}"
                        for form, result in data.items()
                    )
                ),
                evidence_type="written conditional proof + checked finite instances",
                checked=ok,
                minimal="principle-minimal on the selected finite instances",
                interpretation=(
                    "This is a conditional theorem, not an unrestricted ladder-independent theorem: "
                    "the construction applies to every valid witness only when W_{h+1} is present, "
                    "with h = max(GNEP u, 2009 WQA high level). The two checked finite instances "
                    "use the selected witness on W_-2..W_7; the thesis closing condition is an "
                    "N-form, not a weak edge."
                ),
                next_experiment="check the conditional construction against additional source formalizations and ladders",
                result_scope="checked conditional theorem (finite instances)",
                formalization_tier="mechanized population construction with bounded CLI instances",
                witness_conditions="every valid GNEP/WQA-negative/IA witness with W_{h+1} present; selected WITNESS checked on W_-2..W_7",
                novelty_status="candidate-new-result",
                status="confirmed" if ok else "refuted",
            )
        ]
    )
    print(json.dumps(data, indent=1))


if __name__ == "__main__":
    main()
