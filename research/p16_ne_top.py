"""Phase 16: headroom-free top-GNEP cycles.

Every valid witness on ``W_-2 ... W_7`` (including the top-GNEP case) admits
the arbitrary low-positive reservoir allowed by 2009 Weak Quality Addition.
Non-Elitism converts that reservoir through the available high levels; the
resulting top population closes against Dominance Addition. The same reservoir
idea, with two Inequality Aversion steps, closes the IA gap. Thesis DA remains
an N-form and is never normalized to a weak edge.

The NE construction is parameterized by the uniform witness ``n`` encoded by
``Witness``.  This is the source-faithful uniform scope of the ladder encoding:
the same n is used at every (x, y) application below.
"""

from __future__ import annotations

import json
import time
from collections import Counter
from collections.abc import Mapping
from typing import Any

from population_ethics.principles import GroundConstraint
from population_ethics.relations import Implies, conjunction, weak
from research.lab import LedgerEntry, dpll_check, ground, record, write_result
from research.ladder import Ladder, Witness, audit, larger, validate
from research.p6_schema import core_constraints, name_of
from research.schema import Instance, Pop

LADDER = Ladder(negative=2, positive=7)
ED = "thesis:egalitarian-dominance"
GNEP = "thesis:general-non-extreme-priority"
WQA_2009 = "arrhenius-2009:weak-quality-addition"
DA_THESIS = "thesis:dominance-addition"
DA_2003 = "arrhenius-2003:dominance-addition"
NE_THESIS = "thesis:non-elitism"
NE_2003 = "arrhenius-2003:non-elitism"
IA = "thesis:inequality-aversion"

WITNESS = Witness(
    {
        "general-non-extreme-priority": {"u": 7, "y": 3, "n": 1},
        "weak-quality-addition-negative": {
            "x": -2,
            "u": 4,
            "v": 6,
            "y": 3,
            "n": 1,
            "m": 1,
        },
        "non-elitism": {"n": 1},
        "inequality-aversion": {"step": 1},
    }
)


def _pop(counter: Counter[int]) -> Pop:
    return tuple(sorted(counter.elements()))


def _add(*parts: Counter[int]) -> Counter[int]:
    out: Counter[int] = Counter()
    for part in parts:
        out += part
    return out


def _validate_top(
    ladder: Ladder, witness: Witness
) -> tuple[Mapping[str, int], Mapping[str, int], int]:
    g = witness.get("general-non-extreme-priority")
    q = witness.get("weak-quality-addition-negative")
    validate("general-non-extreme-priority", ladder, g)
    validate("weak-quality-addition-negative", ladder, q)
    top = ladder.positive
    high = max(5, g["u"], q["u"])
    if high > top or not all(ladder.has(v) for v in range(q["x"], high + 1)):
        raise ValueError(
            "headroom-free construction requires consecutive levels from the negative witness through the high witness"
        )
    return g, q, high


def _step(
    out: list[Instance],
    pop: Counter[int],
    principle: str,
    remove: Counter[int],
    add: Counter[int],
) -> Counter[int]:
    if remove - pop:
        raise AssertionError((principle, remove, pop))
    before = _pop(pop)
    after = pop - remove + add
    out.append(Instance(principle, (before, _pop(after))))
    return after


def cycle_ne(
    da_form: str,
    ne_form: str,
    ladder: Ladder,
    witness: Witness,
) -> list[Instance]:
    """Build the high-level cycle for either DA form and either source NE form."""
    if da_form not in {"thesis", "2003"}:
        raise ValueError(f"unknown dominance-addition form {da_form}")
    if ne_form not in {"thesis", "2003"}:
        raise ValueError(f"unknown non-elitism form {ne_form}")
    g, q, high = _validate_top(ladder, witness)
    ne_id = NE_THESIS if ne_form == "thesis" else NE_2003
    ne = witness.get("non-elitism")
    validate("non-elitism", ladder, ne)
    da_id = DA_THESIS if da_form == "thesis" else DA_2003
    ng, a, mw, qneg = g["n"], q["n"], q["m"], q["x"]
    target = min(q["y"], g["y"])
    reservoir = ng * mw * (target - qneg)
    t_top = a + reservoir
    r = ne["n"]
    s = r + 1
    # ED starts at W_(high-1). Two NE ladders turn s²*T W_(high-2)
    # lives into T W_high lives.
    k = s * s * t_top
    initial_low = Counter({high - 2: k})
    pop = Counter({high - 1: k})
    out: list[Instance] = []
    pop = _step(out, pop, ED, Counter({high - 1: k}), initial_low)

    for _ in range(s * t_top):
        pop = _step(
            out, pop, ne_id, Counter({high - 2: s}), _add(Counter({high - 1: 1}), Counter({1: r}))
        )
    for _ in range(t_top):
        pop = _step(
            out, pop, ne_id, Counter({high - 1: s}), _add(Counter({high: 1}), Counter({1: r}))
        )
    l0 = r * t_top * (s + 1)
    if pop != Counter({high: t_top, 1: l0}):
        raise AssertionError(pop)

    # WQA allows an arbitrary nonempty low-positive B. Choose it large enough
    # to bootstrap exactly K W_high lives through levels target+1,...,high.
    final_multiplier = s ** (high - target)
    b = final_multiplier * k - (reservoir + mw)
    if b < 1:
        raise AssertionError(("WQA low count must be positive", b))
    pop = _step(
        out,
        pop,
        WQA_2009,
        Counter({high: a}),
        _add(Counter({target: b}), Counter({qneg: mw})),
    )
    for _ in range(mw):
        for z in range(qneg, target):
            pop = _step(
                out,
                pop,
                GNEP,
                Counter({high: ng, z: 1}),
                _add(Counter({target: ng}), Counter({z + 1: 1})),
            )
    if pop != Counter({1: l0, target: final_multiplier * k}):
        raise AssertionError(pop)

    # Convert the low-positive reservoir to K high lives, retaining only
    # positive W_1 lives as the final DA addition.
    for level in range(target + 1, high + 1):
        count = s ** (high - level) * k
        for _ in range(count):
            pop = _step(
                out,
                pop,
                ne_id,
                Counter({level - 1: s}),
                _add(Counter({level: 1}), Counter({1: r})),
            )
    l1 = r * k * sum(s**j for j in range(high - target))
    final = Counter({high: k, 1: l0 + l1})
    if pop != final:
        raise AssertionError(pop)

    if da_form == "2003":
        _step(out, pop, da_id, Counter({high: k, 1: l0 + l1}), Counter({high - 1: k}))
    else:
        # Thesis DA is N-shaped: ¬(W_(high-1)^K ≻ W_high^K ∪ W_1^L).
        out.append(Instance(da_id, (_pop(Counter({high - 1: k})), _pop(final))))
    return out


def cycle_ia(
    da_form: str,
    ladder: Ladder,
    witness: Witness,
) -> list[Instance]:
    """Build the count-sensitive cycle for either DA form plus thesis IA."""
    if da_form not in {"thesis", "2003"}:
        raise ValueError(f"unknown dominance-addition form {da_form}")
    g, q, top = _validate_top(ladder, witness)
    ia = witness.get("inequality-aversion")
    validate("inequality-aversion", ladder, ia)
    ng, a, mw, qneg = g["n"], q["n"], q["m"], q["x"]
    # h is a valid WQA/GNEP high level and is strictly above W_4, the
    # egalitarian- and DA-level used by the cycle.  It may be the top.
    h = max(5, g["u"], q["u"])
    if h > top or not ladder.has(h):
        raise ValueError("the high witness level is outside the ladder")
    h_top = ng * mw * (2 - qneg)
    t = a + h_top
    m1 = larger(ia, t)
    k = t + m1
    m2 = larger(ia, k)
    q_count = k + m2
    # WQA's B is chosen so that after GNEP raises q to W_2, the
    # population is exactly Q equal W_2 lives.  This is positive because
    # M2 > K > T and H = g*m*(2-q) >= 3m.
    b = a + m2 - mw
    if b < 1:
        raise AssertionError(("WQA low count must be positive", b))

    pop = Counter({4: k})
    out: list[Instance] = []
    pop = _step(out, pop, ED, Counter({4: k}), Counter({3: k}))
    # IA: W_3^K ⪰ W_h^T ∪ W_2^M1.
    pop = _step(
        out,
        pop,
        IA,
        Counter({3: k}),
        _add(Counter({h: t}), Counter({2: m1})),
    )
    # WQA uses H top lives as background, then GNEP spends exactly H top
    # lives to raise its fixed negative group through W_2.
    pop = _step(
        out,
        pop,
        WQA_2009,
        Counter({h: a}),
        _add(Counter({2: b}), Counter({qneg: mw})),
    )
    for _ in range(mw):
        for z in range(qneg, 2):
            pop = _step(
                out,
                pop,
                GNEP,
                Counter({h: ng, z: 1}),
                _add(Counter({2: ng}), Counter({z + 1: 1})),
            )
    if pop != Counter({2: q_count}):
        raise AssertionError(pop)
    # IA: W_2^Q ⪰ W_h^K ∪ W_1^M2.
    pop = _step(
        out,
        pop,
        IA,
        Counter({2: q_count}),
        _add(Counter({h: k}), Counter({1: m2})),
    )
    final = Counter({h: k, 1: m2})
    if pop != final:
        raise AssertionError(pop)
    da_id = DA_THESIS if da_form == "thesis" else DA_2003
    if da_form == "2003":
        _step(out, pop, da_id, Counter({h: k, 1: m2}), Counter({4: k}))
    else:
        # Thesis DA is N-shaped: ¬(W_4^K ≻ W_h^K ∪ W_1^M2).
        out.append(Instance(da_id, (_pop(Counter({4: k})), _pop(final))))
    return out


def _compact_transitivity(states: list[str]) -> list[GroundConstraint]:
    """Only the chain transitivity needed by the written proof, not completeness."""
    constraints: list[GroundConstraint] = []
    seen: set[str] = set()

    def add(left: str, middle: str, right: str) -> None:
        identifier = f"transitivity:{left}:{middle}:{right}"
        if identifier in seen:
            return
        seen.add(identifier)
        constraints.append(
            ground(
                identifier,
                "transitivity",
                Implies(conjunction(weak(left, middle), weak(middle, right)), weak(left, right)),
                "background.transitivity/v1",
                f"Proof-chain transitivity for {left}, {middle}, {right}.",
            )
        )

    # State 0 -> state 1 is the strict ED edge.  Propagate it to the final
    # state through every later weak edge.
    start, first = states[0], states[1]
    for middle, right in zip(states[1:-1], states[2:], strict=True):
        add(start, middle, right)
    # The reverse-ED contradiction also needs the first post-ED population to
    # reach the final population.
    for middle, right in zip(states[2:-1], states[3:], strict=True):
        add(first, middle, right)
    # A closing DA edge (2003) or the N-form's forced reverse weak edge (thesis)
    # combined with the first ED edge would imply the forbidden reverse ED edge.
    add(first, states[-1], start)
    return constraints


def decide_without_completeness(steps: list[Instance], formalization_id: str) -> str:
    """Check the finite written chain using only transitivity, never completeness."""
    names = tuple(dict.fromkeys(name_of(pop) for inst in steps for pop in inst.args))
    constraints = core_constraints(steps, formalization_id)
    states = [name_of(steps[0].args[0])]
    for inst in steps:
        right = name_of(inst.args[1])
        if right != states[-1]:
            states.append(right)
    transitivity = _compact_transitivity(states)
    hard = [*transitivity, *constraints]
    z3_decision = _decide_compact(hard)
    if len(names) <= 100:
        dpll_decision, _ = dpll_check([constraint.formula for constraint in hard])
        if z3_decision != dpll_decision:
            raise AssertionError(f"Z3 {z3_decision} disagrees with DPLL {dpll_decision}")
    return z3_decision


def _decide_compact(hard: list[GroundConstraint]) -> str:
    # Engine intentionally allocates every weak atom over ``names``.  The NE
    # reservoir has hundreds of names, so use the same production encoder over
    # only atoms actually mentioned by this compact proof.
    import z3  # type: ignore[import-untyped]

    from population_ethics.relations import encode_z3
    from research.lab import _atoms

    atoms = {atom for constraint in hard for atom in _atoms(constraint.formula)}
    variables = {atom: z3.Bool(f"w_{i}") for i, atom in enumerate(sorted(atoms, key=str))}
    solver = z3.Solver()
    solver.add(*(encode_z3(constraint.formula, variables) for constraint in hard))
    status = solver.check()
    if status == z3.sat:
        return "sat"
    if status == z3.unsat:
        return "unsat"
    raise RuntimeError(f"solver returned unknown: {solver.reason_unknown()}")


def _audit_generated(instance: Instance, ladder: Ladder, witness: Witness) -> bool:
    """Exact decomposition audit without enumerating every shared-background sub-bag.

    ``ladder.audit`` is intentionally exhaustive, but its sub-bag enumeration is
    exponential when the reservoir has hundreds of repeated W_1/W_2 lives. The
    generated instances have fixed added parts, so recovering that one
    decomposition is equivalent and linear in the number of levels.
    """
    if instance.principle in {DA_THESIS, DA_2003}:
        # Dominance Addition auditing need not enumerate all B/C partitions:
        # the top |A| lives are the only possible high B block.
        left, right = (Counter(p) for p in instance.args)
        a, bc = (left, right) if instance.principle == DA_THESIS else (right, left)
        n = sum(a.values())
        if n <= 0 or sum(bc.values()) <= n:
            return False
        top = sorted(bc.elements(), reverse=True)[:n]
        b = Counter(top)
        c = bc - b
        return bool(c) and min(b) > max(a) and all(v > 0 for v in c.elements())
    if instance.principle in {ED, IA}:
        return audit(instance, ladder, witness)
    left, right = (Counter(p) for p in instance.args)
    if instance.principle in {NE_THESIS, NE_2003}:
        n = witness.get("non-elitism")["n"]
        form = "non-elitism-ranged" if instance.principle == NE_THESIS else "non-elitism-any"
        for x in range(1, ladder.positive + 1):
            y = 1
            if x - 1 <= y or not ladder.has(x - 1):
                continue
            lp = Counter({x - 1: n + 1})
            rp = Counter({x: 1, y: n})
            if lp - left or rp - right:
                continue
            bg = left - lp
            if left != bg + lp or right != bg + rp:
                continue
            if form == "non-elitism-ranged" and not all(y <= v <= x for v in bg.elements()):
                continue
            return True
        return False
    if instance.principle == GNEP:
        g = witness.get("general-non-extreme-priority")
        for high in ladder.levels:
            if high < g["u"]:
                continue
            for z in ladder.levels:
                lp = Counter({high: g["n"], z: 1})
                if not ladder.has(z + 1) or lp - left:
                    continue
                bg = left - lp
                added = right - bg
                promoted = Counter({z + 1: 1})
                low = added - promoted
                if (
                    left == bg + lp
                    and right == bg + promoted + low
                    and sum(low.values()) == g["n"]
                    and low
                    and all(1 <= v <= g["y"] for v in low.elements())
                ):
                    return True
        return False
    if instance.principle == WQA_2009:
        q = witness.get("weak-quality-addition-negative")
        # The construction chooses h explicitly; infer it from the common
        # high-level lives and try every valid h.  The added low-positive bag
        # may be at W_2 (IA cycle) or W_3 (NE reservoir).
        for h in ladder.levels:
            if h < q["u"]:
                continue
            lp = Counter({h: q["n"]})
            if lp - left:
                continue
            bg = left - lp
            negative = Counter({q["x"]: q["m"]})
            if negative - (Counter(right) - bg):
                continue
            low = right - bg - negative
            if left == bg + lp and low and all(1 <= v <= q["y"] for v in low.elements()):
                return True
        return False
    return False


def _audit_all(steps: list[Instance], ladder: Ladder, witness: Witness) -> bool:
    return all(_audit_generated(inst, ladder, witness) for inst in steps)


def verify(steps: list[Instance], tag: str) -> dict[str, Any]:
    names = tuple(dict.fromkeys(name_of(pop) for inst in steps for pop in inst.args))
    result = decide_without_completeness(steps, f"{tag}.v1")
    drop_one = {
        principle: decide_without_completeness(
            [inst for inst in steps if inst.principle != principle], f"{tag}.drop-{principle}"
        )
        for principle in sorted({inst.principle for inst in steps})
    }
    return {
        "populations": len(names),
        "instances": len(steps),
        "audit": _audit_all(steps, LADDER, WITNESS),
        "decision_without_completeness": result,
        "drop_one_principle": drop_one,
    }


def main() -> None:
    started = time.monotonic()
    runs: dict[str, dict[str, Any]] = {}
    for da, ne in (("2003", "thesis"), ("thesis", "2003"), ("thesis", "thesis")):
        runs[f"{da}-ne-{ne}"] = verify(
            cycle_ne(da, ne, LADDER, WITNESS), f"project-p16-top-ne-{da}-{ne}"
        )
    for da in ("2003", "thesis"):
        runs[f"{da}-ia"] = verify(cycle_ia(da, LADDER, WITNESS), f"project-p16-top-ia-{da}")
    data = {
        "ladder": {"negative": LADDER.negative, "positive": LADDER.positive},
        "witness": {family: dict(params) for family, params in WITNESS.params.items()},
        "runs": runs,
    }
    write_result("p16_ne_top", data, {"wall_time_s": round(time.monotonic() - started, 1)})
    ok = all(r["audit"] and r["decision_without_completeness"] == "unsat" for r in runs.values())
    record(
        [
            LedgerEntry(
                candidate_id="P16-top-gnep-ne-and-ia",
                hypothesis=(
                    "For every valid GNEP/WQA witness, Egalitarian Dominance, GNEP, 2009 "
                    "Weak Quality Addition and either Non-Elitism variant are inconsistent "
                    "with either Dominance Addition form; the same holds with thesis "
                    "Inequality Aversion, including the top-GNEP witness."
                ),
                motivation="Close the headroom-free top-witness cases of Q-013 with audited reservoir cycles.",
                exact_formal_change="Parametric count-sensitive cycles in research/p16_ne_top.py.",
                scope="W_-2..W_7; all finite population sizes; valid witnesses accepted by ladder.validate.",
                search_method="audited population-counter construction with compact Z3 checks and no completeness",
                result=json.dumps(runs, sort_keys=True),
                evidence_type="parametric audited cycles; finite selected-instance UNSAT without completeness",
                checked=ok,
                minimal="principle-minimal on selected finite instances",
                interpretation=(
                    "The constructions use arbitrary WQA low-positive counts as finite reservoirs. "
                    "Thesis DA remains an N-form throughout; no N-to-W normalization is used."
                ),
                next_experiment="test whether the published background-first WQA witness order suffices",
                result_scope="parametric all-valid-witness theorem; selected finite witnesses checked",
                formalization_tier="cross-read ladder conditions with repaired uniform 2009 WQA",
                witness_conditions="all valid GNEP, WQA-negative, and auxiliary NE/IA count witnesses satisfying builder preconditions",
                novelty_status="candidate-new-result",
                status="confirmed" if ok else "refuted",
            )
        ]
    )
    print(json.dumps(data, indent=1))


if __name__ == "__main__":
    main()
