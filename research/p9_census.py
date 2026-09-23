"""Phase 9: the motif census.

Three layers (research/census.py):
- **L0 (shape logic).** Every minimal core with only ⪰/≻ edges is a simple directed cycle with at
  least one strict edge; with one Addition fork it is the fork plus two strict paths converging
  on the fork's middle argument. Both are checked by exhaustive enumeration up to a bound, and
  the cycle counts are compared with the binary-necklace formula.
- **Per theorem.** For each frozen theorem of Phase 8, every principle word that closes a simple
  strict cycle over its principle set, on the same ladder, witness and population bound. The
  source proof's word must reappear.
- **Whole family.** The same over every thesis-family condition form at once, grouped by role
  word, with known-ground classification.

A cross-validation compares the top-down census with MARCO's bottom-up minimal cores on the same
universes. The thesis-family conditions contain no fork shape, so their minimal cores are cycles
and ``cycle_words`` is exhaustive for them up to the length bound.
"""

from __future__ import annotations

import json
import random
import time
from collections import Counter
from math import gcd
from typing import Any

from research.canon import canonical
from research.census import (
    CycleWord,
    cycle_words,
    is_fork_motif,
    is_simple_cycle,
    minimal_cores,
)
from research.known import ROLE, known_ground
from research.lab import LedgerEntry, marco, record, write_result
from research.ladder import FORM, Witness, domain, instances_over
from research.p6_schema import GRIDS
from research.p8_catalogue import FROZEN, LADDER, WITNESS, Frozen
from research.schema import Instance, Pop, RankEngine
from research.schema import domain as grid_domain
from research.schema import instances_over as grid_instances_over

L0_CYCLE_BOUND = 6
L0_FORK_BOUND = 5
# Phase 8's witness plus the primitive thesis-family conditions it does not fix.
FAMILY_WITNESS = Witness(
    {
        **WITNESS.params,
        "non-elitism": {"n": 1},
        "general-non-extreme-priority": {"u": 4, "y": 3, "n": 1},
        "weak-quality-addition-negative": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
    }
)
FAMILY_BOUNDS = ((3, 4), (4, 5))  # (max lives, max cycle length)


def necklaces_with_a_strict_edge(n: int) -> int:
    """Binary necklaces of length n (rotation classes of W/S words) minus the all-W one."""

    def phi(d: int) -> int:
        return sum(1 for k in range(1, d + 1) if gcd(k, d) == 1)

    total: int = sum(phi(d) * 2 ** (n // d) for d in range(1, n + 1) if n % d == 0)
    return total // n - 1


def l0_section() -> dict[str, Any]:
    started = time.monotonic()
    ws = minimal_cores(L0_CYCLE_BOUND, frozenset({"W", "S"}))
    by_len = Counter(len(c[1]) for c in ws.minimal)
    forks = minimal_cores(L0_FORK_BOUND, max_forks=1)
    fork_cores = [c for c in forks.minimal if any(s == "I" for s, _ in c[1])]
    return {
        "cycle_bound": L0_CYCLE_BOUND,
        "cycle_minimal_cores_by_edges": dict(sorted(by_len.items())),
        "necklace_counts": {
            n: necklaces_with_a_strict_edge(n) for n in range(2, L0_CYCLE_BOUND + 1)
        },
        "all_cycle_cores_are_simple_strict_cycles": all(is_simple_cycle(c) for c in ws.minimal),
        "cycle_counts_match_necklaces": all(
            by_len.get(n, 0) == necklaces_with_a_strict_edge(n)
            for n in range(2, L0_CYCLE_BOUND + 1)
        ),
        "fork_bound": L0_FORK_BOUND,
        "one_fork_minimal_cores_by_edges": dict(
            sorted(Counter(len(c[1]) for c in fork_cores).items())
        ),
        "all_one_fork_cores_are_fork_motifs": all(is_fork_motif(c) for c in fork_cores),
        "satisfiable_hypergraphs_explored": ws.satisfiable_explored + forks.satisfiable_explored,
        "seconds": round(time.monotonic() - started, 1),
    }


def _cycle_order(core: list[Instance]) -> list[Instance]:
    """The instances of a cycle core in ⪰/≻ order around the cycle."""
    arrows = {}
    for inst in core:
        a, b = (inst.args[1], inst.args[0]) if inst.shape == "N" else (inst.args[0], inst.args[1])
        arrows[a] = (b, inst)
    start = min(arrows)
    out, node = [], start
    for _ in core:
        node, inst = arrows[node]
        out.append(inst)
    if node != start:
        raise ValueError("core is not a single cycle")
    return out


def _rotation_min(word: tuple[str, ...]) -> tuple[str, ...]:
    return min(word[i:] + word[:i] for i in range(len(word)))


def _describe(w: CycleWord) -> dict[str, Any]:
    roles = tuple(ROLE[p] for p in w.word)
    core = list(w.example)
    kg = known_ground(core)
    return {
        "word": list(w.word),
        "role_word": list(_rotation_min(roles)),
        "length": len(w.word),
        "strict_edges": sum(1 for i in core if i.shape == "S"),
        "example": [[i.principle, [list(p) for p in i.args]] for i in core],
        "exact_known": kg["exact_known"],
        "largest_fragment": f"{kg['largest_fragment']} {kg['largest_fragment_edges']}",
    }


def theorem_census(frozen: Frozen) -> dict[str, Any]:
    core = frozen.instances()
    principles = sorted({i.principle for i in core})
    max_lives = max(len(p) for p in frozen.populations.values())
    started = time.monotonic()
    universe = domain(LADDER, max_lives)
    insts = instances_over(universe, LADDER, WITNESS, principles)
    words = cycle_words(insts, len(core))
    source = _rotation_min(tuple(i.principle for i in _cycle_order(core)))
    found = {w.word for w in words}
    return {
        "principles": principles,
        "max_lives": max_lives,
        "max_length": len(core),
        "instances": len(insts),
        "words": [_describe(w) for w in words],
        "source_word": list(source),
        "source_word_rediscovered": source in found,
        "shortest_length": min((len(w.word) for w in words), default=None),
        "seconds": round(time.monotonic() - started, 1),
    }


def family_census(max_lives: int, max_len: int) -> dict[str, Any]:
    representative: dict[str, str] = {}
    for principle, form in FORM.items():
        representative.setdefault(form, principle)
    started = time.monotonic()
    insts = instances_over(
        domain(LADDER, max_lives), LADDER, FAMILY_WITNESS, representative.values()
    )
    words = cycle_words(insts, max_len)
    described = [_describe(w) for w in words]
    by_role: dict[tuple[str, ...], list[dict[str, Any]]] = {}
    for d in described:
        by_role.setdefault(tuple(d["role_word"]), []).append(d)
    return {
        "max_lives": max_lives,
        "max_length": max_len,
        "principles": sorted(representative.values()),
        "instances": len(insts),
        "words": len(words),
        "words_by_length": dict(sorted(Counter(len(w.word) for w in words).items())),
        "role_words": [
            {
                "role_word": list(k),
                "principle_words": len(v),
                "exact_known": sorted({d["exact_known"] for d in v if d["exact_known"]}),
                "example": v[0],
            }
            for k, v in sorted(by_role.items(), key=lambda kv: (len(kv[0]), kv[0]))
        ],
        "seconds": round(time.monotonic() - started, 1),
    }


def _mus_words(insts: list[Instance]) -> tuple[set[tuple[str, ...]], dict[str, int], int]:
    pops = sorted({x for i in insts for x in i.args})
    engine = RankEngine(pops, insts)
    muses, _ = marco(engine)  # type: ignore[arg-type]
    words: set[tuple[str, ...]] = set()
    kinds: Counter[str] = Counter()
    for mus in muses:
        core = [insts[int(c[1:])] for c in mus]
        if any(i.shape == "I" for i in core):
            kinds["fork"] += 1
            continue
        try:
            words.add(_rotation_min(tuple(i.principle for i in _cycle_order(core))))
            kinds["cycle"] += 1
        except ValueError, KeyError:
            kinds["other"] += 1
    return words, dict(kinds), len(muses)


def cross_validation() -> list[dict[str, Any]]:
    """MARCO's minimal cores against the top-down census on the same universes."""
    out = []
    rng = random.Random(2026)
    for frozen, max_lives, extra in (
        (FROZEN[1], 3, 80),  # thesis Theorem 2
        (FROZEN[0], 4, 80),  # thesis Theorem 1
        (FROZEN[2], 5, 60),  # thesis Theorem 3
    ):
        principles = sorted({p for p, _, _ in frozen.core})
        universe: set[Pop] = set(rng.sample(domain(LADDER, max_lives), extra)) | set(
            frozen.populations.values()
        )
        insts = instances_over(universe, LADDER, WITNESS, principles)
        started = time.monotonic()
        bottom_up, kinds, count = _mus_words(insts)
        top_down = {w.word for w in cycle_words(insts, 32)}
        out.append(
            {
                "principles": principles,
                "universe_populations": len(universe),
                "instances": len(insts),
                "marco_minimal_cores": count,
                "marco_kinds": kinds,
                "agree": bottom_up == top_down and set(kinds) <= {"cycle"},
                "only_marco": sorted(map(list, bottom_up - top_down)),
                "only_census": sorted(map(list, top_down - bottom_up)),
                "seconds": round(time.monotonic() - started, 1),
            }
        )
    grid = GRIDS["relaxed"]
    insts = grid_instances_over(grid_domain(grid, 2), grid, 1, 1)
    pops = sorted({x for i in insts for x in i.args})
    muses, _ = marco(RankEngine(pops, insts))  # type: ignore[arg-type]
    shapes = []
    for mus in muses:
        core = [insts[int(c[1:])] for c in mus]
        n, edges = canonical(core, "L0")
        l0 = (n, tuple((label.strip("'"), args) for label, args in edges))
        shapes.append("cycle" if is_simple_cycle(l0) else "fork" if is_fork_motif(l0) else "other")
    out.append(
        {
            "principles": "v0 (2000) on the relaxed grid, N = 2, W(p=1, q=1)",
            "marco_minimal_cores": len(muses),
            "marco_kinds": dict(Counter(shapes)),
            "agree": "other" not in shapes,
        }
    )
    return out


def main() -> None:
    started = time.monotonic()
    data: dict[str, Any] = {"ladder": {"negative": LADDER.negative, "positive": LADDER.positive}}
    data["l0"] = l0_section()
    data["theorems"] = {f.id: theorem_census(f) for f in FROZEN}
    data["family"] = [family_census(n, k) for n, k in FAMILY_BOUNDS]
    data["cross_validation"] = cross_validation()
    write_result("p9_census", data, {"wall_time_s": round(time.monotonic() - started, 1)})
    _ledger(data)
    print(
        json.dumps({k: v for k, v in data.items() if k != "family"}, indent=1, ensure_ascii=False)[
            :4000
        ]
    )


def _ledger(data: dict[str, Any]) -> None:
    l0 = data["l0"]
    entries = [
        LedgerEntry(
            candidate_id="P9-l0-cycle-motif",
            hypothesis="Every minimal rank-inconsistent set of ⪰/≻ edges is a simple directed cycle with at least one strict edge.",
            motivation="Q-006: whether skeleton logic reduces to a few motifs.",
            exact_formal_change="shape hypergraphs over W, S; exhaustive up to "
            f"{l0['cycle_bound']} edges",
            scope="all shape hypergraphs up to the bound",
            search_method="canonical augmentation (nauty) with an exact difference-constraint test",
            result=f"cores by edges {l0['cycle_minimal_cores_by_edges']}; all simple strict cycles: "
            f"{l0['all_cycle_cores_are_simple_strict_cycles']}; counts equal binary necklaces with a "
            f"strict edge: {l0['cycle_counts_match_necklaces']}",
            evidence_type="exhaustive enumeration + standard difference-constraint argument",
            checked=l0["all_cycle_cores_are_simple_strict_cycles"]
            and l0["cycle_counts_match_necklaces"],
            minimal="n/a",
            interpretation="A logical necessity, not a discovery: a minimal infeasible set of ≥/> "
            "constraints is a simple cycle through a strict edge. Since the thesis-family "
            "conditions have no fork shape, every minimal core they form is such a cycle.",
            next_experiment="classify realizable principle words",
            result_scope="checked theorem",
            formalization_tier="shape logic (complete branch)",
            witness_conditions="none",
            novelty_status="known (standard difference-constraint theory)",
            status="confirmed",
        ),
        LedgerEntry(
            candidate_id="P9-l0-fork-motif",
            hypothesis="Every minimal rank-inconsistent hypergraph with one Addition fork I(a, b, c) is the fork plus two paths a ⇝ b and c ⇝ b, each with a strict edge.",
            motivation="Q-006: the 2000 skeleton's fork.",
            exact_formal_change=f"shape hypergraphs with at most one I edge, up to {l0['fork_bound']} edges",
            scope="all such hypergraphs up to the bound",
            search_method="canonical augmentation with an exact test over both fork branches",
            result=f"fork cores by edges {l0['one_fork_minimal_cores_by_edges']}; all fork motifs: "
            f"{l0['all_one_fork_cores_are_fork_motifs']}",
            evidence_type="exhaustive enumeration",
            checked=l0["all_one_fork_cores_are_fork_motifs"],
            minimal="n/a",
            interpretation="Each branch of the disjunction must close its own strict cycle; the core "
            "is the union of the two. The E&P 2000 skeleton (7 edges) lies beyond the enumeration "
            "bound but has this form.",
            next_experiment="extend the bound; two-fork cores",
            result_scope="bounded conjecture",
            formalization_tier="shape logic (complete branch)",
            witness_conditions="none",
            novelty_status="likely known (disjunctive difference constraints)",
            status="confirmed" if l0["all_one_fork_cores_are_fork_motifs"] else "refuted",
        ),
    ]
    for key, t in data["theorems"].items():
        variants = [w["word"] for w in t["words"] if w["word"] != t["source_word"]]
        entries.append(
            LedgerEntry(
                candidate_id=f"P9-census-{key}",
                hypothesis=f"The cycle census over {key}'s principles rediscovers its source word.",
                motivation="Rediscovery check and variant count for a catalogued theorem.",
                exact_formal_change=f"all simple strict cycles of length <= {t['max_length']} over "
                f"{t['instances']} instances (ladder, Phase 8 witness, <= {t['max_lives']} lives)",
                scope="finite universe",
                search_method="exhaustive simple-cycle search over the audited instance graph",
                result=f"{len(t['words'])} words; source rediscovered: {t['source_word_rediscovered']}; "
                f"shortest length {t['shortest_length']}; {len(variants)} variant words",
                evidence_type="exhaustive search",
                checked=t["source_word_rediscovered"],
                minimal="every simple strict cycle is a minimal core",
                interpretation="Variants reorder adjacent weak steps or, for Theorem 1, shorten the "
                "Quantity chain to what the witness's ranges need.",
                next_experiment="larger witnesses; compare lengths with the source proofs",
                result_scope="finite computational result",
                formalization_tier="frozen agent-cross-read witness",
                witness_conditions="research/p8_catalogue.py WITNESS",
                novelty_status="not-applicable (reproduction)",
                status="confirmed" if t["source_word_rediscovered"] else "refuted",
            )
        )
    for fam in data["family"]:
        short = [r for r in fam["role_words"] if len(r["role_word"]) <= 3]
        entries.append(
            LedgerEntry(
                candidate_id=f"P9-family-N{fam['max_lives']}-L{fam['max_length']}",
                hypothesis="Classify every short strict cycle over all thesis-family condition forms.",
                motivation="The periodic table: which cyclic principle words close.",
                exact_formal_change=f"one principle per form; ladder W_-1..W_6; <= {fam['max_lives']} lives",
                scope="finite universe",
                search_method="exhaustive simple-cycle search",
                result=f"{fam['words']} principle words ({fam['words_by_length']}) in "
                f"{len(fam['role_words'])} role words; role words of length <= 3: "
                f"{[r['role_word'] for r in short]}",
                evidence_type="exhaustive search",
                checked=True,
                minimal="every simple strict cycle is a minimal core",
                interpretation="See docs/journal for the δ / Egalitarian Dominance / Inequality "
                "Aversion triangle, a witness diagnostic like R5.",
                next_experiment="witness families where δ's n grows with m",
                result_scope="finite computational result",
                formalization_tier="unreviewed witness choice over cross-read conditions",
                witness_conditions="research/p9_census.py FAMILY_WITNESS",
                status="confirmed",
            )
        )
    for i, cv in enumerate(data["cross_validation"]):
        entries.append(
            LedgerEntry(
                candidate_id=f"P9-cross-validation-{i}",
                hypothesis="Bottom-up MARCO minimal cores agree with the top-down census.",
                motivation="Independent check of the census code.",
                exact_formal_change=str(cv["principles"]),
                scope="sampled finite universe",
                search_method="MARCO over the rank encoding vs simple-cycle search / L0 classification",
                result=f"{cv['marco_minimal_cores']} MARCO cores, kinds {cv['marco_kinds']}; agree: {cv['agree']}",
                evidence_type="two independent algorithms",
                checked=cv["agree"],
                minimal="n/a",
                interpretation="Agreement in both directions on the same instances.",
                next_experiment="n/a",
                result_scope="finite computational result",
                formalization_tier="implementation check",
                witness_conditions="research/p8_catalogue.py WITNESS",
                novelty_status="not-applicable (implementation check)",
                status="confirmed" if cv["agree"] else "refuted",
            )
        )
    record(entries)


if __name__ == "__main__":
    main()
