"""A possibility map for the thesis-family conditions: which axiologies satisfy which conditions.

Additive axiologies are decided exactly by research/additive.py. Everything else here is a
bounded model check: an axiology is a key function on populations (X ⪰ Y iff key(X) ≥ key(Y)),
and it satisfies a condition if some witness in a finite grid makes every generated instance
over a finite universe hold (research/ladder.py). Two biases follow and are stated with every
result:

- "satisfies" is bounded evidence: a larger universe could expose a violation;
- "violates" may be an artifact: the source lets ∀∃ witnesses vary per group, while a ladder
  witness is one rule for all groups, and the grid is finite.

The map is used in the safe direction: a condition set is *realized* when one axiology
satisfies all of it, which is evidence of consistency. Condition sets that no axiology in the
battery realizes and no known theorem explains are the candidates to examine.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Any

from research.ladder import Ladder, Witness, domain, instances_over
from research.schema import Instance, Pop

Key = Callable[[Pop], Any]


@dataclass(frozen=True)
class Axiology:
    id: str
    description: str
    key: Key


def _total(p: Pop) -> Fraction:
    return Fraction(sum(p))


def _average(p: Pop) -> Fraction:
    return Fraction(sum(p), len(p))


def lexical_threshold(h: int) -> Axiology:
    return Axiology(
        f"lexical-threshold-{h}",
        f"first the total welfare of lives at or above W_{h}, then total welfare",
        lambda p: (sum(v for v in p if v >= h), sum(p)),
    )


def variable_value(k: int) -> Axiology:
    return Axiology(
        f"variable-value-{k}",
        f"average welfare times N/(N+{k}) (Hurka-style)",
        lambda p: _average(p) * Fraction(len(p), len(p) + k),
    )


def rank_discounted(beta: Fraction) -> Axiology:
    return Axiology(
        f"rank-discounted-{beta}",
        f"Σ β^i w_(i) over lives sorted from worst, β = {beta}",
        lambda p: sum(beta**i * v for i, v in enumerate(sorted(p))),
    )


BATTERY: tuple[Axiology, ...] = (
    Axiology("total", "total welfare", _total),
    Axiology("average", "average welfare", _average),
    Axiology("maximin-total", "worst life, then total welfare", lambda p: (min(p), sum(p))),
    Axiology("leximin", "sorted welfare from worst, lexicographically", lambda p: tuple(sorted(p))),
    lexical_threshold(3),
    lexical_threshold(4),
    lexical_threshold(5),
    Axiology(
        "negative-lexical",
        "first total negative welfare, then total welfare",
        lambda p: (sum(v for v in p if v < 0), sum(p)),
    ),
    Axiology(
        "average-then-total",
        "average welfare, then total welfare",
        lambda p: (_average(p), sum(p)),
    ),
    Axiology(
        "total-then-average",
        "total welfare, then average welfare",
        lambda p: (sum(p), _average(p)),
    ),
    variable_value(2),
    variable_value(6),
    rank_discounted(Fraction(1, 2)),
    Axiology(
        "critical-level-2",
        "total of (w − 2)",
        lambda p: sum(v - 2 for v in p),
    ),
)

PRIMITIVE = (
    "thesis:egalitarian-dominance",
    "thesis:quantity",
    "thesis:quality",
    "thesis:dominance-addition",
    "arrhenius-2003:dominance-addition",
    "thesis:inequality-aversion",
    "thesis:non-sadism",
    "thesis:non-extreme-priority",
    "thesis:weak-quality-addition",
    "thesis:non-elitism",
    "arrhenius-2003:non-elitism",
    "thesis:general-non-extreme-priority",
    "thesis:weak-non-sadism",
    "arrhenius-2003:vrc-avoidance",
    "arrhenius-2009:weak-quality-addition",
)


def witness_grid(principle: str, ladder: Ladder) -> Iterator[dict[str, dict[str, int]]]:
    """Candidate witnesses for one principle's existential family (empty dict if none)."""
    from research.ladder import FORM, WITNESS_OF

    family = WITNESS_OF.get(FORM[principle])
    pos = [v for v in ladder.levels if v > 0]
    neg = [v for v in ladder.levels if v < 0]
    lows = [y for y in pos if y >= 3]
    highs = [(u, v) for u in pos for v in pos if v - u >= 2]
    if family is None:
        yield {}
    elif family in {"quantity", "inequality-aversion", "condition-beta"}:
        for step, mult in product((1, 2), (1, 2, 3)):
            yield {family: {"step": step, "mult": mult}}
    elif family == "quality":
        for y, (u, v), n in product(lows, highs, (1, 2)):
            if u > y:
                yield {family: {"u": u, "v": v, "y": y, "n": n}}
    elif family == "weak-quality-addition":
        for y, (x, w), n in product(lows, highs, (1, 2)):
            if x > y:
                yield {family: {"x": x, "w": w, "y": y, "n": n}}
    elif family == "non-extreme-priority":
        for x, y, z, n in product(pos, neg, lows, (1, 2, 3)):
            if x > z:
                yield {family: {"x": x, "y": y, "z": z, "n": n}}
    elif family == "non-elitism":
        for n in (1, 2, 3, 4):
            yield {family: {"n": n}}
    elif family == "general-non-extreme-priority":
        for u, y, n in product(pos, lows, (1, 2, 3)):
            if u > y:
                yield {family: {"u": u, "y": y, "n": n}}
    elif family == "weak-non-sadism":
        for x, n in product(neg, (1, 2, 3)):
            yield {family: {"x": x, "n": n}}
    elif family in {"vrc-avoidance", "weak-quality-addition-negative"}:
        for x, y, (u, v), n, m in product(neg, lows, highs, (1, 2), (1, 2)):
            if u > y:
                yield {family: {"x": x, "u": u, "v": v, "y": y, "n": n, "m": m}}
    else:
        raise ValueError(f"no grid for {family}")


def _holds(inst: Instance, key: Mapping[Pop, Any]) -> bool:
    a, b = key[inst.args[0]], key[inst.args[1]]
    if inst.shape == "S":
        return bool(a > b)
    if inst.shape == "W":
        return bool(a >= b)
    if inst.shape == "N":
        return not a > b
    raise ValueError(f"no fork shapes in the thesis family: {inst}")


def satisfaction(
    ladder: Ladder, lives: int, battery: tuple[Axiology, ...] = BATTERY
) -> dict[str, dict[str, dict[str, Any] | None]]:
    """axiology id -> principle -> a satisfying witness (possibly {}), or None if none found."""
    pops = domain(ladder, lives)
    keys = {ax.id: {p: ax.key(p) for p in pops} for ax in battery}
    out: dict[str, dict[str, dict[str, Any] | None]] = {ax.id: {} for ax in battery}
    for principle in PRIMITIVE:
        pending = {ax.id for ax in battery}
        for params in witness_grid(principle, ladder):
            if not pending:
                break
            try:
                insts = instances_over(pops, ladder, Witness(params), [principle])
            except ValueError:
                continue  # witness violates the source's own constraints on this ladder
            if not insts:
                continue  # vacuous on this universe: not evidence of anything
            for ax_id in sorted(pending):
                if all(_holds(i, keys[ax_id]) for i in insts):
                    out[ax_id][principle] = params
                    pending.discard(ax_id)
        for ax_id in pending:
            out[ax_id][principle] = None
    return out


# ---------------------------------------------------------------------------------------------
# Coverage: which condition sets are realized, and which unrealized ones are explained.

# Implications that hold for every axiology, with the source or argument for each.
IMPLIES: tuple[tuple[str, str, str], ...] = (
    ("thesis:non-sadism", "thesis:weak-non-sadism", "Weak Non-Sadism is a special case."),
    (
        "arrhenius-2003:dominance-addition",
        "thesis:dominance-addition",
        "⪰ implies not worse, and perfectly equal positive C is a case of positive C.",
    ),
    ("arrhenius-2003:non-elitism", "thesis:non-elitism", "any background includes R(y, x)."),
    (
        "arrhenius-2009:weak-quality-addition",
        "arrhenius-2003:vrc-avoidance",
        "take the background X = ∅.",
    ),
    (
        "thesis:weak-quality-addition",
        "thesis:quality",
        "take C = ∅ and R(u, v) = R(x, w).",
    ),
    (
        "thesis:non-elitism",
        "thesis:inequality-aversion",
        "thesis Lemma 5.1: Condition β with D = ∅ is Inequality Aversion (p. 167).",
    ),
)

KNOWN_THEOREMS: dict[str, frozenset[str]] = {
    "thesis-theorem-1": frozenset(
        {"thesis:quality", "thesis:quantity", "thesis:egalitarian-dominance"}
    ),
    "thesis-theorem-2": frozenset(
        {
            "thesis:quality",
            "thesis:inequality-aversion",
            "thesis:egalitarian-dominance",
            "thesis:dominance-addition",
        }
    ),
    "thesis-theorem-3": frozenset(
        {
            "thesis:egalitarian-dominance",
            "thesis:inequality-aversion",
            "thesis:non-sadism",
            "thesis:non-extreme-priority",
            "thesis:weak-quality-addition",
        }
    ),
    "thesis-theorem-4": frozenset(
        {
            "thesis:egalitarian-dominance",
            "thesis:non-elitism",
            "thesis:general-non-extreme-priority",
            "thesis:weak-non-sadism",
            "thesis:weak-quality-addition",
        }
    ),
    "arrhenius-2003": frozenset(
        {
            "thesis:egalitarian-dominance",
            "arrhenius-2003:non-elitism",
            "thesis:general-non-extreme-priority",
            "arrhenius-2003:vrc-avoidance",
            "arrhenius-2003:dominance-addition",
        }
    ),
    "arrhenius-2009": frozenset(
        {
            "thesis:egalitarian-dominance",
            "thesis:general-non-extreme-priority",
            "thesis:non-elitism",
            "thesis:weak-non-sadism",
            "arrhenius-2009:weak-quality-addition",
        }
    ),
}


def closure(conditions: frozenset[str]) -> frozenset[str]:
    out = set(conditions)
    changed = True
    while changed:
        changed = False
        for a, b, _ in IMPLIES:
            if a in out and b not in out:
                out.add(b)
                changed = True
    return frozenset(out)


def explained_by(conditions: frozenset[str]) -> list[str]:
    """Known theorems whose conditions the set implies."""
    c = closure(conditions)
    return sorted(k for k, t in KNOWN_THEOREMS.items() if t <= c)


def minimal_unrealized(
    universe: tuple[str, ...], realized: list[frozenset[str]]
) -> list[frozenset[str]]:
    """Minimal subsets of ``universe`` contained in no realized set."""
    maxima = [r for r in realized if not any(r < s for s in realized)]
    covered = [r for r in maxima]

    def is_realized(s: frozenset[str]) -> bool:
        return any(s <= r for r in covered)

    out: list[frozenset[str]] = []
    frontier: list[frozenset[str]] = [frozenset()]
    seen: set[frozenset[str]] = {frozenset()}
    while frontier:
        nxt = []
        for s in frontier:
            for c in universe:
                if c in s:
                    continue
                t = s | {c}
                if t in seen:
                    continue
                seen.add(t)
                if is_realized(t):
                    nxt.append(t)
                elif all(is_realized(t - {x}) for x in t):
                    out.append(t)
        frontier = nxt
    return sorted(out, key=lambda s: (len(s), sorted(s)))
