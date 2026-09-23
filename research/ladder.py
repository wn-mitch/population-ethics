"""Schema v1 for the thesis-family conditions: ordinal principles over a ladder of levels.

From the 2000 thesis on, Arrhenius states his conditions over indexed consecutive welfare levels
W_x and ranges R(x, y) of at least three consecutive levels, with no averages
(docs/decisions.md D-014, D-016). A ``Ladder`` is a finite chain of such levels, W_−a … W_b,
including the neutral level W_0 unless ``neutral=False``. A population is a sorted tuple of
level indices.

Each principle's cross-read reading is in ``corpus/readings.toml``. Where the source is silent
about empty populations, the generators require nonempty ones, which only drops instances.
Existentials are fixed by a ``Witness``; a finite UNSAT result therefore refutes "source
conditions + W" only (D-005, D-013). A witness is validated against the source's own
constraints on it (for example, ranges of at least three levels with R(u, v) above R(1, y)).

``instances_over`` generates exactly the instances whose populations all lie in a given set;
``audit`` independently recovers each instance's decomposition from its populations.
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from itertools import combinations_with_replacement, product

from research.readings import require_reviewed
from research.schema import Instance, Pop, sub_bags

LADDER_SCHEMA_ID = "arrhenius-thesis-family.schema/v1"


@dataclass(frozen=True)
class Ladder:
    negative: int  # levels W_-negative … W_-1
    positive: int  # levels W_1 … W_positive
    neutral: bool = True  # whether W_0 carries lives

    @property
    def levels(self) -> tuple[int, ...]:
        zero = (0,) if self.neutral else ()
        return (*range(-self.negative, 0), *zero, *range(1, self.positive + 1))

    def has(self, level: int) -> bool:
        return -self.negative <= level <= self.positive and (level != 0 or self.neutral)

    def range(self, lo: int, hi: int) -> tuple[int, ...]:
        """Levels of R(lo, hi) present on the ladder."""
        return tuple(v for v in self.levels if lo <= v <= hi)


def domain(ladder: Ladder, max_lives: int) -> list[Pop]:
    return [
        pop
        for size in range(1, max_lives + 1)
        for pop in combinations_with_replacement(ladder.levels, size)
    ]


def _plus(*parts: Pop) -> Pop:
    return tuple(sorted(v for part in parts for v in part))


def _bags(levels: Sequence[int], size: int) -> list[Pop]:
    return [tuple(c) for c in combinations_with_replacement(sorted(levels), size)] if size else [()]


# ---------------------------------------------------------------------------------------------
# Witnesses. Each existential principle takes named integer parameters; `WITNESS_FIELDS` lists
# them and `validate` checks the constraints the source's quantifier prefix places on them.

WITNESS_FIELDS: dict[str, tuple[str, ...]] = {
    "quantity": ("step",),  # m = mult·n + step (∃m > n); optional "mult" >= 1, default 1
    "quality": ("u", "v", "y", "n"),  # R(u, v), R(1, y), u > y, n > 0
    "inequality-aversion": ("step",),  # m = mult·n + step
    "non-extreme-priority": ("x", "y", "z", "n"),  # W_x, W_y (y < 0), R(1, z), x > z
    "weak-quality-addition": ("x", "w", "y", "n"),  # R(x, w), R(1, y), x > y
    "non-elitism": ("n",),  # n > 0, uniform over (x, y)
    "general-non-extreme-priority": ("u", "y", "n"),  # W_u, R(1, y), u > y, n > 0; uniform in z
    "weak-non-sadism": ("x", "n"),  # W_x, x < 0
    "vrc-avoidance": ("x", "u", "v", "y", "n", "m"),  # x < 0, R(u, v), R(1, y), u > y
    "weak-quality-addition-negative": ("x", "u", "v", "y", "n", "m"),
    "condition-beta": ("step",),  # m = mult·n + step
    "condition-delta": ("u", "y", "n"),  # n(m) = n + n_per_m·(m − 1); optional "n_per_m" >= 0
    "restricted-quality-addition": ("x", "y", "n", "m"),  # W_x, R(1, y), x > y
}


def larger(w: Mapping[str, int], n: int) -> int:
    """The witness for an "∃ m > n" existential: m = mult·n + step."""
    return w.get("mult", 1) * n + w["step"]


def delta_n(w: Mapping[str, int], m: int) -> int:
    """Condition δ's n for m negative lives: n + n_per_m·(m − 1), growing with m if n_per_m > 0."""
    return w["n"] + w.get("n_per_m", 0) * (m - 1)


@dataclass(frozen=True)
class Witness:
    params: Mapping[str, Mapping[str, int]] = field(default_factory=dict)

    def get(self, form: str) -> Mapping[str, int]:
        if form not in self.params:
            raise ValueError(f"witness has no parameters for {form}")
        return self.params[form]


def _is_range(ladder: Ladder, lo: int, hi: int) -> bool:
    return lo < hi and len(ladder.range(lo, hi)) >= 3 and ladder.has(lo) and ladder.has(hi)


def validate(form: str, ladder: Ladder, w: Mapping[str, int]) -> None:
    """Raise ValueError unless ``w`` satisfies the source's constraints for this form."""
    missing = set(WITNESS_FIELDS[form]) - set(w)
    if missing:
        raise ValueError(f"{form}: witness lacks {sorted(missing)}")
    problems: list[str] = []

    def need(ok: bool, what: str) -> None:
        if not ok:
            problems.append(what)

    if form in {"quantity", "inequality-aversion", "condition-beta"}:
        need(w["step"] >= 1 and w.get("mult", 1) >= 1, "step >= 1, mult >= 1")
    if form == "quality":
        need(_is_range(ladder, w["u"], w["v"]) and w["u"] > 0, "R(u, v) positive range")
        need(_is_range(ladder, 1, w["y"]), "R(1, y) range")
        need(w["u"] > w["y"] and w["n"] > 0, "u > y, n > 0")
    if form == "non-extreme-priority":
        need(_is_range(ladder, 1, w["z"]), "R(1, z) range")
        need(ladder.has(w["x"]) and w["x"] > w["z"], "W_x above R(1, z)")
        need(ladder.has(w["y"]) and w["y"] < 0, "W_y negative")
        need(w["n"] >= 1, "n >= 1")
    if form == "weak-quality-addition":
        need(_is_range(ladder, w["x"], w["w"]) and w["x"] > 0, "R(x, w) positive range")
        need(_is_range(ladder, 1, w["y"]) and w["x"] > w["y"], "R(1, y) below R(x, w)")
        need(w["n"] >= 1, "n >= 1")
    if form == "non-elitism":
        need(w["n"] > 0, "n > 0")
    if form in {"general-non-extreme-priority", "condition-delta"}:
        need(ladder.has(w["u"]) and w["u"] > 0, "W_u positive")
        need(_is_range(ladder, 1, w["y"]) and w["u"] > w["y"], "R(1, y) below W_u")
        need(w["n"] > 0 and w.get("n_per_m", 0) >= 0, "n > 0, n_per_m >= 0")
    if form == "weak-non-sadism":
        need(ladder.has(w["x"]) and w["x"] < 0 and w["n"] >= 1, "W_x negative, n >= 1")
    if form in {"vrc-avoidance", "weak-quality-addition-negative"}:
        need(ladder.has(w["x"]) and w["x"] < 0, "W_x negative")
        need(_is_range(ladder, w["u"], w["v"]) and w["u"] > 0, "R(u, v) positive range")
        need(_is_range(ladder, 1, w["y"]) and w["u"] > w["y"], "R(1, y) below R(u, v)")
        need(w["n"] > 0 and w["m"] > 0, "n, m > 0")
    if form == "restricted-quality-addition":
        need(ladder.has(w["x"]) and w["x"] > w["y"], "W_x above R(1, y)")
        need(_is_range(ladder, 1, w["y"]) and w["n"] >= 1 and w["m"] >= 1, "R(1, y), n, m")
    if problems:
        raise ValueError(f"{form}: witness violates {', '.join(problems)}")


# ---------------------------------------------------------------------------------------------
# Principle forms. Several works state the same condition; they share a form but keep their own
# principle ids (and readings). `D` ranges restrict the shared background where a source does.

FORM: dict[str, str] = {
    "thesis:egalitarian-dominance": "egalitarian-dominance",
    "arrhenius-2003:egalitarian-dominance": "egalitarian-dominance",
    "arrhenius-2009:egalitarian-dominance": "egalitarian-dominance",
    "thesis:quantity": "quantity",
    "thesis:quality": "quality",
    "thesis:dominance-addition": "dominance-addition-not-worse",
    "arrhenius-2003:dominance-addition": "dominance-addition-weak",
    "thesis:inequality-aversion": "inequality-aversion",
    "thesis:non-sadism": "non-sadism-equal",
    "thesis:non-extreme-priority": "non-extreme-priority",
    "thesis:weak-quality-addition": "weak-quality-addition",
    "thesis:non-elitism": "non-elitism-ranged",
    "arrhenius-2009:non-elitism": "non-elitism-ranged",
    "arrhenius-2003:non-elitism": "non-elitism-any",
    "thesis:general-non-extreme-priority": "general-non-extreme-priority",
    "arrhenius-2003:general-non-extreme-priority": "general-non-extreme-priority",
    "arrhenius-2009:general-non-extreme-priority": "general-non-extreme-priority",
    "thesis:weak-non-sadism": "weak-non-sadism",
    "arrhenius-2009:weak-non-sadism": "weak-non-sadism",
    "arrhenius-2003:vrc-avoidance": "vrc-avoidance",
    "arrhenius-2009:weak-quality-addition": "weak-quality-addition-negative",
    "thesis:condition-beta": "condition-beta-ranged",
    "arrhenius-2009:condition-beta": "condition-beta-ranged",
    "arrhenius-2003:condition-beta": "condition-beta-any",
    "thesis:condition-delta": "condition-delta",
    "arrhenius-2003:condition-delta": "condition-delta",
    "arrhenius-2009:condition-delta": "condition-delta",
    "arrhenius-2009:restricted-quality-addition": "restricted-quality-addition",
}

# Witness parameters are keyed by the form's witness family.
WITNESS_OF = {
    "quantity": "quantity",
    "quality": "quality",
    "inequality-aversion": "inequality-aversion",
    "non-extreme-priority": "non-extreme-priority",
    "weak-quality-addition": "weak-quality-addition",
    "non-elitism-ranged": "non-elitism",
    "non-elitism-any": "non-elitism",
    "general-non-extreme-priority": "general-non-extreme-priority",
    "weak-non-sadism": "weak-non-sadism",
    "vrc-avoidance": "vrc-avoidance",
    "weak-quality-addition-negative": "weak-quality-addition-negative",
    "condition-beta-ranged": "condition-beta",
    "condition-beta-any": "condition-beta",
    "condition-delta": "condition-delta",
    "restricted-quality-addition": "restricted-quality-addition",
}


@dataclass(frozen=True)
class Move:
    """One application: shared background plus the two added parts, and the instance shape.

    The instance compares ``left = background ⊎ left_part`` with ``right = background ⊎
    right_part`` (and, for shape N, asserts ¬(left ≻ right)).
    """

    left: Pop
    right: Pop
    background_levels: tuple[int, ...] | None  # None: any levels; () : empty background only


def _moves(form: str, ladder: Ladder, w: Mapping[str, int], cap: int) -> Iterator[Move]:
    """Every added-part pair (before backgrounds) for a form, with at most ``cap`` lives each."""
    levels = ladder.levels
    pos = [v for v in levels if v > 0]
    neg = [v for v in levels if v < 0]
    sizes = range(1, cap + 1)
    if form == "egalitarian-dominance":
        for x in levels:
            for n in sizes:
                for b in _bags([v for v in levels if v < x], n):
                    yield Move((x,) * n, b, ())
    elif form == "quantity":
        for y in pos:
            x = y + 1
            if ladder.has(x):
                for n in sizes:
                    m = larger(w, n)
                    if m <= cap:
                        yield Move((y,) * m, (x,) * n, ())
    elif form == "quality":
        for z in ladder.range(w["u"], w["v"]):
            for size in sizes:
                for b in _bags(ladder.range(1, w["y"]), size):
                    if w["n"] <= cap:
                        yield Move((z,) * w["n"], b, ())
    elif form in {"dominance-addition-not-worse", "dominance-addition-weak"}:
        for n in sizes:
            for a in _bags(levels, n):
                for b in _bags([v for v in levels if v > a[-1]], n):
                    if form == "dominance-addition-not-worse":
                        adds = [(y,) * k for y in pos for k in sizes]
                    else:
                        adds = [c for k in sizes for c in _bags(pos, k)]
                    for c in adds:
                        # thesis: ¬(A ≻ B∪C) (shape N, left = A); 2003: B∪C ⪰ A (shape W).
                        if form == "dominance-addition-not-worse":
                            yield Move(a, _plus(b, c), ())
                        else:
                            yield Move(_plus(b, c), a, ())
    elif form == "inequality-aversion":
        for x, y, z in product(levels, repeat=3):
            if x > y > z:
                for n in sizes:
                    m = larger(w, n)
                    if m + n <= cap:
                        yield Move((y,) * (m + n), _plus((x,) * n, (z,) * m), ())
    elif form == "non-sadism-equal":
        for x, y in product(pos, neg):
            for k, j in product(sizes, sizes):
                yield Move((x,) * k, (y,) * j, None)
    elif form == "non-extreme-priority":
        n = w["n"]
        for u in [v for v in levels if v >= w["x"]]:
            for b in _bags(ladder.range(1, w["z"]), n + 1):
                yield Move(_plus((u,) * n, (w["y"],)), b, None)
    elif form == "weak-quality-addition":
        for z in [v for v in levels if v >= w["x"]]:
            for size in sizes:
                for b in _bags(ladder.range(1, w["y"]), size):
                    yield Move((z,) * w["n"], b, None)
    elif form in {"non-elitism-ranged", "non-elitism-any"}:
        n = w["n"]
        for x, y in product(levels, repeat=2):
            if x - 1 > y and ladder.has(x - 1):
                bg = ladder.range(y, x) if form == "non-elitism-ranged" else None
                yield Move(((x - 1),) * (n + 1), _plus((x,), (y,) * n), bg)
    elif form == "general-non-extreme-priority":
        n = w["n"]
        for z in levels:
            if ladder.has(z + 1):
                for x in [v for v in levels if v >= w["u"]]:
                    for b in _bags(ladder.range(1, w["y"]), n):
                        yield Move(_plus((x,) * n, (z,)), _plus(b, (z + 1,)), None)
    elif form == "weak-non-sadism":
        for y in pos:
            for k in sizes:
                yield Move((y,) * k, (w["x"],) * w["n"], None)
    elif form in {"vrc-avoidance", "weak-quality-addition-negative"}:
        bg = () if form == "vrc-avoidance" else None
        for z in [v for v in levels if v >= w["u"]]:
            for size in sizes:
                for b in _bags(ladder.range(1, w["y"]), size):
                    yield Move((z,) * w["n"], _plus(b, (w["x"],) * w["m"]), bg)
    elif form in {"condition-beta-ranged", "condition-beta-any"}:
        for x, y, z in product(levels, repeat=3):
            if x > y > z:
                for n in sizes:
                    m = larger(w, n)
                    bg = ladder.range(z, y + 1) if form == "condition-beta-ranged" else None
                    yield Move((y,) * (m + n), _plus((x,) * n, (z,) * m), bg)
    elif form == "condition-delta":
        if ladder.has(3):
            for z in neg:
                for m in sizes:
                    n = delta_n(w, m)
                    for x in [v for v in levels if v >= w["u"]]:
                        for b in _bags(ladder.range(1, w["y"]), n):
                            yield Move(_plus((x,) * n, (z,) * m), _plus(b, (3,) * m), None)
    elif form == "restricted-quality-addition":
        for z in [v for v in levels if v >= w["x"]]:
            for p in range(w["m"], cap + 1):
                for b in _bags(ladder.range(1, w["y"]), p):
                    yield Move((z,) * w["n"], b, None)
    else:
        raise ValueError(f"unknown form {form}")


def instances_over(
    pops: Iterable[Pop], ladder: Ladder, witness: Witness, principles: Iterable[str]
) -> list[Instance]:
    """Every instance of the given principles whose populations all lie in ``pops``.

    Raises UnreviewedPrinciple before generating anything if a principle has not passed the
    review-first gate, and ValueError if a required witness is missing or invalid.
    """
    principles = list(dict.fromkeys(principles))
    require_reviewed(principles)
    universe = set(pops)
    cap = max((len(p) for p in universe), default=0)
    out: list[Instance] = []
    for principle in principles:
        form = FORM[principle]
        family = WITNESS_OF.get(form)
        w: Mapping[str, int] = {}
        if family is not None:
            w = witness.get(family)
            validate(family, ladder, w)
        backgrounds = sub_bags(universe)
        seen: set[tuple[Pop, Pop]] = set()
        for move in _moves(form, ladder, w, cap):
            if move.background_levels == ():
                candidates: list[Pop] = [()]
            else:
                allowed = move.background_levels
                candidates = [
                    b for b in backgrounds if allowed is None or all(v in allowed for v in b)
                ]
            for b in candidates:
                left, right = _plus(b, move.left), _plus(b, move.right)
                pair = (left, right)
                if left in universe and right in universe and left != right and pair not in seen:
                    seen.add(pair)
                    out.append(Instance(principle, pair))
    return out


# ---------------------------------------------------------------------------------------------
# Independent audit: recover a decomposition (background, added parts) from the populations.


def _sub_bags(common: Counter[int]) -> Iterator[Counter[int]]:
    items = sorted(common.items())
    for counts in product(*(range(c + 1) for _, c in items)):
        yield Counter({k: c for (k, _), c in zip(items, counts, strict=True) if c})


def _levels_in(bag: Counter[int], allowed: Callable[[int], bool]) -> bool:
    return all(allowed(v) for v in bag.elements())


def _single(bag: Counter[int]) -> int | None:
    """The level if the bag is nonempty and perfectly equal, else None."""
    return next(iter(bag)) if len(bag) == 1 else None


def _added_ok(
    form: str, ladder: Ladder, w: Mapping[str, int], lp: Counter[int], rp: Counter[int]
) -> bool:
    """Do these added parts (left, right) match the form's antecedent? Written from the readings."""
    n_l, n_r = sum(lp.values()), sum(rp.values())
    has = ladder.has
    lo = ladder.range
    if form == "quantity":
        y, x = _single(lp), _single(rp)
        return y is not None and x is not None and y > 0 and x == y + 1 and n_l == larger(w, n_r)
    if form == "quality":
        z = _single(lp)
        return (
            z is not None
            and z in lo(w["u"], w["v"])
            and n_l == w["n"]
            and n_r >= 1
            and _levels_in(rp, lambda v: v in lo(1, w["y"]))
        )
    if form == "inequality-aversion" or form.startswith("condition-beta"):
        y = _single(lp)
        if y is None or len(rp) != 2:
            return False
        z, x = sorted(rp)
        return x > y > z and rp[z] == larger(w, rp[x]) and n_l == rp[x] + rp[z]
    if form == "non-sadism-equal":
        x, y = _single(lp), _single(rp)
        return x is not None and y is not None and x > 0 and y < 0
    if form == "non-extreme-priority":
        n = w["n"]
        if lp[w["y"]] != 1:
            return False
        high = lp - Counter({w["y"]: 1})
        u = _single(high)
        return (
            u is not None
            and u >= w["x"]
            and sum(high.values()) == n
            and n_r == n + 1
            and _levels_in(rp, lambda v: v in lo(1, w["z"]))
        )
    if form == "weak-quality-addition":
        z = _single(lp)
        return (
            z is not None
            and z >= w["x"]
            and n_l == w["n"]
            and n_r >= 1
            and _levels_in(rp, lambda v: v in lo(1, w["y"]))
        )
    if form.startswith("non-elitism"):
        n = w["n"]
        c = _single(lp)
        if c is None or n_l != n + 1 or len(rp) != 2:
            return False
        y, x = sorted(rp)
        return rp[x] == 1 and rp[y] == n and c == x - 1 and x - 1 > y
    if form == "general-non-extreme-priority":
        n = w["n"]
        for z in [v for v in lp if has(v + 1)]:
            high = lp - Counter({z: 1})
            low = rp - Counter({z + 1: 1})
            x = _single(high)
            if (
                lp[z] >= 1
                and rp[z + 1] >= 1
                and x is not None
                and x >= w["u"]
                and sum(high.values()) == n
                and sum(low.values()) == n
                and _levels_in(low, lambda v: v in lo(1, w["y"]))
            ):
                return True
        return False
    if form == "weak-non-sadism":
        y = _single(lp)
        return y is not None and y > 0 and rp == Counter({w["x"]: w["n"]})
    if form in {"vrc-avoidance", "weak-quality-addition-negative"}:
        z = _single(lp)
        low = rp - Counter({w["x"]: w["m"]})
        return (
            z is not None
            and z >= w["u"]
            and n_l == w["n"]
            and rp[w["x"]] == w["m"]
            and sum(low.values()) >= 1
            and _levels_in(low, lambda v: v in lo(1, w["y"]))
        )
    if form == "condition-delta":
        for z in [v for v in lp if v < 0]:
            m = lp[z]
            n = delta_n(w, m)
            high = lp - Counter({z: m})
            low = rp - Counter({3: m})
            x = _single(high)
            if (
                rp[3] >= m
                and x is not None
                and x >= w["u"]
                and sum(high.values()) == n
                and sum(low.values()) == n
                and _levels_in(low, lambda v: v in lo(1, w["y"]))
            ):
                return True
        return False
    if form == "restricted-quality-addition":
        z = _single(lp)
        return (
            z is not None
            and z >= w["x"]
            and n_l == w["n"]
            and n_r >= w["m"]
            and _levels_in(rp, lambda v: v in lo(1, w["y"]))
        )
    raise ValueError(f"no audit for {form}")


def _background_ok(form: str, bg: Counter[int], lp: Counter[int], rp: Counter[int]) -> bool:
    if form in {"quantity", "quality", "inequality-aversion", "vrc-avoidance"}:
        return not bg
    if form == "non-elitism-ranged":
        y, x = sorted(rp) if len(rp) == 2 else (0, 0)
        return all(y <= v <= x for v in bg.elements())
    if form == "condition-beta-ranged":
        if len(rp) != 2:
            return False
        low = min(rp)
        mid = _single(lp)
        return mid is not None and all(low <= v <= mid + 1 for v in bg.elements())
    return True


def audit(instance: Instance, ladder: Ladder, witness: Witness) -> bool:
    """Re-derive applicability of one ladder instance from its populations alone."""
    form = FORM[instance.principle]
    left, right = (Counter(p) for p in instance.args)
    if not instance.args[0] or not instance.args[1] or instance.args[0] == instance.args[1]:
        return False
    if not all(ladder.has(v) for p in instance.args for v in p):
        return False
    if form == "egalitarian-dominance":
        x = _single(left)
        return x is not None and sum(left.values()) == sum(right.values()) and max(right) < x
    if form.startswith("dominance-addition"):
        # thesis: args (A, B∪C) with ¬(A ≻ B∪C); 2003: args (B∪C, A).
        a, bc = (left, right) if form.endswith("not-worse") else (right, left)
        n = sum(a.values())
        top = sorted(bc.elements(), reverse=True)
        # B = the n highest lives of B∪C (any valid split has B at least as high as C's
        # remainder only if min B > max A; try every split point that keeps |B| = n).
        for b_levels in {tuple(sorted(s)) for s in _choose(top, n)}:
            b = Counter(b_levels)
            c = bc - b
            if not c or min(b) <= max(a):
                continue
            if form.endswith("not-worse"):
                y = _single(c)
                if y is not None and y > 0:
                    return True
            elif all(v > 0 for v in c.elements()):
                return True
        return False
    family = WITNESS_OF.get(form)
    w = witness.get(family) if family is not None else {}
    common = left & right
    for bg in _sub_bags(common):
        lp, rp = left - bg, right - bg
        if lp and rp and _background_ok(form, bg, lp, rp) and _added_ok(form, ladder, w, lp, rp):
            return True
    return False


def _choose(items: Sequence[int], k: int) -> Iterator[tuple[int, ...]]:
    from itertools import combinations

    return combinations(items, k)
