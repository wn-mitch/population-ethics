"""Phase 18: source-faithful candidate-and-certificate pass on Q-011's three weakenings.

The pass has four parts, in this order:

1. ``SOURCE_MANIFEST`` freezes, per principle, the reviewed reading's quantifier prefix,
   allowed background, level conventions and emptiness assumptions (corpus/readings.toml,
   checked against the cached primary pages: Arrhenius 2003 pp. 168-179, thesis pp. 159-180).
2. ``control_edges`` builds the primitive original-theorem control: the 2003 Lemma 3 chain with
   Condition beta expanded into 35 primitive Non-Elitism applications and Condition delta into
   four primitive GNEP applications. ``verify_edge`` replays every serialized edge from its own
   decomposition without consulting the constructor, and ``compact_closure`` decides the written
   chain with mentioned-atom transitivity and reflexivity only, never completeness.
3. ``bounded_search`` runs the discriminating search on the same ladder and witness, at the two
   fixed focus caps (32 then 64 relata), with the seven p17 principles.
4. ``refine_candidates`` inspects the explicit candidates: an UNSAT core is shrunk and replayed
   edge by edge; a SAT assignment on 32 relata is extended to the 64-relata focus.

Nothing here is a consistency or impossibility certificate for the unrestricted conditions: a
bounded SAT table and an absent cycle are not evidence about them (AGENTS.md; D-005, D-013), and
a fixed-witness or ladder-relative result is labelled as such. Q-011 stays open unless a
source-general witness-parameter construction or a full finite-ladder model is discharged.
"""

from __future__ import annotations

import hashlib
import json
import time
from collections import Counter
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any

from population_ethics.principles import GroundConstraint
from population_ethics.relations import Implies, Not, conjunction, encode_z3, strict, weak
from research.census import cycle_words
from research.lab import (
    Engine,
    LedgerEntry,
    _atoms,
    background,
    dpll_check,
    ground,
    record,
    write_result,
)
from research.ladder import FORM, Ladder, Witness, audit, domain, instances_over, validate
from research.p6_schema import core_constraints, formula_of, name_of
from research.p8_catalogue import LADDER, THEOREM_2003, check
from research.p16_ne_top import decide_without_completeness
from research.p17_vrc_boundary import (
    DA_2003,
    DA_THESIS,
    ED,
    GNEP,
    NE_2003,
    NE_THESIS,
    SOURCE_WITNESS,
    VARIANTS,
    VRC,
)
from research.schema import SHAPE, Instance, Pop

BETA = "arrhenius-2003:condition-beta"
DELTA = "arrhenius-2003:condition-delta"
THEOREM = "arrhenius-2003:theorem"

# The seven generated principles: the five source conditions plus both weakenings.
SEVEN: tuple[str, ...] = (ED, GNEP, VRC, NE_2003, NE_THESIS, DA_2003, DA_THESIS)

# Search domain: at most three lives per relatum, foci of 32 and then 64 populations.
MAX_LIVES = 3
CAPS: tuple[int, ...] = (32, 64)

# The mandatory seeds force one instance of each source shape the weakening argument turns on.
MANDATORY_SEEDS: tuple[Pop, ...] = (
    (5,),  # Egalitarian Dominance: a single unequal high life
    (4,),  # VRC avoidance: the high population at the low end of R(u, v)
    (3, 3),  # Condition delta / W_3 lives on both sides
    (1, 4),  # 2003 Dominance Addition: mixed positive addition below the threshold
    (-1, 3, 3),  # VRC avoidance with a negative life beside positive ones
    (-1, 1, 4),  # GNEP: one life at W_z beside high and low-range lives
    (-1, 4),  # GNEP with the smallest possible pair
    (0, 1),  # GNEP through the neutral level (z = -1 needs W_0)
    (-1, 1),  # Non-Elitism: a disallowed negative background for ranged NE
    (1, 3, 5),  # ranged Non-Elitism with an allowed background in R(y, x)
    (1, 5),  # ranged Non-Elitism: the background is exactly the two endpoints
)


# ---------------------------------------------------------------------------------------------
# Source manifest: what each serialized edge is replayed against.


@dataclass(frozen=True)
class SourceEntry:
    """One reviewed reading's frozen formal content."""

    reading: str
    work: str
    page: str
    quantifiers: str
    background: str
    levels: str
    emptiness: str
    chain: str = "n/a"
    note: str = ""


SOURCE_MANIFEST: dict[str, SourceEntry] = {
    ED: SourceEntry(
        reading=ED,
        work="arrhenius-2003-vrc",
        page="171",
        quantifiers="forall A forall B (N(A)=N(B)) forall W_x :: B subset R(Omega, x-1) and A subset W_x",
        background="none: the condition compares two populations with no shared term",
        levels="W_x ranges over every indexed level, positive, neutral or negative",
        emptiness="A and B must be nonempty (with A = B = empty the condition would assert "
        "empty is better than empty); the text does not say so",
        note="strict shape S; the ladder generator emits empty backgrounds only",
    ),
    DA_2003: SourceEntry(
        reading=DA_2003,
        work="arrhenius-2003-vrc",
        page="171",
        quantifiers="forall A forall B forall C forall W_x :: A subset R(Omega, x-1), B subset "
        "R(x, Omega), N(A)=N(B), C subset R(1, Omega)",
        background="none: C is the addition, not a shared background",
        levels="W_x any level; C must be positive (C subset R(1, Omega))",
        emptiness="the source states only N(A)=N(B), which does not exclude 0; the ladder "
        "encoding drops the empty cases and requires C nonempty at one level (the source's "
        "'any number of lives' is silent about zero)",
        note="weak shape W: B union C is at least as good as A; mixed positive C allowed, and "
        "applicability is an existence question over splits of B union C",
    ),
    DA_THESIS: SourceEntry(
        reading=DA_THESIS,
        work="arrhenius-2000-thesis",
        page="159",
        quantifiers="forall A forall B forall C forall W_x forall W_y (y > 0) :: every A life "
        "below W_x, every B life at or above W_x, N(A)=N(B), C subset W_y",
        background="none",
        levels="W_x any level; W_y positive, C perfectly equal at W_y",
        emptiness="the source states only N(A)=N(B) and leaves N(C) unconstrained; the ladder "
        "encoding drops the empty cases and requires C nonempty at one positive level",
        note="not-strict shape N: not(A better than B union C); C must be a single positive "
        "level, so a mixed positive addition is not an instance; no reverse weak edge without "
        "completeness",
    ),
    NE_2003: SourceEntry(
        reading=NE_2003,
        work="arrhenius-2003-vrc",
        page="172",
        quantifiers="forall W_x forall W_y (x-1 > y) exists n>0 forall A subset W_x (N=1) "
        "forall B subset W_y (N=n) forall C subset W_{x-1} (N=n+1) forall D",
        background="any D, unrestricted ('for any D')",
        levels="no sign restriction; W_{x-1} is the level just below W_x",
        emptiness="A, B, C nonempty by their sizes; D may be empty (unstated)",
        note="weak shape W: C union D is at least as good as A union B union D",
    ),
    NE_THESIS: SourceEntry(
        reading=NE_THESIS,
        work="arrhenius-2000-thesis",
        page="166",
        quantifiers="forall W_x forall W_y (x-1 > y) exists n>0 forall A subset W_x (N=1) "
        "forall B subset W_y (N=n) forall C subset W_{x-1} (N=n+1) forall D subset R(y, x)",
        background="D subset R(y, x): a ranged background, so no life below W_y",
        levels="no sign restriction",
        emptiness="D may be empty (the Condition beta note treats D = empty as admissible)",
        note="the 2003 reading has the same body with any D; this is Q-011's ranged weakening "
        "and it is what loses the derived beta edge's negative background",
    ),
    GNEP: SourceEntry(
        reading=GNEP,
        work="arrhenius-2003-vrc",
        page="171-172",
        quantifiers="forall W_z exists W_u (positive) exists R(1, y) (positive, u > y) "
        "exists n>0 forall x >= u forall A subset W_x forall B subset R(1, y) (N=n) forall "
        "C subset W_z forall D subset W_{z+1} (N=1) forall E",
        background="any E, unrestricted",
        levels="W_z any level including the neutral W_0, so the ladder needs W_0; u > y >= 3 "
        "because a range has at least three levels",
        emptiness="A, B nonempty (n>0); C, D one life each; E may be empty (unstated)",
        note="weak shape W: A union C union E is at least as good as B union D union E",
    ),
    VRC: SourceEntry(
        reading=VRC,
        work="arrhenius-2003-vrc",
        page="172",
        quantifiers="exists W_x (x<0) exists R(u, v) exists R(1, y) (positive, u > y) "
        "exists n>0 exists m>0 forall A subset W_z (z >= u, N=n) forall B subset R(1, y) "
        "forall C subset W_x (N=m)",
        background="none",
        levels="W_x negative; A at any single level z >= u (the upper bound v is unused); B in "
        "R(1, y)",
        emptiness="A and C nonempty (n, m > 0); B's size is unrestricted and may be empty",
        note="weak shape W: A is at least as good as B union C; this is the source's closing "
        "link in Lemma 3",
    ),
    BETA: SourceEntry(
        reading=BETA,
        work="arrhenius-2003-vrc",
        page="173",
        quantifiers="forall W_x forall W_y forall W_z (x > y > z) forall n>0 exists m>n "
        "forall A subset W_x (N=n) forall B subset W_z (N=m) forall C subset W_y (N=m+n) "
        "forall D",
        background="any D in the 2003 statement; the proofs assemble only narrower backgrounds "
        "(Lemma 1.1 uses E subset R(y, x), Lemma 1.2 uses E subset R(z, y+1)) although D was "
        "introduced as any population, so the displayed condition governs the instance and "
        "only the proof text is narrower",
        levels="no sign restriction",
        emptiness="D may be empty; m > n forces B nonempty",
        chain="derived: Non-Elitism implies alpha (Lemma 1.1: n applications of Non-Elitism "
        "with each C_i of size p+1 and each B_i of size p give alpha with m = n*p, where p is "
        "the Non-Elitism witness), and alpha implies beta (Lemma 1.2: r = x - y applications "
        "of alpha with m_i >= f(m_{i-1}) and f(m_i) = m_0+...+m_i, so m = m_1+...+m_r > "
        "m_0 = n)",
        note="Lemma 1.2's strictness claim needs r >= 2, which holds in Lemma 3 where beta is "
        "applied at levels W_{x+2} > W_3 > W_1; the source's own Lemma 3 applies beta with D2 "
        "at the negative VRC level, outside Lemma 1.2's R(1, 4) for that application, so the "
        "negative-background instance rests on the displayed condition, which is exactly the "
        "gap ranged Non-Elitism cannot fill",
    ),
    DELTA: SourceEntry(
        reading=DELTA,
        work="arrhenius-2003-vrc",
        page="177",
        quantifiers="forall W_z (z<0) forall m>0 exists W_u (positive) exists R(1, y) "
        "(positive, u > y) exists n>0 forall x >= u forall A subset W_x forall B subset "
        "R(1, y) (N=n) forall C subset W_z (N=m) forall D subset W_3 (N=m) forall E",
        background="any E",
        levels="W_u, R(1, y) positive with u > y; D at the fixed level W_3",
        emptiness="E may be empty (unstated); the other populations are nonempty by size",
        chain="derived: GNEP implies chi (thesis Lemma 5.2.1 with r = 3 - z applications of "
        "GNEP at W_{z+(i-1)}, i = 1..r, and chi's n = n_1+...+n_r), and chi implies delta "
        "(thesis Lemma 5.2.2 with m copies of chi, so delta's n = m * n_chi)",
        note="the 2003 paper defers this proof to thesis Lemma 5.2 or 2001 Lemma 2",
    ),
    THEOREM: SourceEntry(
        reading=THEOREM,
        work="arrhenius-2003-vrc",
        page="173",
        quantifiers="no population axiology (reflexive, transitive, not necessarily complete "
        "ordering) satisfies (1*)-(5*)",
        background="n/a (theorem scope)",
        levels="the proof uses Discreteness, the W_i indexing and unrestricted population "
        "sizes as background assumptions",
        emptiness="all Lemma 3 populations are nonempty",
        chain="Lemma 1 (NE => beta), Lemma 2 (GNEP => delta), Lemma 3 (ED, VRC, DA, beta, "
        "delta are inconsistent)",
        note="the frozen P8 core is the derived end-point pattern, not a primitive expansion",
    ),
}

# The control's chosen witness. NE, GNEP and VRC are p17's SOURCE_WITNESS values; the two
# derived conditions are fixed at the counts their primitive expansions actually produce:
# delta's n = 1 * (1+1+1+1) = 4 for z = -1 and m = 1 (four GNEP applications at z = -1..2),
# and beta's m = 1*5 + 30 = 35 for n = 5 (5 + 10 + 20 Non-Elitism applications).
CONTROL_WITNESS = Witness(
    {
        **SOURCE_WITNESS.params,
        "condition-delta": {"u": 4, "y": 3, "n": 4},
        "condition-beta": {"step": 30},
    }
)


# ---------------------------------------------------------------------------------------------
# Edge records: the exported decomposition, and its independent replay.


def _plus(*parts: Pop) -> Pop:
    return tuple(sorted(v for part in parts for v in part))


def _counts(pop: Pop) -> list[list[int]]:
    return [[level, count] for level, count in sorted(Counter(pop).items())]


def _counter(pairs: Iterable[Sequence[int]]) -> Counter[int]:
    return Counter({int(level): int(count) for level, count in pairs})


def _pop(pairs: Iterable[Sequence[int]]) -> Pop:
    return tuple(sorted(_counter(pairs).elements()))


@dataclass(frozen=True)
class Edge:
    """One primitive source instance, stored as its decomposition rather than its endpoints.

    ``left = background + left_part`` and ``right = background + right_part``. The instance is
    ``Instance(principle, (left, right))``, so the formula's direction is the reading's own.
    """

    principle: str
    left_part: Pop
    right_part: Pop
    background: Pop = ()
    witness: Mapping[str, int] = field(default_factory=dict)

    @property
    def shape(self) -> str:
        return SHAPE[self.principle]

    @property
    def left(self) -> Pop:
        return _plus(self.background, self.left_part)

    @property
    def right(self) -> Pop:
        return _plus(self.background, self.right_part)

    @property
    def instance(self) -> Instance:
        return Instance(self.principle, (self.left, self.right))

    def record(self) -> dict[str, Any]:
        """The serialized edge the independent replayer consumes."""
        entry = SOURCE_MANIFEST[self.principle]
        return {
            "principle": self.principle,
            "shape": self.shape,
            "source": entry.reading,
            "page": entry.page,
            "left": _counts(self.left),
            "right": _counts(self.right),
            "background": _counts(self.background),
            "left_part": _counts(self.left_part),
            "right_part": _counts(self.right_part),
            "witness": dict(sorted(self.witness.items())),
        }


def _single(bag: Counter[int]) -> int | None:
    """The level if the bag is nonempty and perfectly equal, else None."""
    return next(iter(bag)) if len(bag) == 1 else None


def _levels_in(bag: Counter[int], allowed: Iterable[int]) -> bool:
    allowed = set(allowed)
    return all(v in allowed for v in bag.elements())


def verify_edge(
    record: Mapping[str, Any], ladder: Ladder = LADDER, witness: Witness = CONTROL_WITNESS
) -> list[str]:
    """Replay one serialized edge against the frozen manifest, without the constructor.

    Returns every violation found; an empty list means the record is a source instance of its
    principle at the recorded decomposition under ``witness``. The decomposition is recomputed
    from the count vectors, and each premise (size, level, range, background and sign) is
    re-derived from ``SOURCE_MANIFEST`` rather than read from the constructor.
    """
    problems: list[str] = []
    principle = str(record.get("principle", ""))
    entry = SOURCE_MANIFEST.get(principle)
    if entry is None:
        return [f"unknown principle {principle!r}"]
    if record.get("shape") != SHAPE[principle]:
        problems.append(f"shape {record.get('shape')!r} is not the reading's {SHAPE[principle]}")
    if record.get("source") != entry.reading or record.get("page") != entry.page:
        problems.append("source reading or page does not match the frozen manifest")

    background_counts = _counter(record.get("background", []))
    left_part = _counter(record.get("left_part", []))
    right_part = _counter(record.get("right_part", []))
    left, right = _counter(record.get("left", [])), _counter(record.get("right", []))
    if -left_part or -right_part or -left or -right:
        problems.append("negative counts")
    if left != background_counts + left_part:
        problems.append("left is not background + left_part")
    if right != background_counts + right_part:
        problems.append("right is not background + right_part")
    if not left or not right or left == right:
        problems.append("an edge needs two distinct nonempty populations")
    if not all(ladder.has(v) for v in (*left.elements(), *right.elements())):
        problems.append("a level lies outside the ladder")

    form = FORM[principle]
    lookup = dict(record.get("witness", {}))
    if form == "egalitarian-dominance":
        if background_counts:
            problems.append("Egalitarian Dominance has no background")
        x = _single(left_part)
        if x is None:
            problems.append("Egalitarian Dominance needs a perfectly equal A")
        elif sum(left_part.values()) != sum(right_part.values()):
            problems.append("Egalitarian Dominance needs N(A) = N(B)")
        elif right_part and max(right_part) >= x:
            problems.append("Egalitarian Dominance needs every B life below W_x")
    elif form == "dominance-addition-weak":
        problems += _verify_dominance_addition(left_part, right_part, background_counts, "2003")
    elif form == "dominance-addition-not-worse":
        problems += _verify_dominance_addition(left_part, right_part, background_counts, "thesis")
    else:
        family = {
            "non-elitism-ranged": "non-elitism",
            "non-elitism-any": "non-elitism",
            "general-non-extreme-priority": "general-non-extreme-priority",
            "vrc-avoidance": "vrc-avoidance",
            "condition-beta-ranged": "condition-beta",
            "condition-beta-any": "condition-beta",
            "condition-delta": "condition-delta",
        }.get(form)
        if family is None:
            problems.append(f"no replay for form {form!r}")
        else:
            w = witness.get(family)
            try:
                validate(family, ladder, w)
            except ValueError as error:
                problems.append(f"control witness rejected: {error}")
            if form.startswith("non-elitism"):
                problems += _verify_non_elitism(
                    left_part, right_part, background_counts, lookup, form, w
                )
            elif form == "general-non-extreme-priority":
                problems += _verify_gnep(left_part, right_part, lookup, w, ladder)
            elif form == "vrc-avoidance":
                problems += _verify_vrc(left_part, right_part, background_counts, lookup, w, ladder)
            else:
                problems += _verify_beta_delta(form, left_part, right_part, lookup, w, ladder)
    return problems


def _verify_dominance_addition(
    left_part: Counter[int], right_part: Counter[int], background: Counter[int], which: str
) -> list[str]:
    """Replay Condition (2*) or the thesis form. The two shapes fix which side is A.

    The source quantifies over A, B and C separately and only their union B union C appears in
    the comparison, so an instance is applicable when *some* split of the union gives B the same
    size as A with every B life above every A life and C of the shape that form requires. The
    union's lives above every A life are the only candidates for B, and the first valid split
    decides the edge.
    """
    problems: list[str] = []
    if background:
        problems.append("Dominance Addition has no background")
    a, bc = (right_part, left_part) if which == "2003" else (left_part, right_part)
    size = sum(a.values())
    if size < 1:
        return [*problems, "Dominance Addition needs a nonempty A"]
    if sum(bc.values()) <= size:
        return [*problems, "Dominance Addition needs B union C strictly larger than A"]
    for candidate in _b_splits(bc, size, max(a)):
        rest = bc - candidate
        if not rest:
            continue
        if which == "2003":
            if all(v > 0 for v in rest.elements()):
                return problems
        else:
            y = _single(rest)
            if y is not None and y > 0:
                return problems
    detail = (
        "2003 Dominance Addition allows only a positive C"
        if which == "2003"
        else "thesis Dominance Addition needs C perfectly equal at one positive level"
    )
    return [*problems, f"{detail} under any split of B union C"]


def _b_splits(bc: Counter[int], size: int, above: int) -> Iterable[Counter[int]]:
    """Every sub-multiset of ``bc`` with ``size`` lives, all strictly above ``above``."""
    levels = sorted(level for level in bc if level > above)

    def walk(index: int, left: int, picked: Counter[int]) -> Iterable[Counter[int]]:
        if left == 0:
            yield Counter(picked)
            return
        if index == len(levels) or left > sum(bc[level] for level in levels[index:]):
            return
        level = levels[index]
        for amount in range(min(bc[level], left) + 1):
            picked[level] = amount
            yield from walk(index + 1, left - amount, picked)
        picked.pop(level, None)

    yield from walk(0, size, Counter())


def _verify_non_elitism(
    left_part: Counter[int],
    right_part: Counter[int],
    background: Counter[int],
    lookup: Mapping[str, int],
    form: str,
    w: Mapping[str, int],
) -> list[str]:
    problems: list[str] = []
    n = w["n"]
    c = _single(left_part)
    if c is None or sum(left_part.values()) != n + 1:
        return ["Non-Elitism needs C = n+1 lives at one level"]
    if len(right_part) != 2:
        return ["Non-Elitism needs A at one level and B at one level"]
    low, high = sorted(right_part)
    if right_part[high] != 1 or right_part[low] != n:
        problems.append("Non-Elitism needs N(A) = 1 at W_x and N(B) = n at W_y")
    if c != high - 1:
        problems.append("Non-Elitism needs C at the level just below A's")
    if high - 1 <= low:
        problems.append("Non-Elitism needs x-1 > y")
    if (
        form == "non-elitism-ranged"
        and background
        and not _levels_in(background, range(low, high + 1))
    ):
        problems.append("ranged Non-Elitism needs D inside R(y, x)")
    expected = {"x": high, "y": low, "n": n}
    if any(lookup.get(key) != value for key, value in expected.items()):
        problems.append(f"Non-Elitism witness lookup {lookup} does not match {expected}")
    return problems


def _gnep_z(
    left_part: Counter[int], right_part: Counter[int], w: Mapping[str, int], ladder: Ladder
) -> int | None:
    """The level z that makes this pair a GNEP instance, first in sorted order, else None."""
    n, u, y = w["n"], w["u"], w["y"]
    for z in sorted(left_part):
        if left_part[z] < 1 or not ladder.has(z + 1) or right_part[z + 1] < 1:
            continue
        high = left_part - Counter({z: 1})
        low = right_part - Counter({z + 1: 1})
        x = _single(high)
        if x is None or x < u or sum(high.values()) != n:
            continue
        if sum(low.values()) != n or not _levels_in(low, ladder.range(1, y)):
            continue
        return z
    return None


def _verify_gnep(
    left_part: Counter[int],
    right_part: Counter[int],
    lookup: Mapping[str, int],
    w: Mapping[str, int],
    ladder: Ladder,
) -> list[str]:
    z = _gnep_z(left_part, right_part, w, ladder)
    if z is None:
        return ["no z makes this pair a GNEP instance"]
    expected = {"z": z, "u": w["u"], "y": w["y"], "n": w["n"]}
    if any(lookup.get(key) != value for key, value in expected.items()):
        return [f"GNEP witness lookup {lookup} does not match the decomposition {expected}"]
    return []


def _verify_vrc(
    left_part: Counter[int],
    right_part: Counter[int],
    background: Counter[int],
    lookup: Mapping[str, int],
    w: Mapping[str, int],
    ladder: Ladder,
) -> list[str]:
    problems: list[str] = []
    if background:
        problems.append("VRC avoidance has no background")
    z = _single(left_part)
    if z is None or sum(left_part.values()) != w["n"] or z < w["u"]:
        problems.append("VRC avoidance needs A = n lives at one level z >= u")
        return problems
    negative = Counter({w["x"]: w["m"]})
    if right_part[w["x"]] != w["m"] or negative - right_part:
        problems.append("VRC avoidance needs C = m lives at the negative level W_x")
        return problems
    low = right_part - negative
    if not low or not _levels_in(low, ladder.range(1, w["y"])):
        problems.append("VRC avoidance needs a nonempty B inside R(1, y)")
    expected = {k: w[k] for k in ("x", "u", "v", "y", "n", "m")}
    if any(lookup.get(key) != value for key, value in expected.items()):
        problems.append(f"VRC witness lookup {lookup} does not match {expected}")
    return problems


def _verify_beta_delta(
    form: str,
    left_part: Counter[int],
    right_part: Counter[int],
    lookup: Mapping[str, int],
    w: Mapping[str, int],
    ladder: Ladder,
) -> list[str]:
    """Replay Condition beta or Condition delta when one is serialized explicitly."""
    problems: list[str] = []
    if form.startswith("condition-beta"):
        y = _single(left_part)
        if y is None or len(right_part) != 2:
            return ["Condition beta needs C at one middle level against two outer levels"]
        z, x = sorted(right_part)
        if not x > y > z:
            problems.append("Condition beta needs x > y > z")
        if right_part[z] != w.get("mult", 1) * right_part[x] + w["step"]:
            problems.append("Condition beta's m does not match the witness")
        if sum(left_part.values()) != right_part[x] + right_part[z]:
            problems.append("Condition beta needs N(C) = m + n")
    elif form == "condition-delta":
        for z in sorted(left_part):
            if z >= 0:
                continue
            m = left_part[z]
            n = w["n"] + w.get("n_per_m", 0) * (m - 1)
            high = left_part - Counter({z: m})
            low = right_part - Counter({3: m})
            top = _single(high)
            if (
                right_part[3] >= m
                and top is not None
                and top >= w["u"]
                and sum(high.values()) == n
                and sum(low.values()) == n
                and _levels_in(low, ladder.range(1, w["y"]))
            ):
                return []
        problems.append("no negative z makes this pair a Condition delta instance")
    return problems


def audit_is_cheap(instance: Instance, limit: int = 20000) -> bool:
    """Whether the exhaustive small-instance audit stays affordable for this edge.

    ``ladder.audit`` enumerates every sub-bag of the common part, so the cost grows with the
    product of one more than each common count.
    """
    common = Counter(instance.args[0]) & Counter(instance.args[1])
    cost = 1
    for count in common.values():
        cost *= count + 1
        if cost > limit:
            return False
    return True


def state_sequence(steps: Sequence[Instance]) -> list[str]:
    """The named populations the written chain visits, in trace order."""
    if not steps:
        raise ValueError("an empty chain has no states")
    states = [name_of(steps[0].args[0])]
    for instance in steps:
        right = name_of(instance.args[1])
        if right != states[-1]:
            states.append(right)
    return states


def chain_transitivity(states: Sequence[str]) -> list[GroundConstraint]:
    """Only the chain transitivity the written proof uses, never completeness."""
    out: list[GroundConstraint] = []
    seen: set[str] = set()

    def add(left: str, middle: str, right: str) -> None:
        identifier = f"transitivity:{left}:{middle}:{right}"
        if identifier in seen:
            return
        seen.add(identifier)
        out.append(
            ground(
                identifier,
                "transitivity",
                Implies(conjunction(weak(left, middle), weak(middle, right)), weak(left, right)),
                "background.transitivity/v1",
                f"Proof-chain transitivity for {left}, {middle}, {right}.",
            )
        )

    start, first = states[0], states[1]
    for middle, right in zip(states[1:-1], states[2:], strict=True):
        add(start, middle, right)
    for middle, right in zip(states[2:-1], states[3:], strict=True):
        add(first, middle, right)
    add(first, states[-1], start)
    return out


def _decide_mentioned(hard: Sequence[GroundConstraint]) -> str:
    """Z3 over only the weak atoms the constraints mention (the chain has many populations)."""
    import z3  # type: ignore[import-untyped]

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


def compact_closure(steps: Sequence[Instance], formalization_id: str) -> dict[str, Any]:
    """Confirm the edge path, the strict head edge and the closing link entail UNSAT.

    The chain is read in the order the steps are written: each step's right endpoint is the next
    step's left endpoint (or the chain start again), the first step is the single strict edge,
    and the last weak edge returns to the chain start. Transitivity is instantiated only along
    that path; completeness is never asserted.
    """
    names = tuple(dict.fromkeys(name_of(pop) for inst in steps for pop in inst.args))
    states = state_sequence(steps)
    path_ok = states[0] == name_of(steps[0].args[0]) and states[-1] == states[0]
    for index, instance in enumerate(steps[1:], start=1):
        if name_of(instance.args[0]) != states[index]:
            path_ok = False
    shapes = [instance.shape for instance in steps]
    if shapes.count("S") != 1 or shapes[0] != "S":
        path_ok = False
    constraints = core_constraints(list(steps), formalization_id)
    transitivity = chain_transitivity(states)
    hard = [*transitivity, *constraints]
    decision = _decide_mentioned(hard)
    p16_decision = decide_without_completeness(list(steps), formalization_id)
    if decision != p16_decision:
        raise AssertionError(f"closure {decision} disagrees with p16 {p16_decision}")
    dpll, _ = dpll_check([constraint.formula for constraint in hard])
    if dpll != decision:
        raise AssertionError(f"closure {decision} disagrees with DPLL {dpll}")
    return {
        "formalization_id": formalization_id,
        "instances": len(steps),
        "states": len(states),
        "relata": len(names),
        "strict_edges": sum(shape == "S" for shape in shapes),
        "transitivity_constraints": len(transitivity),
        "path_ok": path_ok,
        "decision_without_completeness": decision,
        "completeness_used": False,
        "dpll_decision": dpll,
        "p16_compact_checker_decision": p16_decision,
    }


# ---------------------------------------------------------------------------------------------
# Fixed focus selection for the bounded search.


def _symmetric_distance(left: Pop, right: Pop) -> int:
    a, b = Counter(left), Counter(right)
    return sum((a - b).values()) + sum((b - a).values())


def focus_populations(cap: int, ladder: Ladder = LADDER) -> tuple[Pop, ...]:
    """The fixed focus: the mandatory seeds plus the nearest remaining populations.

    Remaining slots are filled from ``ladder.domain(ladder, MAX_LIVES)`` by (minimum multiset
    symmetric-difference distance to a mandatory seed, size, tuple), so the focus is a
    deterministic function of the cap.
    """
    universe = domain(ladder, MAX_LIVES)
    chosen: list[Pop] = []
    for seed in MANDATORY_SEEDS:
        if seed not in universe:
            raise ValueError(f"mandatory seed {seed} is not a population of the search domain")
        if seed not in chosen:
            chosen.append(seed)
    if len(chosen) > cap:
        raise ValueError(f"cap {cap} is smaller than the {len(chosen)} mandatory seeds")

    def distance(pop: Pop) -> int:
        return min(_symmetric_distance(pop, seed) for seed in MANDATORY_SEEDS)

    for pop in sorted(universe, key=lambda p: (distance(p), len(p), p)):
        if len(chosen) == cap:
            break
        if pop not in chosen:
            chosen.append(pop)
    if len(chosen) != cap:
        raise ValueError(f"domain too small for cap {cap}")
    return tuple(chosen)


def focus_sha256(focus: Sequence[Pop]) -> str:
    payload = json.dumps([list(pop) for pop in focus], separators=(",", ":"))
    return hashlib.sha256(payload.encode()).hexdigest()


# ---------------------------------------------------------------------------------------------
# Research steps. The constructors and searches below are the candidate side; the replay,
# manifest and closure helpers above are the certificate side and never call them.


def _instance_record(instance: Instance) -> dict[str, Any]:
    return {
        "principle": instance.principle,
        "shape": instance.shape,
        "args": [list(population) for population in instance.args],
    }


def _edge_witness(principle: str, left_part: Pop, right_part: Pop) -> dict[str, int]:
    """The source's existential lookup for one recovered decomposition.

    VRC avoidance and the two derived conditions carry their whole family witness; Non-Elitism
    adds the pair (x, y) its instance selects and GNEP adds the level z, so a serialized edge
    records exactly the existential choices that make it applicable.
    """
    families = {
        "non-elitism-ranged": "non-elitism",
        "non-elitism-any": "non-elitism",
        "general-non-extreme-priority": "general-non-extreme-priority",
        "vrc-avoidance": "vrc-avoidance",
        "condition-beta-ranged": "condition-beta",
        "condition-beta-any": "condition-beta",
        "condition-delta": "condition-delta",
    }
    family = families.get(FORM[principle])
    lookup = dict(CONTROL_WITNESS.get(family)) if family is not None else {}
    form = FORM[principle]
    left, right = Counter(left_part), Counter(right_part)
    if form.startswith("non-elitism"):
        c = _single(left)
        if c is not None and len(right) == 2:
            low, high = sorted(right)
            lookup.update({"x": high, "y": low})
    elif form == "general-non-extreme-priority":
        z = _gnep_z(
            left,
            right,
            CONTROL_WITNESS.get("general-non-extreme-priority"),
            LADDER,
        )
        if z is not None:
            lookup["z"] = z
    return lookup


def _edge_for_instance(instance: Instance) -> Edge:
    """Recover one independently replayable decomposition for a generated instance."""
    left, right = (Counter(population) for population in instance.args)
    common = left & right
    items = sorted(common.items())

    def search(index: int, picked: Counter[int]) -> Edge | None:
        if index == len(items):
            left_part = tuple(sorted((left - picked).elements()))
            right_part = tuple(sorted((right - picked).elements()))
            edge = Edge(
                instance.principle,
                left_part,
                right_part,
                tuple(sorted(picked.elements())),
                _edge_witness(instance.principle, left_part, right_part),
            )
            return edge if not verify_edge(edge.record()) else None
        level, count = items[index]
        for amount in range(count + 1):
            picked[level] = amount
            found = search(index + 1, picked)
            if found is not None:
                return found
        picked.pop(level, None)
        return None

    found = search(0, Counter())
    if found is None:
        raise AssertionError(f"could not recover replay decomposition for {instance}")
    return found


def _expected_formula(instance: Instance) -> Any:
    left, right = (name_of(population) for population in instance.args[:2])
    if instance.shape == "S":
        return strict(left, right)
    if instance.shape == "W":
        return weak(left, right)
    if instance.shape == "N":
        return Not(strict(left, right))
    raise AssertionError(f"unexpected candidate shape {instance.shape!r}")


def _assert_audited_formula(instance: Instance) -> None:
    if not audit(instance, LADDER, CONTROL_WITNESS):
        raise AssertionError(f"ladder audit rejected {instance}")
    if formula_of(instance) != _expected_formula(instance):
        raise AssertionError(f"formula mismatch for {instance}")


def _core_result(
    instances: Sequence[Instance],
    engine: Engine,
    mus: Sequence[str],
    *,
    decision: str,
) -> dict[str, Any]:
    constraints = {
        constraint.id: constraint for constraint in core_constraints(list(instances), "p18-refine")
    }
    chosen: list[Instance] = []
    for identifier in mus:
        constraint = constraints.get(identifier)
        if constraint is None:
            raise AssertionError(f"MUS id {identifier!r} is not a primitive instance")
        index = int(identifier.rsplit(":", 1)[1])
        chosen.append(instances[index])
    for instance in chosen:
        _assert_audited_formula(instance)
    replay: list[dict[str, Any]] = []
    for instance in chosen:
        edge = _edge_for_instance(instance)
        serialized = edge.record()
        problems = verify_edge(serialized)
        if problems:
            raise AssertionError(f"replay rejected MUS edge: {problems}")
        replay.append(serialized)
    # Re-confirm the core against the same background that made it conflict, over the engine's
    # own relata. Full transitivity is a background axiom here; completeness never enters.
    recheck_engine = Engine(
        engine.relata,
        engine.hard,
        soft=core_constraints(chosen, "p18-refine-confirmed"),
        timeout_ms=60000,
    )
    recheck = recheck_engine.check(list(recheck_engine.soft))
    if recheck.decision != "unsat":
        raise AssertionError(f"refined MUS did not recheck UNSAT: {recheck}")
    return {
        "decision": decision,
        "mus": list(mus),
        "instances": [_instance_record(instance) for instance in chosen],
        "replay": {"verified": len(replay), "failures": [], "edges": replay},
        "recheck": recheck.decision,
    }


def _fixed_atom_constraints(
    names: Sequence[str], assignment: Mapping[Any, bool], tag: str
) -> list[GroundConstraint]:
    return [
        ground(
            f"{tag}:{left}:{right}",
            tag,
            weak(left, right) if assignment[weak(left, right)] else Not(weak(left, right)),
            "p18-focus-extension/v1",
            f"Cap-32 assignment fixes weak({left}, {right}) to {assignment[weak(left, right)]}.",
        )
        for left in names
        for right in names
    ]


def _variant_instances(
    pops: Sequence[Pop], ne: str, da: str
) -> tuple[tuple[str, ...], list[Instance]]:
    principles = (ED, GNEP, VRC, ne, da)
    all_instances = instances_over(pops, LADDER, CONTROL_WITNESS, principles)
    return principles, all_instances


def _cycles_for(instances: Sequence[Instance]) -> list[dict[str, Any]]:
    words = cycle_words((instance for instance in instances if instance.shape in {"W", "S"}), 8)
    cycles: list[dict[str, Any]] = []
    for word in words:
        for instance in word.example:
            _assert_audited_formula(instance)
        cycles.append(
            {
                "word": list(word.word),
                "instances": [_instance_record(instance) for instance in word.example],
            }
        )
    return cycles


def _lost_edge(ne: str) -> str | None:
    return (
        "negative-background derived beta not available from ranged NE" if ne == NE_THESIS else None
    )


def _changed_da(da: str) -> str | None:
    return (
        "source DA edge is absent: its positive addition is mixed, whereas thesis DA requires equal "
        "added lives; applicable thesis DA clauses are N-shaped, not reverse weak edges"
        if da == DA_THESIS
        else None
    )


def control_edges() -> list[Edge]:
    """The 42 primitive edges of the original-theorem control, in downhill trace order."""

    def pop(counts: Counter[int]) -> Pop:
        return tuple(sorted(counts.elements()))

    edges: list[Edge] = [
        Edge(ED, (5,), (4,)),
        Edge(
            VRC,
            (4,),
            _pop(((3, 40), (-1, 1))),
            witness={"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
        ),
    ]

    def alpha_block(count: int, high: int, low_count: int, negative: bool) -> list[Edge]:
        initial = Counter({high: count, 1: low_count})
        if negative:
            initial[-1] = 1
        block: list[Edge] = []
        for index in range(count, 0, -1):
            previous = Counter(initial)
            reduction = index - 1
            previous[high] -= reduction
            previous[high - 1] += 2 * reduction
            previous[1] -= reduction
            right_part = Counter({high: 1, 1: 1})
            background_counts = previous - right_part
            edge = Edge(
                NE_2003,
                pop(Counter({high - 1: 2})),
                pop(right_part),
                pop(background_counts),
                witness={"x": high, "y": 1, "n": 1},
            )
            assert Counter(edge.left) == previous - right_part + Counter({high - 1: 2})
            assert Counter(edge.right) == previous
            block.append(edge)
        return block

    # Emit each alpha block from M_k to M_0: the right endpoint is the next lower M.
    edges.extend(alpha_block(20, 4, 20, True))
    edges.extend(alpha_block(10, 5, 30, True))
    edges.extend(alpha_block(5, 6, 35, True))

    for index in range(1, 5):
        background_counts = Counter({6: 5 - index, 1: 34 + index})
        z = -1 + index - 1
        edges.append(
            Edge(
                GNEP,
                pop(Counter({6: 1, z: 1})),
                pop(Counter([1, z + 1])),
                pop(background_counts),
                witness={"z": z, "u": 4, "y": 3, "n": 1},
            )
        )

    edges.append(Edge(DA_2003, pop(Counter({6: 1, 1: 39, 3: 1})), (5,)))
    assert len(edges) == 42
    assert Counter(edge.principle for edge in edges) == Counter(
        {ED: 1, DA_2003: 1, VRC: 1, NE_2003: 35, GNEP: 4}
    )
    assert all(not verify_edge(edge.record()) for edge in edges)
    assert all(
        edge.right == following.left
        for edge, following in zip(edges, [*edges[1:], edges[0]], strict=True)
    )
    return edges


def bounded_search(cap: int) -> dict[str, Any]:
    """One focus cap of the discriminating bounded search."""
    pops = focus_populations(cap)
    focus = [list(population) for population in pops]
    names = tuple(name_of(population) for population in pops)
    bg = background(names)
    instances = instances_over(pops, LADDER, CONTROL_WITNESS, SEVEN)
    audit_failures = [
        _instance_record(instance)
        for instance in instances
        if not audit(instance, LADDER, CONTROL_WITNESS)
    ]
    per_principle = {
        principle: sum(instance.principle == principle for instance in instances)
        for principle in SEVEN
    }
    shape_counts = {
        shape: sum(instance.shape == shape for instance in instances) for shape in ("S", "W", "N")
    }
    variants: dict[str, dict[str, Any]] = {}
    for label, ne, da in VARIANTS:
        principles, insts = _variant_instances(pops, ne, da)
        hard = [
            *bg["reflexivity"],
            *bg["transitivity"],
            *core_constraints(insts, "p18-vrc-focused/v1"),
        ]
        result = Engine(names, hard, timeout_ms=60000).check()
        cycle_instances = [instance for instance in insts if instance.shape in {"W", "S"}]
        variant_cycles = _cycles_for(insts)
        partial = any(instance.shape == "N" for instance in insts)
        focused = sorted({population for instance in insts for population in instance.args})
        variant: dict[str, Any] = {
            "principles": list(principles),
            "instance_count": len(insts),
            "decision": result.decision,
            "core": list(result.core),
            "shape_counts": {
                shape: sum(instance.shape == shape for instance in insts)
                for shape in ("S", "W", "N")
            },
            "focused_relata": [list(population) for population in focused],
            "cycles_max_8_weak_strict_only": variant_cycles,
            "cycle_scope": (
                "W/S subset only; N-shaped DA excluded"
                if da == DA_THESIS
                else "all source instances on the focus"
            ),
            "lost_source_proof_edge": _lost_edge(ne),
            "changed_source_proof_da": _changed_da(da),
            "cycles": {
                "partial": partial,
                "reason": (
                    "N-shaped instances are excluded from the W/S cycle scan"
                    if partial
                    else "W/S scan is complete for this variant"
                ),
                "max_len": 8,
            },
        }
        if result.decision == "unknown":
            variant["reason"] = result.reason
        variants[label] = variant
        assert all(audit(instance, LADDER, CONTROL_WITNESS) for instance in cycle_instances)
    partial = any(instance.shape == "N" for instance in instances)
    return {
        "cap": cap,
        "focus": focus,
        "focus_sha256": focus_sha256(pops),
        "instances": len(instances),
        "per_principle": per_principle,
        "shape_counts": shape_counts,
        "instances_audited": not audit_failures,
        "audit_failures": audit_failures,
        "coverage": {principle: per_principle[principle] > 0 for principle in SEVEN},
        "variants": variants,
        "cycles": {
            "partial": partial,
            "reason": (
                "the seven-principle scan includes N-shaped thesis Dominance Addition instances"
                if partial
                else "all generated instances have W/S shapes"
            ),
            "max_len": 8,
        },
    }


def refine_candidates(searches: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    """Counterexample-guided refinement of the explicit candidates the search reports."""
    by_cap: dict[int, Mapping[str, Any]] = {}
    for index, search in enumerate(searches):
        cap_value = search.get("cap", CAPS[index] if index < len(CAPS) else None)
        if cap_value is None:
            raise ValueError("each search must identify its focus cap")
        by_cap[int(cap_value)] = search

    cores: dict[int, dict[str, Any]] = {}
    extensions: dict[int, dict[str, Any]] = {}
    candidates: list[dict[str, Any]] = []
    notes: list[str] = []

    for cap, search in by_cap.items():
        pops = tuple(tuple(int(level) for level in population) for population in search["focus"])
        names = tuple(name_of(population) for population in pops)
        variant_cores: dict[str, Any] = {}
        variant_extensions: dict[str, Any] = {}
        for label, ne, da in VARIANTS:
            payload = search["variants"][label]
            principles, insts = _variant_instances(pops, ne, da)
            decision = payload["decision"]
            if decision == "unsat":
                bg = background(names)
                soft = core_constraints(insts, f"p18-refine/{cap}/{label}")
                engine = Engine(
                    names,
                    [*bg["reflexivity"], *bg["transitivity"]],
                    soft=soft,
                    timeout_ms=60000,
                )
                mus = engine.shrink(sorted(engine.soft))
                variant_cores[label] = _core_result(insts, engine, mus, decision=decision)
            elif decision == "sat" and cap == CAPS[0]:
                cap64 = CAPS[-1]
                search64 = by_cap.get(cap64)
                if search64 is None:
                    notes.append(f"{label}: cap-{cap64} search unavailable")
                    continue
                pops64 = tuple(
                    tuple(int(level) for level in population) for population in search64["focus"]
                )
                names64 = tuple(name_of(population) for population in pops64)
                _, insts64 = _variant_instances(pops64, ne, da)
                bg32 = background(names)
                soft32 = core_constraints(insts, f"p18-refine-32/{label}")
                engine32 = Engine(
                    names,
                    [*bg32["reflexivity"], *bg32["transitivity"]],
                    soft=soft32,
                    timeout_ms=60000,
                )
                check32 = engine32.check(sorted(engine32.soft))
                if check32.decision != "sat" or check32.assignment is None:
                    raise AssertionError(f"cap-{cap} payload said SAT but replay was {check32}")
                bg64 = background(names64)
                soft64 = core_constraints(insts64, f"p18-refine-64/{label}")
                engine64 = Engine(
                    names64,
                    [*bg64["reflexivity"], *bg64["transitivity"]],
                    soft=soft64,
                    timeout_ms=60000,
                )
                extra = [
                    engine64.w(left, right) == check32.assignment[weak(left, right)]
                    for left in names
                    for right in names
                ]
                extension_check = engine64.check(sorted(engine64.soft), extra=extra)
                extension: dict[str, Any] = {"decision": extension_check.decision}
                # Retain the exact finite preorder whose extension is being tested;
                # SAT solvers may choose a different cap-32 model on another run.
                extension["fixed_assignment_rows"] = [
                    "".join(
                        "1" if check32.assignment[weak(left, right)] else "0" for right in names
                    )
                    for left in names
                ]
                extension["assignment_order"] = "search focus order, row and column"
                if extension_check.decision == "unknown":
                    extension["reason"] = extension_check.reason
                    variant_extensions[label] = extension
                    notes.append(f"{label}: cap-64 extension returned unknown")
                    continue
                if extension_check.decision == "sat":
                    if extension_check.assignment is None:
                        raise AssertionError("SAT extension omitted its preorder assignment")
                    incomparable = sum(
                        not extension_check.assignment[weak(left, right)]
                        and not extension_check.assignment[weak(right, left)]
                        for index, left in enumerate(names64)
                        for right in names64[index + 1 :]
                    )
                    extension.update(
                        {
                            "finite": True,
                            "relata": len(names64),
                            "incomparable_pairs": incomparable,
                        }
                    )
                    variant_extensions[label] = extension
                    candidates.append(
                        {
                            "cap": cap,
                            "cap_extension": cap64,
                            "variant": label,
                            "kind": "finite-preorder",
                            "incomparable_pairs": incomparable,
                        }
                    )
                    continue

                fixed = _fixed_atom_constraints(names, check32.assignment, f"cap-{cap}:{label}")
                conflict_engine = Engine(
                    names64,
                    [*bg64["reflexivity"], *bg64["transitivity"], *fixed],
                    soft=soft64,
                    timeout_ms=60000,
                )
                conflict_check = conflict_engine.check(sorted(conflict_engine.soft))
                if conflict_check.decision != "unsat":
                    raise AssertionError(
                        f"extension changed decision from UNSAT to {conflict_check.decision}"
                    )
                conflict_mus = conflict_engine.shrink(sorted(conflict_engine.soft))
                extension["core"] = _core_result(
                    insts64, conflict_engine, conflict_mus, decision=conflict_check.decision
                )
                variant_extensions[label] = extension
            elif decision == "unknown":
                notes.append(f"{label}: cap-{cap} search returned unknown")
        if variant_cores:
            cores[cap] = variant_cores
        if variant_extensions:
            extensions[cap] = variant_extensions

    return {
        "cores": cores,
        "extensions": extensions,
        "candidates": candidates,
        "notes": notes,
    }


# ---------------------------------------------------------------------------------------------
# Sections and report.


EXPECTED_CONTROL_CENSUS = Counter({NE_2003: 35, GNEP: 4, ED: 1, DA_2003: 1, VRC: 1})


def control_targets(edges: Sequence[Edge]) -> dict[str, Any]:
    """Recover the plan's outer targets from the trace and audit them as source instances.

    The trace order is [Egalitarian Dominance, VRC avoidance, the Non-Elitism run realizing
    Condition beta, the GNEP run realizing Condition delta, Dominance Addition]. The runs must
    be contiguous, their shared endpoint must be one population, and each realized condition
    must pass the independent ladder audit as a source instance under the control witness. The
    two derived conditions are therefore targets of the trace, never serialized premises.
    """
    from research.ladder import delta_n, larger

    census = Counter(edge.principle for edge in edges)
    if census != EXPECTED_CONTROL_CENSUS:
        raise AssertionError(f"control census {dict(census)} is not {EXPECTED_CONTROL_CENSUS}")
    if [edge.principle for edge in edges[:2]] != [ED, VRC] or edges[-1].principle != DA_2003:
        raise AssertionError("trace order must be ED, VRC, the beta run, the delta run, DA")
    beta, delta = list(edges[2:37]), list(edges[37:41])
    if {edge.principle for edge in beta} != {NE_2003}:
        raise AssertionError("the beta run must be exactly the 35 Non-Elitism edges")
    if {edge.principle for edge in delta} != {GNEP}:
        raise AssertionError("the delta run must be exactly the four GNEP edges")

    beta_top, beta_bottom = beta[0].left, beta[-1].right
    delta_top, delta_bottom = delta[0].left, delta[-1].right
    if beta_bottom != delta_top:
        raise AssertionError("the delta run must start where the beta run ends")
    if edges[1].right != beta_top or edges[-1].left != delta_bottom:
        raise AssertionError("the outer edges must meet the runs they realize")
    if beta_top != _plus((3,) * 40, (-1,)) or beta_bottom != _plus((6,) * 5, (1,) * 35, (-1,)):
        raise AssertionError("the realized Condition beta endpoints are not the source's")
    if delta_bottom != _plus((6,), (1,) * 39, (3,)):
        raise AssertionError("the realized Condition delta endpoints are not the source's")
    if edges[0].left != (5,) or edges[0].right != (4,) or edges[-1].right != (5,):
        raise AssertionError("the strict Egalitarian Dominance link does not close the cycle")
    if edges[1].left != (4,):
        raise AssertionError("VRC avoidance must close onto the strict link's worse side")

    beta_instance = Instance(BETA, (beta_top, beta_bottom))
    delta_instance = Instance(DELTA, (delta_top, delta_bottom))
    if not audit(beta_instance, LADDER, CONTROL_WITNESS):
        raise AssertionError("the realized Condition beta target is not a source instance")
    if not audit(delta_instance, LADDER, CONTROL_WITNESS):
        raise AssertionError("the realized Condition delta target is not a source instance")
    return {
        "egalitarian_dominance": {"better": list(edges[0].left), "worse": list(edges[0].right)},
        "dominance_addition": {"left": list(edges[-1].left), "right": list(edges[-1].right)},
        "vrc_avoidance": {"left": list(edges[1].left), "right": list(edges[1].right)},
        "beta": {
            "left": list(beta_top),
            "right": list(beta_bottom),
            "applications": len(beta),
            "n": 5,
            "m": larger(CONTROL_WITNESS.get("condition-beta"), 5),
            "audited": True,
        },
        "delta": {
            "left": list(delta_top),
            "right": list(delta_bottom),
            "applications": len(delta),
            "m": 1,
            "n": delta_n(CONTROL_WITNESS.get("condition-delta"), 1),
            "audited": True,
        },
        "recorded_realizations": ["non-elitism-to-beta", "gnep-to-delta"],
    }


def control_section() -> dict[str, Any]:
    edges = control_edges()
    records = [edge.record() for edge in edges]
    failures: list[dict[str, Any]] = []
    for index, serialized in enumerate(records):
        problems = verify_edge(serialized)
        if problems:
            failures.append({"index": index, "problems": problems, "record": serialized})
    if failures:
        raise AssertionError(f"control replay failed: {failures[:3]}")
    if Counter(edge.principle for edge in edges) != EXPECTED_CONTROL_CENSUS:
        raise AssertionError("control census drifted from the plan's 35 Non-Elitism and four GNEP")
    targets = control_targets(edges)
    instances = [edge.instance for edge in edges]
    by_principle = Counter(edge.principle for edge in edges)
    shapes = Counter(edge.shape for edge in edges)
    audited, skipped = 0, 0
    for instance in instances:
        if audit_is_cheap(instance):
            if not audit(instance, LADDER, CONTROL_WITNESS):
                raise AssertionError(f"ladder audit rejected {instance}")
            audited += 1
        else:
            skipped += 1
    closure = compact_closure(instances, "p18-vrc-control/v1")
    if closure["decision_without_completeness"] != "unsat" or not closure["path_ok"]:
        raise AssertionError(f"control closure is not an UNSAT path: {closure}")
    populations = [list(pop) for pop in dict.fromkeys(edge.left for edge in edges)]
    return {
        "scope": (
            "one chosen-witness finite instance set: the original 2003 Lemma 3 chain with the "
            "derived beta and delta edges replaced by their primitive expansions"
        ),
        "edges": len(edges),
        "per_principle": dict(sorted(by_principle.items())),
        "shape_counts": {shape: shapes.get(shape, 0) for shape in ("S", "W", "N")},
        "populations": len(populations),
        "replay": {"verified": len(records), "failures": []},
        "ladder_audit": {
            "audited": audited,
            "skipped_large_background": skipped,
            "witness": {family: dict(params) for family, params in CONTROL_WITNESS.params.items()},
        },
        "closure": closure,
        "targets": targets,
        "serialized": records,
    }


def derived_section() -> dict[str, Any]:
    derived = check(THEOREM_2003)
    return {
        "label": "separately labeled derived control: the published beta/delta proof",
        "kind": "derived premises (Conditions beta and delta), not primitive source instances",
        "statement": THEOREM_2003.statement,
        "decision_without_completeness": derived["decision_without_completeness"],
        "audit": all(derived["audit"].values()),
        "drop_one_principle": derived["drop_one_principle"],
        "cli_decision": derived["cli_decision"],
        "cli_verify_accepted": derived["cli_verify_accepted"],
    }


def search_section(cap: int) -> dict[str, Any]:
    run = bounded_search(cap)
    required = (
        "focus",
        "focus_sha256",
        "instances",
        "per_principle",
        "shape_counts",
        "instances_audited",
        "coverage",
        "variants",
        "cycles",
    )
    missing = [key for key in required if key not in run]
    if missing:
        raise AssertionError(f"cap {cap} search result lacks {missing}")
    if not all(run["coverage"][p] for p in (ED, GNEP, VRC, NE_2003, NE_THESIS, DA_2003, DA_THESIS)):
        raise AssertionError(f"cap {cap} focus does not cover every principle: {run['coverage']}")
    return run


def refinement_section(searches: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    return refine_candidates(searches)


# Findings of the independent source audit, recorded with the result. None of them changes an
# edge: the control's instances are nonempty, use the 2003 Non-Elitism background that is
# unrestricted, and take witness values the source leaves existential.
FIDELITY_NOTES: tuple[str, ...] = (
    "The exact Egalitarian Dominance and both Dominance Addition statements quantify over "
    "equal-sized populations without a positive-size condition, so requiring nonempty A, B and C "
    "is the ladder encoding's convention, which only drops instances, not the text's.",
    "Condition beta's displayed statement quantifies over any D, but the Lemma 1.1 and Lemma 1.2 "
    "proofs assemble only E inside R(y, x) and R(z, y+1) respectively; the paper's own Lemma 3 "
    "applies beta with the negative D2, which only the displayed statement licenses. This is the "
    "same boundary that ranged Non-Elitism cannot cross.",
    "The control's numbers are chosen-witness consequences, not source-forced values: four GNEP "
    "applications with n_i = 1 give delta's n = 4 at z = -1, m = 1, and the greedy "
    "m_i = f(m_{i-1}) = 5, 10, 20 give 35 Non-Elitism applications with m = 35 > 5 = n.",
    "Lemma 1.2's strictness assertion needs r >= 2, since the stated inequalities allow equality "
    "at r = 1; the control uses r = 3.",
)


def run() -> dict[str, Any]:
    control = control_section()
    derived = derived_section()
    searches = [search_section(cap) for cap in CAPS]
    refinement = refinement_section(searches)
    return {
        "scope": (
            "Q-011 pass: one chosen-witness primitive control of the original 2003 theorem, an "
            "independent replay of every edge, and a two-cap discriminating search on a fixed "
            "32/64-population focus with at most three lives per relatum. No unrestricted "
            "consistency or impossibility claim is made."
        ),
        "fidelity_notes": list(FIDELITY_NOTES),
        "ladder": list(LADDER.levels),
        "max_lives": MAX_LIVES,
        "caps": list(CAPS),
        "mandatory_seeds": [list(seed) for seed in MANDATORY_SEEDS],
        "manifest": {
            principle: {
                "reading": entry.reading,
                "work": entry.work,
                "page": entry.page,
                "quantifiers": entry.quantifiers,
                "background": entry.background,
                "levels": entry.levels,
                "emptiness": entry.emptiness,
                "chain": entry.chain,
                "note": entry.note,
            }
            for principle, entry in SOURCE_MANIFEST.items()
        },
        "control": control,
        "derived_control": derived,
        "search": searches,
        "refinement": refinement,
    }


def _summary(data: Mapping[str, Any]) -> str:
    control = data["control"]
    refinement = data["refinement"]
    variants = {
        run["cap"]: {label: payload["decision"] for label, payload in run["variants"].items()}
        for run in data["search"]
    }
    return json.dumps(
        {
            "control_edges": control["edges"],
            "control_per_principle": control["per_principle"],
            "control_shapes": control["shape_counts"],
            "control_closure": control["closure"]["decision_without_completeness"],
            "control_replay_failures": len(control["replay"]["failures"]),
            "control_targets_audited": sorted(
                name
                for name, payload in control["targets"].items()
                if isinstance(payload, dict) and payload.get("audited")
            ),
            "derived_control": data["derived_control"]["decision_without_completeness"],
            "search_variants": variants,
            "extension_decisions": {
                cap: {label: payload["decision"] for label, payload in run.items()}
                for cap, run in refinement["extensions"].items()
            },
            "minimal_cores": {str(cap): sorted(run) for cap, run in refinement["cores"].items()},
            "finite_candidates": len(refinement["candidates"]),
            "refinement_notes": list(refinement["notes"]),
        },
        sort_keys=True,
    )


def main() -> None:
    started = time.monotonic()
    data = run()
    path = write_result(
        "p18_vrc_certificate", data, {"wall_time_s": round(time.monotonic() - started, 1)}
    )
    closure = data["control"]["closure"]
    record(
        [
            LedgerEntry(
                candidate_id="P18-vrc-primitive-control-and-bounded-search",
                hypothesis=(
                    "The original 2003 VRC theorem has a primitive chosen-witness control with "
                    "35 Non-Elitism and four GNEP applications, and the three weakened variants "
                    "have no contradiction at the fixed witness on the 32- and 64-population foci."
                ),
                motivation=(
                    "Replace P17's derived beta/delta control with a primitive one, then use it "
                    "to calibrate a bounded discriminating search over the Q-011 weakenings."
                ),
                exact_formal_change=(
                    "research/p18_vrc_certificate.py: primitive Lemma 1.1/1.2 and 5.2.1/5.2.2 "
                    "expansions at the p17 SOURCE_WITNESS, with seven-principle instance "
                    "generation on a fixed 32/64-population focus."
                ),
                scope=data["scope"],
                search_method=(
                    "serialized-decomposition replay plus exhaustive ladder audit, compact "
                    "mentioned-atom transitivity closure without completeness, and Z3 per "
                    "variant with W/S cycle replay"
                ),
                result=_summary(data),
                evidence_type=(
                    "chosen-witness primitive control with independent replay; bounded finite "
                    "search; separately labeled derived control"
                ),
                checked=closure["decision_without_completeness"] == "unsat",
                minimal="control is not claimed minimal; UNSAT cores, where found, are shrunk",
                interpretation=(
                    "A bounded SAT table and an absent cycle are not consistency evidence. No "
                    "source-general witness construction and no full finite-ladder model is "
                    "discharged here, so Q-011 stays open."
                ),
                next_experiment=(
                    "parameterize the primitive control over arbitrary n(x, y) and "
                    "(u(z), y(z), n(z)) with a witness-dependency DAG, or build a "
                    "background-sensitive model class"
                ),
                result_scope=(
                    "finite selected-witness control and bounded two-cap search; not the "
                    "unrestricted conditions"
                ),
                formalization_tier=(
                    "agent-cross-read source principles, thesis Lemma 5.2 chain, fixed ladder "
                    "W_-1..W_6"
                ),
                witness_conditions=(
                    "NE n=1; GNEP (u=4, y=3, n=1) at every z; VRC (x=-1, u=4, v=6, y=3, n=1, "
                    "m=1); the derived delta witness n=4 and beta witness m=35 at n=5"
                ),
                novelty_status="not-applicable (bounded selected-witness control and diagnostic)",
                status="open",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            )
        ]
    )
    print(json.dumps(data, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
