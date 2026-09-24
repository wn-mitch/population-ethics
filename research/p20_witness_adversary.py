"""Phase 20, route A: an adversarial existential-witness stress test for Q-011.

Q-011 asks whether the 2003 VRC impossibility theorem survives weakening Non-Elitism to the
thesis's ranged background (``D subset R(y, x)``), Dominance Addition to the thesis's not-worse,
single-level-``C`` form, or both.  Phase 19 attacked the question through the *derived* Conditions
beta and delta: the repaired chain closes only at derived witnesses, and arbitrary source-order
witnesses are obstructed either by a count identity that is unsatisfiable over the integers or by
a level bound no source condition supplies.

This module is route A *independently of that template*.  It uses primitive instances only -
Egalitarian Dominance, ranged/unrestricted Non-Elitism, the General Non-Extreme Priority
Condition, VRC avoidance and both Dominance Addition forms - and it treats the existential
witnesses of those conditions as an adversary.

The object of study is a **bare cycle**: a cyclic sequence of populations ``v_0 ... v_m`` with one
Egalitarian Dominance edge (shape S) and weak edges (shape W) on the rest, closed by a chord that
is either weak (completing the ``>=`` cycle) or the thesis not-worse Dominance Addition (shape N,
contradicting the strict relation the weak path already derives).  A bare cycle refutes a weakened
set only when its instances exist:

* the source quantifies the witnesses as it states them - Non-Elitism picks ``n`` for each level
  pair, GNEP picks ``u(z), y(z), n(z)`` for each ``z``, VRC avoidance picks one tuple - so a
  refutation must instantiate the cycle for *every* legal witness assignment.  A single legal
  witness under which no instantiation exists defeats the cycle;
* the background and "splat" populations are the refuter's own choice.

Grammar (``MAX_PATH``, ``MAX_ATOMS``, ``VARIANTS``).  ``enumerate_variant`` enumerates bare cycles
over the declared primitive templates:

* the Egalitarian Dominance edge is placed first (a rotation of the cycle, losing no generality);
* the weak path after it is an ordered product of length ``t <= MAX_PATH`` drawn from the variant's
  weak templates.  Repetition is allowed, so the Non-Elitism and GNEP amplification chains are
  represented;
* the chord is any weak template, or the thesis Dominance Addition where the variant uses it.

Every population carries at most ``MAX_ATOMS`` distinct welfare levels and every count is positive.
The existential counts of Non-Elitism and GNEP are *fresh per application*: the source keys them by
level pair and by ``z``, so distinct applications may take independent values and the adversary may
set them independently.  VRC avoidance keeps one shared tuple, as the source quantifies it once.
``Builder(shared=True)`` instead pins one value per template, which is the restriction the finite
ladder encoding in ``research.ladder.Witness`` imposes; the run reports both readings as a control.

Witness bookkeeping.  Because the enumeration gives every repeated application a fresh level pair or
``z``, the witness assignments it ranges over are a superset of the source's (the source additionally
requires applications at the same level value to share their witness).  A ``dead`` verdict is
therefore sound for the source order - no instance in the larger set means none in the source set -
while a ``blocked`` or ``live`` verdict would additionally need the keying to be enforced; the
concrete adversary certificates are constant witness functions and so are legal source witnesses.

Verdicts.  With ``I(W)`` the statement "some instantiation of this cycle exists at witness W", and
"legal W" the witness assignments satisfying the source's own side conditions,

* ``dead``    - ``not I(W)`` for every legal ``W``: the cycle cannot be instantiated at all;
* ``blocked`` - ``I(W)`` for some legal ``W`` but not for all; an explicit legal ``W`` with
  ``not I(W)`` is returned and independently replayed;
* ``live``    - ``I(W)`` for every legal ``W``: the cycle is a source-general refutation of the
  weakened set, and the module replays a concrete contradictory ground instance.

All counting and level constraints are decided by Z3 over linear integer arithmetic (the
"constraint" solver).  The combinatorial wiring - which atom is which, which template is where -
is enumerated separately in Python (the "map" solver), so neither solver decides the other's
question.  Every finite claim is replayed through ``research.ladder.audit`` and
``research.lab.Engine``; ``structure_checks`` re-derives the counting facts that explain the
outcome directly from the fits.

Result.  Every cycle in the declared grammar is ``dead``, in both witness readings.  Three
symbolically verified facts explain it: Non-Elitism (both forms) and GNEP preserve the total number
of lives, the Dominance Addition chords require the closing node to carry at least one life more
than the Egalitarian Dominance node, and VRC avoidance's high side is a single level.  So the path
must gain lives through VRC avoidance and then carry VRC's negative lives up to the closing node,
lifted above the Egalitarian Dominance level; no bounded combination of the templates does that.
This is a scoped obstruction, not a consistency proof, and it does not exclude longer primitive
expansions - see ``run()["remaining_obligation"]``.
"""

from __future__ import annotations

import itertools
import json
import time
from collections.abc import Callable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any

import z3  # type: ignore[import-untyped]
from z3.z3util import get_vars  # type: ignore[import-untyped]

from research.lab import Engine, background, dpll_check
from research.ladder import Ladder, Witness, audit
from research.p6_schema import core_constraints, name_of
from research.p8_catalogue import LADDER, THEOREM_2003
from research.p8_catalogue import WITNESS as FROZEN_WITNESS
from research.p17_vrc_boundary import (
    DA_2003,
    DA_THESIS,
    ED,
    GNEP,
    NE_2003,
    NE_THESIS,
    VRC,
)
from research.schema import Instance, Pop

# ---------------------------------------------------------------------------------------------
# Declared grammar bounds.

MAX_PATH = 3  # weak edges on the path after the Egalitarian Dominance edge
MAX_ATOMS = 4  # distinct welfare levels per population
MAX_MOTIFS = 20000  # budget per variant (the enumerations below stay far inside it)

VARIANTS: dict[str, tuple[tuple[str, ...], bool]] = {
    # label -> (weak templates allowed, whether thesis not-worse Dominance Addition is available)
    "ranged-ne+2003-da": ((NE_THESIS, GNEP, VRC, DA_2003), False),
    "2003-ne+not-worse-da": ((NE_2003, GNEP, VRC), True),
    "both-weakened": ((NE_THESIS, GNEP, VRC), True),
}


# ---------------------------------------------------------------------------------------------
# Section 1: symbolic layer.  A bag is a multiset of (level, count) atoms whose levels and counts
# are Z3 integer expressions.  Level keys are (base, offset) pairs, so the two offsets the source
# produces (Non-Elitism's ``x-1`` and GNEP's ``z+1``) keep a stable identity.

Key = tuple[str, int]
Bag = tuple[tuple[str, Key, "z3.ArithRef"], ...]  # (canonical key text, key, count expression)
# (principle, left node, right node, witness parameters) for one edge of a bare cycle.
Edge = tuple[str, Bag, Bag, Mapping[str, Mapping[str, Any]]]
# One step of the grammar enumeration: node bags, edges, instantiation and legality constraints.
State = tuple[tuple[Bag, ...], tuple[Edge, ...], tuple[Any, ...], tuple[Any, ...]]


def lvl_expr(key: Key) -> z3.ArithRef:
    base, off = key
    e = z3.Int("L_" + base)
    return e + off if off else e


def key_text(key: Key) -> str:
    base, off = key
    return f"{base}{off:+d}" if off else base


def bag(*atoms: tuple[Key, Any]) -> Bag:
    """Multiset over levels; atoms at one level merge by summing their counts."""
    merged: dict[str, tuple[Key, Any]] = {}
    for key, count in atoms:
        text = key_text(key)
        if text in merged:
            merged[text] = (key, merged[text][1] + count)
        else:
            merged[text] = (key, count)
    return tuple((text, key, count) for text, (key, count) in merged.items())


def bag_keys(a: Bag) -> frozenset[str]:
    return frozenset(text for text, _, _ in a)


def bag_eq_constraints(a: Bag, b: Bag) -> list[z3.BoolRef] | None:
    """Constraints making two bags the same multiset, or None when their levels differ."""
    if bag_keys(a) != bag_keys(b):
        return None
    da = {text: count for text, _, count in a}
    db = {text: count for text, _, count in b}
    return [da[text] == db[text] for text in da]


def bag_total(a: Bag) -> z3.ArithRef:
    total = z3.IntVal(0)
    for _, _, count in a:
        total = total + count
    return total


def bag_repr(a: Bag) -> dict[str, str]:
    return {text: str(count) for text, _, count in sorted(a)}


class Builder:
    """Allocates fresh levels, the refuter's counts, and the witness parameters of one sketch."""

    def __init__(self, label: str, shared: bool = False) -> None:
        self.label = label
        self.shared = shared
        self.index = 0
        self.levels: dict[str, Any] = {}
        self.ours: list[Any] = []
        self.theirs: list[Any] = []
        self.witness: dict[str, Any] = {}

    def level(self) -> Key:
        name = f"l{self.index}"
        self.index += 1
        self.levels[name] = z3.Int("L_" + name)
        self.ours.append(self.levels[name])
        return (name, 0)

    def witness_level(self, name: str) -> Key:
        """A welfare level the adversary chooses (GNEP's ``u(z)``, VRC avoidance's ``W_x``)."""
        base = "w_" + name
        if base not in self.levels:
            self.levels[base] = z3.Int("L_" + base)
            self.theirs.append(self.levels[base])
        return (base, 0)

    def count(self) -> Any:
        name = f"c{self.index}"
        self.index += 1
        var = z3.Int("C_" + name)
        self.ours.append(var)
        return var

    def witness_count(self, name: str) -> Any:
        """An existential count the adversary chooses (Non-Elitism's ``n``, VRC's ``n``, ``m``).

        In the ``shared`` mode one value serves every application of a template, which is the
        restriction ``research.ladder.Witness`` imposes; in the default mode each application has
        its own value, as the source's quantifier prefix states.
        """
        if self.shared:
            name = name.rstrip("0123456789").rstrip("_")
        if name not in self.witness:
            self.witness[name] = z3.Int("W_" + self.label + "_" + name)
            self.theirs.append(self.witness[name])
        return self.witness[name]


@dataclass(frozen=True)
class Fit:
    """One way to read a template's left population as the current node."""

    right: Bag
    inst: tuple[Any, ...]  # instantiation constraints (may mention the refuter's variables)
    legal: tuple[Any, ...]  # the source's own constraints on the witness parameters
    witness: Mapping[str, Mapping[str, Any]]


@dataclass
class Sketch:
    """One scored bare cycle."""

    label: str
    seq: tuple[str, ...]
    chord: str
    nodes: tuple[Bag, ...]
    edges: tuple[Edge, ...]
    inst: tuple[Any, ...]
    legal: tuple[Any, ...]
    builder: Builder


# ---------------------------------------------------------------------------------------------
# Section 2: the fits.  Each returns every way a template can have the current node as its *left*
# population, with the resulting right population and both constraint systems.  Side conditions
# are re-derived from the readings (corpus/readings.toml lines 374-389, 513-529, 718-808).


def fit_ed(b: Builder, left: Bag) -> list[Fit]:
    """Egalitarian Dominance: A perfectly equal, N(A) = N(B), every B life below W_x.  Shape S."""
    if len(left) != 1:
        return []
    _, akey, size = left[0]
    out = []
    for shape in (1, 2):
        keys = [b.level() for _ in range(shape)]
        if shape == 1:
            counts = [size]
        else:
            split = b.count()
            counts = [split, size - split]
        right = bag(*[(k, c) for k, c in zip(keys, counts, strict=True)])
        inst = [lvl_expr(k) < lvl_expr(akey) for k in keys]
        inst += [c >= 1 for c in counts]
        out.append(Fit(right, tuple(inst), (), {}))
    return out


def fit_ne(b: Builder, left: Bag, principle: str) -> list[Fit]:
    """Non-Elitism: C (n+1 lives at W_{x-1}) with background D is at least as good as A (one life
    at W_x) plus B (n lives at W_y); x-1 > y; D subset R(y, x) in the thesis form, any D in 2003."""
    out = []
    for i, (_, key, count) in enumerate(left):
        n = b.witness_count("ne_n" if b.shared else f"ne_n_{b.index}")
        b.index += 1
        x: Key = (key[0], key[1] + 1)
        y = b.level()
        rest = [(k, c) for j, (_, k, c) in enumerate(left) if j != i]
        right = bag(*rest, (x, z3.IntVal(1)), (y, n))
        inst = [count == n + 1, lvl_expr(x) > lvl_expr(y)]
        legal: list[Any] = [n >= 1]
        if principle == NE_THESIS:
            for k, _ in rest:
                inst.append(lvl_expr(k) >= lvl_expr(y))
                inst.append(lvl_expr(k) <= lvl_expr(x))
        out.append(
            Fit(
                right,
                tuple(inst),
                tuple(legal),
                {"non-elitism": {"n": n}},
            )
        )
    return out


def fit_gnep(b: Builder, left: Bag) -> list[Fit]:
    """GNEP: A (n lives at W_x) plus C (one life at W_z) is at least as good as B (n lives in
    R(1, y(z))) plus D (one life at W_{z+1}); x >= u(z), u > y >= 3; background E arbitrary."""
    out = []
    for i, (_, kz, cz) in enumerate(left):
        if not (z3.is_int_value(cz) and cz.as_long() == 1):
            continue
        for j, (_, ka, na) in enumerate(left):
            if j == i:
                continue
            rest = [(k, c) for m, (_, k, c) in enumerate(left) if m not in (i, j)]
            tag = "" if b.shared else f"_{b.index}"
            u = b.witness_count(f"gn_u{tag}")
            y = b.witness_count(f"gn_y{tag}")
            ng = b.witness_count(f"gn_n{tag}")
            b.index += 1
            kb = b.level()
            right = bag(*rest, (kb, na), ((kz[0], kz[1] + 1), z3.IntVal(1)))
            inst = [
                lvl_expr(ka) >= u,
                lvl_expr(kz) >= u,
                lvl_expr(kb) >= 1,
                lvl_expr(kb) <= y,
                na == ng,
            ]
            legal = [u >= 4, y >= 3, u > y, ng >= 1]
            out.append(
                Fit(
                    right,
                    tuple(inst),
                    tuple(legal),
                    {"general-non-extreme-priority": {"u": u, "y": y, "n": ng}},
                )
            )
    return out


def fit_vrc(b: Builder, left: Bag, splat: int) -> list[Fit]:
    """VRC avoidance: A (n lives at one level z >= u) is at least as good as B (any population in
    R(1, y)) together with C (m lives at the negative level W_x).  One tuple, quantified once."""
    if len(left) != 1:
        return []
    _, kz, ncount = left[0]
    u = b.witness_count("vr_u")
    y = b.witness_count("vr_y")
    n = b.witness_count("vr_n")
    m = b.witness_count("vr_m")
    x = b.witness_level("vr_x")
    atoms: list[tuple[Key, Any]] = [(x, m)]
    inst = [lvl_expr(kz) >= u, ncount == n]
    for _ in range(splat):
        kb = b.level()
        cb = b.count()
        atoms.append((kb, cb))
        inst += [lvl_expr(kb) >= 1, lvl_expr(kb) <= y, cb >= 1]
    legal = [u >= 4, y >= 3, u > y, lvl_expr(x) < 0, n >= 1, m >= 1]
    return [
        Fit(
            bag(*atoms),
            tuple(inst),
            tuple(legal),
            {"vrc-avoidance": {"x": x, "u": u, "v": u + 2, "y": y, "n": n, "m": m}},
        )
    ]


def fit_da_weak(b: Builder, left: Bag) -> list[Fit]:
    """2003 Dominance Addition: A below a threshold, B at or above it, N(A) = N(B), C positive;
    B union C is at least as good as A.  Shape W."""
    out = []
    for mask in range(1, 2 ** len(left)):
        bkeys = [(k, c) for i, (_, k, c) in enumerate(left) if mask >> i & 1]
        ckeys = [(k, c) for i, (_, k, c) in enumerate(left) if not (mask >> i & 1)]
        if not bkeys or not ckeys:
            continue
        total = z3.IntVal(0)
        for _, c in bkeys:
            total = total + c
        for shape in (1, 2):
            keys = [b.level() for _ in range(shape)]
            if shape == 1:
                counts = [total]
            else:
                split = b.count()
                counts = [split, total - split]
            right = bag(*[(k, c) for k, c in zip(keys, counts, strict=True)])
            inst = [c >= 1 for _, c in ckeys]
            inst += [lvl_expr(k) >= 1 for k, _ in ckeys]
            inst += [counts[0] >= 1] if shape == 1 else [c >= 1 for c in counts]
            for k, _ in bkeys:
                inst += [lvl_expr(a) < lvl_expr(k) for a in keys]
            out.append(Fit(right, tuple(inst), (), {}))
    return out


def fit_da_thesis(b: Builder, left: Bag) -> list[Fit]:
    """Thesis Dominance Addition: A below a threshold, B at or above it, N(A) = N(B), C one
    positive level; not(A better than B union C).  Shape N."""
    out = []
    total = bag_total(left)
    for shape in (1, 2):
        keys = [b.level() for _ in range(shape)]
        if shape == 1:
            counts = [total]
        else:
            split = b.count()
            counts = [split, total - split]
        kc = b.level()
        cc = b.count()
        right = bag(*[(k, c) for k, c in zip(keys, counts, strict=True)], (kc, cc))
        inst = [lvl_expr(kc) >= 1, cc >= 1]
        inst += [counts[0] >= 1] if shape == 1 else [c >= 1 for c in counts]
        for _, k, _ in left:
            inst += [lvl_expr(k) < lvl_expr(bk) for bk in keys]
        out.append(Fit(right, tuple(inst), (), {}))
    return out


def grow(b: Builder, node: Bag, principle: str) -> list[Fit]:
    if principle in (NE_2003, NE_THESIS):
        return fit_ne(b, node, principle)
    if principle == GNEP:
        return fit_gnep(b, node)
    if principle == VRC:
        return [f for i in (0, 1, 2) for f in fit_vrc(b, node, i)]
    if principle == DA_2003:
        return fit_da_weak(b, node)
    if principle == DA_THESIS:
        return fit_da_thesis(b, node)
    raise ValueError(f"unknown principle {principle!r}")


def fit_da_weak_chord(left: Bag, a_bag: Bag) -> list[Fit]:
    """2003 Dominance Addition as the closing chord: its A is exactly ``a_bag``.

    ``left = B union C`` with every B level above every A level and C positive; N(A) = N(B).
    """
    out = []
    for mask in range(1, 2 ** len(left)):
        bkeys = [(k, c) for i, (_, k, c) in enumerate(left) if mask >> i & 1]
        ckeys = [(k, c) for i, (_, k, c) in enumerate(left) if not (mask >> i & 1)]
        if not bkeys or not ckeys:
            continue
        total = z3.IntVal(0)
        for _, c in bkeys:
            total = total + c
        cons = [total == bag_total(a_bag)]
        for k, _ in bkeys:
            for _, ka, _ in a_bag:
                cons.append(lvl_expr(ka) < lvl_expr(k))
        for k, c in ckeys:
            cons.append(lvl_expr(k) >= 1)
            cons.append(c >= 1)
        out.append(Fit(a_bag, tuple(cons), (), {}))
    return out


def fit_da_thesis_chord(start: Bag, last: Bag) -> list[Fit]:
    """Thesis Dominance Addition as the closing chord: left = A is exactly ``start``, and the
    right node ``last`` splits into B (at or above A) and C (one positive level); not(A > B u C)."""
    out = []
    for i, (_, kc, cc) in enumerate(last):
        bkeys = [(k, c) for j, (_, k, c) in enumerate(last) if j != i]
        if not bkeys:
            continue
        cons = [balance(bkeys) == bag_total(start), lvl_expr(kc) >= 1, cc >= 1]
        for _, k, _ in start:
            for k2, _ in bkeys:
                cons.append(lvl_expr(k) < lvl_expr(k2))
        cons += [c >= 1 for _, c in bkeys]
        out.append(Fit(last, tuple(cons), (), {}))
    return out


def balance(atoms: Sequence[tuple[Key, Any]]) -> z3.ArithRef:
    total = z3.IntVal(0)
    for _, c in atoms:
        total = total + c
    return total


def close_cycle(b: Builder, last: Bag, start: Bag, chord: str) -> Iterator[Fit]:
    """Every way ``chord`` closes the cycle with left population ``last`` and right ``start``."""
    if chord == DA_THESIS:
        # the not-worse chord: left = A is the *start* node, right = B union C is the last node.
        yield from fit_da_thesis_chord(start, last)
        return
    if chord == DA_2003:
        # Dominance Addition closes the cycle as B union C = last is at least as good as A = start.
        yield from fit_da_weak_chord(last, start)
        return
    if chord in (NE_2003, NE_THESIS):
        fits = fit_ne(b, last, chord)
    elif chord == GNEP:
        fits = fit_gnep(b, last)
    elif chord == VRC:
        fits = [f for i in (0, 1, 2) for f in fit_vrc(b, last, i)]
    else:
        raise ValueError(f"unknown chord {chord!r}")
    for f in fits:
        eq = bag_eq_constraints(f.right, start)
        if eq is not None:
            yield f


# ---------------------------------------------------------------------------------------------
# Section 3: grammar enumeration (the "map" solver).  Only wiring is enumerated here.


def enumerate_variant(
    label: str,
    weak: tuple[str, ...],
    not_worse: bool,
    shared: bool = False,
    max_atoms: int = MAX_ATOMS,
    only: Sequence[tuple[str, ...]] | None = None,
) -> list[Sketch]:
    sketches: list[Sketch] = []
    words: list[tuple[tuple[str, ...], str]] = []
    seqs: Sequence[tuple[str, ...]] = (
        list(only)
        if only is not None
        else [
            s for length in range(0, MAX_PATH + 1) for s in itertools.product(weak, repeat=length)
        ]
    )
    for seq in seqs:
        chords = list(weak)
        if not_worse and DA_THESIS not in seq:
            chords.append(DA_THESIS)
        for chord in chords:
            words.append((seq, chord))
    for seq, chord in words:
        if len(sketches) >= MAX_MOTIFS:
            break
        builder = Builder(f"{label}#{len(sketches)}", shared)
        start = bag((builder.level(), builder.count()))
        for ed_fit in fit_ed(builder, start):
            states: list[State] = [
                (
                    (start, ed_fit.right),
                    ((ED, start, ed_fit.right, {}),),
                    tuple(ed_fit.inst),
                    tuple(ed_fit.legal),
                )
            ]
            for principle in seq:
                nxt: list[State] = []
                for nodes, edges, inst, legal in states:
                    for f in grow(builder, nodes[-1], principle):
                        if len(f.right) > max_atoms:
                            continue
                        nxt.append(
                            (
                                nodes + (f.right,),
                                edges + ((principle, nodes[-1], f.right, f.witness),),
                                inst + f.inst,
                                legal + f.legal,
                            )
                        )
                states = nxt
                if not states:
                    break
            for nodes, edges, inst, legal in states:
                for f in close_cycle(builder, nodes[-1], nodes[0], chord):
                    if len(f.right) > max_atoms:
                        continue
                    closes = chord == DA_THESIS
                    edge = (
                        chord,
                        nodes[0] if closes else nodes[-1],
                        nodes[-1] if closes else nodes[0],
                        f.witness,
                    )
                    positive = tuple(c >= 1 for node in nodes for _, _, c in node)
                    sketches.append(
                        Sketch(
                            builder.label,
                            seq,
                            chord,
                            nodes,
                            edges + (edge,),
                            inst + f.inst + positive,
                            legal + f.legal,
                            builder,
                        )
                    )
    return sketches


# ---------------------------------------------------------------------------------------------
# Section 4: verdicts (the "constraint" solver).


@dataclass
class Verdict:
    kind: str  # dead | blocked | live | conditional
    instantiable: str
    blocking_witness_exists: str
    adversary: dict[str, int] = field(default_factory=dict)
    adversary_replay: str = ""
    ground: str = ""


def _solver(timeout_ms: int = 30000) -> z3.Solver:
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)
    return solver


def decide(sketch: Sketch) -> Verdict:
    ours = list(sketch.builder.ours)
    inst = list(sketch.inst)
    legal = list(sketch.legal)

    s_inst = _solver()
    s_inst.add(*inst, *legal)
    instantiable = str(s_inst.check())

    s_block = _solver()
    if ours:
        s_block.add(z3.ForAll(ours, z3.Not(z3.And(*inst))))
    s_block.add(*legal)
    blocking = s_block.check()

    verdict = Verdict("dead", instantiable, str(blocking))
    if instantiable != "sat":
        return verdict
    # Instantiation alone is not a refutation: the ground instance must also be inconsistent.
    replayed = replay_sketch(sketch)
    verdict.ground = replayed.get("ground", {}).get("decision_without_completeness", "n/a")
    if not replayed.get("instantiated") or verdict.ground != "unsat":
        verdict.kind = "conditional"
        return verdict
    if blocking == z3.unsat:
        verdict.kind = "live"
        return verdict
    if blocking != z3.sat:
        verdict.kind = "conditional"
        return verdict
    verdict.kind = "blocked"
    model = s_block.model()
    values: dict[str, int] = {}
    substitution = []
    for name, var in sketch.builder.witness.items():
        value = model.eval(var, model_completion=True)
        if z3.is_int_value(value):
            values[name] = value.as_long()
            substitution.append(var == z3.IntVal(value.as_long()))
    for name, key in sketch.builder.levels.items():
        if key not in sketch.builder.theirs:
            continue
        value = model.eval(key, model_completion=True)
        if z3.is_int_value(value):
            values["level:" + name] = value.as_long()
            substitution.append(key == z3.IntVal(value.as_long()))
    verdict.adversary = values
    replay = _solver()
    replay.add(*inst, *legal, *substitution)
    verdict.adversary_replay = str(replay.check())
    return verdict


# ---------------------------------------------------------------------------------------------
# Section 5: finite replay through ``research.ladder.audit`` and ``research.lab.Engine``.


def instantiate(
    sketch: Sketch, ladder: Ladder = LADDER
) -> tuple[list[Pop], list[Instance], list[Witness]] | None:
    """Solve for a concrete model with every level on ``ladder``."""
    solver = _solver(60000)
    solver.add(*sketch.inst, *sketch.legal)
    lo, hi = min(ladder.levels), max(ladder.levels)
    level_exprs = {text: lvl_expr(key) for node in sketch.nodes for text, key, _ in node}
    for expr in level_exprs.values():
        solver.add(expr >= lo, expr <= hi)
    if solver.check() != z3.sat:
        return None
    model = solver.model()

    def value(expr: Any) -> z3.ArithRef:
        return model.eval(expr, model_completion=True)

    pops: list[Pop] = []
    for node in sketch.nodes:
        levels: list[int] = []
        for _, key, count in node:
            c = value(count).as_long()
            if c < 1:
                return None
            levels += [value(lvl_expr(key)).as_long()] * c
        pops.append(tuple(sorted(levels)))

    index = {node: i for i, node in enumerate(sketch.nodes)}
    instances, witnesses = [], []
    for principle, left, right, wit_exprs in sketch.edges:
        if left not in index or right not in index:
            return None
        params: dict[str, dict[str, int]] = {}
        for family, fields in wit_exprs.items():
            resolved = {}
            for name, expr in fields.items():
                v = value(expr)
                if not z3.is_int_value(v):
                    return None
                resolved[name] = v.as_long()
            params[family] = resolved
        instances.append(Instance(principle, (pops[index[left]], pops[index[right]])))
        witnesses.append(Witness(params))
    return pops, instances, witnesses


def ground_decision(instances: Sequence[Instance], tag: str) -> dict[str, Any]:
    names = tuple(dict.fromkeys(name_of(p) for inst in instances for p in inst.args))
    bg = background(names)
    constraints = core_constraints(list(instances), tag)
    hard = [*bg["reflexivity"], *bg["transitivity"], *constraints]
    engine = Engine(names, hard, timeout_ms=60000)
    decision = engine.check().decision
    dpll, _ = dpll_check([c.formula for c in hard])
    return {"decision_without_completeness": decision, "dpll": dpll, "relata": len(names)}


def replay_sketch(sketch: Sketch, ladder: Ladder = LADDER) -> dict[str, Any]:
    """Audit every edge as its own source instance, then decide the ground set."""
    found = instantiate(sketch, ladder)
    if found is None:
        return {"instantiated": False, "ladder": list(ladder.levels)}
    pops, instances, witnesses = found
    audits = []
    for inst, wit in zip(instances, witnesses, strict=True):
        problems: list[str] = []
        try:
            ok = audit(inst, ladder, wit)
        except ValueError as error:
            ok = False
            problems.append(str(error))
        audits.append(
            {
                "principle": inst.principle,
                "shape": inst.shape,
                "left": list(inst.args[0]),
                "right": list(inst.args[1]),
                "witness": {family: dict(values) for family, values in wit.params.items()},
                "audit": ok,
                "problems": problems,
            }
        )
    return {
        "instantiated": True,
        "ladder": list(ladder.levels),
        "populations": [list(p) for p in pops],
        "edges": audits,
        "all_audited": all(entry["audit"] for entry in audits),
        "ground": ground_decision(instances, f"p20-{sketch.label}"),
    }


# ---------------------------------------------------------------------------------------------
# Section 6: the candidate cycle, the adversary's witness choice, and the report.

CANDIDATE = ((NE_THESIS, NE_THESIS), DA_2003)

# The adversary's concrete witness choice: the least legal witness function of every template.
# It is a total witness assignment (each template gets one value at every key it is used at).
MINIMAL_WITNESS: tuple[tuple[str, int], ...] = (
    ("ne_n", 1),
    ("gn_u", 4),
    ("gn_y", 3),
    ("gn_n", 1),
    ("vr_n", 1),
    ("vr_m", 1),
    ("vr_u", 4),
    ("vr_y", 3),
    ("vr_x", -1),
)


def witness_value(name: str) -> int:
    """The adversary's value for a witness parameter, matched by its declared prefix."""
    for prefix, value in MINIMAL_WITNESS:
        if name.startswith(prefix):
            return value
    raise KeyError(name)


def witness_substitution(builder: Builder) -> tuple[list[Any], dict[str, int]]:
    """Pin every witness parameter (and witness level) to the adversary's concrete choice."""
    substitution: list[Any] = []
    values: dict[str, int] = {}
    for name, var in builder.witness.items():
        value = witness_value(name)
        values[name] = value
        substitution.append(var == z3.IntVal(value))
    for name, var in builder.levels.items():
        if name.startswith("w_"):
            value = witness_value(name[2:])
            values["level:" + name] = value
            substitution.append(var == z3.IntVal(value))
    return substitution, values


def dead_certificate(sketch: Sketch) -> dict[str, Any]:
    """Replay the adversary's concrete witness choice against one dead cycle."""
    substitution, values = witness_substitution(sketch.builder)
    solver = _solver()
    solver.add(*sketch.inst, *sketch.legal, *substitution)
    return {"witness": values, "instantiable_at_witness": str(solver.check())}


def witness_sweep(variant: str = "ranged-ne+2003-da", shared: bool = False) -> dict[str, Any]:
    """Challenge the candidate with legal, fast-growing witness values.

    The candidate is the two-application Non-Elitism telescope closed by 2003 Dominance Addition,
    the shortest primitive amplification the grammar generates.  Its two Non-Elitism witnesses are
    existential and independent under the source order, so the adversary may set them separately;
    the sweep reports for which values an instance still exists.
    """
    weak, not_worse = VARIANTS[variant]
    sketches = enumerate_variant(variant, weak, not_worse, shared=shared)
    picks = [s for s in sketches if s.seq == CANDIDATE[0] and s.chord == CANDIDATE[1]]
    if not picks:
        return {"candidate_found": False}
    sketch = picks[0]
    used = {str(v) for constraint in sketch.inst for v in get_vars(constraint)}
    names = sorted(
        name
        for name, var in sketch.builder.witness.items()
        if name.startswith("ne_n") and str(var) in used
    )
    rows = []
    for n1 in (1, 2, 3, 5):
        for n2 in (1, 2, 4, 8, 16):
            solver = _solver()
            solver.add(*sketch.inst, *sketch.legal)
            if len(names) >= 1:
                solver.add(sketch.builder.witness[names[0]] == n1)
            if len(names) >= 2:
                solver.add(sketch.builder.witness[names[1]] == n2)
            rows.append({"n_first": n1, "n_second": n2, "instantiable": str(solver.check())})
    return {
        "candidate_found": True,
        "mode": "shared" if shared else "source",
        "candidate": {
            "seq": [p.split(":")[1] for p in sketch.seq],
            "chord": sketch.chord.split(":")[1],
            "nodes": [bag_repr(n) for n in sketch.nodes],
        },
        "non_elitism_witnesses_exercised": names,
        "instantiable_values": sum(1 for r in rows if r["instantiable"] == "sat"),
        "blocked_values": sum(1 for r in rows if r["instantiable"] == "unsat"),
        "sweep": rows,
    }


def scan_variant(label: str, shared: bool) -> dict[str, Any]:
    weak, not_worse = VARIANTS[label]
    sketches = enumerate_variant(label, weak, not_worse, shared=shared)
    counts = {"dead": 0, "blocked": 0, "live": 0, "conditional": 0}
    blocked_here: list[dict[str, Any]] = []
    live_here: list[dict[str, Any]] = []
    replay_ok = {"instantiated": 0, "audited": 0, "unsat_ground": 0}
    for sketch in sketches:
        verdict = decide(sketch)
        counts[verdict.kind] += 1
        entry = {
            "seq": [p.split(":")[1] for p in sketch.seq],
            "chord": sketch.chord.split(":")[1],
            "nodes": [bag_repr(n) for n in sketch.nodes],
            "adversary": verdict.adversary,
            "adversary_replay": verdict.adversary_replay,
        }
        if verdict.kind == "blocked":
            blocked_here.append(entry)
        elif verdict.kind == "live":
            entry["replay"] = replay_sketch(sketch)
            live_here.append(entry)
        if verdict.kind in ("blocked", "live"):
            replayed = replay_sketch(sketch)
            if replayed.get("instantiated"):
                replay_ok["instantiated"] += 1
                replay_ok["audited"] += int(bool(replayed.get("all_audited")))
                replay_ok["unsat_ground"] += int(
                    replayed.get("ground", {}).get("decision_without_completeness") == "unsat"
                )
    sample: list[Sketch] = []
    seen: set[Any] = set()
    for candidate in sketches:
        if not candidate.builder.witness:
            continue
        key = (
            candidate.seq,
            candidate.chord,
            tuple(tuple(sorted(bag_repr(node).items())) for node in candidate.nodes),
        )
        if key in seen:
            continue
        seen.add(key)
        sample.append(candidate)
        if len(sample) >= 5:
            break
    certificates = [
        {
            "seq": [p.split(":")[1] for p in s.seq],
            "chord": s.chord.split(":")[1],
            "nodes": [bag_repr(node) for node in s.nodes],
            **dead_certificate(s),
            "ladder_replay": replay_sketch(s),
        }
        for s in sample
    ]
    return {
        "sketches": len(sketches),
        "verdicts": counts,
        "blocked": blocked_here[:6],
        "live": live_here[:4],
        "replay": replay_ok,
        "replay_note": (
            "instantiate/audit/Engine replay runs only for blocked or live cycles; dead cycles have "
            "no instance to replay, and their adversary certificates carry a ladder replay attempt"
        ),
        "example_adversary": certificates[0] if certificates else {},
        "adversary_certificates": certificates,
    }


def control_replay() -> dict[str, Any]:
    """Positive control for the audit/Engine replay, run on the frozen 2003 core.

    The core is published-derived material, not a bare cycle of this grammar; it is used only to
    show that ``audit`` accepts each edge as a source instance and that ``ground_decision``
    reproduces the inconsistency the catalogue records.
    """
    instances = THEOREM_2003.instances()
    audits = []
    for inst in instances:
        try:
            ok = audit(inst, LADDER, FROZEN_WITNESS)
        except ValueError:
            ok = False
        audits.append({"principle": inst.principle, "shape": inst.shape, "audit": ok})
    return {
        "instances": len(instances),
        "all_audited": all(entry["audit"] for entry in audits),
        "ground": ground_decision(instances, "p20-control/frozen-2003"),
    }


def amplification_probe(max_k: int = 4, max_atoms: int = 5) -> dict[str, Any]:
    """Lengthen the amplification deliberately, with a relaxed atom cap.

    The shortest primitive amplification is a chain of Non-Elitism applications.  The probe builds
    every ordering of one VRC-avoidance edge with ``k`` Non-Elitism edges (and, where the variant
    allows it, the mixed GNEP variants), closed by a Dominance Addition chord, for ``k`` up to
    ``max_k``, and reports how many instantiations exist.  Its cap and its word list are stated so
    the result is not read as a general bound.
    """
    out: dict[str, Any] = {"max_k": max_k, "max_atoms": max_atoms, "chains": {}}
    for label, (weak, not_worse) in VARIANTS.items():
        template = NE_THESIS if label != "2003-ne+not-worse-da" else NE_2003
        for k in range(0, max_k + 1):
            words = set(itertools.permutations((VRC, *((template,) * k))))
            sketches = enumerate_variant(
                label, weak, not_worse, max_atoms=max_atoms, only=sorted(words)
            )
            instantiable = 0
            for sketch in sketches:
                solver = _solver()
                solver.add(*sketch.inst, *sketch.legal)
                if solver.check() == z3.sat:
                    instantiable += 1
            out["chains"].setdefault(label, []).append(
                {"k": k, "cycles": len(sketches), "instantiable": instantiable}
            )
    return out


def self_test() -> dict[str, Any]:
    """Exercise the replay pipeline on a degenerate single-edge sketch.

    A lone Egalitarian Dominance edge is instantiable and auditable but not contradictory, so it
    must be reported ``conditional``, not ``live``: instantiability alone is never a refutation.
    """
    builder = Builder("self-test")
    start = bag((builder.level(), builder.count()))
    fit = fit_ed(builder, start)[0]
    positive = tuple(c >= 1 for node in (start, fit.right) for _, _, c in node)
    sketch = Sketch(
        builder.label,
        (),
        ED,
        (start, fit.right),
        ((ED, start, fit.right, {}),),
        tuple(fit.inst) + positive,
        tuple(fit.legal),
        builder,
    )
    verdict = decide(sketch)
    return {
        "kind": verdict.kind,
        "ground": verdict.ground,
        "replay": replay_sketch(sketch),
    }


def structure_checks() -> dict[str, Any]:
    """Symbolically verify the counting facts that explain the grammar's verdicts.

    Each check asks Z3 whether the *negation* of a claimed invariant is satisfiable together with
    one template's constraints; ``unsat`` means the invariant holds for every instance.
    """
    out: dict[str, Any] = {}
    makers: tuple[tuple[str, Callable[[Builder, Bag], list[Fit]]], ...] = (
        ("non-elitism", lambda b, node: fit_ne(b, node, NE_THESIS)),
        ("non-elitism-2003", lambda b, node: fit_ne(b, node, NE_2003)),
        ("gnep", lambda b, node: fit_gnep(b, node)),
    )
    for name, maker in makers:
        b = Builder("struct-" + name)
        node = (
            bag((b.level(), b.count()), (b.level(), b.count()))
            if name != "gnep"
            else bag((b.level(), b.count()), (b.level(), z3.IntVal(1)))
        )
        results = []
        for f in maker(b, node):
            solver = _solver()
            solver.add(*f.inst, *f.legal, bag_total(f.right) != bag_total(node))
            results.append(str(solver.check()))
        out[f"{name}_preserves_total_size"] = sorted(set(results))

    # Both Dominance Addition chords need the closing node to carry at least one extra life.
    b = Builder("struct-chord")
    start = bag((b.level(), b.count()))
    last = bag((b.level(), b.count()), (b.level(), b.count()))
    results = []
    for f in list(fit_da_weak_chord(last, start)) + list(fit_da_thesis_chord(start, last)):
        solver = _solver()
        solver.add(*f.inst, *f.legal, bag_total(last) < bag_total(start) + 1)
        results.append(str(solver.check()))
    out["dominance_addition_chord_needs_growth"] = sorted(set(results))

    # VRC avoidance's high side is a single level, so a non-uniform node can never be its left.
    b = Builder("struct-vrc")
    node = bag((b.level(), b.count()), (b.level(), b.count()))
    out["vrc_left_requires_single_level"] = len(fit_vrc(b, node, 0)) == 0
    return out


def run() -> dict[str, Any]:
    started = time.monotonic()
    source_mode: dict[str, Any] = {}
    shared_mode: dict[str, Any] = {}
    for label in VARIANTS:
        source_mode[label] = scan_variant(label, shared=False)
        shared_mode[label] = scan_variant(label, shared=True)
    totals = {"dead": 0, "blocked": 0, "live": 0, "conditional": 0}
    for entry in source_mode.values():
        for key in totals:
            totals[key] += entry["verdicts"][key]
    shared_totals = {"dead": 0, "blocked": 0, "live": 0, "conditional": 0}
    for entry in shared_mode.values():
        for key in shared_totals:
            shared_totals[key] += entry["verdicts"][key]

    candidate_source = witness_sweep("ranged-ne+2003-da", shared=False)
    candidate_shared = witness_sweep("ranged-ne+2003-da", shared=True)

    if totals["live"]:
        verdict_text = "a live motif exists in the declared grammar"
    elif totals["blocked"]:
        verdict_text = (
            "no motif in the declared grammar is a source-general refutation; the surviving cycles "
            "are blocked by the explicit legal witness recorded for each"
        )
    else:
        verdict_text = (
            "no motif in the declared grammar is a source-general refutation: every cycle is dead, "
            "so no legal witness admits an instance"
        )
    return {
        "route": "A",
        "approach": (
            "primitive bare-cycle grammar (Egalitarian Dominance, ranged/unrestricted Non-Elitism, "
            "GNEP, VRC avoidance, both Dominance Addition forms) with the source's existential "
            "witnesses as an adversary; independent of the derived beta/delta template"
        ),
        "scope": (
            f"bare cycles with one Egalitarian Dominance edge, up to {MAX_PATH} weak edges from the "
            f"variant's templates, at most {MAX_ATOMS} levels per population, budget {MAX_MOTIFS} "
            "motifs per variant; the source-order reading gives each Non-Elitism and GNEP "
            "application its own witness (the source keys them by level pair and by z), while the "
            "'shared' reading pins one value per template, which is the restriction the finite "
            f"ladder encoding imposes; finite replays on the ladder {list(LADDER.levels)}"
        ),
        "verdict": verdict_text,
        "evidence": {
            "source_order": {"variants": source_mode, "totals": totals},
            "constant_witness_encoding": {"variants": shared_mode, "totals": shared_totals},
            "candidate_cycle": {
                "definition": "two Non-Elitism applications closed by 2003 Dominance Addition",
                "source_order": candidate_source,
                "constant_witness_encoding": candidate_shared,
            },
            "structural_checks": structure_checks(),
            "amplification_probe": amplification_probe(),
            "control_frozen_2003": control_replay(),
            "self_test": self_test(),
            "adversary_witness_choice": {
                "values": dict(MINIMAL_WITNESS),
                "note": (
                    "each source template receives the least legal value of its witness; every "
                    "dead cycle is infeasible at this choice, which is verified by substitution"
                ),
            },
        },
        "remaining_obligation": (
            "Outside this grammar the question stays open.  Three exclusions matter.  (1) Unbounded "
            "amplification: the published proof uses 35 Non-Elitism and four GNEP applications, and "
            "a bare cycle in this grammar reaches only MAX_PATH weak edges, with the deliberate "
            "probe stopping at four Non-Elitism edges and five atoms per population; so the derived "
            "beta/delta nesting obstructed in phase 19 is not represented here, a longer expansion "
            "may be instantiable, and no bounded grammar settles that.  (2) Identification of "
            "Non-Elitism witnesses across level pairs: the source keys n by its level pair, so a "
            "motif that re-uses one level pair must share n, and this enumeration gives repeated "
            "applications independent levels.  (3) Multi-level backgrounds that mix levels from two "
            "different principles inside one population, and ladders other than the frozen one.  A "
            "positive result needs a parametric construction valid for every legal witness with its "
            "witness dependencies recorded; a negative result needs the same argument over a "
            "strictly larger grammar."
        ),
        "seconds": round(time.monotonic() - started, 3),
    }


def main() -> None:
    data = run()
    print(json.dumps(data, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
