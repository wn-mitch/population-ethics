"""Phase 19: the two universal certificate routes for Q-011's three 2003 weakenings.

Q-011 asks whether the 2003 VRC impossibility theorem survives weakening Non-Elitism to the
thesis's ranged background (D subset R(y, x)) and Dominance Addition to the thesis's not-worse,
single-level-C form. Phase 17 and 18 left the question open with a bounded reading. Phase 19
attacks it on two routes and reports a scoped verdict for each variant:

A. a source-general primitive contradiction, valid for arbitrary source-order witness functions;
B. an explicit background/count-sensitive axiology satisfying every source instance at every
   finite population size on the ladder.

What this phase establishes, and what it does not:

1. **Reading correction (certified).** ``SOURCE_MANIFEST`` in phase 18 records thesis Condition
   beta's background as ``D subset R(z, y+1)`` and annotates ranged Non-Elitism as losing the
   negative background. That is true only at the *published* level choice. The range is closed at
   its lower end, so whenever beta's own low level is negative (``z < 0``) the range
   ``R(z, y+1)`` contains a negative level and a negative background is admissible. The
   ``ranged_beta`` replayer below re-derives this from the serialized decomposition, so the
   single losing edge of the P18 control is a level-choice artefact, not a consequence of the
   weakening. ``verify_beta_ranged`` accepts the repaired instance and rejects it under the
   published levels.

2. **Chain mechanics (certified, fixed witness).** The repaired chain ED, DA, delta, beta, VRC
   closes as an UNSAT written chain with transitivity and reflexivity alone, for *both* Dominance
   Addition forms. In particular the N-shaped (not-worse) thesis Dominance Addition does **not**
   block the closure: the chain's weak edges plus transitivity derive the atom ``P2 >= M1`` that
   the N-edge's ``not(P2 > M1)`` negates. That answers the local obstruction phase 17 recorded
   (thesis DA "gives no reverse weak edge without completeness") - locally true, globally
   irrelevant inside a cycle. ``closure`` exhibits the derivation and the negative control.

3. **Obstruction (certified arithmetic, nested branch).** The repaired chain's nested placement
   cannot be instantiated by any witness family: its shared high lives put delta's A inside beta's
   single A level. Placing delta's A in beta's background instead requires
   ``x_delta <= y_beta + 1 <= y_v + 1`` - a bound
   on the *axiology's* GNEP witness level relative to its own VRC range top, which no source
   condition supplies. The nesting branch is closed by the source's own count identities:
   thesis Lemma 5.2.2 gives ``n_delta = m_delta * n_chi`` with ``n_chi >= 1``, beta's strictly
   growing m with ``m_beta > n_beta``, and the negative lives ``m_delta = m_beta + m_v``, so
   ``n_beta = n_delta + n_v >= n_delta >= m_delta > m_beta > n_beta``. ``nesting_obstruction``
   proves this branch UNSAT over the integers; the independent phase-19 template scan
   (``research/p19_impossibility_ranged_ne.py``) finds the same count tension in 88 templates.
   The bound placement was not instantiated on this phase's frozen ladder; phase 20 exhibits a
   primitive fixed-witness cycle with that placement on W_7.

4. **Model route (no certificate).** ``research/p19_vrc_model.py`` checks six explicit
   count-sensitive total preorders; this phase re-verifies the two decisive counterexamples
   (level-count lexicographic fails Non-Elitism at every (x, y); critical-level total utility
   fails thesis Dominance Addition) with ``ladder.audit``. No candidate satisfies all five
   conditions for all finite sizes, and no candidate's failure proves inconsistency, so route B is
   unresolved rather than refuted.

Scope: route A is unresolved for all three weakenings - the phase delivers a certified reading
correction, a certified closure mechanism and a certified obstruction of the nested placement,
not an impossibility theorem. Route B is unresolved with no certified model. Nothing here is a
consistency or impossibility claim beyond the stated preimage, and no novelty claim is made.
"""

from __future__ import annotations

import itertools
import json
import time
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

import z3  # type: ignore[import-untyped]

from population_ethics.relations import encode_z3
from research.lab import Engine, LedgerEntry, background, dpll_check, record, write_result
from research.ladder import Ladder, Witness, audit
from research.p6_schema import core_constraints, name_of
from research.p8_catalogue import LADDER
from research.p17_vrc_boundary import (
    DA_2003,
    DA_THESIS,
    ED,
    GNEP,
    NE_2003,
    NE_THESIS,
    VRC,
)
from research.p18_vrc_certificate import (
    BETA,
    CONTROL_WITNESS,
    DELTA,
    SEVEN,
    SOURCE_MANIFEST,
    Edge,
    verify_edge,
)
from research.p19_vrc_model_background import run as background_model_run
from research.p19_vrc_translation_invariant import decide as translation_invariant_decide
from research.schema import SHAPE, Instance, Pop

# The three weakened variants plus the original as control, in p17 order.
WEAKENED: tuple[tuple[str, str, str], ...] = (
    ("original", NE_2003, DA_2003),
    ("ranged-ne", NE_THESIS, DA_2003),
    ("not-worse-da", NE_2003, DA_THESIS),
    ("both-weakened", NE_THESIS, DA_THESIS),
)


# ---------------------------------------------------------------------------------------------
# Section 1: the two reading items the weakening argument turns on.


def beta_ranged_range(z: int, y: int, ladder: Ladder = LADDER) -> tuple[int, ...]:
    """Thesis Condition beta's background range R(z, y+1) on the ladder."""
    return ladder.range(z, y + 1)


def verify_beta_ranged(record: Mapping[str, Any], ladder: Ladder = LADDER) -> list[str]:
    """Replay one serialized Condition beta edge against the *thesis* statement.

    The thesis reading of Lemma 5.1 (corpus/readings.toml ``thesis:lemma-5.1``) is the 2003
    statement with ``D subset R(z, y+1)``. The decomposition is recomputed from the serialized
    count vectors and every premise is re-derived from the source text:

    * ``C`` is one level ``y`` with ``N(C) = m + n``,
    * the other side is ``A`` (one level ``x``, ``n`` lives) plus ``B`` (one level ``z``, ``m``),
    * ``x > y > z`` and ``m > n``,
    * the shared background lies inside ``R(z, y+1)``; the lower endpoint ``z`` itself is closed,
      so a negative background is admissible exactly when ``z < 0``.
    """
    problems: list[str] = []
    if record.get("principle") != BETA:
        return ["ranged beta replay requires a Condition beta edge"]
    entry = SOURCE_MANIFEST.get(record.get("principle", ""))
    if entry is None:
        return ["unknown principle"]
    if record.get("shape") != SHAPE[entry.reading]:
        problems.append("shape does not match the reading")
    if record.get("source") != entry.reading or record.get("page") != entry.page:
        problems.append("source reading or page does not match the frozen manifest")

    def counter(key: str) -> Counter[int]:
        return Counter({int(level): int(count) for level, count in record.get(key, [])})

    left, right = counter("left"), counter("right")
    left_part, right_part, shared = (
        counter("left_part"),
        counter("right_part"),
        counter("background"),
    )
    for key in ("left", "right", "left_part", "right_part", "background"):
        pairs = record.get(key, [])
        levels = [int(level) for level, _ in pairs]
        if levels != sorted(set(levels)) or any(int(count) <= 0 for _, count in pairs):
            problems.append(f"{key} must be sorted positive count pairs")
    if any(not ladder.has(level) for level in (*left, *right)):
        problems.append("an endpoint lies outside the ladder")
    if left != shared + left_part or right != shared + right_part:
        problems.append("left/right are not background plus their parts")
    y_levels = sorted(left_part)
    if len(y_levels) != 1:
        return [*problems, "beta needs C at a single level"]
    y = y_levels[0]
    outer = sorted(right_part)
    if len(outer) != 2:
        return [*problems, "beta needs A and B at one level each"]
    z, x = outer
    if not x > y > z:
        problems.append(f"beta needs x > y > z, got x={x}, y={y}, z={z}")
    lookup = record.get("witness", {})
    step = int(lookup.get("step", 0))
    mult = int(lookup.get("mult", 1))
    n, m = right_part[x], right_part[z]
    if m != mult * n + step or step < 1:
        problems.append(f"beta's m={m} is not mult*n+step for n={n}, step={step}")
    if m <= n:
        problems.append("beta needs m > n")
    if sum(left_part.values()) != m + n:
        problems.append("beta needs N(C) = m + n")
    outside = sorted(level for level in shared if level not in beta_ranged_range(z, y, ladder))
    if outside:
        problems.append(f"background levels {outside} lie outside R({z}, {y + 1})")
    return problems


def ranged_background_note(z: int, y: int) -> str:
    """The reading item the phase-18 annotation gets wrong at the published level choice."""
    return (
        f"beta levels (x, y, z) = (*, {y}, {z}): the background range R({z}, {y + 1}) is closed, so "
        + ("a negative level is available" if z < 0 else "no negative level is available")
    )


# ---------------------------------------------------------------------------------------------
# Section 2: a derived-edge chain and its candidate witness dependencies.


@dataclass(frozen=True)
class ChainWitness:
    """Derived β/δ edge parameters for a schematic chain, not primitive source witnesses.

    VRC contributes ``n_v``, ``m_v``, ``u_v``, ``y_v`` and the negative level ``x_v``; δ
    contributes ``u_d``, ``y_d`` and ``n_d`` for (``x_v``, ``m_d``); β contributes ``n_b``
    and ``m_b`` for its level triple. The primitive GNEP→δ count dependency is tested
    separately by ``nesting_obstruction``; ``x_h`` must exceed ``u_v + 1``.
    """

    n_v: int
    m_v: int
    u_v: int
    y_v: int
    x_v: int
    u_d: int
    y_d: int
    n_d: int
    m_d: int
    n_b: int
    m_b: int
    x_h: int

    def problems(self) -> list[str]:
        problems: list[str] = []
        if self.x_v >= 0:
            problems.append("VRC's negative level must be negative")
        if not self.u_v > self.y_v >= 3:
            problems.append("VRC needs u_v > y_v >= 3")
        if not (self.u_d > self.y_d >= 3 and self.x_h >= self.u_d):
            problems.append("delta needs u_d > y_d >= 3 and x_h >= u_d")
        if not self.x_h > self.u_v + 1:
            problems.append("the chain's high level must exceed u_v + 1")
        if min(self.n_v, self.m_v, self.n_d, self.m_d, self.n_b, self.m_b) < 1:
            problems.append("every count must be positive")
        if self.m_b <= self.n_b:
            problems.append("beta needs m > n")
        if self.m_d != self.m_b + self.m_v:
            problems.append("M2's negative lives are beta's B plus beta's background")
        if self.n_b != self.n_d + self.n_v:
            problems.append("the nesting case needs beta's A to hold delta's A and E")
        if not self.y_v > 0:
            problems.append("the VRC-side level is positive")
        return problems

    # -- the four populations the source conditions compare --------------------------------
    @property
    def p1(self) -> Pop:
        return tuple(sorted([self.u_v] * self.n_v))

    @property
    def p2(self) -> Pop:
        return tuple(sorted([self.u_v + 1] * self.n_v))

    @property
    def m1(self) -> Pop:
        """delta's right side: its B (at W_3) and D (at W_3) plus the shared background E."""
        return tuple(sorted([3] * (self.n_d + self.m_d) + [self.x_h] * self.n_v))

    @property
    def m2(self) -> Pop:
        """delta's left side: its A and C plus E; beta's right side: A, B and the background."""
        return tuple(sorted([self.x_h] * (self.n_d + self.n_v) + [self.x_v] * self.m_d))

    @property
    def m3(self) -> Pop:
        """beta's left side: C at the VRC range top plus the background holding VRC's C."""
        return tuple(sorted([self.y_v] * (self.m_b + self.n_b) + [self.x_v] * self.m_v))

    def edges(self, da_form: str) -> list[Edge]:
        """The five written edges, in the chain's order, for one Dominance Addition form."""
        dominance = (
            Edge(DA_2003, self.m1, self.p2)
            if da_form == DA_2003
            else Edge(DA_THESIS, self.p2, self.m1)
        )
        return [
            Edge(ED, self.p2, self.p1),
            dominance,
            Edge(
                DELTA,
                tuple(sorted([self.x_h] * self.n_d + [self.x_v] * self.m_d)),
                tuple(sorted([3] * (self.n_d + self.m_d))),
                tuple(sorted([self.x_h] * self.n_v)),
                witness={"u": self.u_d, "y": self.y_d, "n": self.n_d},
            ),
            Edge(
                BETA,
                tuple(sorted([self.y_v] * (self.m_b + self.n_b))),
                tuple(sorted([self.x_h] * self.n_b + [self.x_v] * self.m_b)),
                tuple(sorted([self.x_v] * self.m_v)),
                witness={"step": self.m_b - self.n_b},
            ),
            Edge(
                VRC,
                self.p1,
                self.m3,
                witness={
                    "x": self.x_v,
                    "u": self.u_v,
                    "v": self.u_v + 2,
                    "y": self.y_v,
                    "n": self.n_v,
                    "m": self.m_v,
                },
            ),
        ]

    def instances(self, da_form: str) -> list[Instance]:
        return [edge.instance for edge in self.edges(da_form)]

    def report(self, da_form: str) -> dict[str, Any]:
        edges = self.edges(da_form)
        # The phase-18 replayer checks each edge's premises against the frozen manifest; the
        # derived conditions must be replayed at *this* chain's witness, not phase 17's.
        witness = Witness(
            {
                "condition-beta": {"step": self.m_b - self.n_b},
                "condition-delta": {"u": self.u_d, "y": self.y_d, "n": self.n_d},
                "vrc-avoidance": {
                    "x": self.x_v,
                    "u": self.u_v,
                    "v": self.u_v + 2,
                    "y": self.y_v,
                    "n": self.n_v,
                    "m": self.m_v,
                },
                "general-non-extreme-priority": {"u": self.u_d, "y": self.y_d, "n": self.n_d},
                "non-elitism": {"n": 1},
            }
        )
        return {
            "witness": {
                key: getattr(self, key)
                for key in (
                    "n_v",
                    "m_v",
                    "u_v",
                    "y_v",
                    "x_v",
                    "u_d",
                    "y_d",
                    "n_d",
                    "m_d",
                    "n_b",
                    "m_b",
                    "x_h",
                )
            },
            "populations": {
                "P1": list(self.p1),
                "P2": list(self.p2),
                "M1": list(self.m1),
                "M2": list(self.m2),
                "M3": list(self.m3),
            },
            "edges": [edge.record() for edge in edges],
            "source_problems": {
                "p18_replay": {
                    edge.principle: problems
                    for edge in edges
                    if (problems := verify_edge(edge.record(), LADDER, witness))
                },
                "ranged_beta_replay": (verify_beta_ranged(edges[3].record())),
            },
            "beta_background_note": ranged_background_note(self.x_v, self.y_v),
            "count_problems": self.problems(),
        }


def ladder_chain() -> ChainWitness:
    """A ladder-sized instantiation whose every edge is a source instance at fixed witnesses."""
    return ChainWitness(
        n_v=1,
        m_v=1,
        u_v=4,
        y_v=3,
        x_v=-1,
        u_d=4,
        y_d=3,
        n_d=1,
        m_d=15,
        n_b=2,
        m_b=14,
        x_h=6,
    )


def audit_cheap(instance: Instance, limit: int = 20000) -> bool:
    """Whether the exhaustive ladder audit stays affordable for this edge (see phase 18)."""
    common = Counter(instance.args[0]) & Counter(instance.args[1])
    cost = 1
    for count in common.values():
        cost *= count + 1
        if cost > limit:
            return False
    return True


# ---------------------------------------------------------------------------------------------
# Section 3: chain mechanics - the written chain closes without completeness, N-shape included.


def cycle_states(witness: ChainWitness) -> list[str]:
    """The logical cycle the written chain closes: P2 > P1 >= M3 >= M2 >= M1, back to P2."""
    names = {
        "P1": name_of(witness.p1),
        "P2": name_of(witness.p2),
        "M1": name_of(witness.m1),
        "M2": name_of(witness.m2),
        "M3": name_of(witness.m3),
    }
    return [names["P2"], names["P1"], names["M3"], names["M2"], names["M1"], names["P2"]]


def _decide_mentioned(hard: Sequence[Any]) -> str:
    """Z3 over only the weak atoms these constraints mention; completeness never enters."""
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


def chain_closure(steps: Sequence[Instance], tag: str, states: Sequence[str]) -> dict[str, Any]:
    """Decide the written chain with reflexivity, the cycle's transitivity, and its own edges.

    The chain is ``P1 < P2 <= M1 <= M2 <= M3 <= P1`` read as the sources state it, i.e. the weak
    edges are oriented ``P1 >= M3``, ``M3 >= M2``, ``M2 >= M1`` and the not-worse Dominance
    Addition edge is ``not(P2 > M1)``. The cycle's own transitivity yields ``P2 >= P1 >= M1``, so
    the N-edge's ``not(P2 > M1)`` forces ``M1 >= P2``; transitivity along ``P1 >= M1 >= P2`` then
    contradicts the strict head edge's ``not(P1 >= P2)``.

    Greedy written-chain checkers read the edges in the order they are listed, so an N-edge whose
    endpoints are not adjacent in that order (here ``P2`` and ``M1``) is not decided by them; the
    closure is therefore stated over the cycle, not over the written path.
    """
    names = tuple(dict.fromkeys(name for name in states))
    hard = [
        *background(names)["reflexivity"],
        *background(names)["transitivity"],
        *core_constraints(list(steps), tag),
    ]
    full = Engine(names, hard, timeout_ms=60000).check()
    if full.decision == "unknown":
        raise RuntimeError(f"closure returned unknown: {full.reason}")
    from research.p18_vrc_certificate import chain_transitivity

    cycle = [
        *chain_transitivity(states),
        *core_constraints(list(steps), f"{tag}/cycle"),
    ]
    compact = _decide_mentioned(cycle)
    dpll, _ = dpll_check([constraint.formula for constraint in cycle])
    if not (full.decision == compact == dpll):
        raise AssertionError(
            f"closure disagrees: full {full.decision}, cycle {compact}, dpll {dpll}"
        )
    return {
        "formalization_id": tag,
        "instances": len(steps),
        "relata": len(names),
        "states": list(states),
        "strict_edges": sum(inst.shape == "S" for inst in steps),
        "shapes": [inst.shape for inst in steps],
        "decision_without_completeness": full.decision,
        "cycle_transitivity_decision": compact,
        "cycle_transitivity_constraints": len(cycle) - len(steps),
        "dpll_decision": dpll,
        "full_transitivity_decision": full.decision,
        "completeness_used": False,
    }


def control_drop_dominance(witness: ChainWitness, da_form: str) -> str:
    """Negative control: without the Dominance Addition link the written chain no longer closes."""
    steps = [inst for inst in witness.instances(da_form) if inst.principle != da_form]
    names = tuple(dict.fromkeys(name for name in cycle_states(witness)))
    hard = [
        *background(names)["reflexivity"],
        *background(names)["transitivity"],
        *core_constraints(steps, "p19-drop-dominance/v1"),
    ]
    return Engine(names, hard, timeout_ms=60000).check().decision


# ---------------------------------------------------------------------------------------------
# Section 4: the obstruction. Two branches, and the arithmetic that closes the first.


def nested_high_levels(witness: ChainWitness) -> int:
    """The high lives shared by delta's A and beta's A in the nesting branch."""
    if witness.n_b != witness.n_d + witness.n_v:
        raise ValueError("this witness is not in the nesting branch")
    return witness.n_b


def beta_background_bound(witness: ChainWitness) -> int:
    """Upper bound beta's *permitted* background range places on delta's A level."""
    return witness.y_v + 1


def nesting_obstruction() -> dict[str, Any]:
    """Prove over the integers that the nesting branch has no source-consistent witness.

    Variables: ``n_v`` (VRC's n), ``m_v`` (VRC's m), ``n_b`` (beta's n), ``m_b`` (beta's m),
    ``n_d`` (delta's n), and ``m_d`` (delta's m). Source-facing constraints:

    * every count positive and ``m_b > n_b`` (beta's "there is m > n" and the readings' sizes);
    * ``m_d = m_b + m_v``: M2's negative lives are beta's B (m_b) plus beta's background D, and
      VRC's C is m_v of them, so delta's C (m_d lives) is exactly their sum;
    * ``n_d >= m_d``: thesis Lemma 5.2.2 gives ``n_d = m_d * n_chi`` for a positive integer
      ``n_chi``. This linear consequence suffices and avoids a bounded nonlinear query;
    * ``n_b = n_d + n_v``: the nesting branch forces beta's A to hold delta's A and E. A delta's A
      lives are at one level >= ``u_d``; they can enter beta's right side only as beta's A (this
      branch; beta's B sits below beta's middle level and beta's background is range-bounded),
      which fixes ``n_b = n_d + n_v``.
    """
    n_v, m_v, n_b, m_b, n_d, m_d = z3.Ints("n_v m_v n_b m_b n_d m_d")
    solver = z3.Solver()
    solver.add(
        n_v >= 1,
        m_v >= 1,
        m_b > n_b,
        n_b >= 1,
        m_d == m_b + m_v,
        n_d >= m_d,
        n_b == n_d + n_v,
    )
    status = solver.check()
    if status != z3.unsat:
        raise AssertionError(f"nesting branch was expected UNSAT, got {status}")
    # The same system without the nesting equation is satisfiable, so the obstruction is exactly
    # the nesting, not a defect of the source constraints.
    relaxed = z3.Solver()
    relaxed.add(
        n_v >= 1,
        m_v >= 1,
        m_b > n_b,
        n_b >= 1,
        m_d == m_b + m_v,
        n_d >= m_d,
    )
    relaxed_status = relaxed.check()
    if relaxed_status != z3.sat:
        raise AssertionError(f"relaxed system should be satisfiable, got {relaxed_status}")
    return {
        "decision": str(status),
        "relaxed_without_nesting": str(relaxed_status),
        "inequality": "n_b = n_d + n_v >= n_d = m_d*n_chi >= m_d = m_b + m_v > m_b > n_b",
        "branch": "beta's A level equals delta's A level (nesting branch)",
        "other_branch": (
            "delta's A lives lie in beta's permitted background, requiring x_d <= y_b + 1 <= "
            "y_v + 1: an upper bound on the axiology's GNEP witness level relative to its own VRC "
            "range top, which no source condition supplies"
        ),
    }


def witness_grid(limit: int = 3) -> list[ChainWitness]:
    """Small count assignments used to exercise the derived chain's mechanics, not source-general witnesses."""
    out: list[ChainWitness] = []
    for n_v, m_v, n_d, m_b, x_h in itertools.product(
        range(1, limit + 1), range(1, limit + 1), range(1, limit + 1), range(2, limit + 3), (6,)
    ):
        n_b = n_d + n_v
        if m_b <= n_b:
            continue
        out.append(
            ChainWitness(
                n_v=n_v,
                m_v=m_v,
                u_v=4,
                y_v=3,
                x_v=-1,
                u_d=4,
                y_d=3,
                n_d=n_d,
                m_d=m_b + m_v,
                n_b=n_b,
                m_b=m_b,
                x_h=x_h,
            )
        )
    return out


# ---------------------------------------------------------------------------------------------
# Section 5: the model route's decisive counterexamples, re-verified here.


def level_count_lex(order: str) -> Any:
    """The level-count lexicographic order: compare counts from the top level down."""

    def key(pop: Pop) -> tuple[int, ...]:
        counts = Counter(pop)
        return tuple(counts.get(level, 0) for level in reversed(LADDER.levels))

    return key


def model_counterexamples() -> dict[str, Any]:
    """Re-verify the two counterexamples that decide the count-sensitive model classes.

    * level-count lexicographic satisfies Egalitarian Dominance, GNEP, VRC avoidance and both
      Dominance Addition forms, and fails Non-Elitism at *every* pair (x, y): one life at W_x is
      strictly better than any number of lives at W_{x-1}, so no witness n exists.
    * critical-level total utility ``sum(level - c)`` satisfies Egalitarian Dominance, both
      Non-Elitism forms, GNEP and VRC avoidance, and fails thesis Dominance Addition: adding
      enough lives at a positive level y below the critical level c makes the mixed population
      strictly worse than A, which the not-worse clause forbids.
    """
    key = level_count_lex("lex")
    lex_witnesses: list[dict[str, Any]] = []
    for x in (5, 6):
        for y in (-1, 1, 3):
            if not x - 1 > y:
                continue
            left = tuple(sorted([x - 1] * 2))
            right = tuple(sorted([x] + [y]))
            lex_witnesses.append(
                {
                    "x": x,
                    "y": y,
                    "left": list(left),
                    "right": list(right),
                    "left_better": key(left) > key(right),
                    "right_better": key(right) > key(left),
                    "fails_non_elitism": key(right) > key(left),
                }
            )
    # Critical-level total at c = 6 fails thesis Dominance Addition once C is large enough.
    c = 6
    critical: list[dict[str, Any]] = []
    for size in (1, 2, 8):
        a = (5,) * 1
        b = (6,) * 1
        added = (1,) * size
        left = tuple(sorted(a))
        right = tuple(sorted(b + added))
        critical.append(
            {
                "C_size": size,
                "A": list(left),
                "B_union_C": list(right),
                "total_A": sum(level - c for level in left),
                "total_B_union_C": sum(level - c for level in right),
                "A_strictly_better": sum(level - c for level in left)
                > sum(level - c for level in right),
            }
        )
    instance = Instance(DA_THESIS, ((5,), tuple(sorted((6,) + (1,) * 8))))
    if not audit(instance, LADDER, CONTROL_WITNESS):
        raise AssertionError("the critical-level counterexample is not a thesis DA instance")
    ne_instance = Instance(NE_THESIS, ((4, 4), (5, 3)))
    if not audit(ne_instance, LADDER, CONTROL_WITNESS):
        raise AssertionError("the lexicographic counterexample is not a thesis NE instance")
    return {
        "level_count_lex": {
            "non_elitism_witness_scan": lex_witnesses,
            "verdict": "fails Non-Elitism for every pair (x, y) and every witness n",
        },
        "critical_level_total": {
            "critical_level": c,
            "dominance_addition_scan": critical,
            "audited_thesis_da_instance": {
                "args": [list(pop) for pop in instance.args],
                "audit": True,
            },
            "verdict": "fails thesis Dominance Addition for C large enough below the critical level",
        },
        "reference": "research/p19_vrc_model.py holds the six-candidate table and its checker",
    }


# ---------------------------------------------------------------------------------------------
# Section 6: sections, verdicts and report.


def reading_section() -> dict[str, Any]:
    """The reading correction, replayed on the phase-18 control's own losing edge."""
    published = ChainWitness(
        n_v=1,
        m_v=1,
        u_v=4,
        y_v=3,
        x_v=-1,
        u_d=4,
        y_d=3,
        n_d=1,
        m_d=15,
        n_b=2,
        m_b=14,
        x_h=6,
    )
    beta_edge = published.edges(DA_2003)[3]
    record = beta_edge.record()
    # Re-express the published level choice (beta at W_6 > W_3 > W_1 with a negative background).
    published_record = dict(record)
    published_record["background"] = [[-1, 1]]
    published_record["left_part"] = [[3, 3]]
    published_record["right_part"] = [[1, 2], [6, 1]]
    published_record["left"] = [[-1, 1], [3, 3]]
    published_record["right"] = [[-1, 1], [1, 2], [6, 1]]
    published_record["witness"] = {"step": 1}
    repaired = verify_beta_ranged(record)
    rejected = verify_beta_ranged(published_record)
    if repaired or rejected != ["background levels [-1] lie outside R(1, 4)"]:
        raise AssertionError("ranged beta controls do not isolate the background restriction")
    return {
        "claim": "thesis Condition beta admits a negative background exactly when its own low "
        "level z is negative, because R(z, y+1) is closed at z",
        "repaired_instance": {
            "levels": {"x": 6, "y": 3, "z": -1},
            "background": [[-1, 1]],
            "problems": repaired,
            "admissible": not repaired,
        },
        "published_level_choice": {
            "levels": {"x": 6, "y": 3, "z": 1},
            "background": [[-1, 1]],
            "problems": rejected,
            "admissible": not rejected,
        },
        "note": ranged_background_note(-1, 3),
        "consequence": (
            "phase 17/18's 'negative-background derived beta not available from ranged NE' holds "
            "at the published levels (x+2, 3, 1) only; it is not a property of the weakening"
        ),
    }


def mechanics_section() -> dict[str, Any]:
    witness = ladder_chain()
    out: dict[str, Any] = {"witness_problems": witness.problems(), "runs": {}}
    for label, ne, da in WEAKENED:
        payload = witness.report(da)
        closure = chain_closure(
            witness.instances(da), f"p19-mechanics/{label}", cycle_states(witness)
        )
        control = control_drop_dominance(witness, da)
        out["runs"][label] = {
            "principles": [ED, GNEP, VRC, ne, da],
            "dominance_form_used": da,
            "beta_form_used": ne,
            "source_problems": payload["source_problems"],
            "closure": closure,
            "without_dominance_decision": control,
            "populations": payload["populations"],
        }
    return out


def obstruction_section() -> dict[str, Any]:
    witness = ladder_chain()
    return {
        "nesting_branch": nesting_obstruction(),
        "bound_branch": {
            "bound": beta_background_bound(witness),
            "statement": "if delta's A lives are not nested in beta's A level they must lie in "
            "beta's permitted background R(z_beta, y_beta+1), so x_delta <= y_beta + 1 <= y_v + 1",
            "why_not_supplied": "u_delta is the axiology's GNEP-derived witness level and y_v its "
            "own VRC range top; the source fixes no relation between them",
        },
        "independent_corroboration": {
            "module": "research/p19_impossibility_ranged_ne.py",
            "finding": "88 repaired templates obstruct with n_delta = 4*n_gnep*(m_beta+m_vrc) > "
            "n_beta, the same count tension",
        },
    }


def model_section() -> dict[str, Any]:
    return {
        "candidates": [
            "critical-level total utility sum(level - c)",
            "level-count lexicographic from the top level down",
            "count of lives at level >= u, then a secondary aggregator",
            "thresholded sum ignoring lives below a cut",
            "lexicographic on (count at >= u, then critical-level total)",
            "exponential additive orders exp(level)",
        ],
        "background_sensitive": background_model_run(),
        "translation_invariant": {
            "scope": "all finite population sizes on W_-1..W_6; lexicographic-linear orders",
            "necessary_first_tier": translation_invariant_decide(vrc_unbounded_b=True),
            "without_vrc_unbounded_b": translation_invariant_decide(vrc_unbounded_b=False),
            "proof": (
                "DA makes all positive first-tier coefficients nonnegative; VRC's arbitrary low "
                "bag makes levels 1..3 nonpositive; NE at (4,1),(5,1),(6,1) makes levels 4..6 "
                "nonpositive. ED bounds levels 0 and -1 above by zero, while GNEP at z=0,-1 "
                "bounds both below by zero. No nonzero first functional remains."
            ),
            "reference": "research/p19_vrc_translation_invariant.py",
        },
        "verdict": "no candidate satisfies all five conditions for all finite sizes; no candidate's "
        "failure proves inconsistency",
        "tension": {
            "statement": "the three requirements pull in different directions; the initial "
            "six additive or lexicographic candidates isolate individual failures",
            "unbounded_vrc_dominance": "critical-level total at the VRC threshold and 2^level "
            "satisfy Egalitarian Dominance, both Non-Elitism forms, GNEP and both Dominance "
            "Addition forms but fail VRC avoidance, because arbitrary-size B keeps adding weight",
            "ne_mass_trade": "level-count lexicographic and the count-first orders tested satisfy "
            "Egalitarian Dominance, GNEP, VRC avoidance and both Dominance Addition forms but "
            "fail Non-Elitism for every pair (x, y), because one life at W_x outranks any number "
            "at W_{x-1}",
            "da_positive_insensitivity": "critical-level total with the critical level above the "
            "added lives satisfies Egalitarian Dominance, Non-Elitism, GNEP and VRC avoidance "
            "but fails thesis Dominance Addition, because enough added lives below the critical "
            "level sink the side that is uniformly above",
            "consequence": "no translation-invariant lexicographic-linear order can satisfy "
            "the weakest five-condition set on this ladder; a surviving model must have "
            "background-dependent comparisons",
        },
        "counterexamples": model_counterexamples(),
        "reference": "research/p19_vrc_model.py",
    }


def verdicts_section() -> dict[str, Any]:
    """Keep the published original theorem distinct from the three unresolved weakenings."""
    out: dict[str, Any] = {}
    for label, ne, da in WEAKENED:
        weakened = label != "original"
        out[label] = {
            "principles": [ED, GNEP, VRC, ne, da],
            "route_a": (
                "unresolved: no source-general contradiction; the repaired family is obstructed "
                "by the nesting count cycle or by the level bound on beta's background"
                if weakened
                else "certified contradiction, published: the 2003 theorem is a source-general "
                "impossibility for this set; this phase's contribution is the fixed-witness chain "
                "mechanics (both Dominance Addition forms) plus the phase-18 primitive control, "
                "not an independent parameterized primitive proof"
            ),
            "route_b": (
                "unresolved: no certified model; the count-sensitive classes tried fail "
                "Non-Elitism, VRC avoidance or thesis Dominance Addition, one requirement each"
                if weakened
                else "impossible: a model of this set would contradict the published theorem"
            ),
            "certified": [
                "reading correction for ranged Condition beta's background",
                "chain closure for both Dominance Addition forms without completeness",
                "arithmetic obstruction of the nesting branch",
            ]
            + ([] if weakened else ["published 2003 theorem (external, not re-proved here)"]),
        }
    return out


def run() -> dict[str, Any]:
    chain = ladder_chain()
    replay = chain.report(DA_2003)["source_problems"]
    controls = {
        "chain_witness_problems": chain.problems(),
        "chain_replays_clean": not replay["p18_replay"] and not replay["ranged_beta_replay"],
        "seven_principles": list(SEVEN),
        "ladder": list(LADDER.levels),
    }
    return {
        "scope": "Q-011 dual route pass; fixed-witness chain mechanics, reading correction, "
        "arithmetic obstruction, and ladder-relative class exclusion; no new source-general "
        "impossibility or model claim",
        "controls": controls,
        "reading": reading_section(),
        "mechanics": mechanics_section(),
        "obstruction": obstruction_section(),
        "models": model_section(),
        "verdicts": verdicts_section(),
    }


def _summary(data: Mapping[str, Any]) -> str:
    mechanics = data["mechanics"]["runs"]
    decisions = ", ".join(
        f"{label}: {run['closure']['decision_without_completeness']}"
        for label, run in mechanics.items()
    )
    return (
        f"reading correction admissible={data['reading']['repaired_instance']['admissible']} "
        f"published={data['reading']['published_level_choice']['admissible']}; "
        f"closures {decisions}; nesting branch "
        f"{data['obstruction']['nesting_branch']['decision']}"
    )


def main() -> None:
    started = time.monotonic()
    data = run()
    path = write_result(
        "p19_vrc_universal", data, {"wall_time_s": round(time.monotonic() - started, 1)}
    )
    record(
        [
            LedgerEntry(
                candidate_id="P19-vrc-universal-routes",
                hypothesis="The 2003 theorem's Non-Elitism and Dominance Addition weakenings either admit a source-general contradiction or an exact model.",
                motivation="Q-011's three weakened variants have no certificate at fixed witnesses; test the negative-background repair of ranged Condition beta.",
                exact_formal_change="Ranged Condition beta with a negative low level; the repaired ED/DA/delta/beta/VRC chain; the nesting count identity.",
                scope=data["scope"],
                search_method="independent source-edge replay; chain closure without completeness; z3 witness arithmetic; first-tier coefficient argument and necessary-system control",
                result=json.dumps(
                    {
                        "closures": {
                            label: run["closure"]["decision_without_completeness"]
                            for label, run in data["mechanics"]["runs"].items()
                        },
                        "nesting": data["obstruction"]["nesting_branch"]["decision"],
                        "translation_invariant": data["models"]["translation_invariant"][
                            "necessary_first_tier"
                        ],
                        "reading_admissible": data["reading"]["repaired_instance"]["admissible"],
                    },
                    sort_keys=True,
                ),
                evidence_type="fixed-witness chain mechanics, reading correction, arithmetic obstruction, and ladder-relative translation-invariant exclusion",
                checked=True,
                minimal="the obstruction is proved for the family that stacks beta and delta at the shared population and closes on VRC",
                interpretation="The original variant is settled by the published 2003 theorem (external to this phase); the three weakenings stay open. The first-tier coefficient proof excludes translation-invariant orders on the ladder, while the tested background-sensitive relations each fail an audited premise. Neither route supplies a full Q-011 certificate.",
                next_experiment="seek a chain avoiding beta's background range without nesting, or a background-sensitive model satisfying all five conditions at every size",
                result_scope="source readings; a fixed-witness ladder chain; an integer identity; and an all-size ladder-relative translation-invariant class exclusion",
                formalization_tier="agent-cross-read source conditions with the phase-18 manifest and phase-19 replay",
                witness_conditions="research/p19_vrc_universal.py ChainWitness and ladder_chain(); ladder W_-1..W_6",
                novelty_status="not-applicable (fidelity correction and obstruction)",
                status="open",
                artifacts=[str(path.relative_to(path.parent.parent.parent))],
            )
        ]
    )
    print(json.dumps(data, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
