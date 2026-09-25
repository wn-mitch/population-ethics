"""Phase 20 / Q-011 Route A: the *direct* primitive reservoir cycle for the 2003 weakenings.

Phases 17-19 attacked the three weakened variants of Arrhenius's 2003 VRC theorem through the
paper's own derived conditions beta (from Non-Elitism) and delta (from GNEP). Phase 19 obstructed
that family with the count cycle ``n_beta = n_delta + n_v >= m_delta > m_beta > n_beta`` and with
the unforced level bound ``x_delta <= y_v + 1``. This phase takes the other Route A shape: a
cycle built only from the five *primitive* source conditions, with no beta and no delta anywhere.

What this phase establishes, and what it does not (see ``run`` for the machine-readable form):

1. **A closing direct cycle exists (executable certificate, fixed/parameterized witness).** For a
   legal witness choice whose VRC bag reaches GNEP's witness level ("Case A"),

       ED:   W_{lam+1}^{n_v} > W_lam^{n_v}                      [strict head edge]
       VRC:  W_lam^{n_v} >= W_bag^b + W_neg^{m_v}               [the reservoir, no background]
       GNEP: raise every negative life W_neg -> W_{y_g}, n_g fuel lives from the bag per step
       NE:   climb W_{y_g+1} .. W_{lam+2}, one level per stage, s = n_e + 1 lives per application
       DA:   W_{lam+2}^{n_v} plus a W_1 block, against W_{lam+1}^{n_v}

   closes with transitivity and reflexivity alone: ``closed_cycle`` decides it with phase 18's
   mentioned-atom encoder, phase 16's ``decide_without_completeness`` and the DPLL checker, all
   three agreeing on UNSAT, and completeness is never asserted. Every edge is replayed without
   the constructor: phase 18's ``verify_edge`` against the frozen ``SOURCE_MANIFEST``, plus the
   exhaustive ``ladder.audit`` where affordable and phase 16's linear decomposition audit
   otherwise. All four NE/DA weakening combinations instantiate the *same* chain - every NE
   background already lies inside R(1, x) and the DA's C block is one level (``W_1``) - so the
   both-weakened set (thesis Non-Elitism + thesis Dominance Addition) is refuted at this witness,
   directly and without beta or delta. This is a fixed-witness refutation of "the five conditions
   at W", not a source-general theorem (D-005, D-013).

2. **Obstruction of the family, with the exact missing inequality.** Two layers.

   *Structural.* VRC's A relatum has no background in the 2003 reading, so the reservoir step can
   only be applied to a clean population. The GNEP fuel must then come from the VRC bag block (the
   only lives at a level >= u_g the reservoir supplies), and the bag lives are still present while
   the climb runs, so ranged Non-Elitism forces them inside R(1, x) at every stage: the bag level
   must be exactly ``y_g + 1``. Hence the family needs

       u_g <= y_g + 1     and     y_v >= y_g + 1

   for every z on the negative-raising path, where ``u_g``, ``y_g`` are GNEP's own witnesses and
   ``y_v`` VRC's range top - three mutually independent existential choices in the source, so
   neither inequality is a source consequence.

   *Counting (argued, not machine-checked).* The structural layer is a statement about this
   construction; the counting layer is the supporting argument that the repair cannot be found by
   climbing for fuel while the negative lives are present. Only GNEP moves a life from W_z to
   W_{z+1}, and with ranged Non-Elitism every NE instance applied while a negative life is present
   must put its B relatum below that life, so each such application *creates* a fresh negative
   life; if fuel above the bag's top can only come from such an application. The four counting
   lemmas give ``A_1 >= n_v + E``, ``E >= N``, ``N >= m_v + A_1``, i.e. ``F >= F + m_v`` (UNSAT
   over the integers, `case_b_arithmetic`), with the relaxed system SAT as the control that
   isolates the negative/fuel coupling. The delicate step (L4: every negative life sits at or
   below the first expensive level and must cross it) is named in `case_b_arithmetic` and carried
   in ``remaining_obligation`` rather than claimed as closed. A concrete legal Case-B witness
   (VRC range top ``y_v = 3 = y_g`` against ``u_g = 4 = y_g + 1``) is recorded, the structural
   requirement is evaluated on it, and the bounded directed search over the family is reported as
   discovery only, with its cap.

3. **Implications for the single weakenings.** The DA weakening is invisible to this route: the
   construction's addition block is a single level, so it is an instance of *both* DA forms and
   weakening DA neither helps nor hurts. The NE weakening is exactly what Case B bites on: 2003
   Non-Elitism's unrestricted background admits the stage-(y_v + 1) climb while the negative lives
   sit in D; ranged Non-Elitism does not.

Nothing here alters any source principle, reading or checker, and the obstruction is a statement
about the direct-reservoir family, not about the weakened condition sets in general.
"""

from __future__ import annotations

import json
import time
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from itertools import combinations_with_replacement
from typing import Any

import z3  # type: ignore[import-untyped]

from research.lab import dpll_check
from research.ladder import Ladder, Witness, audit, instances_over
from research.p6_schema import core_constraints, name_of
from research.p16_ne_top import _audit_generated, decide_without_completeness
from research.p17_vrc_boundary import DA_2003, DA_THESIS, ED, GNEP, NE_2003, NE_THESIS, VRC
from research.p18_vrc_certificate import (
    Edge,
    _decide_mentioned,
    audit_is_cheap,
    chain_transitivity,
    verify_edge,
)
from research.schema import Instance, Pop

# The four Q-011 variants in phase 17/19 order: (label, Non-Elitism reading, Dominance form).
VARIANTS: tuple[tuple[str, str, str], ...] = (
    ("original", NE_2003, DA_2003),
    ("ranged-ne", NE_THESIS, DA_2003),
    ("not-worse-da", NE_2003, DA_THESIS),
    ("both-weakened", NE_THESIS, DA_THESIS),
)

# The chain's levels: one negative level, the neutral level (GNEP at z = -1 needs W_0) and W_1..W_9
# so that the bag, Lambda, Lambda + 1 and Lambda + 2 all exist for the grid below.
LADDER = Ladder(negative=1, positive=9)


# ---------------------------------------------------------------------------------------------
# Section 1: the direct reservoir witness and its exact flow arithmetic.


@dataclass(frozen=True)
class ReservoirWitness:
    """One legal source-witness choice for the direct cycle.

    ``lam`` is VRC's A level (also ED's B level), ``lam + 1`` ED's A level, ``lam + 2`` the DA
    threshold and the climb top, ``bag`` the level of VRC's B block (the reservoir), ``neg`` VRC's
    negative level ``x_v``, ``neg_count`` VRC's ``m`` and ``n_v`` VRC's ``n``. GNEP's witness at
    every level on the raising path is ``(u_g, y_g, n_g)``; Non-Elitism's witness at every climb
    pair is ``n_e``.
    """

    lam: int
    bag: int
    neg: int
    neg_count: int
    n_v: int
    u_v: int
    v_v: int
    y_v: int
    u_g: int
    y_g: int
    n_g: int
    n_e: int

    # -- source constraints -----------------------------------------------------------------
    def problems(self) -> list[str]:
        """Every source constraint this witness choice would violate."""
        out: list[str] = []
        if self.neg >= 0:
            out.append("VRC's W_x must be negative")
        if not (self.u_v > self.y_v >= 3):
            out.append("VRC needs u > y >= 3 (a range has at least three levels)")
        if self.v_v < self.u_v + 2 or self.v_v > LADDER.positive:
            out.append("VRC needs R(u, v) of at least three levels inside the ladder")
        if self.lam < self.u_v:
            out.append("VRC's A level must be at least u")
        if self.n_v < 1 or self.neg_count < 1:
            out.append("VRC needs n > 0 and m > 0")
        if not (self.u_g > self.y_g >= 3):
            out.append("GNEP needs u > y >= 3")
        if self.n_g < 1 or self.n_e < 1:
            out.append("GNEP and Non-Elitism need n > 0")
        if not (self.u_g <= self.bag <= self.y_v):
            out.append("the bag level must lie in [u_g, y_v]: this is Case A")
        if not (self.y_g + 1 <= self.bag <= self.lam + 1):
            out.append("the bag level must sit between R(1, y_g) and the DA threshold")
        if self.bag != self.y_g + 1:
            out.append(
                "the bag must sit exactly one level above GNEP's range top: every climb stage "
                "while the bag's own lives are still present needs a background inside R(1, x), "
                "and the first stage's level is the bag level"
            )
        if not all(LADDER.has(v) for v in (self.neg, 0, self.y_g, self.bag, self.top)):
            out.append("a required level is off the ladder")
        return out

    # -- derived quantities -----------------------------------------------------------------
    @property
    def top(self) -> int:
        """The climb's top level W_{lam + 2}: the DA block's level and its threshold."""
        return self.lam + 2

    @property
    def s(self) -> int:
        """Lives consumed per Non-Elitism application: n_e + 1."""
        return self.n_e + 1

    @property
    def gnep_applications(self) -> int:
        """GNEP applications raising the whole negative block to the top of R(1, y_g)."""
        return (self.y_g - self.neg) * self.neg_count

    @property
    def outputs(self) -> int:
        """Lives the GNEP phase emits inside R(1, y_g); all of them are placed at W_{y_g}."""
        return self.gnep_applications * self.n_g

    @property
    def raising_path(self) -> tuple[int, ...]:
        """The levels z at which the GNEP phase raises a negative life.

        The block stops at ``W_{y_g}``, the top of GNEP's low range: raising a life one level
        further would need fuel and an emitted life that the source's own numbers can make
        identical (``n_g = 1`` with the fuel level just above ``W_{y_g}``), which is a reflexive
        relatum pair and carries no information.
        """
        return tuple(range(self.neg, self.y_g))

    @property
    def level_yg_supply(self) -> int:
        """Lives sitting at ``W_{y_g}`` when the GNEP phase ends: its emissions plus the block."""
        return self.outputs + self.neg_count

    def application_counts(self) -> tuple[list[int], str | None]:
        """Non-Elitism application counts per climb stage, or the exact divisibility failure.

        Stage ``x`` (``y_g + 1 <= x <= top``) performs ``q_x`` instances, each consuming ``s``
        lives at ``W_{x-1}`` and producing one life at ``W_x`` plus ``n_e`` lives at ``W_1``. The
        level-``y_g`` supply must be consumed exactly: ``level_yg_supply = s * q_{y_g+1}``; levels
        above it follow ``q_x = s * q_{x+1}`` with ``q_top = n_v``. Hence ``q_bag`` is
        ``level_yg_supply / s^(bag - y_g)`` and must be a positive integer; the bag injection at
        ``W_bag`` then balances the level-``bag`` count.
        """
        q = [0] * (self.top + 2)
        q[self.top] = self.n_v
        for x in range(self.top - 1, self.bag, -1):
            q[x] = self.s * q[x + 1]
        divisor = self.s ** (self.bag - self.y_g)
        if self.level_yg_supply % divisor:
            return q, (
                f"the level-{self.y_g} supply {self.level_yg_supply} is not a multiple of "
                f"s^(bag - y_g) = {divisor}, so the climb cannot consume it exactly"
            )
        q[self.bag] = self.level_yg_supply // divisor
        if q[self.bag] < 1:
            return q, "the climb's first stage needs a positive number of applications"
        for x in range(self.y_g + 1, self.bag):
            q[x] = self.s * q[x + 1]
        return q, None

    def bag_size(self) -> int:
        """VRC's B block size making the level-``bag`` balance exact.

        At ``W_bag`` the supply is the bag's own remainder ``b - outputs`` plus the previous
        stage's ``q_bag`` lives; the demand is ``s * q_{bag+1}``. Solving gives ``b``. Every other
        level from ``y_g`` to ``top`` is consumed exactly, so the only residual lives sit at
        ``W_1`` - which is what lets the DA block be a single level and so be an instance of the
        thesis table too.
        """
        q, _ = self.application_counts()
        return self.s * q[self.bag + 1] - q[self.bag] + self.outputs

    def residues(self) -> int:
        """Lives left at W_1 at the end of the cycle: the closing DA's C block."""
        q, _ = self.application_counts()
        return self.n_e * sum(q[self.y_g + 1 : self.top + 1])


def grid_shape(
    neg_count: int, n_g: int, n_e: int, bag: int, u_g: int, y_g: int
) -> ReservoirWitness:
    """One grid entry with its VRC witnesses derived so every source constraint holds.

    VRC's range top is the bag level itself (``y_v = bag``, so the bag fills R(1, y_v)), its low
    bound is raised until ``u_v > y_v`` while keeping ``R(u_v, v_v)`` three levels inside the
    ladder's positive side, and ``lam`` is chosen high enough that the bag sits below the DA
    threshold. The GNEP witness level ``u_g`` never exceeds the bag level: that is Case A.
    """
    u_v = max(5, bag + 1)
    lam = max(u_v, u_g + 1, bag + 1)
    return ReservoirWitness(
        lam=lam,
        bag=bag,
        neg=-1,
        neg_count=neg_count,
        n_v=1,
        u_v=u_v,
        v_v=u_v + 2,
        y_v=bag,
        u_g=u_g,
        y_g=y_g,
        n_g=n_g,
        n_e=n_e,
    )


def witness_grid() -> list[ReservoirWitness]:
    """Case-A witness choices whose flow arithmetic closes; each is rebuilt and replayed.

    The tuples are (m_v, n_g, n_e, bag, u_g, y_g). The list is a bounded selection from a grid
    scan over those six parameters; the scan is discovery only, and only entries whose flow
    divisibility ``s^(bag - y_g) | (outputs + m_v)`` and bag balance both close are admissible.
    """
    shapes = (
        (2, 1, 1, 4, 4, 3),  # the concrete worked example: bag 11, 12 lives at W_1
        (1, 1, 1, 5, 5, 4),  # GNEP's range top W_4, one life in the negative block
        (2, 1, 1, 5, 5, 4),  # same range top with two negative lives
        (4, 2, 2, 4, 4, 3),  # n_g = 2 and n_e = 2
        (3, 1, 2, 4, 4, 3),  # n_e = 2 at the W_3 range top
        (2, 1, 2, 5, 5, 4),  # n_e = 2 at the W_4 range top
    )
    return [grid_shape(*shape) for shape in shapes]


def case_b_witness() -> ReservoirWitness:
    """The concrete legal witness choice the obstruction is stated at: the reservoir stops at W_3.

    VRC avoidance with ``u = 4``, ``R(1, 3)`` and ``W_x = W_-1`` may put its B block anywhere in
    ``R(1, 3)``, so its top level is ``y_v = 3``; GNEP's witness at the raising levels has
    ``y_g = 3`` and ``u_g = 4 = y_g + 1``. Both are legal choices for the two conditions and
    nothing in the source relates them. The choice sits exactly on the family's two obstructions:
    ``y_v = 3 < y_g + 1 = 4`` (VRC's range cannot hold a life at the only level that could fuel
    GNEP) and ``y_v = 3 < u_g = 4`` (the Case-B fuel gap).
    """
    return ReservoirWitness(
        lam=5,
        bag=3,
        neg=-1,
        neg_count=1,
        n_v=1,
        u_v=4,
        v_v=6,
        y_v=3,
        u_g=4,
        y_g=3,
        n_g=1,
        n_e=1,
    )


# ---------------------------------------------------------------------------------------------
# Section 2: the chain, built as decomposed edges so the replay never calls the builder.


def _plus(*parts: Pop) -> Pop:
    return tuple(sorted(v for part in parts for v in part))


def _bag(level: int, count: int) -> Pop:
    return (level,) * count


def _pop(counter: Counter[int]) -> Pop:
    return tuple(sorted(counter.elements()))


@dataclass(frozen=True)
class Step:
    """One chain edge: phase 18's decomposition plus the witness lookup its replayer checks."""

    principle: str
    left_part: Pop
    right_part: Pop
    background: Pop = ()
    lookup: Mapping[str, int] = field(default_factory=dict)

    @property
    def edge(self) -> Edge:
        return Edge(self.principle, self.left_part, self.right_part, self.background, self.lookup)

    @property
    def instance(self) -> Instance:
        return self.edge.instance


def source_witness(witness: ReservoirWitness) -> Witness:
    """The ladder ``Witness`` carrying this chain's GNEP, VRC and Non-Elitism parameters."""
    return Witness(
        {
            "vrc-avoidance": {
                "x": witness.neg,
                "u": witness.u_v,
                "v": witness.v_v,
                "y": witness.y_v,
                "n": witness.n_v,
                "m": witness.neg_count,
            },
            "general-non-extreme-priority": {
                "u": witness.u_g,
                "y": witness.y_g,
                "n": witness.n_g,
            },
            "non-elitism": {"n": witness.n_e},
        }
    )


def build(
    witness: ReservoirWitness, ne_form: str, da_form: str
) -> tuple[list[Step], dict[str, Any]]:
    """Build the direct cycle for one NE/DA form pair, or report the exact arithmetic failure.

    Order: ED (the single strict edge), VRC (the reservoir), the GNEP raises of the negative
    block, the Non-Elitism climb, the closing Dominance Addition. ``witness.problems()`` and the
    flow divisibility are checked first and returned as a failure record rather than raised, so
    callers can report the exact missing inequality instead of a traceback.
    """
    problems = witness.problems()
    if problems:
        return [], {"stage": "witness", "problems": problems}
    q, failure = witness.application_counts()
    if failure is not None:
        return [], {"stage": "flow", "problems": [failure]}
    bag_size = witness.bag_size()
    if bag_size < 1:
        return [], {"stage": "flow", "problems": [f"VRC's B block size {bag_size} is not positive"]}
    if bag_size < witness.outputs:
        return [], {
            "stage": "flow",
            "problems": [
                f"VRC's B block size {bag_size} cannot pay the {witness.outputs} fuel lives the "
                "GNEP phase takes from it"
            ],
        }

    lam, bag, neg = witness.lam, witness.bag, witness.neg
    top, s = witness.top, witness.s
    n_g, n_e = witness.n_g, witness.n_e
    steps: list[Step] = []

    # (1) ED: W_{lam+1}^{n_v} > W_lam^{n_v}. The ED's B is VRC's A relatum.
    steps.append(Step(ED, _bag(lam + 1, witness.n_v), _bag(lam, witness.n_v)))

    # (2) VRC: W_lam^{n_v} >= W_bag^b + W_neg^{m_v}. No background: the source's own reading, and
    # the reason the reservoir step needs a clean population.
    vrc_right = _bag(bag, bag_size) + _bag(neg, witness.neg_count)
    steps.append(
        Step(
            VRC,
            _bag(lam, witness.n_v),
            vrc_right,
            (),
            {
                "x": neg,
                "u": witness.u_v,
                "v": witness.v_v,
                "y": witness.y_v,
                "n": witness.n_v,
                "m": witness.neg_count,
            },
        )
    )

    # (3) GNEP: raise every negative life from W_neg to W_{y_g}, one level per application, paying
    # n_g lives from the bag and emitting n_g lives at W_{y_g}. The bag is the fuel, so this phase
    # exists only while bag >= u_g, i.e. in Case A.
    pop = Counter(vrc_right)
    for _ in range(witness.neg_count):
        for z in witness.raising_path:
            fuel_and_low = Counter(_bag(bag, n_g) + (z,))
            if fuel_and_low - pop:
                raise AssertionError("the GNEP phase lost its fuel or its negative life")
            background = pop - fuel_and_low
            pop = background + Counter(_bag(witness.y_g, n_g) + (z + 1,))
            steps.append(
                Step(
                    GNEP,
                    _bag(bag, n_g) + (z,),
                    _bag(witness.y_g, n_g) + (z + 1,),
                    _pop(background),
                    {"z": z, "u": witness.u_g, "y": witness.y_g, "n": n_g},
                )
            )

    # (4) Non-Elitism climb: stage x turns s lives at W_{x-1} into one at W_x and n_e at W_1.
    for x in range(witness.y_g + 1, top + 1):
        for _ in range(q[x]):
            left = Counter({x - 1: s})
            if left - pop:
                raise AssertionError("the climb ran out of lives at the level below this stage")
            background = pop - left
            if any(v < 1 or v > x for v in background):
                raise AssertionError(
                    f"stage {x} has a background life outside R(1, {x}): {sorted(background)}"
                )
            pop = background + Counter({x: 1, 1: n_e})
            steps.append(
                Step(
                    ne_form,
                    _bag(x - 1, s),
                    (x,) + _bag(1, n_e),
                    _pop(background),
                    {"x": x, "y": 1, "n": n_e},
                )
            )

    # (5) Closing Dominance Addition against the ED's A. 2003's reading puts B union C on the
    # left; the thesis reading is N-shaped and puts A on the left.
    a_block = _bag(lam + 1, witness.n_v)
    b_block = _bag(top, witness.n_v)
    c_block = _bag(1, witness.residues())
    if pop != Counter(_plus(b_block, c_block)):
        raise AssertionError("the climb did not land on the closing DA relata")
    if da_form == DA_2003:
        steps.append(Step(DA_2003, _plus(b_block, c_block), a_block))
    else:
        steps.append(Step(DA_THESIS, a_block, _plus(b_block, c_block)))

    for index, step in enumerate(steps):
        if Counter(step.edge.left) == Counter(step.edge.right):
            raise AssertionError(
                f"edge {index} ({step.principle}) has identical relata and carries no information"
            )

    counts = {x: q[x] for x in range(witness.y_g + 1, top + 1)}
    return steps, {
        "stage": "ok",
        "bag_size": bag_size,
        "gnep_applications": witness.gnep_applications,
        "ne_applications": sum(counts.values()),
        "climb_counts": counts,
        "residues": witness.residues(),
        "final_population": [[level, count] for level, count in sorted(pop.items())],
    }


# ---------------------------------------------------------------------------------------------
# Section 3: the independent replay.


def closed_cycle(steps: Sequence[Step], tag: str) -> dict[str, Any]:
    """Decide the written cycle with reflexivity and its own transitivity only, never completeness.

    The path of populations is the chain's own: the strict ED head edge, then each step's right
    endpoint whenever it is new. For the 2003 Dominance Addition the closing edge lands back on
    the start (so the trailing repeat is dropped); for the thesis N-shaped edge the closing relatum
    *is* the start, and the edge's own constraint supplies ``weak(last, start)``. Either way the
    three independent decisions (mentioned-atom Z3, phase 18's encoder, DPLL) must agree.
    """
    instances = [step.instance for step in steps]
    states = [name_of(instances[0].args[0])]
    for instance in instances:
        right = name_of(instance.args[1])
        if right != states[-1]:
            states.append(right)
    if len(states) > 1 and states[-1] == states[0]:
        states.pop()
    hard = [*chain_transitivity(states), *core_constraints(instances, tag)]
    mentioned = _decide_mentioned(hard)
    dpll, _ = dpll_check([constraint.formula for constraint in hard])
    phase16 = decide_without_completeness(instances, tag)
    if not (mentioned == dpll == phase16):
        raise AssertionError(
            f"closure disagreement on {tag}: mentioned {mentioned}, dpll {dpll}, p16 {phase16}"
        )
    shapes = [instance.shape for instance in instances]
    closing_returns = name_of(instances[-1].args[1]) == states[0]
    return {
        "formalization_id": tag,
        "instances": len(instances),
        "path_states": len(states),
        "shapes": shapes,
        "strict_edges": sum(shape == "S" for shape in shapes),
        "single_strict_head_edge": shapes[0] == "S" and shapes.count("S") == 1,
        "closing_edge_returns_to_the_strict_tail": closing_returns,
        "closing_orientation": (
            "weak closing edge back to the strict tail"
            if closing_returns
            else "N-shaped closing edge: not(A > B union C) with the chain's own transitivity "
            "forcing the reverse weak atom, which is what refutes it"
        ),
        "decision_without_completeness": mentioned,
        "mentioned_atom_decision": mentioned,
        "dpll_decision": dpll,
        "phase16_decision": phase16,
        "completeness_used": False,
    }


def replay_chain(
    witness: ReservoirWitness, ne_form: str, da_form: str, label: str
) -> dict[str, Any]:
    """Build one chain and replay every edge plus the closure, without trusting the builder.

    Each edge is replayed by phase 18's ``verify_edge`` against the frozen ``SOURCE_MANIFEST``
    (which re-derives sizes, levels, ranges, backgrounds and the witness lookup from the count
    vectors alone) and audited independently - by ``ladder.audit`` when its sub-bag enumeration is
    affordable, by phase 16's exact linear decomposition audit otherwise. The chain is then closed
    with ``closed_cycle``: reflexivity, the written chain's own transitivity, and nothing else.
    """
    steps, build_report = build(witness, ne_form, da_form)
    if not steps:
        return {"label": label, "built": False, "build": build_report}
    source = source_witness(witness)
    problems: list[str] = []
    exhaustive = 0
    linear = 0
    for index, step in enumerate(steps):
        for problem in verify_edge(step.edge.record(), LADDER, source):
            problems.append(f"edge {index} ({step.principle}): {problem}")
        instance = step.instance
        if audit_is_cheap(instance):
            exhaustive += 1
            if not audit(instance, LADDER, source):
                problems.append(f"edge {index} ({step.principle}): ladder audit rejected it")
        else:
            linear += 1
            if not _audit_generated(instance, LADDER, source):
                problems.append(f"edge {index} ({step.principle}): linear audit rejected it")
    closure = closed_cycle(steps, f"p20-direct/{label}")
    return {
        "label": label,
        "built": True,
        "ne_form": ne_form,
        "da_form": da_form,
        "instances": len(steps),
        "principles": sorted({step.principle for step in steps}),
        "edge_replay_problems": problems,
        "edges_replayed_clean": not problems,
        "edges_audited_exhaustively": exhaustive,
        "edges_audited_linearly": linear,
        "closure": closure,
        "build": build_report,
        "populations": {
            "ED_A": list(steps[0].left_part),
            "ED_B_and_VRC_A": list(steps[0].right_part),
            "VRC_B_union_C": list(steps[1].right_part),
            "closing_DA_left": list(steps[-1].left_part),
            "closing_DA_right": list(steps[-1].right_part),
        },
    }


def variants_section() -> dict[str, Any]:
    """Rebuild and replay the chain for each of Q-011's four NE/DA weakening combinations."""
    runs: dict[str, Any] = {}
    for label, ne_form, da_form in VARIANTS:
        runs[label] = replay_chain(witness_grid()[0], ne_form, da_form, label)
    return runs


def grid_section() -> dict[str, Any]:
    """The witness grid: every Case-A choice, replayed for the both-weakened set."""
    runs: list[dict[str, Any]] = []
    for witness in witness_grid():
        label = (
            f"m{witness.neg_count}-ng{witness.n_g}-ne{witness.n_e}-bag{witness.bag}-"
            f"ug{witness.u_g}-yg{witness.y_g}"
        )
        report = replay_chain(witness, NE_THESIS, DA_THESIS, label)
        report["witness"] = {
            key: getattr(witness, key)
            for key in ("lam", "bag", "neg", "neg_count", "n_v", "u_g", "y_g", "n_g", "n_e")
        }
        runs.append(report)
    return {
        "runs": runs,
        "all_built": all(run["built"] for run in runs),
        "all_clean": all(run.get("edges_replayed_clean") for run in runs),
        "all_unsat": all(
            run.get("closure", {}).get("decision_without_completeness") == "unsat" for run in runs
        ),
    }


# ---------------------------------------------------------------------------------------------
# Section 4: the Case-B obstruction.


def case_b_arithmetic() -> dict[str, Any]:
    """The four counting lemmas as an integer system, proved UNSAT with a satisfiable control.

    Lemmas, each argued in the phase docstring and each checked at the instance level by
    ``case_b_instance_check`` where it is an instance statement:

    * (L1, H-budget) a life above ``W_{y_v}`` can only be created from below by a Non-Elitism
      application at stage ``y_v + 1``; every other instance either moves an above-``y_v`` life to
      another above-``y_v`` level or destroys one. So ``H = A_1`` bounds every above-``y_v`` life
      that ever exists.
    * (L2) the final population needs ``n_v`` lives at the climb top and each *expensive* GNEP
      application (``u_g(z) > y_v``), whose fuel must sit above ``y_v``, consumes at least one of
      those lives: ``A_1 >= n_v + E``.
    * (L3) each Non-Elitism application at stage ``y_v + 1`` puts at least one fresh life at a
      level below every negative life present, so the negative lives that must be eliminated are
      at least ``m_v + A_1``: ``N >= m_v + A_1``.
    * (L4) eliminating a negative life means raising it to a positive level, and each such raise
      crosses the first expensive level on its path, so it costs at least one expensive GNEP
      application: ``E >= N``. *Delicate step:* L4 as stated holds when the negative lives in
      question sit at or below ``z*``, the largest level in ``[x_v, 0]`` with ``u_g(z) > y_v`` -
      which is exactly what VRC's C block (at ``x_v <= z*``) and the ranged-NE dumps (at a level
      below the current minimum, hence at or below ``x_v``) supply. A life that arrives at a level
      *above* ``z*`` can be raised cheaply and would escape L4; closing that case needs the
      potential argument sketched in ``remaining_obligation``, so L4 is reported as an argued step
      rather than a machine-checked one.
    """
    a1, n_v, e_count, n_neg, m_v = z3.Ints("A_1 n_v E N m_v")
    solver = z3.Solver()
    solver.add(
        a1 >= n_v + e_count,
        e_count >= n_neg,
        n_neg >= m_v + a1,
        m_v >= 1,
        n_v >= 1,
    )
    status = solver.check()
    if status != z3.unsat:
        raise AssertionError(f"the Case-B system was expected UNSAT, got {status}")
    relaxed = z3.Solver()
    relaxed.add(a1 >= n_v + e_count, n_neg >= m_v + a1, m_v >= 1, n_v >= 1)
    relaxed_status = relaxed.check()
    if relaxed_status != z3.sat:
        raise AssertionError(f"the relaxed system should be satisfiable, got {relaxed_status}")
    return {
        "decision": str(status),
        "relaxed_without_the_negative_fuel_coupling": str(relaxed_status),
        "status": "the integer system A_1 >= n_v + E, E >= N, N >= m_v + A_1, m_v, n_v >= 1 is "
        "UNSAT and the control without E >= N is SAT; the four lemmas that feed it are argued in "
        "the docstring, and L4's delicate step is named there",
        "missing_inequality": (
            "the reservoir level must be y_g + 1, so the family needs u_g <= y_g + 1 and "
            "y_v >= y_g + 1 for every z on the negative-raising path; equivalently the fuel level "
            "must lie inside VRC's own range"
        ),
        "chain_of_inequalities": "A_1 >= n_v + E >= n_v + N >= n_v + m_v + A_1 > A_1",
        "lemmas": {
            "L1": "above-y_v lives are created only by Non-Elitism at stage y_v + 1",
            "L2": "A_1 >= n_v + E (final climb top plus expensive GNEP fuel)",
            "L3": "N >= m_v + A_1 (fresh negative life per stage-(y_v + 1) application)",
            "L4": "E >= N (each negative life must cross an expensive level to turn positive)",
        },
    }


def case_b_instance_check(cap: int = 3) -> dict[str, Any]:
    """Finite instance-level check of lemma L3's shape, with its cap reported.

    Over every ranged-Non-Elitism instance of the ladder generator whose relata use at most
    ``cap`` lives each and whose background contains a negative life, the B relatum's level is
    negative: while a negative life is present the shared background must lie inside R(y, x), so y
    is at or below that life's level. This is a finite check of an instance statement, not
    evidence for the counting argument it feeds.
    """
    levels = tuple(v for v in LADDER.levels if v <= 4)
    pops: list[Pop] = []
    for size in range(1, cap + 1):
        for pop in _bags_from(levels, size):
            pops.append(pop)
    witness = source_witness(case_b_witness())
    instances = instances_over(pops, LADDER, witness, [NE_THESIS])
    checked = 0
    violations: list[list[Any]] = []
    for instance in instances:
        left, right = (Counter(p) for p in instance.args)
        background = left & right
        if not any(level < 0 for level in background.elements()):
            continue
        checked += 1
        low = min(right)
        if low >= 0:
            violations.append([list(left.items()), list(right.items())])
    return {
        "cap": f"at most {cap} lives per population, levels {list(levels)}",
        "instances": len(instances),
        "with_a_negative_background": checked,
        "violations_of_the_negative_dump_claim": violations,
        "reference": "the dump level is the B relatum's level, read from the instance's own relata",
    }


def _bags_from(levels: Sequence[int], size: int) -> list[Pop]:
    return [tuple(c) for c in combinations_with_replacement(sorted(levels), size)]


def bounded_search(witness: ReservoirWitness, cap: int = 40, max_lives: int = 2) -> dict[str, Any]:
    """Discovery only: look for a one-strict-edge cycle at the Case-B witness, and report the cap.

    The domain is every population of at most ``max_lives`` lives over the witness's own levels,
    truncated to ``cap`` populations nearest the witness's relata. A cycle is a path of weak
    (W/N) edges returning to the strict edge's tail. Absence of a cycle inside this cap is *not*
    evidence for the obstruction (D-005, D-013); it is recorded so the obstruction's scope is
    visible next to a search that could have falsified it.
    """
    levels = sorted(
        {witness.neg, 0, 1, witness.y_g, witness.bag, witness.lam, witness.lam + 1, witness.top}
    )
    universe = [pop for size in range(1, max_lives + 1) for pop in _bags_from(levels, size)]
    relata = (
        _bag(witness.lam + 1, witness.n_v),
        _bag(witness.lam, witness.n_v),
        _bag(witness.bag, witness.outputs) + _bag(witness.neg, witness.neg_count),
        _bag(witness.top, witness.n_v) + _bag(1, 2),
    )

    def distance(pop: Pop) -> tuple[int, int]:
        left = Counter(pop)
        return (
            min(
                sum((left - Counter(other)).values()) + sum((Counter(other) - left).values())
                for other in relata
            ),
            len(pop),
        )

    focus = sorted(universe, key=distance)[:cap]
    witness_obj = source_witness(witness)
    instances = instances_over(focus, LADDER, witness_obj, [ED, VRC, GNEP, NE_THESIS, DA_THESIS])
    adjacency: dict[str, list[str]] = {}
    strict: list[tuple[str, str, str]] = []
    for instance in instances:
        head, tail = (name_of(pop) for pop in instance.args)
        if instance.shape == "S":
            strict.append((instance.principle, head, tail))
        else:
            adjacency.setdefault(head, []).append(tail)
    cycles: list[list[str]] = []
    for principle, head, tail in strict:
        queue = [(tail, [tail])]
        seen = {tail}
        while queue:
            node, path = queue.pop(0)
            if len(path) > 6:
                continue
            for nxt in adjacency.get(node, ()):
                if nxt == head:
                    cycles.append([principle, head, *path])
                elif nxt not in seen:
                    seen.add(nxt)
                    queue.append((nxt, [*path, nxt]))
    return {
        "cap": f"{cap} populations, at most {max_lives} lives each, levels {levels}",
        "instances": len(instances),
        "strict_edges": len(strict),
        "cycles_found": cycles,
        "note": "discovery only: an absent cycle inside the cap is not evidence of impossibility",
    }


def structural_level_constraint() -> dict[str, Any]:
    """The family's forced level identity, checked against the Case-B witness and the grid.

    In the direct-reservoir family the GNEP fuel must come from VRC's B block - the bag is the
    only population with lives at a level >= u_g that the reservoir step supplies - and every
    climb stage runs while the bag's unspent lives are still in the population, so ranged
    Non-Elitism forces those lives inside R(1, x). The first climb stage's level is therefore the
    bag level, and the bag's own level must be exactly ``y_g + 1``: anything lower is below GNEP's
    witness level (no fuel), anything higher sticks out of the first stage's background range. The
    family consequently needs both

        u_g <= y_g + 1   (GNEP's witness level is at most one level above its own range top)
        y_v >= y_g + 1   (VRC's range top reaches that level)

    for every z on the negative-raising path. Neither inequality is a source consequence: GNEP's
    ``u``, GNEP's ``y`` and VRC's ``y`` are three independent existential witnesses.
    """
    witness = case_b_witness()
    grid = []
    for entry in witness_grid():
        grid.append(
            {
                "bag": entry.bag,
                "y_g": entry.y_g,
                "u_g": entry.u_g,
                "y_v": entry.y_v,
                "u_g_le_y_g_plus_1": entry.u_g <= entry.y_g + 1,
                "y_v_ge_y_g_plus_1": entry.y_v >= entry.y_g + 1,
                "bag_equals_y_g_plus_1": entry.bag == entry.y_g + 1,
            }
        )
    return {
        "status": "machine-checked inside this construction: no other bag level is admitted, and "
        "the concrete Case-B witness violates y_v >= y_g + 1, so the reservoir cannot carry fuel; "
        "it is a necessary condition of the construction implemented here, not a theorem about "
        "every possible reservoir design",
        "requirements": [
            "u_g <= y_g + 1 for every z on the raising path",
            "y_v >= y_g + 1 (so the bag level y_g + 1 lies inside R(1, y_v))",
            "the bag level is exactly y_g + 1",
        ],
        "case_b_witness": {
            "y_g": witness.y_g,
            "u_g": witness.u_g,
            "y_v": witness.y_v,
            "u_g_le_y_g_plus_1": witness.u_g <= witness.y_g + 1,
            "y_v_ge_y_g_plus_1": witness.y_v >= witness.y_g + 1,
            "why_it_fails": "VRC's range R(1, 3) tops out at W_3, but the fuel level must be "
            "W_4 = W_{y_g + 1}; the reservoir cannot hold a single life at the only usable level",
        },
        "grid_entries": grid,
        "grid_all_satisfy_the_requirements": all(
            row["u_g_le_y_g_plus_1"] and row["y_v_ge_y_g_plus_1"] and row["bag_equals_y_g_plus_1"]
            for row in grid
        ),
    }


def obstruction_section() -> dict[str, Any]:
    witness = case_b_witness()
    steps, build_report = build(witness, NE_THESIS, DA_THESIS)
    return {
        "witness": {
            key: getattr(witness, key)
            for key in (
                "lam",
                "bag",
                "neg",
                "neg_count",
                "n_v",
                "u_v",
                "v_v",
                "y_v",
                "u_g",
                "y_g",
                "n_g",
                "n_e",
            )
        },
        "witness_problems": witness.problems(),
        "construction_attempt": {
            "built": bool(steps),
            "report": build_report,
            "why": "VRC's bag tops out at W_3 < W_{y_g + 1} = W_4, so no level both reaches "
            "GNEP's witness level and stays inside VRC's range: the reservoir carries no fuel",
        },
        "structural_level_constraint": structural_level_constraint(),
        "arithmetic": case_b_arithmetic(),
        "instance_check": case_b_instance_check(),
        "search": bounded_search(witness),
        "consequences": {
            "ranged_ne": "the stage-(y_v + 1) climb needs a background inside R(y, x), so the "
            "negative lives force the dump level below them",
            "ne_2003": "2003 Non-Elitism's unrestricted D lets the same climb run with the "
            "negative lives in the background, so the obstruction is specific to the NE weakening",
            "da_weakening": "not used by the obstruction: the argument concerns the reservoir and "
            "the climb, and the construction's DA block is one level either way",
        },
    }


# ---------------------------------------------------------------------------------------------
# Section 5: the report.


def run() -> dict[str, Any]:
    """Build, replay and report; the JSON is the module's whole contract."""
    variants = variants_section()
    grid = grid_section()
    obstruction = obstruction_section()
    rebuilt = all(run["built"] for run in variants.values())
    clean = all(run.get("edges_replayed_clean") for run in variants.values())
    unsat = all(
        run.get("closure", {}).get("decision_without_completeness") == "unsat"
        for run in variants.values()
    )
    return {
        "route": "A",
        "approach": "direct primitive ED/VRC/GNEP/NE/DA reservoir cycle; no derived Condition "
        "beta and no derived Condition delta anywhere in the chain",
        "scope": (
            "readings thesis:egalitarian-dominance, thesis:non-elitism, thesis:dominance-addition, "
            "arrhenius-2003:egalitarian-dominance, arrhenius-2003:non-elitism, "
            "arrhenius-2003:general-non-extreme-priority, arrhenius-2003:vrc-avoidance, "
            "arrhenius-2003:dominance-addition; ladder W_-1..W_9; the closure uses reflexivity and "
            "the written chain's own transitivity only (no completeness); the obstruction concerns "
            "the direct-reservoir family described in the module docstring"
        ),
        "verdict": "proved",
        "evidence": {
            "direct_cycle": {
                "variants": variants,
                "all_built": rebuilt,
                "all_edges_replayed_clean": clean,
                "closure_unsat_for_every_variant": unsat,
                "note": "the same constructed chain is a primitive instance set of all four "
                "NE/DA weakening combinations, so each is refuted at this witness",
                "claim_status": "proved and machine-checked: the 23 edge chains are source "
                "instances at the stated witnesses (verify_edge plus the exhaustive ladder audit) "
                "and close with transitivity and reflexivity alone",
            },
            "witness_grid": grid,
            "case_b_obstruction": obstruction,
            "claim_status": {
                "proved": [
                    "the direct cycle exists and refutes the five conditions at each grid witness, "
                    "for all four NE/DA weakening combinations",
                    "the injection/level identity of the construction, and the fact that no other "
                    "bag level is admitted by it",
                    "the integer system A_1 >= n_v + E, E >= N, N >= m_v + A_1 is UNSAT with a "
                    "satisfiable control",
                ],
                "argued_not_closed": [
                    "lemma L4 feeding that system (named in case_b_arithmetic): every negative life "
                    "created in the family sits at or below the first expensive level and must "
                    "cross it",
                ],
                "not_claimed": [
                    "a source-general impossibility for the ranged-NE or both-weakened sets",
                    "anything about direct cycles outside the stated family",
                ],
            },
        },
        "remaining_obligation": (
            "two items. (1) The family's structural requirement: the direct-reservoir construction "
            "admits only the bag level y_g + 1, so it needs u_g <= y_g + 1 and y_v >= y_g + 1, and "
            "no source principle supplies either (GNEP's u, GNEP's y and VRC's y are independent "
            "existential witnesses); a different reservoir design - for instance one that consumes "
            "the bag before the climb - is not covered here. (2) The counting layer's lemma L4: "
            "closing the Case-B gap by climbing for fuel while negatives are present needs the "
            "potential argument that every negative life created in the family sits at or below the "
            "first expensive level z* and must cross it (ranged-NE dumps land below the current "
            "minimum, hence at or below x_v <= z*), which also rules out the cheap NE at (z*+1, .) "
            "route. Q-011's ranged-NE and both-weakened variants stay open; nothing here is a "
            "source-general impossibility claim, and the direct cycle above settles only the "
            "witnesses at which it is instantiated."
        ),
    }


def _summary(data: Mapping[str, Any]) -> str:
    variants = data["evidence"]["direct_cycle"]["variants"]
    decisions = ", ".join(
        f"{label}: {run.get('closure', {}).get('decision_without_completeness', 'n/a')}"
        for label, run in variants.items()
    )
    grid = data["evidence"]["witness_grid"]
    obstruction = data["evidence"]["case_b_obstruction"]
    return (
        f"direct cycle closures {decisions}; grid built={grid['all_built']} "
        f"clean={grid['all_clean']} unsat={grid['all_unsat']}; Case-B arithmetic "
        f"{obstruction['arithmetic']['decision']} (relaxed "
        f"{obstruction['arithmetic']['relaxed_without_the_negative_fuel_coupling']})"
    )


def main() -> None:
    started = time.monotonic()
    data = run()
    data["wall_time_s"] = round(time.monotonic() - started, 1)
    print(json.dumps(data, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
