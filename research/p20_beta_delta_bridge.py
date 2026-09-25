"""Phase 20: Route A, an alternative high-level placement for the phase-19 beta/delta bridge.

Phase 19 closes the repaired five-edge chain ``M ⪰ M1 ⪰ P2 ≻ P1 ⪰ M3 ⪰ M`` but can only
instantiate it with beta's A level *nested* at delta's A level, forcing ``n_beta = n_delta +
n_v`` and the count cycle ``n_beta = n_delta + n_v >= n_delta = m_delta*n_chi >= m_delta =
m_beta + m_vrc > m_beta > n_beta``.  It records a second, unused branch - delta's A lives inside
beta's permitted background ``D subset R(z_beta, y_beta+1)`` - and dismisses it because that
needs ``x_delta <= y_beta + 1 <= y_vrc + 1``, a bound "no source condition supplies".

This phase shows the dismissal is too strong, and quantifies exactly where the bridge does and
does not work.

1. **The bound is on delta's A *level*, which is free.**  Condition delta quantifies
   ``forall x >= u`` over A's level, so its A may sit at *any* level ``a >= u_delta``; the source
   fixes no relation between ``a`` and VRC's range top ``y_vrc``.  Choosing the smallest legal
   ``a = u_delta`` and beta's middle level ``beta = a - 1`` puts delta's high lives inside
   beta's ranged background ``R(z_beta, y_beta+1) = R(c, a)``, and the shared population ``M`` is
   no longer forced to nest.  ``bound_placement`` builds that chain
   from the axiology's own witnesses; ``run`` replays every one of its five edges with two
   independent checkers (``p18.verify_edge`` and ``ladder.audit``), audits the beta edge against
   the *ranged* reading as well, and decides the closure on the frozen ladder *plus* W_7..W_9.
   It closes UNSAT for both Dominance Addition forms and for both Non-Elitism readings.

2. **Why phase 19's searches could not have seen it: an arithmetic fact.**  The bound placement
   needs ``a <= y_vrc``, ``u_vrc > y_vrc``, VRC's A level ``z >= u_vrc``, ED's successor
   ``z+1``, and a Dominance-Addition threshold above that; the smallest legal instance therefore
   has ``y_vrc >= u_delta >= 4``, ``z >= 5`` and a beta top level ``alpha >= z + 2 >= 7``.
   ``level_budget`` proves ``alpha >= 7`` over the integers: one level above the frozen ladder's
   top W_6.  No search over W_-1..W_6 can exhibit this chain, and at the *frozen* witness the
   placement is additionally unavailable because ``y_vrc = 3 < u_delta = 4``.

3. **A quantified no-go for the bridge where the placement is unavailable.**  The bound
   placement exists exactly when ``y_vrc >= u_delta`` (it needs a level ``a`` with
   ``u_delta <= a <= y_vrc``).  When ``y_vrc < u_delta`` - a genuine two-parameter family, since
   all that is forced is ``y_vrc >= 3`` and ``u_delta >= 4``, so ``(3, 4)``, ``(4, 5)``,
   ``(3, 7)`` and so on are all legal - every legal ``a >= u_delta`` exceeds ``y_vrc``, so
   delta's A lives can only sit at beta's A level: ``alpha = a``, ``A_delta subset A_beta``,
   hence ``n_delta <= n_beta``.  The two remaining ways to place beta's low level ``c`` both
   fail: at ``c`` equal to VRC's negative level the count at ``c`` reads ``m_delta + E[c] =
   m_beta + D_beta[c]``, the Dominance-Addition leg forces ``E`` to have no negative life, so
   ``m_delta = m_beta + D_beta[c] >= m_beta``, and with delta's derived ``n_delta =
   m_delta*n_chi`` (thesis Lemma 5.2.1 gives ``n_chi = sum of r = 3 - z GNEP counts >= 4`` at
   ``z = -1``) and beta's strictness ``m_beta > n_beta`` the integer system
   ``count_certificates`` decides - a system with no ``y_vrc`` in it - is UNSAT; at ``c`` below
   VRC's negative level beta's B lands on a level of delta's background ``E``, so ``E`` carries
   a negative life and no Dominance Addition instance exists for ``M1 = B_d union D_d union E``.
   So no chain of *this* architecture closes for any pair with ``y_vrc < u_delta``: the bridge is
   not repairable by placement alone in that regime.

4. **The derived edges are expanded into primitive instances.**  ``primitive_report`` replaces
   Conditions beta and delta by their expansions at the same witness: 15 primitive Non-Elitism
   instances in four Lemma 1.1/1.2 blocks carrying 1, 2, 4 and 8 instances whose outputs sum to
   ``m_beta = 15 = 1+2+4+8`` at ``n_beta = 1`` (``r = alpha - beta_low = 4``), and
   ``m_d * (3 - c) = 16 * 4 = 64`` primitive GNEP instances in sixteen disjoint Lemma 5.2.1/5.2.2
   copies.  With ED, VRC and Dominance Addition that is an 82-edge chain, each edge replayed by
   ``p18.verify_edge`` and ``ladder.audit`` (and each Non-Elitism edge additionally audited under
   the ranged reading), closing UNSAT under the mentioned-atom solver, the pure-Python DPLL and
   the phase-16 compact checker for both Dominance Addition forms.

   The recurrence *fixes* that count at this witness: under the uniform Non-Elitism witness
   ``p = 1`` the expansion realizes ``m_beta = 15`` and nothing in it supplies another value, so
   ``witness_kind`` marks whether a row is ``primitive-expansion`` (exactly the recurrence value,
   the only kind ``primitive_chain`` will expand) or ``derived-beta-witness`` (Condition beta
   assumed at a different witness, with no primitive claim made and no expansion emitted).

What this phase does and does not establish.  The positive half is a fixed-witness certificate:
an audited, independently replayed chain whose instances are legal source instances at one
chosen witness (with the two derived conditions expanded primitively), so it neither proves nor
refutes Q-011's source-general question.  The negative half is a no-go for the one repaired
architecture (the shared-population bridge) in the regime ``y_vrc < u_delta`` - a two-parameter
family, so ``y_vrc = 3, u_delta = 4`` (the frozen witness) is one member and not the whole of it:
it does not exclude a chain that avoids the shared population, and that regime is the remaining
obligation.  Nothing here is a new source principle, a consistency claim or a model; no source
checker is altered.

Scope/domain: the ladder W_-1..W_9 (the frozen ladder is W_-1..W_6; the extension is stated
because the placement provably needs W_7), the frozen readings (corpus/readings.toml) with the
phase-18 manifest, and the derived Conditions beta and delta at the count laws that manifest
records.
"""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

import z3  # type: ignore[import-untyped]

from research.lab import Engine, background, dpll_check
from research.ladder import Ladder, Witness, audit, validate
from research.p6_schema import core_constraints, name_of
from research.p17_vrc_boundary import (
    DA_2003,
    DA_THESIS,
    ED,
    GNEP,
    NE_2003,
    NE_THESIS,
    VRC,
)
from research.p18_vrc_certificate import BETA, DELTA, Edge, verify_edge
from research.p19_vrc_universal import verify_beta_ranged
from research.schema import Instance, Pop

# The frozen search ladder is W_-1..W_6 (research/p8_catalogue.LADDER).  The bound placement
# provably needs W_7 (see ``level_budget``), so this phase states its own domain.
BRIDGE_LADDER = Ladder(negative=1, positive=9)
FROZEN_TOP = 6

THESIS_BETA = "thesis:condition-beta"


def _pop(*pairs: tuple[int, int]) -> Pop:
    """The population holding ``count`` lives at each ``level``."""
    return tuple(sorted(level for level, count in pairs for _ in range(count)))


def _counts(pop: Pop) -> list[list[int]]:
    return [[level, count] for level, count in sorted(Counter(pop).items())]


# ---------------------------------------------------------------------------------------------
# Section 0: the primitive-expansion counts of the two derived conditions.
#
# Research/p18_vrc_certificate.SOURCE_MANIFEST records the derivations the bridge uses.  BETA:
# "Lemma 1.1: n applications of Non-Elitism with each C_i of size p+1 and each B_i of size p
# give alpha with m = n*p ... alpha implies beta (Lemma 1.2: r = x - y applications of alpha
# with m_i >= f(m_{i-1}) and f(m_i) = m_0+...+m_i, so m = m_1+...+m_r > m_0 = n)".  DELTA:
# "GNEP implies chi (thesis Lemma 5.2.1 with r = 3 - z applications of GNEP at W_{z+(i-1)},
# i = 1..r, and chi's n = n_1+...+n_r), and chi implies delta (thesis Lemma 5.2.2 with m copies
# of chi, so delta's n = m * n_chi)".  The helpers below turn those recurrences into explicit
# finite step counts, so a beta or delta count is *derived* rather than asserted.


def beta_expansion(n: int, r: int, p: int = 1) -> dict[str, Any]:
    """The greedy Lemma 1.1/1.2 expansion of Condition beta at ``n`` lives and ``r`` steps.

    ``r = x_beta - y_beta`` is the number of Condition alpha applications inside Lemma 1.2, and
    ``p`` is the Non-Elitism witness Lemma 1.1 consumes (``B_i`` of size ``p``, ``C_i`` of size
    ``p+1``).  The recurrence the manifest records is ``m_0 = n`` and ``m_i = m_0 + ... +
    m_{i-1}``, so ``m_i = 2**(i-1) * n`` and beta's ``m = m_1 + ... + m_r = (2**r - 1) * n``:
    the smallest count the recurrence realizes.  The manifest writes ``m_i >= f(m_{i-1})``, so a
    larger ``m`` is equally realizable, and the bridge's populations simply grow with it.
    """
    counts = [n]
    steps = []
    for i in range(1, r + 1):
        output = sum(counts)
        counts.append(output)
        steps.append(
            {
                "step": i,
                "input_m": counts[i - 1],
                "output_m": output,
                "beta_m_after_step": sum(counts[1:]),
                "ne_B_size": p,
                "ne_C_size": p + 1,
            }
        )
    return {
        "n": n,
        "r": r,
        "ne_witness_p": p,
        "steps": steps,
        "greedy_m": sum(counts[1:]),
        "closed_form": f"(2**{r} - 1) * {n}",
    }


def delta_expansion_n(m: int, z: int, n_g: int) -> int:
    """The thesis Lemma 5.2.1/5.2.2 count: ``r = 3 - z`` GNEP counts summed, then m copies."""
    return m * (3 - z) * n_g


# ---------------------------------------------------------------------------------------------
# Section 1: the bound placement, read off the axiology's own witnesses.


@dataclass(frozen=True)
class Placement:
    """Levels and counts of the bound-placement bridge for one legal witness choice.

    VRC contributes ``n_v``, ``m_v``, ``u_v``, ``v_v``, ``y_v`` and the negative level ``x_v``.
    Condition delta contributes ``u_g``, ``y_g`` (its GNEP-derived witness levels) and the count
    law ``n_d = m_d * n_chi``; ``n_chi = (3 - z) * n_gnep`` follows from thesis Lemma 5.2.1-5.2.2.
    Condition beta is instantiated at ``n_b`` with ``m_b = n_b + step``.

    The placement fixes the free level choices: VRC's A sits at the lowest legal level
    ``z_v = u_v``, delta's A at the lowest legal level ``a = u_g``, beta's middle level one below
    it (``beta_low = a - 1``, so beta's ranged background ``R(c, beta_low + 1) = R(c, a)`` admits
    delta's A level), beta's low level ``c`` at VRC's negative level, and beta's top level
    ``alpha`` two above VRC's A level so the Dominance Addition threshold ``x = alpha`` has an
    A (= P2) strictly below it.
    """

    n_v: int
    m_v: int
    u_v: int
    v_v: int
    y_v: int
    x_v: int
    u_g: int
    y_g: int
    n_g: int
    n_b: int
    m_b: int
    n_chi: int
    witness_kind: str = "primitive-expansion"

    # -- the derived level and count choices -------------------------------------------------
    @property
    def z_v(self) -> int:
        return self.u_v

    @property
    def a(self) -> int:
        """delta's A level, chosen at its lowest legal value ``u_delta``."""
        return self.u_g

    @property
    def beta_low(self) -> int:
        """beta's middle level ``y_beta``: one below delta's A level."""
        return self.a - 1

    @property
    def alpha(self) -> int:
        """beta's top level ``x_beta``: two above VRC's A level."""
        return self.z_v + 2

    @property
    def c(self) -> int:
        """Condition delta's negative level, normalised to VRC's negative level."""
        return self.x_v

    @property
    def m_d(self) -> int:
        return self.m_b + self.m_v

    @property
    def n_d(self) -> int:
        """delta's n from the GNEP derivation: ``n = m * n_chi``."""
        return self.m_d * self.n_chi

    @property
    def precondition_met(self) -> bool:
        """The bound placement needs delta's smallest legal A level to fit VRC's B range."""
        return self.u_g <= self.y_v

    @property
    def r_beta(self) -> int:
        """Lemma 1.2's step count for this beta instance: ``r = x_beta - y_beta``."""
        return self.alpha - self.beta_low

    @property
    def beta_expansion(self) -> dict[str, Any]:
        return beta_expansion(self.n_b, self.r_beta)

    @property
    def primitive_expansion_available(self) -> bool:
        """Whether the manifest's expansion supplies exactly this ``m_b``."""
        return self.witness_kind == "primitive-expansion"

    def derivation_problems(self) -> list[str]:
        """Check the two counts against the primitive expansions the manifest records.

        Under uniform Non-Elitism witness ``p`` the Lemma 1.1/1.2 recurrence *fixes* beta's count
        at ``m = (2**r - 1) * n_b`` for ``r = alpha - beta_low``: the greedy chain
        ``m_0 = n_b``, ``m_i = m_0 + ... + m_{i-1}`` is what the derivation realizes, and nothing
        in it supplies a larger value.  A row carrying a larger ``m_b`` is therefore labelled
        ``witness_kind = "derived-beta-witness"``: it assumes Condition beta at that witness and
        makes no primitive claim.  Delta's ``n_chi`` is the sum of the ``r = 3 - z`` GNEP counts,
        which under the project's uniform GNEP witness equals ``(3 - z) * n_g``.
        """
        problems: list[str] = []
        exact = self.beta_expansion["greedy_m"]
        if self.primitive_expansion_available:
            if self.m_b != exact:
                problems.append(
                    f"primitive-expansion rows must use the exact recurrence m_b={exact} at "
                    f"n_b={self.n_b}, r={self.r_beta}; got {self.m_b}. Use witness_kind="
                    f"'derived-beta-witness' to assume a different beta witness instead"
                )
        elif self.m_b < exact:
            problems.append(
                f"beta m_b={self.m_b} is below the expansion value {exact} at n_b={self.n_b}, "
                f"r={self.r_beta}"
            )
        floor = 3 - self.c
        if self.n_chi < floor:
            problems.append(
                f"delta n_chi={self.n_chi} is below the {floor} GNEP counts at z={self.c}"
            )
        uniform = delta_expansion_n(1, self.c, self.n_g)
        if self.n_chi != uniform:
            problems.append(
                f"delta n_chi={self.n_chi} is not the uniform-witness value {uniform} = "
                f"(3 - z) * n_g at z={self.c}"
            )
        if self.n_d != self.m_d * self.n_chi:
            problems.append("delta needs n_d = m_d * n_chi")
        return problems

    def problems(self) -> list[str]:
        problems: list[str] = []
        if not self.u_v > self.y_v >= 3:
            problems.append("VRC needs u_v > y_v >= 3")
        if not self.u_g > self.y_g >= 3:
            problems.append("delta needs u_g > y_g >= 3")
        if self.x_v >= 0:
            problems.append("VRC's negative level must be negative")
        if min(self.n_v, self.m_v, self.n_g, self.n_b, self.n_chi) < 1:
            problems.append("every count must be positive")
        if self.m_b <= self.n_b:
            problems.append("beta needs m > n")
        if not self.precondition_met:
            problems.append(
                f"bound placement needs u_g <= y_v, got u_g={self.u_g} > y_v={self.y_v}"
            )
        if self.alpha <= self.beta_low:
            problems.append("beta needs x > y")
        if self.beta_low <= self.c:
            problems.append("beta needs y > z")
        return problems


def bound_placement(
    *,
    n_v: int,
    m_v: int,
    u_v: int,
    v_v: int,
    y_v: int,
    x_v: int,
    u_g: int,
    y_g: int,
    n_g: int,
    n_b: int,
    m_b: int,
    n_chi: int,
    witness_kind: str = "primitive-expansion",
) -> Placement:
    return Placement(n_v, m_v, u_v, v_v, y_v, x_v, u_g, y_g, n_g, n_b, m_b, n_chi, witness_kind)


def _witness(p: Placement) -> Witness:
    """The source witness carried by every replay: four readings plus the two derived ones."""
    return Witness(
        {
            "condition-beta": {"step": p.m_b - p.n_b, "mult": 1},
            "condition-delta": {"u": p.u_g, "y": p.y_g, "n": p.n_chi, "n_per_m": p.n_chi},
            "vrc-avoidance": {
                "x": p.x_v,
                "u": p.u_v,
                "v": p.v_v,
                "y": p.y_v,
                "n": p.n_v,
                "m": p.m_v,
            },
            "non-elitism": {"n": 1},
            "general-non-extreme-priority": {"u": p.u_g, "y": p.y_g, "n": p.n_g},
        }
    )


def bridge_populations(p: Placement) -> dict[str, Pop]:
    """The five relata of the cycle ``P2 ≻ P1 ⪰ M3 ⪰ M ⪰ M1 ⪰ P2``.

    ``M`` is simultaneously delta's left side and beta's right side; on the bound placement its
    high lives sit in beta's background ``D_b = n_d @ a + m_v @ c`` rather than in beta's A, so
    ``n_b`` is independent of ``n_d``.
    """
    d_b = _pop((p.a, p.n_d), (p.c, p.m_v))
    m = _pop((p.alpha, p.n_b), (p.c, p.m_b)) + d_b
    m3 = _pop((p.beta_low, p.m_b + p.n_b)) + d_b
    m1 = _pop((3, p.n_d + p.m_d), (p.alpha, p.n_b))
    return {
        "P1": _pop((p.z_v, p.n_v)),
        "P2": _pop((p.z_v + 1, p.n_v)),
        "M3": tuple(sorted(m3)),
        "M": tuple(sorted(m)),
        "M1": m1,
    }


def bridge_edges(p: Placement, da_form: str) -> list[Edge]:
    """The five written edges: ED, Dominance Addition, delta, beta, VRC."""
    pops = bridge_populations(p)
    dominance = (
        Edge(DA_2003, pops["M1"], pops["P2"])
        if da_form == DA_2003
        else Edge(DA_THESIS, pops["P2"], pops["M1"])
    )
    return [
        Edge(ED, pops["P2"], pops["P1"]),
        dominance,
        Edge(
            DELTA,
            _pop((p.a, p.n_d), (p.c, p.m_d)),
            _pop((3, p.n_d), (3, p.m_d)),
            _pop((p.alpha, p.n_b)),
            witness={"u": p.u_g, "y": p.y_g, "n": p.n_chi, "n_per_m": p.n_chi},
        ),
        Edge(
            BETA,
            _pop((p.beta_low, p.m_b + p.n_b)),
            _pop((p.alpha, p.n_b), (p.c, p.m_b)),
            _pop((p.a, p.n_d), (p.c, p.m_v)),
            witness={"step": p.m_b - p.n_b, "mult": 1},
        ),
        Edge(
            VRC,
            pops["P1"],
            pops["M3"],
            witness={
                "x": p.x_v,
                "u": p.u_v,
                "v": p.v_v,
                "y": p.y_v,
                "n": p.n_v,
                "m": p.m_v,
            },
        ),
    ]


def cycle_states(p: Placement) -> list[str]:
    pops = bridge_populations(p)
    return [
        name_of(pops["P2"]),
        name_of(pops["P1"]),
        name_of(pops["M3"]),
        name_of(pops["M"]),
        name_of(pops["M1"]),
        name_of(pops["P2"]),
    ]


# ---------------------------------------------------------------------------------------------
# Section 2: independent replay and closure for the placement.


def closure_decisions(steps: Sequence[Instance], tag: str, states: Sequence[str]) -> dict[str, Any]:
    """Decide the cycle with reflexivity, the cycle's transitivity and its own edges.

    Three decision procedures are run and must agree: the Z3 ``Engine`` over the full relata, Z3
    over only the mentioned weak atoms, and the pure-Python DPLL.  Completeness is never used.
    """
    names = tuple(dict.fromkeys(states))
    hard = [
        *background(names)["reflexivity"],
        *background(names)["transitivity"],
        *core_constraints(list(steps), tag),
    ]
    full = Engine(names, hard, timeout_ms=60000).check()
    from research.p18_vrc_certificate import chain_transitivity

    cycle = [*chain_transitivity(states), *core_constraints(list(steps), f"{tag}/cycle")]
    mentioned = _decide_mentioned(cycle)
    dpll, _ = dpll_check([constraint.formula for constraint in cycle])
    if full.decision == "unknown":
        raise RuntimeError(f"engine returned unknown: {full.reason}")
    if not (full.decision == mentioned == dpll):
        raise AssertionError(f"disagreement: full {full.decision}, mentioned {mentioned}, {dpll}")
    return {
        "engine": full.decision,
        "mentioned_atoms": mentioned,
        "dpll": dpll,
        "relata": len(names),
        "completeness_used": False,
    }


def _decide_mentioned(hard: Sequence[Any]) -> str:
    from population_ethics.relations import encode_z3
    from research.lab import _atoms

    atoms = {atom for constraint in hard for atom in _atoms(constraint.formula)}
    variables = {atom: z3.Bool(f"w_{i}") for i, atom in enumerate(sorted(atoms, key=str))}
    solver = z3.Solver()
    solver.add(*(encode_z3(constraint.formula, variables) for constraint in hard))
    status = solver.check()
    if status == z3.unknown:
        raise RuntimeError(f"mentioned-atom solve unknown: {solver.reason_unknown()}")
    return "sat" if status == z3.sat else "unsat"


def replay(p: Placement, ladder: Ladder = BRIDGE_LADDER) -> dict[str, Any]:
    """Replay and close the bound-placement bridge for both Dominance Addition forms.

    Every edge is checked twice - ``p18.verify_edge`` against the frozen manifest, and
    ``ladder.audit`` re-deriving applicability from the populations alone - and the beta edge is
    additionally audited against the *ranged* reading, which is the form the ranged Thesis
    Non-Elitism derives.
    """
    witness = _witness(p)
    problems = p.problems()
    out: dict[str, Any] = {
        "problems": problems,
        "derivation": {
            "problems": p.derivation_problems(),
            "witness_kind": p.witness_kind,
            "primitive_expansion_available": (
                p.primitive_expansion_available and p.m_b == p.beta_expansion["greedy_m"]
            ),
            "beta": p.beta_expansion,
            "delta": {
                "z": p.c,
                "n_g": p.n_g,
                "m_d": p.m_d,
                "n_d": p.n_d,
                "n_chi": p.n_chi,
                "uniform_value": delta_expansion_n(1, p.c, p.n_g),
                "law": "n_d = m_d * n_chi with n_chi = sum of r = 3 - z GNEP counts",
            },
        },
        "populations": {},
        "edges": {},
        "closures": {},
    }
    if problems:
        return out
    pops = bridge_populations(p)
    out["populations"] = {key: _counts(pop) for key, pop in pops.items()}
    for da_form in (DA_2003, DA_THESIS):
        edges = bridge_edges(p, da_form)
        rows: dict[str, Any] = {}
        for edge in edges:
            record = edge.record()
            rows[edge.principle] = {
                "record": record,
                "verify_edge": verify_edge(record, ladder, witness),
                "ladder_audit": audit(edge.instance, ladder, witness),
            }
        beta_edge = edges[3]
        rows[BETA]["ranged_replay"] = verify_beta_ranged(beta_edge.record(), ladder)
        rows[BETA]["ranged_ladder_audit"] = audit(
            Instance(THESIS_BETA, beta_edge.instance.args), ladder, witness
        )
        out["edges"][da_form] = rows
        out["closures"][da_form] = closure_decisions(
            [edge.instance for edge in edges], f"p20-beta-delta-bridge/{da_form}", cycle_states(p)
        )
    out["witness"] = {key: dict(value) for key, value in witness.params.items()}
    out["ranged_ne_variant"] = {
        "note": "the same five edges serve the ranged reading: the beta edge's background "
        "D_b = n_d @ a + m_v @ c lies inside R(c, beta_low + 1) = R(c, a) by construction",
        "beta_background": _counts(_pop((p.a, p.n_d), (p.c, p.m_v))),
        "ranged_range": [p.c, p.beta_low + 1],
    }
    return out


def all_clean(report: Mapping[str, Any]) -> bool:
    if report.get("problems") or report["derivation"]["problems"]:
        return False
    for rows in report["edges"].values():
        for row in rows.values():
            if row["verify_edge"] or not row["ladder_audit"]:
                return False
            if row.get("ranged_replay") or row.get("ranged_ladder_audit") is False:
                return False
    return all(entry["engine"] == "unsat" for entry in report["closures"].values())


def primitive_chain(p: Placement, da_form: str, ne_principle: str = NE_2003) -> list[Edge]:
    """The full primitive expansion at this witness: ED, VRC, DA plus every NE and GNEP edge.

    The beta leg is Lemma 1.1/1.2's expansion.  ``r = alpha - beta_low`` blocks climb beta's C
    from ``beta_low`` to ``alpha``: the block at level ``h`` carries ``n_b * 2**(h - beta_low - 1)``
    Non-Elitism instances, each turning ``2`` lives at ``W_{h-1}`` into one at ``W_h`` and one at
    beta's low level ``c``; the counts sum to ``(2**r - 1) * n_b = m_b``, matching the beta edge's
    B.  The delta leg is Lemma 5.2.1/5.2.2's expansion: ``m_d`` disjoint copies of the
    ``r = 3 - c``-step GNEP climb, each step exchanging ``n_g`` lives at level ``a`` for ``n_g``
    in ``R(1, y_g)`` and walking one life from ``c`` up to ``W_3``; the edge count is
    ``m_d * (3 - c)`` and the totals land exactly on the delta edge's endpoints.

    Every edge is a legal primitive source instance at this witness: the Non-Elitism edges are
    created by ``ne_principle`` (both readings accept them, since every background lies inside
    ``R(c, level)``), and the GNEP edges carry an unrestricted background.
    """
    pops = bridge_populations(p)
    exact = p.beta_expansion["greedy_m"]
    if not p.primitive_expansion_available or p.m_b != exact:
        raise AssertionError(
            f"the primitive expansion realizes beta's m = {exact} exactly at n_b={p.n_b}, "
            f"r={p.r_beta}; a placement with m_b={p.m_b} has no primitive expansion here"
        )
    edges: list[Edge] = [Edge(ED, pops["P2"], pops["P1"])]
    edges.append(
        Edge(
            VRC,
            pops["P1"],
            pops["M3"],
            witness={
                "x": p.x_v,
                "u": p.u_v,
                "v": p.v_v,
                "y": p.y_v,
                "n": p.n_v,
                "m": p.m_v,
            },
        )
    )

    def bag(counts: Counter[int]) -> Pop:
        return tuple(sorted(counts.elements()))

    current = Counter(pops["M3"])
    for index in range(p.r_beta):
        level = p.beta_low + 1 + index
        count = p.n_b * 2 ** (p.r_beta - 1 - index)
        for _ in range(count):
            left_part = Counter({level - 1: 2})
            right_part = Counter({level: 1, p.c: 1})
            background_counts = current - left_part
            if any(value < 0 for value in background_counts.values()):
                raise AssertionError("the Non-Elitism expansion ran out of lives")
            edges.append(
                Edge(
                    ne_principle,
                    bag(left_part),
                    bag(right_part),
                    bag(background_counts),
                    witness={"x": level, "y": p.c, "n": 1},
                )
            )
            current = background_counts + right_part
    if current != Counter(pops["M"]):
        raise AssertionError("the Non-Elitism leg does not land on the beta edge's right endpoint")

    for _copy in range(p.m_d):
        for index in range(3 - p.c):
            z = p.c + index
            left_part = Counter({p.a: p.n_g, z: 1})
            right_part = Counter({3: p.n_g})
            right_part[z + 1] += 1
            background_counts = current - left_part
            if any(value < 0 for value in background_counts.values()):
                raise AssertionError("the GNEP expansion ran out of lives")
            edges.append(
                Edge(
                    GNEP,
                    bag(left_part),
                    bag(right_part),
                    bag(background_counts),
                    witness={"z": z, "u": p.u_g, "y": p.y_g, "n": p.n_g},
                )
            )
            current = background_counts + right_part
    if current != Counter(pops["M1"]):
        raise AssertionError("the GNEP leg does not land on the delta edge's right endpoint")

    edges.append(
        Edge(DA_2003, pops["M1"], pops["P2"])
        if da_form == DA_2003
        else Edge(DA_THESIS, pops["P2"], pops["M1"])
    )
    head, closing = edges[:-1], edges[-1]
    for edge, following in zip(head[:-1], head[1:], strict=True):
        if edge.right != following.left:
            raise AssertionError(f"the primitive chain is not linked at {edge.principle}")
    if da_form == DA_2003:
        # (2*) is a path edge: it continues the path and closes it on the strict head edge.
        if closing.left != head[-1].right or closing.right != edges[0].left:
            raise AssertionError("the primitive chain does not close on Dominance Addition")
    elif closing.right != head[-1].right or closing.left != edges[0].left:
        # The thesis (not-worse) instance is N-shaped: it is written A = P2 against B union C =
        # M1 across the closing gap, so it sits between the path's last node and its first.
        raise AssertionError("the thesis Dominance Addition edge does not close the path")
    return edges


def primitive_closure(edges: Sequence[Edge], tag: str) -> dict[str, Any]:
    """Decide the primitive chain along its own path, without completeness.

    The path transitivity, the mentioned weak atoms, the pure-Python DPLL and the phase-16
    compact checker are each run independently and must agree.  No all-pairs transitivity is
    asserted, so the decision is exactly what the source proof consumes.
    """
    from research.p16_ne_top import decide_without_completeness
    from research.p18_vrc_certificate import chain_transitivity

    steps = [edge.instance for edge in edges]
    # Path nodes come from the endpoints, not from each edge's left: the N-shaped thesis
    # Dominance Addition edge is written (A, B union C) across the closing gap, so its left is
    # the path's *first* node while its right is the path's last.
    states = [name_of(edges[0].left)]
    for edge in edges:
        if name_of(edge.right) != states[-1]:
            states.append(name_of(edge.right))
    if states[-1] != states[0]:
        states.append(states[0])
    hard = [*chain_transitivity(states), *core_constraints(steps, tag)]
    mentioned = _decide_mentioned(hard)
    dpll, _ = dpll_check([constraint.formula for constraint in hard])
    compact = decide_without_completeness(steps, tag)
    if not (mentioned == dpll == compact):
        raise AssertionError(f"primitive closure disagrees: {mentioned}, {dpll}, {compact}")
    return {
        "instances": len(steps),
        "states": len(states),
        "strict_edges": sum(step.shape == "S" for step in steps),
        "mentioned_atom_decision": mentioned,
        "dpll_decision": dpll,
        "p16_compact_checker_decision": compact,
        "completeness_used": False,
    }


def primitive_report(p: Placement, ladder: Ladder = BRIDGE_LADDER) -> dict[str, Any]:
    """Replay and close the full primitive chain for both Dominance Addition forms.

    Replaces the derived beta and delta edges by their primitive expansions, so no edge's
    legality rests on a derived condition that is not itself expanded: ED and VRC and DA are
    primitive source conditions, and every other edge is a primitive Non-Elitism or GNEP
    instance audited at this witness.  Each Non-Elitism edge is additionally audited under the
    ranged reading, which is what the ranged Thesis Non-Elitism demands.
    """
    witness = _witness(p)
    out: dict[str, Any] = {"problems": p.problems() + p.derivation_problems(), "runs": {}}
    if out["problems"]:
        return out
    for da_form in (DA_2003, DA_THESIS):
        edges = primitive_chain(p, da_form)
        failures: list[dict[str, Any]] = []
        for index, edge in enumerate(edges):
            record = edge.record()
            problems = verify_edge(record, ladder, witness)
            instance = edge.instance
            audited = audit(instance, ladder, witness)
            ranged = (
                audit(Instance(NE_THESIS, instance.args), ladder, witness)
                if edge.principle == NE_2003
                else True
            )
            if problems or not audited or not ranged:
                failures.append(
                    {
                        "index": index,
                        "principle": edge.principle,
                        "problems": problems,
                        "audit": audited,
                        "ranged_audit": ranged,
                    }
                )
        out["runs"][da_form] = {
            "edges": len(edges),
            "per_principle": dict(Counter(edge.principle for edge in edges)),
            "failures": failures,
            "closure": primitive_closure(edges, f"p20-primitive/{da_form}"),
        }
    return out


# ---------------------------------------------------------------------------------------------
# Section 3: the arithmetic.  Placement forcing, the level budget, and the two count systems.


def level_budget() -> dict[str, Any]:
    """Prove over the integers that the bound placement needs a level above the frozen ladder.

    Variables and source-facing constraints: VRC's A level ``z >= u_v``; ``u_v > y_v``; ED's
    successor ``z+1``; delta's A level ``a >= u_g >= 4`` with ``a <= y_v`` (the placement's
    precondition); beta's middle level ``beta = a - 1`` and top level ``alpha > beta`` with
    ``alpha >= z + 2`` (the Dominance-Addition threshold must clear P2's level).  The smallest
    legal ``alpha`` is then at least 7, one above the frozen ladder's top W_6.
    """
    u_g, y_v, u_v, z, a, beta, alpha = z3.Ints("u_g y_v u_v z a beta alpha")
    base = [
        u_g >= 4,  # GNEP's u is positive with u > y >= 3
        y_v >= 3,  # VRC's B range R(1, y) needs at least three levels
        u_v > y_v,  # VRC's u > y
        z >= u_v,  # VRC's A level is at or above u
        a >= u_g,  # delta's x >= u
        a <= y_v,  # the placement: delta's A lives inside VRC's B range
        beta == a - 1,  # beta's middle level one below delta's A
        beta > 0,
        alpha >= z + 2,  # Dominance Addition's threshold clears P2 = z + 1
        alpha > beta,
    ]
    solver = z3.Solver()
    solver.add(*base, alpha <= FROZEN_TOP)
    frozen_status = solver.check()
    if frozen_status != z3.unsat:
        raise AssertionError(f"expected the frozen ladder to be too small, got {frozen_status}")
    attainment = z3.Solver()
    attainment.add(*base, alpha == FROZEN_TOP + 1)
    if attainment.check() != z3.sat:
        raise AssertionError("the placement should be attainable at alpha = 7")
    model = attainment.model()
    return {
        "frozen_ladder_decision": str(frozen_status),
        "attainable_decision": "sat",
        "minimal_beta_top_level": FROZEN_TOP + 1,
        "attained_at": {
            key: model.eval(z3.Int(key), model_completion=True).as_long()
            for key in ("u_g", "y_v", "u_v", "z", "a", "beta", "alpha")
        },
        "statement": (
            "any bound placement needs alpha >= z + 2 >= u_v + 2 >= y_v + 3 >= u_g + 3 >= 7, "
            "because VRC needs z >= u_v > y_v and the placement needs y_v >= u_g >= 4; the "
            "smallest legal alpha is W_7, one above the frozen ladder's top W_6"
        ),
    }


def count_certificates() -> dict[str, Any]:
    """Three integer systems over the bridge's counts.

    * ``nesting``: P19's identity branch, ``n_b >= n_d`` with ``m_d >= m_b`` - UNSAT.
    * ``bound``: the bound branch, which decouples ``n_b`` from ``n_d`` - SAT, with the model.
    * ``stranded``: the regime ``y_v < u_g``, where nesting is forced and the Dominance-Addition
      leg forces ``E`` negative-free: ``n_d <= n_b``, ``m_d >= m_b``, ``n_d = m_d*n_chi`` with
      ``n_chi >= 4`` and ``m_b > n_b`` - UNSAT.
    """
    out: dict[str, Any] = {}

    n_v, m_v, n_b, m_b, n_d, m_d, n_chi = z3.Ints("n_v m_v n_b m_b n_d m_d n_chi")
    nesting = z3.Solver()
    nesting.add(
        n_v >= 1,
        m_v >= 1,
        m_b > n_b,
        n_b >= 1,
        m_d == m_b + m_v,
        n_d == m_d * n_chi,
        n_chi >= 1,
        n_b >= n_d,
    )
    out["nesting"] = {
        "decision": str(nesting.check()),
        "statement": (
            "the nesting placement (beta's A at delta's A level) forces n_b >= n_d = m_d*n_chi "
            ">= m_d = m_b + m_v > m_b > n_b"
        ),
    }
    if out["nesting"]["decision"] != "unsat":
        raise AssertionError("nesting count system was expected UNSAT")

    bound = z3.Solver()
    bound.add(
        n_v >= 1,
        m_v >= 1,
        m_b > n_b,
        n_b >= 1,
        m_d == m_b + m_v,
        n_d == m_d * n_chi,
        n_chi >= 1,
    )
    status = bound.check()
    out["bound"] = {
        "decision": str(status),
        "statement": "the bound placement leaves n_b free, so the same count laws are satisfiable",
        "assignment": {
            key: bound.model().eval(z3.Int(key), model_completion=True).as_long()
            for key in ("n_v", "m_v", "n_b", "m_b", "n_d", "m_d", "n_chi")
        }
        if status == z3.sat
        else None,
    }
    if status != z3.sat:
        raise AssertionError("bound count system was expected SAT")

    stranded = z3.Solver()
    stranded.add(
        n_b >= 1,
        m_b > n_b,
        m_d >= m_b,
        n_d == m_d * n_chi,
        n_chi >= 4,
        n_d <= n_b,
    )
    out["stranded"] = {
        "decision": str(stranded.check()),
        "statement": (
            "when y_v < u_g the nesting is forced (n_d <= n_b) while the Dominance-Addition leg "
            "makes E negative-free (m_d >= m_b); with delta's derived n_d = m_d*n_chi and "
            "n_chi >= 4 this contradicts m_b > n_b"
        ),
    }
    if out["stranded"]["decision"] != "unsat":
        raise AssertionError("stranded count system was expected UNSAT")
    return out


def _forcing_checks() -> dict[str, Any]:
    """Machine-check the two structural steps the no-go uses, over the levels and counts.

    * ``high_in_background``: a delta-A life at level ``a`` is a life of ``M`` and, if it lies in
      beta's background ``D_b``, of ``M3``; ``M3`` is VRC's ``B union C``, so that life is either
      in ``R(1, y_v)`` or at VRC's negative level.  With ``a >= u_g > y_v >= 3 > 0 > x_v`` no
      such life can exist, so the high option is empty and nesting is forced.
    * ``negative_blocks_dominance``: both Dominance Addition forms write ``M1 = B union C`` with
      ``B`` above A and ``C`` positive, and A = P2 sits at a positive level, so no life of ``M1``
      is negative; a negative life in delta's background ``E`` therefore admits no instance.
    """
    a, u_g, y_v, x_v, high_in_bg = z3.Ints("a u_g y_v x_v high_in_bg")
    forced = z3.Solver()
    forced.add(
        u_g >= 4,
        y_v >= 3,
        y_v < u_g,  # the no-go's precondition
        x_v < 0,
        a >= u_g,
        high_in_bg >= 1,
    )
    forced.add(z3.Or(a <= y_v, a == x_v))
    nesting_status = forced.check()

    p_level, threshold, c_level, negative_in_m1 = z3.Ints(
        "p_level threshold c_level negative_in_m1"
    )
    dominance = z3.Solver()
    dominance.add(
        p_level >= 5,  # P2 = VRC's A + 1 with VRC's A >= u_v > y_v >= 3
        threshold >= p_level + 1,  # A = P2 lies below the Dominance Addition threshold
        c_level < 0,
        negative_in_m1 >= 1,
    )
    dominance.add(z3.Or(c_level >= threshold, c_level >= 1))
    dominance_status = dominance.check()
    return {
        "high_in_background_forces_a_le_y_v": {
            "decision": str(nesting_status),
            "statement": (
                "with y_v < u_g a >= u_g and x_v < 0, a delta-A life inside beta's background "
                "would need a <= y_v or a = x_v: neither is available"
            ),
        },
        "negative_life_blocks_dominance_addition": {
            "decision": str(dominance_status),
            "statement": (
                "M1 = B union C with B above P2's positive level and C positive cannot contain a "
                "negative life, so delta's background E must be negative-free"
            ),
        },
    }


def no_go_regime() -> dict[str, Any]:
    """The quantified precondition of the no-go, its adverse legal witnesses, and its cases.

    The precondition is ``y_v < u_g``, with ``y_v >= 3`` (VRC's B range needs three positive
    levels) and ``u_g >= 4`` (GNEP's u is positive with ``u > y >= 3``).  That is a two-parameter
    family, not a single point: ``(3, 4)``, ``(3, 7)``, ``(4, 5)``, ``(6, 8)`` are all legal.  The
    frozen witness is one member, ``y_v = 3, u_g = 4``; the second example below is a legal
    member outside it.
    """
    examples = {
        "frozen_witness_point": {
            "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
            "general-non-extreme-priority": {"u": 4, "y": 3, "n": 1},
        },
        "non_frozen_point": {
            "vrc-avoidance": {"x": -1, "u": 6, "v": 8, "y": 4, "n": 1, "m": 1},
            "general-non-extreme-priority": {"u": 5, "y": 3, "n": 1},
        },
    }
    reported: dict[str, Any] = {}
    for label, reader_params in examples.items():
        assignment = Witness(
            {
                **reader_params,
                "non-elitism": {"n": 1},
                "condition-delta": {"u": 4, "y": 3, "n": 4, "n_per_m": 4},
                "condition-beta": {"step": 14, "mult": 1},
            }
        )
        checks = {}
        for family in (
            "vrc-avoidance",
            "general-non-extreme-priority",
            "non-elitism",
            "condition-delta",
            "condition-beta",
        ):
            try:
                validate(family, BRIDGE_LADDER, assignment.get(family))
                checks[family] = "accepted"
            except ValueError as error:
                checks[family] = f"rejected: {error}"
        vrc = reader_params["vrc-avoidance"]
        gnep = reader_params["general-non-extreme-priority"]
        blocked = bound_placement(
            n_v=vrc["n"],
            m_v=vrc["m"],
            u_v=vrc["u"],
            v_v=vrc["v"],
            y_v=vrc["y"],
            x_v=vrc["x"],
            u_g=gnep["u"],
            y_g=gnep["y"],
            n_g=gnep["n"],
            n_b=1,
            m_b=15,
            n_chi=4,
        )
        reported[label] = {
            "y_v": vrc["y"],
            "u_g": gnep["u"],
            "y_v_lt_u_g": vrc["y"] < gnep["u"],
            "legality": checks,
            "bound_placement_problems": blocked.problems(),
        }
    return {
        "precondition": (
            "y_v < u_g, a two-parameter family with y_v >= 3 and u_g >= 4 (e.g. (3,4), (3,7), "
            "(4,5), (6,8)); the frozen witness (y_v=3, u_g=4) is one member, not the family"
        ),
        "examples": reported,
        "why_bound_placement_is_unavailable": (
            "the placement needs a level a with u_g <= a <= y_v; when y_v < u_g that interval is "
            "empty, so no legal a fits and delta's A lives can only sit at beta's A level"
        ),
        "forcing_checks": _forcing_checks(),
        "cases": {
            "alpha = a (nesting, forced when y_v < u_g)": (
                "delta's A lives are all of M's level-a lives, so n_d <= n_b; at gamma = c the "
                "count at c reads m_d + E[c] = m_b + D_b[c], and the Dominance-Addition leg "
                "forces E negative-free, so E[c] = 0 and m_d >= m_b, which the UNSAT 'stranded' "
                "system contradicts against n_d = m_d * n_chi, n_chi >= 4 and m_b > n_b"
            ),
            "alpha = a with gamma < c": (
                "M's c-lives cannot then be beta's B, so they must be beta's background D_b, "
                "which forces c = x_v; beta's B = m_b @ gamma is then a level of M outside "
                "{a, c}, hence a level of delta's background E, so E carries a negative life and "
                "the Dominance-Addition leg has no instance for M1"
            ),
            "alpha != a (the bound placement)": (
                "excluded by the precondition: it needs a <= y_v, and every legal a >= u_g > y_v"
            ),
        },
        "case_coverage": (
            "the two cases are exhaustive for this architecture: gamma <= c always holds because "
            "the c-lives must lie in beta's B (gamma) or beta's background D_b, whose range "
            "R(gamma, beta_low + 1) contains c only if gamma <= c; alpha is not free because "
            "every level-a life of M must be beta's A, its B or its background, and only A can "
            "hold it; D_b's contents are unconstrained by the counts, so the argument covers "
            "every shared-background placement.  What is not covered is a chain that avoids the "
            "shared population M altogether, and beta's low level is the only remaining choice"
        ),
        "conclusion": (
            "in the regime y_v < u_g every assembly of the shared-population bridge is blocked: "
            "one case is arithmetically impossible, the other breaks the Dominance-Addition leg"
        ),
    }


# ---------------------------------------------------------------------------------------------
# Section 4: bounded parametric evidence that the construction is not a numeric accident.


# Legal witness/count choices for the bound placement; the sweep cap is the list length.  Each
# entry keeps ``n_b = n_v`` so that the thesis (not-worse) Dominance Addition split leaves C at
# one level, ``u_v > y_v`` as VRC requires, ``u_g <= y_v`` as the placement requires, and
# ``m_b`` exactly at the greedy Lemma 1.1/1.2 value ``(2**r - 1) * n_b`` for
# ``r = alpha - beta_low`` - the recurrence fixes that count, so rows are ``primitive-expansion``
# only when they match it.  The last row carries a larger ``m_b`` and is labelled
# ``derived-beta-witness``: it exercises the derived-edge certificate at a beta witness the
# manifest's expansion does not supply, and makes no primitive claim.
SWEEP: tuple[Placement, ...] = (
    bound_placement(
        n_v=1, m_v=1, u_v=5, v_v=7, y_v=4, x_v=-1, u_g=4, y_g=3, n_g=1, n_b=1, m_b=15, n_chi=4
    ),
    bound_placement(
        n_v=1, m_v=2, u_v=5, v_v=7, y_v=4, x_v=-1, u_g=4, y_g=3, n_g=1, n_b=1, m_b=15, n_chi=4
    ),
    bound_placement(
        n_v=3, m_v=2, u_v=7, v_v=9, y_v=6, x_v=-1, u_g=5, y_g=3, n_g=1, n_b=3, m_b=93, n_chi=4
    ),
    bound_placement(
        n_v=1, m_v=1, u_v=6, v_v=8, y_v=5, x_v=-1, u_g=4, y_g=3, n_g=1, n_b=1, m_b=31, n_chi=4
    ),
    bound_placement(
        n_v=1, m_v=3, u_v=5, v_v=7, y_v=4, x_v=-1, u_g=4, y_g=3, n_g=2, n_b=1, m_b=15, n_chi=8
    ),
    bound_placement(
        n_v=1,
        m_v=1,
        u_v=5,
        v_v=7,
        y_v=4,
        x_v=-1,
        u_g=4,
        y_g=3,
        n_g=1,
        n_b=1,
        m_b=400,
        n_chi=4,
        witness_kind="derived-beta-witness",
    ),
)


def sweep() -> dict[str, Any]:
    runs = []
    for p in SWEEP:
        report = replay(p)
        exact = p.beta_expansion["greedy_m"]
        runs.append(
            {
                "placement": {
                    "witness_kind": p.witness_kind,
                    "a": p.a,
                    "beta_low": p.beta_low,
                    "alpha": p.alpha,
                    "n_d": p.n_d,
                    "m_d": p.m_d,
                    "levels": {
                        "P1": p.z_v,
                        "P2": p.z_v + 1,
                        "M3_beta": p.beta_low,
                        "M3_high": p.a,
                        "M_alpha": p.alpha,
                    },
                },
                "primitive_expansion": {
                    "available": p.primitive_expansion_available and p.m_b == exact,
                    "recurrence_m_b": exact,
                    "edges": 3 + exact + p.m_d * (3 - p.c),
                },
                "derivation_problems": p.derivation_problems(),
                "clean": all_clean(report),
                "closures": {
                    form: entry["engine"] for form, entry in report.get("closures", {}).items()
                },
            }
        )
    return {
        "cap": len(SWEEP),
        "runs": runs,
        "all_clean": all(run["clean"] and not run["derivation_problems"] for run in runs),
        "note": (
            "exploration only, never a proof: every row is a legal witness choice, and only the "
            "rows whose m_b equals the recurrence value (2**r - 1) * n_b carry a primitive "
            "expansion; the labelled derived-beta-witness row assumes Condition beta instead"
        ),
    }


# ---------------------------------------------------------------------------------------------
# Section 5: report.


def run() -> dict[str, Any]:
    """The phase-20 report: bound placement, primitive expansion, arithmetic, and the no-go."""
    placement = min(SWEEP, key=lambda p: (p.u_g, p.y_v))
    report = replay(placement)
    if not all_clean(report):
        raise AssertionError("the exhibited bound-placement chain did not replay cleanly")
    primitive = primitive_report(placement)
    for entry in primitive["runs"].values():
        if entry["failures"] or entry["closure"]["mentioned_atom_decision"] != "unsat":
            raise AssertionError("the primitive expansion did not replay cleanly")
    beta_steps = placement.beta_expansion
    return {
        "route": "A",
        "approach": (
            "repair the phase-19 beta/delta alignment by an alternative high-level placement: "
            "delta's A level is chosen at its smallest legal value a = u_delta and beta's middle "
            "level at a - 1, so delta's high lives sit in beta's ranged background R(c, a) "
            "instead of beta's A level; the shared population is then not nested and n_beta is "
            "independent of n_delta.  The derived beta and delta edges are also expanded into "
            "their primitive Non-Elitism and GNEP instances at the same witness"
        ),
        "scope": (
            "fixed-witness certificate on the ladder W_-1..W_9 (frozen ladder W_-1..W_6, extended "
            "because level_budget proves the placement needs W_7), with the frozen readings, the "
            "phase-18 manifest replays, the primitive 82-edge expansion at the exhibited witness, "
            "an integer certificate for the counts and the level budget, and a bounded sweep"
        ),
        "verdict": "refuted-candidate",
        "evidence": {
            "refuted_candidate": (
                "phase 19's obstruction is placement-specific, not family-wide: the repaired "
                "ED/DA/delta/beta/VRC chain it declared obstructed has a legal instance on the "
                "bound placement, and that instance's beta and delta edges are themselves "
                "expanded into primitive Non-Elitism and GNEP instances"
            ),
            "bound_placement_chain": {
                "witness": report["witness"],
                "populations": report["populations"],
                "derivation": report["derivation"],
                "edges": report["edges"],
                "closures": report["closures"],
                "ranged_ne_variant": report["ranged_ne_variant"],
                "variants_covered": [
                    {
                        "ne": ne,
                        "da": da,
                        "beta_reading_used": (THESIS_BETA if ne == NE_THESIS else BETA),
                        "note": (
                            "the same edges serve every variant: the beta edge's background lies "
                            "inside R(c, beta_low + 1) so the ranged reading holds, both Dominance "
                            "Addition forms are decided UNSAT above, and the certificate is pure "
                            "derived-edge, i.e. it assumes the Conditions beta and delta"
                        ),
                    }
                    for ne, da in (
                        (NE_2003, DA_2003),
                        (NE_THESIS, DA_2003),
                        (NE_2003, DA_THESIS),
                        (NE_THESIS, DA_THESIS),
                    )
                ],
                "delta_source": (
                    f"{DELTA} (GNEP, thesis Lemma 5.2.1-5.2.2): delta's n = m * n_chi; the "
                    f"chain uses n_d = {placement.n_d} = {placement.m_d} * {placement.n_chi}"
                ),
                "gnep_principle": GNEP,
            },
            "primitive_expansion": {
                "counts": {
                    "non_elitism": sum(step["output_m"] for step in beta_steps["steps"]),
                    "general_non_extreme_priority": placement.m_d * (3 - placement.c),
                    "egalitarian_dominance": 1,
                    "vrc_avoidance": 1,
                    "dominance_addition": 1,
                },
                "beta_expansion": beta_steps,
                "beta_expansion_note": (
                    "the four Lemma 1.1/1.2 blocks carry 1, 2, 4 and 8 Non-Elitism instances "
                    "(15 in total) and their outputs sum to m_beta = 15 at n_beta = 1. The "
                    "recurrence fixes this count, so the beta edge's counts are derived and not "
                    "assumed; rows with any other m_b are labelled derived-beta-witness in the "
                    "sweep and are not expanded"
                ),
                "delta_expansion_note": (
                    f"{placement.m_d} disjoint copies of the {3 - placement.c}-step GNEP climb, "
                    f"i.e. {placement.m_d * (3 - placement.c)} primitive GNEP instances, with "
                    f"delta's n_d = {placement.n_d} = m_d * n_chi"
                ),
                "runs": primitive["runs"],
            },
            "why_phase_19_missed_it": level_budget(),
            "count_systems": count_certificates(),
            "quantified_no_go": no_go_regime(),
            "sweep": sweep(),
        },
        "remaining_obligation": (
            "the certificate is a single-witness construction, so it does not settle Q-011: it "
            "proves neither that a source-general chain exists nor that an axiology satisfying "
            "the five weakened conditions does. The shared-population bridge is now proved "
            "unassemblable exactly when y_vrc < u_delta - a two-parameter regime, so the frozen "
            "witness (y_vrc=3, u_delta=4) is one member and not the whole of it - and the bound "
            "placement covers y_vrc >= u_delta at a ladder one level above the frozen top. What "
            "remains unknown for all three weakened variants is whether a closing chain exists "
            "in the regime y_vrc < u_delta that avoids the shared population M (for example by "
            "an extra source-legal Non-Elitism or GNEP move between VRC's B union C and beta's "
            "left side), or whether a background/count-sensitive model survives there. The "
            "primitive expansion also inherits the manifest's recorded derivations: the "
            "Non-Elitism block sizes follow the manifest's greedy recurrence and delta's count "
            "law n = m * n_chi, which this phase replays but does not re-derive from the primary "
            "pages."
        ),
    }


def main() -> None:
    print(json.dumps(run(), indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
