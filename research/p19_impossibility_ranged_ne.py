"""Q-011 Route A: ranged Non-Elitism (variant (b)).

This pass deliberately separates three scopes:

* the P18 chosen-witness control, replayed with the thesis/ranged NE reading;
* a small exact search over source instances, whose SAT result is only bounded evidence; and
* a parameterized five-edge repair attempt (ED, VRC, beta-ranged, delta, DA).

The last attempt grants the repaired derived beta and delta edges more directly than a
primitive NE/GNEP expansion.  Its failure is therefore an obstruction to this particular
repair, not a source-general consistency theorem.  No fixed-witness or bounded result is
promoted to an unrestricted claim.
"""

from __future__ import annotations

import json
import time
from collections import Counter, defaultdict
from collections.abc import Iterable, Mapping, Sequence
from itertools import product
from typing import Any

from research.lab import Engine, background, write_result
from research.ladder import Witness, audit, instances_over
from research.p6_schema import core_constraints, name_of
from research.p8_catalogue import LADDER
from research.p16_ne_top import decide_without_completeness
from research.p17_vrc_boundary import (
    DA_2003,
    ED,
    GNEP,
    NE_THESIS,
    SOURCE_WITNESS,
    VRC,
)
from research.p18_vrc_certificate import (
    BETA,
    DELTA,
    SOURCE_MANIFEST,
    Edge,
    compact_closure,
    control_edges,
    focus_populations,
    verify_edge,
)
from research.schema import Instance, Pop

THESIS_BETA = "thesis:condition-beta"
THESIS_DELTA = "thesis:condition-delta"
VARIANT = "ranged-ne"
SEARCH_CAP = 12
MAX_CHAIN_EDGES = 6


def _pop(counter: Counter[int]) -> Pop:
    return tuple(sorted(counter.elements()))


def _plus(*parts: Pop) -> Pop:
    return tuple(sorted(v for part in parts for v in part))


def _counts(pop: Pop) -> list[list[int]]:
    return [[level, count] for level, count in sorted(Counter(pop).items())]


def _manifest_record(
    edge: Edge, witness: Witness, audit_principle: str | None = None
) -> dict[str, Any]:
    """Replay an Edge with the witness carried by that candidate, not P18's default.

    P18's serialized manifest has only the 2003 IDs for the derived beta/delta readings.
    ``audit_principle`` lets the ranged-beta attempt independently audit the same endpoints
    against the thesis/ranged background restriction.
    """
    record = edge.record()
    instance = edge.instance
    if audit_principle is not None:
        instance = Instance(audit_principle, instance.args)
    return {
        "record": record,
        "verify_edge": verify_edge(record, LADDER, witness),
        "ladder_audit": audit(instance, LADDER, witness),
    }


def _replay_ok(items: Sequence[Mapping[str, Any]]) -> bool:
    return all(not item["verify_edge"] and item["ladder_audit"] for item in items)


def _control_variant_report() -> dict[str, Any]:
    """Reproduce P18's control and identify the exact ranged-NE loss."""
    edges = control_edges()
    original_closure = compact_closure(
        [edge.instance for edge in edges], "p19-ranged-ne-control/v1"
    )
    p16_control_decision = decide_without_completeness(
        [edge.instance for edge in edges], "p19-ranged-ne-control-direct-p16/v1"
    )

    # The 35 NE edges are the primitive expansion of beta.  Rewrite only the source id,
    # source page, and shape; the serialized decomposition and witness lookup stay untouched.
    beta_edges = edges[2:37]
    ranged_failures: list[dict[str, Any]] = []
    for index, edge in enumerate(beta_edges, start=2):
        record = edge.record()
        ranged_record = {
            **record,
            "principle": NE_THESIS,
            "shape": "W",
            "source": SOURCE_MANIFEST[NE_THESIS].reading,
            "page": SOURCE_MANIFEST[NE_THESIS].page,
        }
        problems = verify_edge(ranged_record, LADDER, SOURCE_WITNESS)
        ranged_instance = Instance(NE_THESIS, (edge.left, edge.right))
        ranged_audit = audit(ranged_instance, LADDER, SOURCE_WITNESS)
        if problems or not ranged_audit:
            ranged_failures.append(
                {
                    "index": index,
                    "left": _counts(edge.left),
                    "right": _counts(edge.right),
                    "background": _counts(edge.background),
                    "problems": problems,
                    "ladder_audit": ranged_audit,
                }
            )

    # The derived beta target itself is checked as a ranged condition as well.  This is the
    # exact premise that the NE expansion was supposed to supply; its D contains W_-1.
    beta_top, beta_bottom = beta_edges[0].left, beta_edges[-1].right
    beta_target = Instance(THESIS_BETA, (beta_top, beta_bottom))
    beta_target_witness = Witness({"condition-beta": {"step": 30}})
    da_edge = edges[-1]
    da_replay = _manifest_record(da_edge, SOURCE_WITNESS)
    return {
        "scope": "chosen-witness P18 control only; not source-general",
        "control_edges": len(edges),
        "control_closure": original_closure,
        "beta_primitive_edges": len(beta_edges),
        "p16_direct_control_decision": p16_control_decision,
        "ranged_ne_losing_primitive_edges": len(ranged_failures),
        "ranged_ne_first_loss": ranged_failures[0] if ranged_failures else None,
        "ranged_ne_loss_reason": (
            "ranged Non-Elitism needs D subset R(y,x), but the first beta edge has "
            "D = W_-1 + 38 W_3 while (x,y)=(4,1); W_-1 is outside R(1,4)"
        ),
        "derived_beta_target": {
            "left": _counts(beta_top),
            "right": _counts(beta_bottom),
            "ranged_audit": audit(beta_target, LADDER, beta_target_witness),
            "ranged_audit_premise": (
                "Condition beta-ranged requires every background life in R(z,y+1); "
                "the target has z=1, y=3 and D=W_-1, so -1 is not in R(1,4)"
            ),
        },
        "da_2003": {
            "replay": da_replay,
            "kept": not da_replay["verify_edge"] and da_replay["ladder_audit"],
        },
    }


def _source_witness(ne_n: int, g_n: int, v_n: int, v_m: int) -> Witness:
    """A valid chosen witness for the five source principles in bounded search."""
    return Witness(
        {
            "non-elitism": {"n": ne_n},
            "general-non-extreme-priority": {"u": 4, "y": 3, "n": g_n},
            "vrc-avoidance": {
                "x": -1,
                "u": 4,
                "v": 6,
                "y": 3,
                "n": v_n,
                "m": v_m,
            },
        }
    )


def _cycle_scan(
    instances: Sequence[Instance], max_len: int = MAX_CHAIN_EDGES
) -> list[list[Instance]]:
    """Enumerate W/S cycles up to max_len, always starting at a strict edge."""
    outgoing: dict[Pop, list[Instance]] = defaultdict(list)
    for instance in instances:
        if instance.shape in {"S", "W"}:
            outgoing[instance.args[0]].append(instance)
    found: list[list[Instance]] = []
    for first in instances:
        if first.shape != "S":
            continue
        start = first.args[0]

        def extend(path: list[Instance], start: Pop = start) -> None:
            if len(path) >= 2 and path[-1].args[1] == start:
                found.append(path.copy())
                return
            if len(path) >= max_len:
                return
            current = path[-1].args[1]
            for nxt in outgoing.get(current, ()):
                if nxt.args[1] == start or nxt.args[1] not in {step.args[0] for step in path}:
                    extend([*path, nxt], start)

        extend([first])
    # The first edge is fixed as the only strict edge, so this is already canonical enough for
    # this bounded diagnostic.  Deduplicate repeated paths from duplicate generated instances.
    unique: dict[tuple[tuple[str, Pop, Pop], ...], list[Instance]] = {}
    for cycle in found:
        key = tuple((step.principle, step.args[0], step.args[1]) for step in cycle)
        unique[key] = cycle
    return list(unique.values())


def _bounded_variant_run(witness: Witness, label: str) -> dict[str, Any]:
    """Bounded source-instance search; SAT is explicitly not consistency evidence."""
    populations = focus_populations(SEARCH_CAP, LADDER)
    principles = (ED, GNEP, VRC, NE_THESIS, DA_2003)
    instances = instances_over(populations, LADDER, witness, principles)
    names = tuple(sorted({name_of(pop) for instance in instances for pop in instance.args}))
    bg = background(names)
    soft = core_constraints(instances, f"p19-bounded/{label}")
    engine = Engine(names, [*bg["reflexivity"], *bg["transitivity"]], soft=soft, timeout_ms=60000)
    check = engine.check([constraint.id for constraint in soft])
    cycles = _cycle_scan(instances)
    cycle_results: list[dict[str, Any]] = []
    for cycle in cycles:
        # Every cycle is independently checked before a closure result is reported.
        audits = [audit(step, LADDER, witness) for step in cycle]
        if not all(audits):
            cycle_results.append({"audited": False, "closure": None})
            continue
        closure = compact_closure(cycle, f"p19-bounded-cycle/{label}")
        cycle_results.append({"audited": True, "closure": closure})
    return {
        "scope": "bounded chosen-witness scan on the 12-population focus; not consistency evidence",
        "witness": {key: dict(value) for key, value in witness.params.items()},
        "populations": len(populations),
        "relata": len(names),
        "instances": len(instances),
        "shape_counts": dict(Counter(instance.shape for instance in instances)),
        "engine_decision": check.decision,
        "engine_reason": check.reason,
        "p16_note": (
            "decide_without_completeness is applied only to audited closed cycles; the full finite "
            "instance set is checked by Engine"
        ),
        "cycles_up_to_6": len(cycles),
        "cycle_results": cycle_results,
    }


def _parameter_grid() -> Iterable[dict[str, int]]:
    """Integer witness/count grid; all values obey the source inequalities."""
    for ne_n, g_n, v_n, v_m, beta_n, beta_m in product(
        range(1, 3), range(1, 3), range(1, 3), range(1, 3), range(1, 4), range(2, 5)
    ):
        if beta_m <= beta_n:
            continue
        # Keep every displayed relatum at most eight lives.  The template's largest relata
        # have n_beta + m_beta + m_vrc lives.
        if beta_n + beta_m + v_m > 8:
            continue
        # n_ne is retained in the record even though this favorable beta abstraction does not
        # need its exact alpha realization.  This avoids silently turning a chosen n into a theorem.
        yield {
            "n_ne": ne_n,
            "n_gnep": g_n,
            "n_vrc": v_n,
            "m_vrc": v_m,
            "n_beta": beta_n,
            "m_beta": beta_m,
        }


def _repaired_chain_attempt(params: Mapping[str, int]) -> dict[str, Any]:
    """Try the negative-z beta / delta / DA repair and return the first failed premise.

    We grant the chain a beta-ranged edge directly.  If even this favorable derived-edge
    relaxation cannot reach delta, replacing beta by an explicit NE expansion cannot rescue this
    particular five-edge template.
    """
    n_v = params["n_vrc"]
    m_v = params["m_vrc"]
    n_b = params["n_beta"]
    m_b = params["m_beta"]
    n_g = params["n_gnep"]
    m_total = m_v + m_b
    delta_steps = 4  # z=-1 to W_3 requires GNEP at z=-1,0,1,2.
    delta_n_per_negative = delta_steps * n_g
    n_delta = delta_n_per_negative * m_total
    # ED, VRC, beta use h=5,u=4; VRC B is chosen at W_3 so that it can be beta's ranged D.
    vrc_b = (3,) * (n_b + m_b)
    p0 = (5,) * n_v
    p1 = (4,) * n_v
    p2 = _plus(vrc_b, (-1,) * m_v)
    beta_bg = (-1,) * m_v
    beta_left_part = (3,) * (n_b + m_b)
    beta_right_part = _plus((6,) * n_b, (-1,) * m_b)
    p3 = _plus(beta_bg, beta_right_part)

    source_witness = _source_witness(params["n_ne"], n_g, n_v, m_v)
    edges: list[Edge] = [
        Edge(ED, p0, p1, witness={}),
        Edge(
            VRC,
            p1,
            p2,
            witness={"x": -1, "u": 4, "v": 6, "y": 3, "n": n_v, "m": m_v},
        ),
        Edge(
            BETA,
            beta_left_part,
            beta_right_part,
            beta_bg,
            witness={"step": m_b - n_b, "mult": 1},
        ),
    ]
    prefix_replay = [_manifest_record(edge, source_witness) for edge in edges[:2]]
    beta_witness = Witness({"condition-beta": {"step": m_b - n_b, "mult": 1}})
    prefix_replay.append(_manifest_record(edges[2], beta_witness, THESIS_BETA))
    if not _replay_ok(prefix_replay):
        return {
            "params": dict(params),
            "status": "failed replay",
            "replay": prefix_replay,
            "failed_premise": "ED/VRC/beta-ranged prefix did not pass independent replay",
        }

    # A delta derived from GNEP at z=-1 needs four GNEP levels per negative life, hence
    # n_delta = 4*n_g*m_total high lives.  The beta endpoint contains only n_b W_6 lives.
    if n_delta > n_b:
        return {
            "params": dict(params),
            "status": "obstructed",
            "replay": prefix_replay,
            "endpoints": {
                "ED": {"left": _counts(p0), "right": _counts(p1)},
                "VRC": {"left": _counts(p1), "right": _counts(p2)},
                "beta_ranged": {"left": _counts(p2), "right": _counts(p3)},
            },
            "delta_required": {
                "negative_lives": m_total,
                "gnep_witness_n": n_g,
                "required_high_lives": n_delta,
                "available_W6_at_beta_endpoint": n_b,
            },
            "failed_premise": (
                "delta from GNEP at z=-1 needs n_delta = 4*n_g*(m_beta+m_vrc) high lives "
                "at W_6, but beta supplies only n_beta high lives; n_g>=1, m_vrc>0 and "
                "m_beta>n_beta imply n_delta>n_beta"
            ),
            "symbolic_obstruction": ("n_delta = 4*n_g(m_beta+m_vrc) >= 4(m_beta+m_vrc) > n_beta"),
        }

    # This branch is retained as a guard: should a future source interpretation change the count
    # law, finish the replay and closure rather than silently calling it a result.
    retained = n_b - n_delta
    if retained < n_v:
        return {
            "params": dict(params),
            "status": "obstructed",
            "replay": prefix_replay,
            "failed_premise": "DA needs n_v retained W_6 lives, but delta leaves too few",
            "delta_required": {"required_high_lives": n_delta, "available_W6": n_b},
        }
    delta_bg = (6,) * retained
    delta_edge = Edge(
        DELTA,
        _plus((6,) * n_delta, (-1,) * m_total),
        _plus((1,) * n_delta, (3,) * m_total),
        delta_bg,
        witness={"u": 4, "y": 3, "n": delta_n_per_negative, "n_per_m": delta_n_per_negative},
    )
    p4 = delta_edge.right
    da_edge = Edge(DA_2003, p4, p0)
    delta_witness = Witness(
        {
            "condition-delta": {
                "u": 4,
                "y": 3,
                "n": delta_n_per_negative,
                "n_per_m": delta_n_per_negative,
            }
        }
    )
    replay = [*prefix_replay, _manifest_record(delta_edge, delta_witness)]
    replay.append(_manifest_record(da_edge, source_witness))
    if any(item["verify_edge"] or not item["ladder_audit"] for item in replay):
        return {"params": dict(params), "status": "failed replay", "replay": replay}
    chain = [edge.instance for edge in [*edges, delta_edge, da_edge]]
    closure = compact_closure(chain, "p19-ranged-ne-repaired-chain/v1")
    return {
        "params": dict(params),
        "status": "candidate",
        "replay": replay,
        "closure": closure,
        "chain": [edge.record() for edge in [*edges, delta_edge, da_edge]],
    }


def _repaired_search() -> dict[str, Any]:
    attempts = [_repaired_chain_attempt(params) for params in _parameter_grid()]
    return {
        "scope": (
            "parameterized negative-z beta-ranged/delta/DA template; favorable derived-edge "
            "relaxation, not a source-general search over all chains"
        ),
        "max_chain_edges": MAX_CHAIN_EDGES,
        "parameter_grid_size": len(attempts),
        "attempted": attempts,
        "status_counts": dict(Counter(attempt["status"] for attempt in attempts)),
        "symbolic_obstruction": (
            "For this template, beta has m_beta>n_beta and VRC contributes m_vrc>0 negative lives. "
            "Raising W_-1 to W_3 through GNEP needs 4*n_g*(m_beta+m_vrc)>n_beta high lives, "
            "while beta's endpoint has only n_beta high lives."
        ),
    }


def run() -> dict[str, Any]:
    control = _control_variant_report()
    # Four small chosen-witness points exercise the integer witness variables.  They are not a
    # model certificate; bounded SAT remains explicitly labelled as such.
    bounded: list[dict[str, Any]] = []
    for ne_n, g_n, v_n, v_m in ((1, 1, 1, 1), (1, 2, 1, 2), (2, 1, 2, 1), (2, 2, 2, 2)):
        witness = _source_witness(ne_n, g_n, v_n, v_m)
        bounded.append(_bounded_variant_run(witness, f"{VARIANT}-n{ne_n}-g{g_n}-v{v_n}-m{v_m}"))
    repaired = _repaired_search()
    return {
        "variant": VARIANT,
        "verdict": "unresolved",
        "control": control,
        "bounded_search": bounded,
        "repaired_chain_search": repaired,
        "scope_statement": (
            "No source-general contradiction or exact all-size model was established. The P18 "
            "control is chosen-witness evidence; Engine SAT and the six-edge scan are bounded only. "
            "The reported obstruction is proved only for the displayed negative-z beta/delta/DA "
            "template."
        ),
    }


def _summary(data: Mapping[str, Any]) -> str:
    control = data["control"]
    bounded = data["bounded_search"]
    repaired = data["repaired_chain_search"]
    return json.dumps(
        {
            "variant": data["variant"],
            "verdict": data["verdict"],
            "control_edges": control["control_edges"],
            "control_closure": control["control_closure"]["decision_without_completeness"],
            "ranged_ne_losing_primitive_edges": control["ranged_ne_losing_primitive_edges"],
            "ranged_ne_beta_audit": control["derived_beta_target"]["ranged_audit"],
            "da_kept": control["da_2003"]["kept"],
            "bounded_engine_decisions": [item["engine_decision"] for item in bounded],
            "bounded_cycles_up_to_6": [item["cycles_up_to_6"] for item in bounded],
            "repaired_status_counts": repaired["status_counts"],
            "failed_premise": repaired["attempted"][0].get("failed_premise"),
        },
        sort_keys=True,
    )


def main() -> None:
    started = time.monotonic()
    data = run()
    write_result(
        "p19_impossibility_ranged_ne", data, {"wall_time_s": round(time.monotonic() - started, 1)}
    )
    print(json.dumps(data, indent=2, ensure_ascii=False))
    print("VERDICT ranged-ne: unresolved")
    print("SUMMARY " + _summary(data))


if __name__ == "__main__":
    main()
