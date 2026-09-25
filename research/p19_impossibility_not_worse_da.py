"""Phase 19: Route A search for the thesis not-worse Dominance Addition weakening.

This is a bounded, source-faithful diagnostic.  It keeps thesis Dominance Addition as its
actual N-shaped clause (not(A ≻ B ⊎ C)); it never turns that clause into a weak edge.  Source
edges are constructed with explicit decompositions, replayed from their serialized count
vectors, and checked by ``ladder.audit``.  The search varies the integer witnesses in a finite
ladder range independently per candidate edge.  Consequently a SAT table or an empty bounded
chain census is not a source-general consistency or impossibility result.
"""

from __future__ import annotations

import hashlib
import json
import time
from collections import Counter
from collections.abc import Iterable, Mapping, Sequence
from itertools import combinations, combinations_with_replacement, product
from typing import Any

from population_ethics.relations import Not, conjunction, strict, weak
from research.lab import Engine, background, ground
from research.ladder import FORM, Witness, audit, domain, validate
from research.p6_schema import core_constraints, name_of
from research.p8_catalogue import LADDER
from research.p16_ne_top import decide_without_completeness
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
    Edge,
    verify_edge,
)
from research.schema import Instance, Pop

VARIANTS: tuple[tuple[str, str, str], ...] = (
    ("original", NE_2003, DA_2003),
    ("ranged-ne", NE_THESIS, DA_2003),
    ("not-worse-da", NE_2003, DA_THESIS),
    ("both-weakened", NE_THESIS, DA_THESIS),
)

# The search is deliberately finite but reaches eight lives per relatum, as requested.  The
# focus contains every equal-level population up to this bound and then a deterministic nearest
# neighbourhood of the source proof seeds.  It is not the full D_8 domain.
MAX_LIVES = 8
FOCUS_CAP = 96
MAX_CHAIN_EDGES = 6
WITNESS_MAX = 8

SEEDS: tuple[Pop, ...] = (
    (5,),
    (4,),
    (3, 3),
    (1, 4),
    (-1, 3, 3),
    (-1, 1, 4),
    (-1, 4),
    (0, 1),
    (-1, 1),
    (1, 3, 5),
    (1, 5),
)


def _plus(*parts: Pop) -> Pop:
    return tuple(sorted(v for part in parts for v in part))


def _symmetric_distance(left: Pop, right: Pop) -> int:
    a, b = Counter(left), Counter(right)
    return sum((a - b).values()) + sum((b - a).values())


def focus_populations(cap: int = FOCUS_CAP) -> tuple[Pop, ...]:
    universe = domain(LADDER, MAX_LIVES)
    chosen: list[Pop] = []
    equal = [(level,) * size for size in range(1, MAX_LIVES + 1) for level in LADDER.levels]
    for pop in [*equal, *SEEDS]:
        if pop in universe and pop not in chosen:
            chosen.append(pop)
    for pop in sorted(
        universe, key=lambda p: (min(_symmetric_distance(p, s) for s in SEEDS), len(p), p)
    ):
        if len(chosen) == cap:
            break
        if pop not in chosen:
            chosen.append(pop)
    if len(chosen) != cap:
        raise AssertionError(f"focus has {len(chosen)} populations, wanted {cap}")
    return tuple(chosen)


def _subbags(populations: Iterable[Pop]) -> list[Pop]:
    """All subbags of the finite focus, including empty, in deterministic order."""
    out: set[Pop] = {()}
    for pop in set(populations):
        items = sorted(Counter(pop).items())
        for picks in product(*(range(count + 1) for _, count in items)):
            out.add(
                tuple(
                    level
                    for (level, _), amount in zip(items, picks, strict=True)
                    for _ in range(amount)
                )
            )
    return sorted(out, key=lambda p: (len(p), p))


def _bags(levels: Sequence[int], size: int) -> list[Pop]:
    if size < 0:
        return []
    return [tuple(x) for x in combinations_with_replacement(sorted(levels), size)]


def _witness_options(principle: str) -> list[Witness]:
    """Finite integer witness grid; every retained tuple passes the source inequalities."""
    form = FORM[principle]
    options: list[Witness] = []
    if form in {"non-elitism-ranged", "non-elitism-any"}:
        family = "non-elitism"
        for n in range(1, WITNESS_MAX + 1):
            w = Witness({family: {"n": n}})
            validate(family, LADDER, w.get(family))
            options.append(w)
    elif form == "general-non-extreme-priority":
        family = "general-non-extreme-priority"
        for u in LADDER.levels:
            for y in LADDER.levels:
                for n in range(1, WITNESS_MAX + 1):
                    w = Witness({family: {"u": u, "y": y, "n": n}})
                    try:
                        validate(family, LADDER, w.get(family))
                    except ValueError:
                        continue
                    options.append(w)
    elif form == "vrc-avoidance":
        family = "vrc-avoidance"
        for x in LADDER.levels:
            for u in LADDER.levels:
                for v in LADDER.levels:
                    for y in LADDER.levels:
                        for n in range(1, WITNESS_MAX + 1):
                            for m in range(1, WITNESS_MAX + 1):
                                params = {"x": x, "u": u, "v": v, "y": y, "n": n, "m": m}
                                w = Witness({family: params})
                                try:
                                    validate(family, LADDER, params)
                                except ValueError:
                                    continue
                                options.append(w)
    else:
        options = [Witness({})]
    return options


def _checker_witness(edge: Edge) -> Witness:
    form = FORM[edge.principle]
    family = {
        "non-elitism-ranged": "non-elitism",
        "non-elitism-any": "non-elitism",
        "general-non-extreme-priority": "general-non-extreme-priority",
        "vrc-avoidance": "vrc-avoidance",
    }.get(form)
    if family is None:
        return Witness({})
    fields = {
        "non-elitism": ("n",),
        "general-non-extreme-priority": ("u", "y", "n"),
        "vrc-avoidance": ("x", "u", "v", "y", "n", "m"),
    }[family]
    return Witness({family: {key: edge.witness[key] for key in fields}})


def _dynamic_edge_witness(
    principle: str, params: Mapping[str, int], **extra: int
) -> dict[str, int]:
    form = FORM[principle]
    if form in {"non-elitism-ranged", "non-elitism-any"}:
        return {"n": params["n"], **extra}
    if form == "general-non-extreme-priority":
        return {"u": params["u"], "y": params["y"], "n": params["n"], **extra}
    if form == "vrc-avoidance":
        return {key: params[key] for key in ("x", "u", "v", "y", "n", "m")}
    return {}


def _edge_key(edge: Edge) -> tuple[str, Pop, Pop]:
    return edge.principle, edge.left, edge.right


def _dedup(edges: Iterable[Edge]) -> list[Edge]:
    chosen: dict[tuple[str, Pop, Pop], Edge] = {}
    for edge in edges:
        chosen.setdefault(_edge_key(edge), edge)
    return [chosen[key] for key in sorted(chosen, key=lambda k: (k[0], k[1], k[2]))]


def _ed_edges(focus: Sequence[Pop]) -> list[Edge]:
    out: list[Edge] = []
    for left in focus:
        if not left or len(set(left)) != 1:
            continue
        for right in focus:
            if right != left and len(right) == len(left) and right and max(right) < left[0]:
                out.append(Edge(ED, left, right))
    return _dedup(out)


def _da_split(bc: Pop, a: Pop, *, uniform: bool) -> tuple[Pop, Pop] | None:
    if len(bc) <= len(a) or not a or not bc:
        return None
    counts = Counter(bc)
    levels = sorted(level for level in counts if level > max(a))
    for picked in combinations(bc, len(a)):
        b = Counter(picked)
        if any(b[level] > counts[level] for level in b):
            continue
        c = counts - b
        if not c:
            continue
        if uniform and (len(c) != 1 or next(iter(c)) <= 0):
            continue
        if not uniform and not all(level > 0 for level in c.elements()):
            continue
        # ``b`` is selected from lives strictly above every A life, as required by the reading.
        if not all(level in levels for level in b.elements()):
            continue
        return tuple(sorted(b.elements())), tuple(sorted(c.elements()))
    return None


def _da_edges(focus: Sequence[Pop], principle: str) -> list[Edge]:
    uniform = principle == DA_THESIS
    out: list[Edge] = []
    for a in focus:
        for bc in focus:
            split = _da_split(bc, a, uniform=uniform)
            if split is None:
                continue
            b, c = split
            if uniform:
                out.append(Edge(principle, a, _plus(b, c)))
            else:
                out.append(Edge(principle, _plus(b, c), a))
    return _dedup(out)


def _w_edges(
    focus: Sequence[Pop], principle: str, witnesses: Sequence[Witness], subbags: Sequence[Pop]
) -> list[Edge]:
    """Construct source W edges with their decomposition retained, not inferred by a solver."""
    form = FORM[principle]
    out: list[Edge] = []
    for witness in witnesses:
        params = dict(
            witness.get(
                {
                    "non-elitism-ranged": "non-elitism",
                    "non-elitism-any": "non-elitism",
                    "general-non-extreme-priority": "general-non-extreme-priority",
                    "vrc-avoidance": "vrc-avoidance",
                }[form]
            )
        )
        if form in {"non-elitism-ranged", "non-elitism-any"}:
            n = params["n"]
            for x, y in product(LADDER.levels, repeat=2):
                if not LADDER.has(x - 1) or x - 1 <= y:
                    continue
                lp, rp = (x - 1,) * (n + 1), tuple(sorted((x,) + (y,) * n))
                allowed = set(LADDER.range(y, x)) if form == "non-elitism-ranged" else None
                for bg in subbags:
                    if allowed is not None and not all(level in allowed for level in bg):
                        continue
                    left, right = _plus(bg, lp), _plus(bg, rp)
                    if left in focus and right in focus and left != right:
                        out.append(
                            Edge(
                                principle,
                                lp,
                                rp,
                                bg,
                                _dynamic_edge_witness(principle, params, x=x, y=y),
                            )
                        )
        elif form == "general-non-extreme-priority":
            n, u, y = params["n"], params["u"], params["y"]
            for z in LADDER.levels:
                if not LADDER.has(z + 1):
                    continue
                for x in (level for level in LADDER.levels if level >= u):
                    for low in _bags(LADDER.range(1, y), n):
                        lp, rp = _plus((x,) * n, (z,)), _plus(low, (z + 1,))
                        for bg in subbags:
                            left, right = _plus(bg, lp), _plus(bg, rp)
                            if left in focus and right in focus and left != right:
                                out.append(
                                    Edge(
                                        principle,
                                        lp,
                                        rp,
                                        bg,
                                        _dynamic_edge_witness(principle, params, z=z),
                                    )
                                )
        elif form == "vrc-avoidance":
            x, u, y, n, m = params["x"], params["u"], params["y"], params["n"], params["m"]
            for z in (level for level in LADDER.levels if level >= u):
                lp = (z,) * n
                for size in range(1, MAX_LIVES + 1):
                    for low in _bags(LADDER.range(1, y), size):
                        rp = _plus(low, (x,) * m)
                        if lp in focus and rp in focus and lp != rp:
                            out.append(
                                Edge(
                                    principle, lp, rp, (), _dynamic_edge_witness(principle, params)
                                )
                            )
        else:
            raise AssertionError(f"unexpected W principle {principle}")
    return _dedup(out)


def _pool(focus: Sequence[Pop], principle: str, subbags: Sequence[Pop]) -> list[Edge]:
    if principle == ED:
        return _ed_edges(focus)
    if principle in {DA_2003, DA_THESIS}:
        return _da_edges(focus, principle)
    return _w_edges(focus, principle, _witness_options(principle), subbags)


def _subbag_counters(common: Counter[int]) -> Iterable[Counter[int]]:
    items = sorted(common.items())
    for picks in product(*(range(count + 1) for _, count in items)):
        yield Counter(
            {level: amount for (level, _), amount in zip(items, picks, strict=True) if amount}
        )


def _replay(edge: Edge) -> list[str]:
    """Recompute a decomposition from endpoints, then run the independent p18 verifier."""
    problems: list[str] = []
    checker = _checker_witness(edge)
    direct = verify_edge(edge.record(), ladder=LADDER, witness=checker)
    if direct:
        problems.extend(f"direct: {problem}" for problem in direct)
    left, right = Counter(edge.left), Counter(edge.right)
    found = False
    for bg in _subbag_counters(left & right):
        candidate = Edge(
            edge.principle,
            tuple(sorted((left - bg).elements())),
            tuple(sorted((right - bg).elements())),
            tuple(sorted(bg.elements())),
            edge.witness,
        )
        if not verify_edge(candidate.record(), ladder=LADDER, witness=checker):
            found = True
            break
    if not found:
        problems.append("count-vector decomposition replay found no valid source split")
    try:
        if not audit(edge.instance, LADDER, checker):
            problems.append("research.ladder.audit rejected the replayed instance")
    except (ValueError, AssertionError) as error:
        problems.append(f"research.ladder.audit raised {error}")
    return problems


def _instance(edge: Edge) -> Instance:
    return edge.instance


def _engine_decision(edges: Sequence[Edge], tag: str) -> tuple[str, str | None]:
    instances = [_instance(edge) for edge in edges]
    names = tuple(sorted({name_of(pop) for inst in instances for pop in inst.args}))
    hard = [
        *background(names)["reflexivity"],
        *background(names)["transitivity"],
        *core_constraints(instances, tag),
    ]
    result = Engine(names, hard, timeout_ms=60000).check()
    return result.decision, result.reason


def _p16_if_path(edges: Sequence[Edge]) -> str:
    """Run p16's compact checker for a genuine closed S/W chain; N is deliberately excluded."""
    if not edges or any(edge.shape not in {"S", "W"} for edge in edges):
        return "not-applicable:N-shaped edge is not a weak/strict path edge"
    if edges[0].shape != "S" or any(
        edges[i].right != edges[i + 1].left for i in range(len(edges) - 1)
    ):
        return "not-applicable:not a written S/W chain"
    if edges[-1].right != edges[0].left:
        return "not-applicable:not closed"
    return decide_without_completeness([edge.instance for edge in edges], "p19-route-a-p16/v1")


def _search_chains(edges: Sequence[Edge], *, include_n: bool) -> dict[str, Any]:
    ws = [edge for edge in edges if edge.shape in {"S", "W"}]
    ns = [edge for edge in edges if edge.shape == "N"] if include_n else []
    by_left: dict[Pop, list[Edge]] = {}
    for edge in ws:
        by_left.setdefault(edge.left, []).append(edge)
    for choices in by_left.values():
        choices.sort(key=lambda edge: (edge.principle, edge.right))
    found: list[dict[str, Any]] = []
    unknown: list[dict[str, Any]] = []
    checked = 0
    seen: set[tuple[tuple[str, Pop, Pop], ...]] = set()

    def evaluate(path: list[Edge], nedge: Edge | None = None) -> None:
        nonlocal checked
        chosen = [*path, *([nedge] if nedge is not None else [])]
        key = tuple((_edge_key(edge)) for edge in chosen)
        if key in seen:
            return
        seen.add(key)
        checked += 1
        decision, reason = _engine_decision(chosen, f"p19-route-a-{len(chosen)}")
        payload = {
            "edges": [edge.record() for edge in chosen],
            "decision": decision,
            "reason": reason,
            "p16_decision": _p16_if_path(path),
        }
        if decision == "unsat":
            found.append(payload)
        elif decision == "unknown":
            unknown.append(payload)

    def walk(start: Pop, node: Pop, path: list[Edge], seen_nodes: set[Pop]) -> None:
        if len(path) >= MAX_CHAIN_EDGES:
            return
        for edge in by_left.get(node, ()):
            if (
                edge.right == start
                and edge.shape == "S"
                or edge.right == start
                and edge.shape == "W"
            ):
                evaluate([*path, edge])
            if edge.right in seen_nodes:
                continue
            nxt = [*path, edge]
            if include_n and len(nxt) < MAX_CHAIN_EDGES:
                nodes = [start, *[step.right for step in nxt]]
                node_set = set(nodes)
                for nedge in ns:
                    if nedge.left in node_set and nedge.right in node_set:
                        evaluate(nxt, nedge)
            walk(start, edge.right, nxt, seen_nodes | {edge.right})

    for start in sorted(by_left):
        walk(start, start, [], {start})

    # N-shaped DA has no path direction.  This direct check catches the only one-edge / one-S
    # possibility and supplies an explicit obstruction record rather than silently dropping N.
    if include_n:
        for nedge in ns:
            evaluate([], nedge)
            for sedge in ws:
                if sedge.left in {nedge.left, nedge.right} and sedge.right in {
                    nedge.left,
                    nedge.right,
                }:
                    evaluate([sedge], nedge)

    return {
        "checked": checked,
        "unsat_candidates": found[:20],
        "unknown_candidates": unknown[:20],
        "unsat_count": len(found),
        "unknown_count": len(unknown),
    }


def _n_shape_obstruction() -> dict[str, Any]:
    """Machine-check the exact logical loss: N does not entail a reverse weak edge."""
    a, b = "A_not_worse", "B_not_worse"
    n_formula = Not(strict(a, b))
    hard = [
        *background((a, b))["reflexivity"],
        *background((a, b))["transitivity"],
        ground("da-thesis-n", DA_THESIS, n_formula, "p19-n-shape/v1", "thesis DA N-form"),
        ground(
            "incomparable-ab",
            "obstruction",
            conjunction(Not(weak(a, b)), Not(weak(b, a))),
            "p19-n-shape/v1",
            "incomparability witness",
        ),
    ]
    check = Engine((a, b), hard, timeout_ms=60000).check()
    rows = None
    if check.decision == "sat" and check.assignment is not None:
        rows = [
            "".join("1" if check.assignment[weak(left, right)] else "0" for right in (a, b))
            for left in (a, b)
        ]
    return {
        "formula": "not(strict(A, B union C))",
        "uniform_C": True,
        "background": "none",
        "reverse_weak_constraint": "not(weak(B union C, A)) is not derivable",
        "incomparable_model_decision": check.decision,
        "incomparable_model_reason": check.reason,
        "incomparable_model_relata": [a, b],
        "incomparable_model_rows": rows,
        "completeness_used": False,
    }


def _mixed_da_replay() -> dict[str, Any]:
    mixed = _plus((1,) * 39, (3,), (6,))
    source = Edge(DA_2003, mixed, (5,))
    thesis = Edge(DA_THESIS, (5,), mixed)
    return {
        "source_da_record": source.record(),
        "thesis_replay_problems": verify_edge(thesis.record(), ladder=LADDER, witness=Witness({})),
        "thesis_ladder_audit": audit(thesis.instance, LADDER, Witness({})),
        "conclusion": "the published mixed positive addition is not a thesis-DA instance",
    }


def run() -> dict[str, Any]:
    focus = focus_populations()
    subbags = _subbags(focus)
    all_principles = (ED, GNEP, VRC, NE_2003, NE_THESIS, DA_2003, DA_THESIS)
    pools = {principle: _pool(focus, principle, subbags) for principle in all_principles}
    replay: dict[str, Any] = {}
    for principle, edges in pools.items():
        failures = []
        for index, edge in enumerate(edges):
            problems = _replay(edge)
            if problems:
                failures.append({"index": index, "problems": problems, "record": edge.record()})
        replay[principle] = {
            "candidates": len(edges),
            "verified": len(edges) - len(failures),
            "failures": failures[:20],
            "failure_count": len(failures),
        }

    variants: dict[str, Any] = {}
    for label, ne, da in VARIANTS:
        selected = [*pools[ED], *pools[GNEP], *pools[VRC], *pools[ne], *pools[da]]
        chain = _search_chains(selected, include_n=da == DA_THESIS)
        variants[label] = {
            "principles": [ED, GNEP, VRC, ne, da],
            "edge_pool_counts": {
                principle: len(pools[principle]) for principle in (ED, GNEP, VRC, ne, da)
            },
            "chain_bound_edges": MAX_CHAIN_EDGES,
            "population_life_bound": MAX_LIVES,
            "witness_integer_bound": WITNESS_MAX,
            "chain_search": chain,
            "decision": "unsat"
            if chain["unsat_count"]
            else ("unknown" if chain["unknown_count"] else "sat"),
            "verdict": "bounded-unsat-candidate"
            if chain["unsat_count"]
            else "bounded-no-certified-contradiction",
            "interpretation": "N-shaped thesis DA is retained; bounded SAT/no-chain is not consistency evidence",
        }

    return {
        "scope": "bounded Route A edge-pool and <=6-edge chain search on a deterministic 96-population focus from D_8; not source-general and not a finite-ladder model",
        "ladder": list(LADDER.levels),
        "focus": [list(pop) for pop in focus],
        "focus_sha256": hashlib.sha256(
            json.dumps([list(pop) for pop in focus], separators=(",", ":")).encode()
        ).hexdigest(),
        "bounds": {
            "max_lives_per_relatum": MAX_LIVES,
            "focus_populations": len(focus),
            "max_chain_edges": MAX_CHAIN_EDGES,
            "witness_integer_max": WITNESS_MAX,
        },
        "witness_scope": "NE and GNEP witnesses are varied per edge in the finite valid integer grid; VRC tuples are varied in the same grid; this does not quantify arbitrary source witness functions n(x,y) or (u(z),y(z),n(z))",
        "witness_grid": {
            principle: len(_witness_options(principle))
            for principle in (NE_2003, NE_THESIS, GNEP, VRC)
        },
        "thesis_da_obstruction": _n_shape_obstruction(),
        "mixed_da_replay": _mixed_da_replay(),
        "replay": replay,
        "serialized_edge_pools": {
            principle: [edge.record() for edge in pools[principle]] for principle in all_principles
        },
        "variants": variants,
        "unknown_policy": "unknown is preserved with solver reason; no unknown was converted to SAT or UNSAT",
        "machine_checker": "research.lab.Engine with reflexivity+transitivity and research.p16_ne_top.decide_without_completeness on every closed S/W path",
    }


def main() -> None:
    started = time.monotonic()
    data = run()
    data["wall_time_s"] = round(time.monotonic() - started, 1)
    print(json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False))


if __name__ == "__main__":
    main()
