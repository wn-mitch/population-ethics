"""Edge realizations: principle paths that realize one derived-principle edge (D-011).

``research/realizations.toml`` records each realization with its source lemma and one or more
solver-found example chains. ``verify_example`` re-checks an example: every instance passes the
ladder audit, and the chain entails the target in every preorder (no completeness).
``contractions`` applies the realizations to a core and returns every distinct fully contracted
core; canon.py turns those into the L2 form.
"""

from __future__ import annotations

import tomllib
from collections import Counter
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import Any

from population_ethics.relations import Not, weak
from research.lab import Engine, background, ground
from research.ladder import Ladder, Witness, audit
from research.p6_schema import core_constraints, name_of
from research.readings import require_reviewed
from research.schema import Instance, Pop

PATH = Path(__file__).with_name("realizations.toml")
MAX_CONTRACTIONS = 256  # distinct intermediate cores explored per call


@dataclass(frozen=True)
class Variant:
    realization: str
    pattern: str  # "run" or "exact"
    sources: tuple[str, ...]  # the `from` principles
    target: str  # the derived principle
    lemma: str  # reading id of the source lemma


@dataclass(frozen=True)
class Realization:
    id: str
    pattern: str
    reason: str
    variants: tuple[Variant, ...]
    examples: tuple[Mapping[str, Any], ...]


@cache
def load(path: Path = PATH) -> tuple[Realization, ...]:
    rows = tomllib.loads(path.read_text())["realizations"]
    out = []
    for row in rows:
        if row["pattern"] not in {"run", "exact"}:
            raise ValueError(f"{row['id']}: unknown pattern {row['pattern']}")
        variants = tuple(
            Variant(row["id"], row["pattern"], tuple(v["from"]), v["to"], v["source"])
            for v in row["variants"]
        )
        for v in variants:
            require_reviewed([*v.sources, v.target, v.lemma])
            if v.pattern == "run" and len(v.sources) != 1:
                raise ValueError(f"{row['id']}: a run pattern takes one source principle")
        out.append(
            Realization(
                row["id"], row["pattern"], row["reason"], variants, tuple(row.get("example", ()))
            )
        )
    return tuple(out)


def variants() -> tuple[Variant, ...]:
    return tuple(v for r in load() for v in r.variants)


# ---------------------------------------------------------------------------------------------
# Example verification.


def _pop(values: Sequence[int]) -> Pop:
    return tuple(sorted(values))


def _resolve(name: str, variant: Variant) -> str:
    """Example principles without a work prefix stand for the variant's own principles."""
    if ":" in name:
        return name
    if name == variant.target.split(":", 1)[1]:
        return variant.target
    (source,) = variant.sources
    return source


def example_instances(
    example: Mapping[str, Any], variant: Variant
) -> tuple[list[Instance], Instance]:
    chain = [
        Instance(_resolve(c["principle"], variant), tuple(_pop(a) for a in c["args"]))
        for c in example["chain"]
    ]
    t = example["target"]
    return chain, Instance(_resolve(t["principle"], variant), tuple(_pop(a) for a in t["args"]))


def verify_example(example: Mapping[str, Any], variant: Variant) -> dict[str, Any]:
    ladder = Ladder(**example["ladder"])
    witness = Witness(example["witness"])
    chain, target = example_instances(example, variant)
    names = tuple(sorted({name_of(p) for i in [*chain, target] for p in i.args}))
    bg = background(names)
    negated = ground(
        "target-negation",
        "target",
        Not(weak(name_of(target.args[0]), name_of(target.args[1]))),
        "realization-check/v1",
        "The target fails.",
    )
    constraints = core_constraints(chain, "realization-check/v1")
    decision = (
        Engine(names, [*bg["reflexivity"], *bg["transitivity"], *constraints, negated])
        .require()
        .decision
    )
    return {
        "chain_audit": all(audit(i, ladder, witness) for i in chain),
        "target_audit": audit(target, ladder, witness),
        "chain_principles_match": Counter(i.principle for i in chain).keys() <= set(variant.sources)
        and (
            variant.pattern == "run"
            or Counter(i.principle for i in chain) == Counter(variant.sources)
        ),
        "entailed_without_completeness": decision == "unsat",
        "is_path": _as_path(chain, target.args[0], target.args[1]) is not None,
    }


def _as_path(chain: Sequence[Instance], start: Pop, end: Pop) -> list[Instance] | None:
    """Order the chain as start ⪰ … ⪰ end, if it is one directed path."""
    by_left = {i.args[0]: i for i in chain}
    if len(by_left) != len(chain):
        return None
    path: list[Instance] = []
    node = start
    while node in by_left and len(path) < len(chain):
        edge = by_left[node]
        path.append(edge)
        node = edge.args[1]
    return path if node == end and len(path) == len(chain) else None


# ---------------------------------------------------------------------------------------------
# Contraction.


def _weak(inst: Instance) -> tuple[Pop, Pop] | None:
    """The instance as a directed ⪰ edge (complete-branch normalization), or None."""
    if inst.shape == "W":
        return inst.args[0], inst.args[1]
    if inst.shape == "N":
        return inst.args[1], inst.args[0]
    return None


def _windows(core: Sequence[Instance], variant: Variant) -> Iterator[tuple[list[int], Pop, Pop]]:
    """Series windows the variant contracts: (edge indices in path order, start, end).

    A window is a directed ⪰ path of the variant's source edges whose internal relata are
    incident to nothing else in the core (degree 2), so replacing it by one edge loses no
    other structure. ``run`` windows are maximal; ``exact`` windows match the sources exactly.
    """
    degree: Counter[Pop] = Counter(x for inst in core for x in inst.args)
    edges = {
        j: e
        for j, inst in enumerate(core)
        if inst.principle in variant.sources and (e := _weak(inst)) is not None
    }
    out_of: dict[Pop, int] = {}
    into: dict[Pop, int] = {}
    for j, (a, b) in edges.items():
        out_of.setdefault(a, j)
        into.setdefault(b, j)

    def forward(j: int, limit: int) -> list[int]:
        path = [j]
        node = edges[j][1]
        while (
            len(path) < limit and degree[node] == 2 and node in out_of and out_of[node] not in path
        ):
            path.append(out_of[node])
            node = edges[path[-1]][1]
        return path

    seen: set[frozenset[int]] = set()
    if variant.pattern == "run":
        for j in edges:
            first = j
            while True:
                a = edges[first][0]
                if degree[a] == 2 and a in into and into[a] != j and into[a] != first:
                    first = into[a]
                    if first == j:
                        break
                else:
                    break
            path = forward(first, len(edges))
            key = frozenset(path)
            if key not in seen:
                seen.add(key)
                s, stop = edges[path[0]][0], edges[path[-1]][1]
                if s != stop:
                    yield path, s, stop
        return
    need = Counter(variant.sources)
    for j in edges:
        path = forward(j, sum(need.values()))
        key = frozenset(path)
        if Counter(core[k].principle for k in path) == need and key not in seen:
            seen.add(key)
            s, stop = edges[path[0]][0], edges[path[-1]][1]
            if s != stop:
                yield path, s, stop


def contract_once(core: Sequence[Instance]) -> Iterator[tuple[Instance, ...]]:
    for variant in variants():
        for path, start, end in _windows(core, variant):
            kept = [inst for k, inst in enumerate(core) if k not in path]
            yield tuple([*kept, Instance(variant.target, (start, end))])


def contractions(core: Sequence[Instance]) -> list[tuple[Instance, ...]]:
    """Every distinct fully contracted core reachable by applying realizations in any order."""
    start = tuple(sorted(core, key=repr))
    seen = {start}
    frontier = [start]
    finals: set[tuple[Instance, ...]] = set()
    while frontier:
        current = frontier.pop()
        successors = [tuple(sorted(c, key=repr)) for c in contract_once(current)]
        if not successors:
            finals.add(current)
        for s in successors:
            if s not in seen:
                if len(seen) >= MAX_CONTRACTIONS:
                    raise RuntimeError("contraction search exceeded MAX_CONTRACTIONS")
                seen.add(s)
                frontier.append(s)
    return sorted(finals, key=repr)
