"""Exact canonical forms of proof skeletons, by nauty canonical labelling.

A skeleton is a hypergraph: relata, and labelled edges with ordered arguments. It is encoded as
a vertex-coloured simple graph with one vertex per relatum, one vertex per edge coloured by its
label, and one vertex per argument slot coloured by position, joined to its edge and its
relatum. Two skeletons have equal canonical forms exactly when some relabelling of relata maps
one edge multiset onto the other, at any size (``schema.canonical_skeleton`` is exact only up to
9 relata).

Levels, from coarsest to finest:
- ``L0``: shape only, complete-branch normalized (``N`` becomes ``W`` with arguments swapped).
  This is the motif level.
- ``L1``: role and normalized shape (research/roles.toml).
- ``principle``: principle id and raw shape; used to cross-check the brute-force form.
- ``L2`` (``canonical_l2``): L1 after contracting recorded edge realizations, such as a run of
  Non-Elitism steps into one Condition β edge.
"""

from __future__ import annotations

from collections.abc import Hashable, Sequence
from typing import Literal

import pynauty  # type: ignore[import-untyped]

from research.known import normalize
from research.schema import Instance

Level = Literal["L0", "L1", "principle"]
LabelledEdge = tuple[Hashable, tuple[int, ...]]
Form = tuple[int, tuple[tuple[str, tuple[int, ...]], ...]]  # (relata count, sorted edges)


def labelled_edges(core: Sequence[Instance], level: Level) -> tuple[int, list[LabelledEdge]]:
    """Relata count and edges over relata indices, labelled for the requested level."""
    if level == "principle":
        nodes = sorted({x for inst in core for x in inst.args})
        index = {x: i for i, x in enumerate(nodes)}
        return len(nodes), [
            ((inst.principle, inst.shape), tuple(index[x] for x in inst.args)) for inst in core
        ]
    nodes, edges = normalize(core)
    if level == "L0":
        return len(nodes), [(shape, args) for _, shape, args in edges]
    return len(nodes), [((role, shape), args) for role, shape, args in edges]


def canonical_form(relata: int, edges: Sequence[LabelledEdge]) -> Form:
    """Canonical (relata count, sorted edge tuple) under relabelling of relata."""
    labels = sorted({repr(label) for label, _ in edges})
    arity = max((len(args) for _, args in edges), default=0)
    label_index = {label: i for i, label in enumerate(labels)}
    n_edges = len(edges)
    slot_base = relata + n_edges
    slots = [(e, pos) for e, (_, args) in enumerate(edges) for pos in range(len(args))]
    adjacency: dict[int, list[int]] = {v: [] for v in range(slot_base + len(slots))}
    for s, (e, pos) in enumerate(slots):
        slot = slot_base + s
        adjacency[slot] += [relata + e, edges[e][1][pos]]
    # Colour classes in a fixed order: relata, one class per edge label, one per slot position.
    classes: list[set[int]] = [set(range(relata))]
    classes += [
        {relata + e for e, (label, _) in enumerate(edges) if label_index[repr(label)] == i}
        for i in range(len(labels))
    ]
    classes += [
        {slot_base + s for s, (_, pos) in enumerate(slots) if pos == p} for p in range(arity)
    ]
    graph = pynauty.Graph(
        len(adjacency),
        directed=False,
        adjacency_dict=adjacency,
        vertex_coloring=[c for c in classes if c],
    )
    order = pynauty.canon_label(graph)  # order[i] = original vertex at canonical position i
    rank = {v: i for i, v in enumerate(v for v in order if v < relata)}
    form = sorted((repr(label), tuple(rank[a] for a in args)) for label, args in edges)
    return relata, tuple(form)


def canonical(core: Sequence[Instance], level: Level = "L1") -> Form:
    return canonical_form(*labelled_edges(core, level))


def canonical_l2(core: Sequence[Instance]) -> tuple[Form, ...]:
    """L2: the L1 forms of every full contraction of the core by the recorded edge realizations
    (research/realizations.toml). More than one form means contractions overlap ambiguously;
    all are reported rather than one being picked.
    """
    from research.realizations import contractions

    return tuple(sorted({canonical(c, "L1") for c in contractions(core)}))
