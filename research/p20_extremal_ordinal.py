"""Phase 20, route B: extremal/support-statistic orders for Q-011's 2003 weakenings.

Q-011 asks whether the 2003 VRC impossibility survives weakening Non-Elitism to the thesis's
ranged background (``D subset R(y, x)``) and/or Dominance Addition to the thesis's not-worse form.
Phase 19 pushed two universal certificate routes and left both open; the coefficient control there
excluded *translation-invariant* lexicographic-linear orders on ``W_-1 .. W_6`` and asked for a
"background-dependent model" instead.  This module answers one structural question on that route
with an exact, all-size result rather than a model:

    No order that depends only on *which levels are occupied* -- a support statistic, i.e. the
    lower and upper support and everything between them, with all multiplicities quotiented away --
    satisfies the three conditions Egalitarian Dominance, thesis ranged Non-Elitism and thesis
    Dominance Addition.  The refutation is a four-step cycle of primitive source instances, so it
    holds at every finite population size and for *every* legal witness of those conditions, and it
    therefore refutes support-statistic orders for all four Q-011 variants (a)-(d) at once.

What is proved, and what is only bounded:

1. **Proved, all sizes, all witnesses (support-determined class).**  The cycle

       {W_3}  >-  {W_2}  ~  {W_2,W_2}  >=  {W_3,W_1}  ~  {W_3,W_3,W_1}  >=  {W_4,W_1,W_1}  ~  {W_4,W_1}  >=  {W_3}

   reads, with ``~`` the quotienting step (a support-determined order cannot separate two
   populations with the same occupied support):

       ED      : {W_3}            >- {W_2}                  (Egalitarian Dominance, x = W_3)
       NE      : {W_2,W_2}        >= {W_3,W_1}              (Non-Elitism, x = W_3, y = W_1, D = empty)
       NE      : {W_3,W_3,W_1}    >= {W_4,W_1,W_1}          (Non-Elitism, x = W_4, y = W_1, D = {W_1})
       DA      : {W_4,W_1}        >= {W_3}                  (Dominance Addition, A = {W_3}, B = {W_4}, C = {W_1})

   giving ``{W_3} >- {W_3}``.  Every one of the four pairs is an audited ladder instance
   (``research.ladder.audit``), and the *support* of each side is independent of the existential
   witness: Non-Elitism's pair has supports ``{W_x-1} union supp(D)`` and ``{W_x, W_y} union
   supp(D)`` whatever ``n`` is, Dominance Addition's pair is ``supp(B) union {W_y}`` versus
   ``supp(A)`` whatever the sizes are, and Egalitarian Dominance has no existential at all.
   So the obstruction is valid for every witness of Non-Elitism (ranged or unrestricted), every
   witness of Dominance Addition (thesis not-worse or 2003 weak), and every legal level choice.
   GNEP and VRC avoidance are not used, so their witnesses are unconstrained.

2. **Proved, all sizes (coarser class).**  A fortiori, any order that ignores the arrangement of the
   levels below ``W_4`` cannot even satisfy Egalitarian Dominance alone: for every ``k >= 1`` the
   instance ``{W_3}^k >- {W_2}^k`` has the same population size and the same ``W_4``-and-above
   multiset (both empty) on its two sides.  Egalitarian Dominance has no existential, so this is
   witness-free.

3. **Bounded (discovery only).**  On the populations of at most six lives over ``W_-1 .. W_6``,
   with the displayed witnesses, the same quotient-and-cycle search is run *per variant* (the four
   variants are never pooled, since their Non-Elitism and Dominance Addition instances differ) and
   refutes the finer support-statistic families -- (support, size), (min, max, size), (support,
   size, count at the top level), (support, size, ``W_3``-and-above multiset) -- on *every* one of
   the four variants, while finding no strict cycle for the count-vector control (an arbitrary
   total preorder) on any of them.  Absence at this cap is not a consistency claim: it only says
   the count-sensitive route is not refuted here, and it agrees with the earlier bounded scans.

4. **Failed explicit candidates.**  Four natural piecewise / extremal / order-statistic candidates
   were tried as models, each refuted by an explicitly audited source instance:
   the conditional-cap order (cap only when a negative life is present) fails GNEP avoidance at
   ``z = W_-1`` with the negative-free background ``E = {W_3}^5``; the always-capped order fails
   Egalitarian Dominance at ``x = W_3``, ``k = 8``; the lower-median-first order statistic fails
   thesis Dominance Addition at ``A = {W_3, W_3}``, ``B = {W_4, W_4}``, ``C = {W_1, W_1}``; and
   total utility fails VRC avoidance against the unbounded low bag ``B = {W_3}^5``.  No order that
   fails an audited instance is a model, and no failure here is a consistency result.

Scope: ladder ``W_-1 .. W_6`` (the project's frozen ladder), finite nonempty populations of level
indices, the four Q-011 variants over the thesis/2003 Non-Elitism and Dominance Addition forms.
Nothing here is a model and nothing here is an impossibility theorem for the weakened condition
sets themselves: the count-sensitive (profile-determined) route remains open.
"""

from __future__ import annotations

import itertools
import json
import time
from collections import Counter, defaultdict, deque
from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from typing import Any

from research.ladder import Witness, audit, instances_over
from research.p8_catalogue import LADDER
from research.schema import Instance, Pop

LEVELS: tuple[int, ...] = LADDER.levels

# The four Q-011 variants, in the phase-17/19 order, as (label, Non-Elitism, Dominance Addition).
ED = "arrhenius-2003:egalitarian-dominance"
ED_THESIS = "thesis:egalitarian-dominance"
NE_2003 = "arrhenius-2003:non-elitism"
NE_THESIS = "thesis:non-elitism"
DA_2003 = "arrhenius-2003:dominance-addition"
DA_THESIS = "thesis:dominance-addition"
GNEP = "arrhenius-2003:general-non-extreme-priority"
VRC = "arrhenius-2003:vrc-avoidance"

VARIANTS: tuple[tuple[str, str, str], ...] = (
    ("(a) original", NE_2003, DA_2003),
    ("(b) ranged Non-Elitism", NE_THESIS, DA_2003),
    ("(c) thesis not-worse Dominance Addition", NE_2003, DA_THESIS),
    ("(d) both weakened (weakest five)", NE_THESIS, DA_THESIS),
)

# Every existential used by the bounded scan is displayed.  Ranged Non-Elitism's n = 1 and the
# GNEP/VRC witnesses are the phase-19 choices; the support-determined refutation below never uses
# GNEP or VRC and does not depend on any of these values.
WITNESSES: Witness = Witness(
    {
        "non-elitism": {"n": 1},
        "general-non-extreme-priority": {"u": 4, "y": 3, "n": 1},
        "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 3, "m": 1},
    }
)
GNEP_N, GNEP_U, GNEP_Y = 1, 4, 3


def _supp(pop: Pop) -> tuple[int, ...]:
    return tuple(sorted(set(pop)))


def _join(*parts: Pop) -> Pop:
    return tuple(sorted(v for part in parts for v in part))


# ---------------------------------------------------------------------------------------------
# Primitive source instances, generated straight from the readings' quantifier structure and each
# replayed by the project's own independent audit before it is used.


def ed_pairs(cap: int) -> Iterator[tuple[str, Pop, Pop, str]]:
    """Egalitarian Dominance: A = {W_x}^k, B any same-size bag with every life below W_x."""
    for x in LEVELS:
        below = [v for v in LEVELS if v < x]
        if not below:
            continue
        for k in range(1, cap + 1):
            for b in itertools.combinations_with_replacement(below, k):
                yield ED, (x,) * k, b, f"ED x=W_{x} k={k}"


def ne_pairs(cap: int, principle: str, n: int) -> Iterator[tuple[str, Pop, Pop, str]]:
    """Non-Elitism: C union D >= A union B union D, A = {W_x}, B = {W_y}^n, C = {W_x-1}^(n+1)."""
    ranged = principle == NE_THESIS
    for x in LEVELS:
        if x - 1 not in LEVELS:
            continue
        for y in LEVELS:
            if not (x - 1 > y):
                continue
            range_levels = [v for v in LEVELS if y <= v <= x] if ranged else list(LEVELS)
            c = (x - 1,) * (n + 1)
            ab = _join((x,), (y,) * n)
            for size in range(0, cap - (n + 1) + 1):
                for d in itertools.combinations_with_replacement(range_levels, size):
                    if len(c) + len(d) > cap or len(ab) + len(d) > cap:
                        continue
                    yield (
                        principle,
                        _join(c, d),
                        _join(ab, d),
                        f"NE x=W_{x} y=W_{y} n={n} D={list(d)}",
                    )


def da_pairs(cap: int, principle: str) -> Iterator[tuple[str, Pop, Pop, str]]:
    """Dominance Addition: A (below W_x), B (same size, at or above W_x), C = {W_y}^k, y > 0."""
    not_worse = principle == DA_THESIS
    for n in range(1, cap + 1):
        for a in itertools.combinations_with_replacement(LEVELS, n):
            for x in LEVELS:
                if not all(v < x for v in a):
                    continue
                for b in itertools.combinations_with_replacement([v for v in LEVELS if v >= x], n):
                    for k in range(1, cap - n + 1):
                        if len(b) + k > cap:
                            continue
                        for y in range(1, 7):
                            bc = _join(b, (y,) * k)
                            # thesis: the instance asserts not(A >- B union C); 2003: B union C >= A
                            yield (
                                principle,
                                a if not_worse else bc,
                                bc if not_worse else a,
                                f"DA A={list(a)} B={list(b)} y=W_{y} k={k}",
                            )


def gnep_pairs(cap: int) -> Iterator[tuple[str, Pop, Pop, str]]:
    """General Non-Extreme Priority: A union C union E >= B union D union E, any background E."""
    for z in LEVELS:
        if z + 1 not in LEVELS:
            continue
        for x in [v for v in LEVELS if v >= GNEP_U]:
            for b in itertools.combinations_with_replacement(range(1, GNEP_Y + 1), GNEP_N):
                for size in range(0, cap - GNEP_N - 1 + 1):
                    for e in itertools.combinations_with_replacement(LEVELS, size):
                        left = _join((x,) * GNEP_N, (z,), e)
                        right = _join(b, (z + 1,), e)
                        if len(left) > cap or len(right) > cap:
                            continue
                        yield GNEP, left, right, f"GNEP z=W_{z} x=W_{x} B={list(b)} E={list(e)}"


def vrc_pairs(cap: int) -> Iterator[tuple[str, Pop, Pop, str]]:
    """VRC avoidance: A (n lives at one level >= W_u) >= B union C, C = m lives at W_x < 0."""
    w = WITNESSES.get("vrc-avoidance")
    for z in [v for v in LEVELS if v >= w["u"]]:
        a = (z,) * w["n"]
        for size in range(1, cap - w["m"] + 1):
            for b in itertools.combinations_with_replacement(range(1, w["y"] + 1), size):
                if len(b) + w["m"] > cap:
                    continue
                right = _join(b, (w["x"],) * w["m"])
                yield VRC, a, right, f"VRC z=W_{z} B={list(b)} C=W_{w['x']}^{w['m']}"


def checked_pairs(
    principles: Sequence[str], cap: int, witness: Witness = WITNESSES
) -> list[tuple[str, Instance, str]]:
    """Generate the primitive instances of the given principles with at most ``cap`` lives.

    Every generated pair is replayed by ``research.ladder.audit``; a pair the audit rejects is a
    generator bug and raises immediately.  The generation is a *bounded* enumeration: it is a
    discovery domain, and only the hand-written cycles below are read as proofs.
    """
    out: list[tuple[str, Instance, str]] = []
    for principle in principles:
        if principle == ED:
            source: Iterable[tuple[str, Pop, Pop, str]] = ed_pairs(cap)
        elif principle in (NE_THESIS, NE_2003):
            source = ne_pairs(cap, principle, WITNESSES.get("non-elitism")["n"])
        elif principle in (DA_THESIS, DA_2003):
            source = da_pairs(cap, principle)
        elif principle == GNEP:
            source = gnep_pairs(cap)
        elif principle == VRC:
            source = vrc_pairs(cap)
        else:
            raise ValueError(f"no generator for {principle}")
        for pid, left, right, note in source:
            if left == right:
                continue  # audit rejects a comparison of a population with itself
            instance = Instance(pid, (left, right))
            if not audit(instance, LADDER, witness):
                raise AssertionError(
                    f"generated instance fails its own audit: {note} {left} {right}"
                )
            out.append((pid, instance, note))
    return out


# ---------------------------------------------------------------------------------------------
# Section 1: the support-determined refutation, written out as explicit populations.

SUPPORT_CYCLE: tuple[tuple[str, Pop, Pop, str, str], ...] = (
    (
        ED,
        (3,),
        (2,),
        "strict",
        "Egalitarian Dominance, x = W_3, one life each, all B lives below W_3",
    ),
    (
        NE_THESIS,
        (2, 2),
        (3, 1),
        "weak",
        "ranged Non-Elitism, x = W_3, y = W_1, n = 1, D = empty: C = {W_2}^2 >= A union B = {W_3, W_1}",
    ),
    (
        NE_THESIS,
        (1, 3, 3),
        (1, 1, 4),
        "weak",
        "ranged Non-Elitism, x = W_4, y = W_1, n = 1, D = {W_1}: C union D = {W_3}^2 union {W_1}",
    ),
    (
        DA_THESIS,
        (3,),
        (1, 4),
        "not-strict",
        "thesis Dominance Addition, A = {W_3}, B = {W_4}, C = {W_1}: not(A >- B union C)",
    ),
)

# support quotienting: a support-determined order gives equal scores to equal supports.
SUPPORT_QUOTIENT: tuple[tuple[Pop, Pop, str], ...] = (
    ((2, 2), (2,), "support {W_2}"),
    ((3, 1), (1, 3, 3), "support {W_1, W_3}"),
    ((1, 1, 4), (1, 4), "support {W_1, W_4}"),
)


def support_cycle_evidence() -> dict[str, Any]:
    """Audit every step of the support-determined refutation and record the chain."""
    rows: list[dict[str, Any]] = []
    for principle, left, right, kind, note in SUPPORT_CYCLE:
        instance = Instance(principle, (left, right))
        ok = audit(instance, LADDER, WITNESSES)
        if not ok:
            raise AssertionError(f"support cycle step fails audit: {instance}")
        rows.append(
            {
                "principle": principle,
                "left": list(left),
                "right": list(right),
                "requirement": kind,
                "note": note,
                "ladder_audit": ok,
            }
        )
    return {
        "claim": (
            "no total preorder determined by the occupied level set satisfies "
            "{Egalitarian Dominance, thesis ranged Non-Elitism, thesis not-worse Dominance Addition}"
        ),
        "chain": (
            "{W_3} >- {W_2} ~ {W_2,W_2} >= {W_3,W_1} ~ {W_3,W_3,W_1} "
            ">= {W_4,W_1,W_1} ~ {W_4,W_1} >= {W_3}"
        ),
        "contradiction": "{W_3} >- {W_3}, by transitivity of the total preorder",
        "steps": rows,
        "quotient_steps": [
            {"same_support": sorted({*p, *q}), "populations": [list(p), list(q)], "why": why}
            for p, q, why in SUPPORT_QUOTIENT
        ],
        "scope": "all finite population sizes; ladder W_-1..W_6",
    }


def witness_independence() -> dict[str, Any]:
    """The support of each Non-Elitism side does not depend on the existential n, either form.

    For every n in the displayed range the generated ranged and unrestricted Non-Elitism instances
    have side supports of the form ``{W_x-1} union S`` and ``{W_x, W_y} union S`` with S = supp(D),
    so the support-determined cycle's two Non-Elitism edges survive every legal witness of either
    form.  The dominance-addition edge has no existential and Egalitarian Dominance has none.
    """
    domain = [p for k in range(1, 7) for p in itertools.combinations_with_replacement(LEVELS, k)]
    ranged: dict[int, set[tuple[tuple[int, ...], tuple[int, ...]]]] = {}
    anyd: dict[int, set[tuple[tuple[int, ...], tuple[int, ...]]]] = {}
    for n in (1, 2, 3, 4):
        w = Witness({"non-elitism": {"n": n}})
        ranged[n] = {
            (_supp(i.args[0]), _supp(i.args[1]))
            for i in instances_over(domain, LADDER, w, [NE_THESIS])
        }
        anyd[n] = {
            (_supp(i.args[0]), _supp(i.args[1]))
            for i in instances_over(domain, LADDER, w, [NE_2003])
        }
    pairs = {
        "ranged W_3/W_1": ((2,), (1, 3)),
        "ranged W_4/W_1 with D = {W_1}": ((1, 3), (1, 4)),
        "unrestricted W_3/W_1": ((2,), (1, 3)),
        "unrestricted W_4/W_1 with D = {W_1}": ((1, 3), (1, 4)),
    }
    present = {
        name: {
            "ranged": all(pair in ranged[n] for n in ranged),
            "unrestricted": all(pair in anyd[n] for n in anyd),
        }
        for name, pair in pairs.items()
    }
    return {
        "non_elitism_witnesses_tested": [1, 2, 3, 4],
        "cycle_support_pairs_present_for_every_witness": present,
        "conclusion": (
            "the two Non-Elitism edges exist with the same supports for every tested witness of "
            "both forms; the argument that the side supports are n-independent is the counting "
            "identity |C| = n+1 at W_x-1 and |A| = 1, |B| = n at W_x and W_y"
        ),
    }


# ---------------------------------------------------------------------------------------------
# Section 2: the coarser class, refuted by Egalitarian Dominance alone.


def sub_w4_refutation(k_max: int) -> dict[str, Any]:
    """Any order indifferent to the arrangement below W_4 fails Egalitarian Dominance.

    For each k, ``{W_3}^k >- {W_2}^k`` is an Egalitarian Dominance instance and the two sides have
    the same size and the same (empty) W_4-and-above multiset.  Egalitarian Dominance has no
    existential, so this holds for every k with no witness dependence.
    """
    rows = []
    for k in (1, 2, 4, 8, k_max):
        left, right = (3,) * k, (2,) * k
        instance = Instance(ED, (left, right))
        rows.append(
            {
                "k": k,
                "left": list(left),
                "right": list(right),
                "size": k,
                "w4_and_above_multiset": [],
                "ladder_audit": audit(instance, LADDER, WITNESSES),
            }
        )
    return {
        "claim": (
            "no total preorder determined by (population size, multiset of lives at or above W_4) "
            "satisfies Egalitarian Dominance"
        ),
        "reason": "{W_3}^k >- {W_2}^k for every k >= 1, with identical size and identical high part",
        "rows": rows,
        "scope": "all finite sizes; witness-free",
    }


# ---------------------------------------------------------------------------------------------
# Section 3: bounded quotient scan over the finer support-statistic families.

FAMILIES: tuple[tuple[str, str, Callable[[Pop], Any]], ...] = (
    (
        "support-determined (extremal support statistic)",
        "depends only on the set of occupied levels",
        lambda p: (_supp(p),),
    ),
    ("support + size", "occupied levels plus the population size", lambda p: (_supp(p), len(p))),
    (
        "min + max + size",
        "lower and upper support plus the size (span statistic)",
        lambda p: (min(p), max(p), len(p)),
    ),
    (
        "support + size + count at the top level",
        "occupied levels, size, and the number of lives at the maximum level",
        lambda p: (_supp(p), len(p), Counter(p)[max(p)]),
    ),
    (
        "support + size + W_3-and-above multiset",
        "occupied levels, size, and the multiset of lives at W_3 and above",
        lambda p: (_supp(p), len(p), tuple(sorted(v for v in p if v >= 3))),
    ),
    (
        "count vector (control: no invariant beyond the population)",
        "the population itself; any total preorder is of this form",
        lambda p: tuple(sorted(p)),
    ),
)


def _scc(nodes: Sequence[Any], adjacency: Mapping[Any, Iterable[Any]]) -> dict[Any, int]:
    """Iterative Tarjan strongly-connected components of a quotient graph."""
    index: dict[Any, int] = {}
    low: dict[Any, int] = {}
    on_stack: dict[Any, bool] = {}
    stack: list[Any] = []
    comp: dict[Any, int] = {}
    counter = 0
    ncomp = 0
    for root in nodes:
        if root in index:
            continue
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on_stack[root] = True
        work: list[tuple[Any, Iterator[Any]]] = [(root, iter(adjacency.get(root, ())))]
        while work:
            node, it = work[-1]
            advanced = False
            for nxt in it:
                if nxt not in index:
                    index[nxt] = low[nxt] = counter
                    counter += 1
                    stack.append(nxt)
                    on_stack[nxt] = True
                    work.append((nxt, iter(adjacency.get(nxt, ()))))
                    advanced = True
                    break
                if on_stack.get(nxt):
                    low[node] = min(low[node], index[nxt])
            if advanced:
                continue
            work.pop()
            if low[node] == index[node]:
                while True:
                    member = stack.pop()
                    on_stack[member] = False
                    comp[member] = ncomp
                    if member == node:
                        break
                ncomp += 1
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[node])
    return comp


def forced_direction(instance: Instance) -> tuple[Pop, Pop]:
    """The instance's two populations in requirement order: ``(better_side, worse_side)``.

    Egalitarian Dominance, Non-Elitism, GNEP and VRC avoidance are all stated as ``left ⪰ right``
    with ``left`` the first argument.  Thesis Dominance Addition is N-shaped: its arguments are
    ``(A, B union C)`` and it asserts ``not(A >- B union C)``, so under completeness the required
    weak comparison runs *from* the second argument *to* the first.  The 2003 weak form already
    states ``B union C ⪰ A`` with that order, so only the thesis form is reversed here.
    """
    left, right = instance.args
    if instance.principle == DA_THESIS:
        return right, left
    return left, right


def _key_cycle(
    pairs: Sequence[tuple[str, Instance, str]],
    key: Callable[[Pop], Any],
    strict_edge: tuple[Pop, Pop, str],
) -> dict[str, Any] | None:
    """Reconstruct the quotient cycle through one violating strict edge.

    The cycle lives in the family's own fibre space: the strict edge ``better >- worse`` fixes two
    classes, and a path from ``key(worse)`` back to ``key(better)`` along the quotient edges -- each
    step realized by a primitive instance -- gives ``worse ⪰ ... ⪰ better``, contradicting the
    strict step for every order constant on the fibres.
    """
    better, worse, principle = strict_edge
    target = key(better)
    start = key(worse)
    adjacency: dict[Any, set[Any]] = defaultdict(set)
    for _, instance, _ in pairs:
        b, w = forced_direction(instance)
        kb, kw = key(b), key(w)
        if kb != kw:
            adjacency[kb].add(kw)
    previous: dict[Any, Any | None] = {start: None}
    work = deque([start])
    found = start == target
    while work and not found:
        cur = work.popleft()
        if cur == target:
            found = True
            break
        for nxt in adjacency.get(cur, ()):
            if nxt not in previous:
                previous[nxt] = cur
                work.append(nxt)
    if not found:
        return None
    keys: list[Any] = []
    cur = target
    while cur is not None:
        keys.append(cur)
        cur = previous[cur]
    keys.reverse()  # start ... target
    steps = []
    for first, second in zip(keys, keys[1:], strict=False):
        for _, instance, _ in pairs:
            b, w = forced_direction(instance)
            if key(b) == first and key(w) == second:
                steps.append(
                    {
                        "principle": instance.principle,
                        "better": list(b),
                        "worse": list(w),
                        "class_before": _render_key(first),
                        "class_after": _render_key(second),
                    }
                )
                break
    return {
        "strict_step": {"principle": principle, "better": list(better), "worse": list(worse)},
        "closing_path": steps,
        "total_steps": len(steps) + 1,
        "reading": (
            "the strict step gives worse-class < better-class while the closing path gives "
            "worse-class >= ... >= better-class, so no order constant on these fibres satisfies it"
        ),
    }


def _render_key(key: Any) -> Any:
    return list(key) if isinstance(key, tuple) else key


def quotient_scan(
    key: Callable[[Pop], Any],
    pairs: Sequence[tuple[str, Instance, str]],
) -> dict[str, Any]:
    """Refute the family when the quotient of one variant's instance graph has a strict cycle.

    A family is a class of orders constant on the fibres of ``key``.  Quotient the forced weak
    edges together with the strict Egalitarian Dominance edges by ``key``; a strict edge whose two
    ends lie in one strongly connected component is a contradiction for *every* member of the
    class, since along the cycle the order is weakly non-decreasing while one step is required to
    be strict.  Instance sets are never pooled across variants: each row uses one variant's own
    Non-Elitism and Dominance Addition forms.
    """
    adjacency: dict[Any, set[Any]] = defaultdict(set)
    strict: dict[tuple[Any, Any], tuple[Pop, Pop, str]] = {}
    same_key_strict = 0
    for _, instance, _ in pairs:
        better, worse = forced_direction(instance)
        kl, kr = key(better), key(worse)
        is_strict = instance.principle == ED
        if kl == kr:
            if is_strict:
                same_key_strict += 1
            continue
        adjacency[kl].add(kr)
        if is_strict:
            strict.setdefault((kl, kr), (better, worse, instance.principle))
    for targets in list(adjacency.values()):
        for node in targets:
            adjacency.setdefault(node, set())
    nodes = sorted(adjacency, key=repr)
    comp = _scc(nodes, adjacency)
    violating = [(u, v) for (u, v) in strict if comp[u] == comp[v]]
    cycle = _key_cycle(pairs, key, strict[violating[0]]) if violating else None
    return {
        "classes": len(nodes),
        "strict_edges": len(strict),
        "same_key_strict_edges": same_key_strict,
        "violating_strict_edges": len(violating),
        "refuted": bool(violating) or same_key_strict > 0,
        "example_cycle": cycle,
    }


def bounded_scan(cap: int = 6) -> dict[str, Any]:
    """Per-variant quotient scan for every named family over populations of at most ``cap`` lives.

    The four variants differ only in the Non-Elitism and Dominance Addition forms; ED, GNEP and VRC
    avoidance are shared.  Pooling them would mix instances that no single variant contains, so each
    variant is scanned on its own instance set.
    """
    variant_rows = []
    for label, ne, da in VARIANTS:
        principles = (ED, ne, da, GNEP, VRC)
        pairs = checked_pairs(principles, cap)
        rows = [
            {
                "family": name,
                "description": description,
                "scan": quotient_scan(key, pairs),
            }
            for name, description, key in FAMILIES
        ]
        variant_rows.append(
            {
                "variant": label,
                "non_elitism": ne,
                "dominance_addition": da,
                "instance_count": len(pairs),
                "families": rows,
            }
        )
    return {
        "cap_lives": cap,
        "population_count": sum(
            1 for k in range(1, cap + 1) for _ in itertools.combinations_with_replacement(LEVELS, k)
        ),
        "witnesses": {
            "non-elitism n": WITNESSES.get("non-elitism")["n"],
            "gnep u, y, n": [GNEP_U, GNEP_Y, GNEP_N],
            "vrc x, u, v, y, n, m": [
                WITNESSES.get("vrc-avoidance")[k] for k in ("x", "u", "v", "y", "n", "m")
            ],
        },
        "variants": variant_rows,
        "boundary": (
            "bounded discovery only: the cap is a search bound, not a completeness claim, and the "
            "witnesses shown are the model's own choices for this scan.  A 'count vector' row that "
            "is not refuted is not a consistency result."
        ),
    }


# ---------------------------------------------------------------------------------------------
# Section 4: explicit piecewise candidates tried as models, each with an audited counterexample.


def conditional_cap_score(pop: Pop, cap: int = 11) -> int:
    """score = (sum of lives at or above W_4) + capped low mass when a negative life is present."""
    high = sum(v for v in pop if v >= 4)
    low = sum(v for v in pop if v <= 3)
    if any(v <= -1 for v in pop):
        low = min(low, cap)
    return high + low


def always_cap_score(pop: Pop, cap: int = 11) -> int:
    """score = (sum of lives at or above W_4) + capped low mass, cap applied unconditionally."""
    return sum(v for v in pop if v >= 4) + min(sum(v for v in pop if v <= 3), cap)


def median_score(pop: Pop) -> tuple[int, int]:
    """Lower-median (an order statistic) with total utility as its tie-break."""
    ordered = sorted(pop)
    middle = ordered[(len(ordered) - 1) // 2]
    return middle, sum(ordered)


def total_utility_score(pop: Pop) -> int:
    """The additive order: sum of the lives' levels."""
    return sum(pop)


def failed_candidates() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    # (1) conditional cap: fails GNEP avoidance at z = W_-1 with a negative-free background.
    left = _join((4, -1), (3,) * 5)
    right = _join((3, 0), (3,) * 5)
    instance = Instance(GNEP, (left, right))
    rows.append(
        {
            "name": "conditional-cap piecewise order",
            "definition": (
                "sigma(P) = sum(lives at or above W_4) + (sum of lives at or below W_3), where the "
                "low sum is replaced by min(low sum, 11) exactly when P contains a negative life"
            ),
            "principle": GNEP,
            "required": "left >= right for z = W_-1 and every background E",
            "left": list(left),
            "right": list(right),
            "left_score": conditional_cap_score(left),
            "right_score": conditional_cap_score(right),
            "ladder_audit": audit(instance, LADDER, WITNESSES),
            "why_it_fails": (
                "the shared negative-free background E = {W_3}^5 saturates the left (which carries "
                "the W_-1 life) but not the right, so the right overtakes the left at E = {W_3}^5 "
                "although the source instance holds at E = {W_3}^4"
            ),
        }
    )
    # (2) always-capped order: fails Egalitarian Dominance.
    k = 8
    left = (3,) * k
    right = (2,) * k
    instance = Instance(ED, (left, right))
    rows.append(
        {
            "name": "always-capped (bounded low mass) order",
            "definition": (
                "sigma(P) = sum(lives at or above W_4) + min(sum of lives at or below W_3, 11), "
                "with the cap applied to every population"
            ),
            "principle": ED,
            "required": "left >- right strictly",
            "left": list(left),
            "right": list(right),
            "left_score": always_cap_score(left),
            "right_score": always_cap_score(right),
            "ladder_audit": audit(instance, LADDER, WITNESSES),
            "why_it_fails": (
                "both sides saturate at the cap once k = 8, so Egalitarian Dominance's strict "
                "requirement is not met; the uncapped low mass this cost is exactly what VRC "
                "avoidance needs bounded"
            ),
        }
    )
    # (3) median-first (order-statistic) order: fails Dominance Addition.
    left = (3, 3)
    right = _join((4, 4), (1, 1))
    instance = Instance(DA_THESIS, (left, right))
    rows.append(
        {
            "name": "lower-median-first order statistic",
            "definition": (
                "compare by (lower median of the lives, total utility); the first tier is the "
                "middle order statistic, an extremal statistic that ignores multiplicities at the "
                "ends"
            ),
            "principle": DA_THESIS,
            "required": "not(left >- right): A = {W_3, W_3} is below W_4, B = {W_4, W_4}, C = {W_1, W_1}",
            "left": list(left),
            "right": list(right),
            "left_score": list(median_score(left)),
            "right_score": list(median_score(right)),
            "ladder_audit": audit(instance, LADDER, WITNESSES),
            "why_it_fails": (
                "the median of {W_3, W_3} is W_3 while the median of {W_4, W_4, W_1, W_1} is W_1, so "
                "the order puts A strictly above B union C, which is exactly the avoided strict "
                "comparison"
            ),
        }
    )
    # (4) total utility: fails VRC avoidance (the size-unconstrained low bag).
    left = (4,) * 3
    right = _join((3,) * 5, (-1,))
    instance = Instance(VRC, (left, right))
    rows.append(
        {
            "name": "total-utility (additive) order",
            "definition": "sigma(P) = sum of the lives' levels",
            "principle": VRC,
            "required": "left >= right for z = W_4 and every bag B in R(W_1, W_3)",
            "left": list(left),
            "right": list(right),
            "left_score": total_utility_score(left),
            "right_score": total_utility_score(right),
            "ladder_audit": audit(instance, LADDER, WITNESSES),
            "why_it_fails": (
                "VRC avoidance's B is unconstrained in size, so {W_3}^5 union {W_-1} outranks the "
                "three high lives once B is large enough; no additive order can meet the source "
                "condition against an unbounded low bag"
            ),
        }
    )
    return rows


# ---------------------------------------------------------------------------------------------
# Section 5: status of the four variants under the support-determined refutation.


def variant_status() -> dict[str, Any]:
    used = {
        "egalitarian-dominance": ED,
        "non-elitism (both forms)": f"{NE_THESIS} and {NE_2003}",
        "dominance-addition (both forms)": f"{DA_THESIS} and {DA_2003}",
    }
    rows = {}
    for label, ne, da in VARIANTS:
        rows[label] = {
            "non_elitism": ne,
            "dominance_addition": da,
            "support_determined": "refuted (same four-step cycle; supports are witness-independent)",
            "reason": (
                "the cycle uses only Egalitarian Dominance, a Non-Elitism instance whose D = empty "
                "or D = {W_1} lies inside R(W_1, W_4) for both forms, and a Dominance Addition "
                "instance whose two forms coincide under completeness"
            ),
        }
    return {
        "conditions_used": used,
        "conditions_not_used": [GNEP, VRC],
        "variants": rows,
        "note": (
            "the weakest variant's GNEP and VRC-avoidance clauses are unused, so the refutation "
            "covers every variant listed and is robust to dropping both clauses"
        ),
    }


# ---------------------------------------------------------------------------------------------
# Driver.


def run() -> dict[str, Any]:
    started = time.monotonic()
    cycle = support_cycle_evidence()
    independence = witness_independence()
    coarse = sub_w4_refutation(k_max=16)
    scan = bounded_scan(cap=6)
    candidates = failed_candidates()
    variants = variant_status()
    weakest = next(v for v in scan["variants"] if v["variant"].startswith("(d)"))
    weakest_families = {
        row["family"]: {
            "refuted": row["scan"]["refuted"],
            "violating_strict_edges": row["scan"]["violating_strict_edges"],
            "same_key_strict_edges": row["scan"]["same_key_strict_edges"],
        }
        for row in weakest["families"]
    }
    remaining = (
        "the count-sensitive (profile-determined) route is open: every named invariant family above "
        "is refuted, and at six lives the scan finds no strict cycle for the count-vector control on "
        "the weakest variant, but no all-size model and no all-size impossibility for the weakened "
        "condition sets is claimed here"
    )
    return {
        "route": "B",
        "approach": (
            "extremal/support-statistic orders on the ladder: proved refutation of the "
            "support-determined class, an Egalitarian-Dominance-only refutation of the coarser "
            "sub-W_4-blind class, a per-variant bounded quotient scan of the finer support "
            "refinements, and four explicit piecewise/order-statistic candidates each refuted by an "
            "audited instance"
        ),
        "scope": (
            "ladder W_-1..W_6; finite nonempty populations of level indices; Q-011's four variants "
            "over {Egalitarian Dominance, Non-Elitism, GNEP, VRC avoidance, Dominance Addition}; "
            "claims marked proved are all-size, claims marked bounded rest on the six-lives scan"
        ),
        "verdict": "refuted-candidate",
        "evidence": {
            "support_determined_refutation": {**cycle, **{"witness_independence": independence}},
            "sub_w4_refutation": coarse,
            "bounded_family_scan": scan,
            "failed_explicit_candidates": candidates,
            "variant_status": variants,
            "summary_rows": {
                "weakest variant (d) family scan": weakest_families,
                "instance counts per variant": {
                    v["variant"]: v["instance_count"] for v in scan["variants"]
                },
            },
            "run_seconds": round(time.monotonic() - started, 2),
        },
        "remaining_obligation": remaining,
    }


def main() -> None:
    print(json.dumps(run(), indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
