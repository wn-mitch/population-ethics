from __future__ import annotations

import random
from dataclasses import replace

import pytest

from population_ethics.domain import ValidationError
from population_ethics.principles import GroundConstraint
from population_ethics.proofs import check_proof
from population_ethics.relations import Formula, Not, conjunction, disjunction, weak
from research.lab import (
    ACTIVE,
    Engine,
    Witness,
    applicability,
    background,
    baseline_witness,
    dpll_check,
    ground,
    is_preorder,
    labeled_posets,
    load_baseline,
    marco,
    pair_id,
    pairs,
    preorders,
    substantive_constraints,
    total_preorders,
)
from research.p4_mutations import AVOID_PAIRS, AVOIDANCE, Theory, build_chain_certificate
from research.schema import Grid, RankEngine, check_instance, domain, instances

RELAXED = Grid(
    "relaxed", (-1, 1, 5, 6, 7, 8), frozenset({8}), frozenset({1, 5, 6, 7}), frozenset({-1})
)


def _c(identifier: str, formula: Formula) -> GroundConstraint:
    return ground(identifier, "test", formula, "test/v1", "Research test premise.")


def test_enumerators_match_known_counts_and_have_no_duplicates() -> None:
    # OEIS A001035 (posets), A000798 (preorders), A000670 (total preorders).
    assert [sum(1 for _ in labeled_posets(n)) for n in range(6)] == [1, 1, 3, 19, 219, 4231]
    assert [sum(1 for _ in preorders(n)) for n in range(6)] == [1, 1, 4, 29, 355, 6942]
    assert [sum(1 for _ in total_preorders(n)) for n in range(7)] == [1, 1, 3, 13, 75, 541, 4683]
    for n in range(5):
        generated = list(preorders(n))
        assert len(generated) == len(set(generated))


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_preorder_enumerator_equals_brute_force(n: int) -> None:
    brute = {mask for mask in range(1 << (n * n)) if is_preorder(mask, n)}
    assert set(preorders(n)) == brute
    complete = {
        m
        for m in brute
        if all((m >> (i * n + j)) & 1 or (m >> (j * n + i)) & 1 for i in range(n) for j in range(n))
    }
    assert set(total_preorders(n)) == complete


def test_dpll_agrees_with_z3_on_random_ground_theories() -> None:
    rng = random.Random(7)
    names = ("X", "Y", "Z")
    atoms = [weak(a, b) for a in names for b in names]
    for trial in range(60):
        formulas: list[Formula] = []
        for _ in range(rng.randint(2, 7)):
            picked = rng.sample(atoms, 2)
            literals = [a if rng.random() < 0.5 else Not(a) for a in picked]
            formulas.append(
                conjunction(*literals) if rng.random() < 0.3 else disjunction(*literals)
            )
        hard = [_c(f"f{i}", f) for i, f in enumerate(formulas)]
        z3_decision = Engine(names, hard).require().decision
        assert dpll_check(formulas)[0] == z3_decision, trial


def test_marco_returns_every_mus_and_keeps_blocking_clauses_out_of_the_engine() -> None:
    soft = [
        _c("xy", weak("X", "Y")),
        _c("not-xy", Not(weak("X", "Y"))),
        _c("yx", weak("Y", "X")),
        _c("not-yx", Not(weak("Y", "X"))),
    ]
    engine = Engine(("X", "Y"), [], soft)
    before = len(engine.solver.assertions())
    muses, msses = marco(engine)
    assert muses == [("not-xy", "xy"), ("not-yx", "yx")]
    assert len(msses) == 4 and all(len(m) == 2 for m in msses)
    assert len(engine.solver.assertions()) == before


def test_baseline_escape_minimum_is_the_unique_aaf_star() -> None:
    spec = load_baseline()
    bg = background(ACTIVE)
    engine = Engine(
        ACTIVE,
        [*bg["reflexivity"], *bg["transitivity"], *substantive_constraints(spec)],
        bg["completeness"],
    )
    count = engine.count_incomparable(pairs(ACTIVE))
    assert engine.require(extra=[count <= 3]).decision == "unsat"
    star = [("AAE", "AAF"), ("AAF", "AB"), ("AAF", "AC"), ("AAF", "G")]
    forced = [engine.incomparable(a, b) for a, b in star]
    assert engine.require(extra=[count <= 4, *forced]).decision == "sat"
    import z3  # type: ignore[import-untyped]

    other = z3.Or([z3.Not(t) for t in forced])
    assert engine.require(extra=[count == 4, other]).decision == "unsat"


def test_four_avoidance_pairs_certificate_checks_and_needs_each_completeness_pair() -> None:
    spec = load_baseline()
    theory = Theory({c.id: c for c in substantive_constraints(spec)})
    hard = [
        *theory.reflexivity,
        *theory.transitivity,
        *substantive_constraints(spec),
        *theory.completeness_on(AVOID_PAIRS),
    ]
    routes = {cid: pair_id(*AVOIDANCE[cid]) for cid in AVOIDANCE}
    certificate, declared = build_chain_certificate(
        hard, routes, "addition:A-AB-implies-AB-AC", weak_addition=False
    )
    result = check_proof(certificate, declared, expected_problem_id=certificate.problem_id)
    assert (
        sorted(p for p in result.declared_premises if p.startswith("completeness")) == AVOID_PAIRS
    )
    for pair in AVOID_PAIRS:
        reduced = {k: v for k, v in declared.items() if k != pair}
        with pytest.raises(ValidationError):
            check_proof(certificate, reduced)


def test_applicability_accepts_baseline_and_rejects_single_semantic_violations() -> None:
    base = baseline_witness(load_baseline())
    assert all(applicability(base).values())

    def broken(**changes: dict[str, int]) -> set[str]:
        levels = {**base.levels, **changes.get("levels", {})}
        sizes = {**base.sizes, **changes.get("sizes", {})}
        return {
            k for k, v in applicability(Witness(levels, sizes, base.categories)).items() if not v
        }

    assert "addition:|C|>|B|" in broken(sizes={"C": 3, "D": 4, "G": 4, "F": 1})
    assert "dominance:min(AC)>max(G)" in broken(levels={"G": 3})
    assert "anti-egal:avg(AAF)<avg(G)" in broken(sizes={"F": 5, "G": 8, "C": 7, "D": 8})
    assert "mnep:E-single-slightly-negative" in broken(sizes={"E": 2})
    assert "mnep:B-q+1-very-low" in broken(sizes={"B": 4})
    assert "addition:max(C)<min(B)" in broken(levels={"C": 4})


def test_rank_encoding_agrees_with_atom_encoding_on_complete_preorders() -> None:
    insts = list(instances(RELAXED, 2, 1, 1))
    pops = domain(RELAXED, 2)
    rank = RankEngine(pops, insts)
    rng = random.Random(11)
    from research.p6_schema import core_constraints, name_of

    triangle = sorted(
        j
        for j, i in enumerate(insts)
        if (i.principle, i.args)
        in {
            ("dominance", ((6, 6), (5, 5))),
            ("non-anti-egalitarianism", ((-1, 8), (5, 5))),
            ("mnep", ((-1, 8), (6, 6))),
        }
    )
    assert len(triangle) == 3
    samples = [triangle] + [
        sorted(rng.sample(range(len(insts)), rng.randint(2, 6))) for _ in range(25)
    ]
    decisions = []
    for chosen in samples:
        subset = [insts[j] for j in chosen]
        names = tuple(sorted({name_of(x) for i in subset for x in i.args}))
        bg = background(names)
        atom = (
            Engine(
                names,
                [
                    *bg["reflexivity"],
                    *bg["transitivity"],
                    *bg["completeness"],
                    *core_constraints(subset),
                ],
            )
            .require()
            .decision
        )
        assert rank.check(chosen)[0] == atom
        decisions.append(atom)
    assert decisions[0] == "unsat" and "sat" in decisions


def test_schema_instances_pass_the_independent_audit_and_corruptions_fail() -> None:
    insts = list(instances(RELAXED, 3, 1, 1))
    assert all(check_instance(i, RELAXED, 1, 1) for i in insts)
    swapped = [replace(i, args=tuple(reversed(i.args))) for i in insts if i.principle != "addition"]
    assert not any(check_instance(i, RELAXED, 1, 1) for i in swapped)
    shrunk = [
        replace(i, args=(i.args[0], i.args[1], i.args[1]))
        for i in insts
        if i.principle == "addition"
    ]
    assert not any(check_instance(i, RELAXED, 1, 1) for i in shrunk)
