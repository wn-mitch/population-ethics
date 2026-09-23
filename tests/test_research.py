from __future__ import annotations

import json
import random
import re
import tomllib
from collections import Counter
from dataclasses import replace
from pathlib import Path
from typing import Any

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
from research.schema import (
    BASELINE_SKELETON,
    Grid,
    Instance,
    Pop,
    RankEngine,
    check_instance,
    domain,
    instances,
)

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


def test_literature_corpus_references_resolve_and_every_report_result_has_a_verdict() -> None:
    corpus = tomllib.loads(Path("corpus/literature.toml").read_text())
    ids = [work["id"] for work in corpus["works"]]
    assert len(ids) == len(set(ids))
    known = set(ids)
    for work in corpus["works"]:
        assert work["read"] in {"firsthand", "partial", "secondary", "not-obtained"}, work["id"]
        assert set(work.get("via", ())) <= known, work["id"]
        assert (work["read"] == "secondary") == bool(work.get("via")), work["id"]
        for key in ("pdf_sha256", "errata_sha256"):
            if key in work:
                assert re.fullmatch(r"[0-9a-f]{64}", work[key]), work["id"]
    verdicts = {c["result"]: c for c in corpus["collisions"]}
    assert set(verdicts) == {f"R{i}" for i in range(1, 7)}
    ledger = {
        e["candidate_id"] for e in json.loads(Path("research/ledger.json").read_text())["entries"]
    }
    covered: list[str] = []
    for collision in verdicts.values():
        assert collision["verdict"] in {"collides", "partial", "none-found"}
        assert collision["sources"] and set(collision["sources"]) <= known
        assert collision["ledger"] and set(collision["ledger"]) <= ledger, collision["result"]
        covered += collision["ledger"]
    assert len(covered) == len(set(covered))


def test_results_register_is_rendered_from_the_current_ledger() -> None:
    from research.render_ledger import RESULTS, render

    assert RESULTS.read_text() == render(), "docs/results.md is stale; run `just docs`"


@pytest.mark.parametrize(
    ("path", "prefix"), [("docs/decisions.md", "D"), ("docs/questions.md", "Q")]
)
def test_decision_and_question_entries_are_unique_and_cite_resolvable_sources(
    path: str, prefix: str
) -> None:
    text = Path(path).read_text()
    ids = re.findall(rf"^## ({prefix}-\d{{3}})\. ", text, flags=re.MULTILINE)
    assert ids and len(ids) == len(set(ids))
    assert ids == sorted(ids)
    works = {w["id"] for w in tomllib.loads(Path("corpus/literature.toml").read_text())["works"]}
    for entry in re.split(rf"^## (?={prefix}-)", text, flags=re.MULTILINE)[1:]:
        assert re.search(r"^- \*\*Status:\*\* ", entry, flags=re.MULTILINE), entry[:40]
        for line in re.findall(r"^- \*\*Sources:\*\*(.*)$", entry, flags=re.MULTILINE):
            for ref in re.findall(r"`([^`]+)`", line):
                assert ref in works or Path(ref).exists(), f"{entry[:5]} cites unknown {ref}"


def test_arrhenius_1999_witness_needs_every_principle_and_no_completeness() -> None:
    from research.p4_mutations import quasi_transitivity, suzumura
    from research.p7_arrhenius1999 import CORE, GRID, _decide, _names, _principle_constraints, audit

    names = _names()
    bg = background(names)
    principles = _principle_constraints()
    assert all(audit(i, GRID) for i in CORE)
    assert _decide([*bg["reflexivity"], *bg["transitivity"], *principles], names) == "unsat"
    for dropped in principles:
        rest = [c for c in principles if c.id != dropped.id]
        assert _decide([*bg["reflexivity"], *bg["transitivity"], *rest], names) == "sat"
    # One weak cycle closed by one strict link: Suzumura consistency forbids exactly that,
    # while quasi-transitivity constrains only strict chains.
    assert _decide([*bg["reflexivity"], *suzumura(names), *principles], names) == "unsat"
    assert _decide([*bg["reflexivity"], *quasi_transitivity(names), *principles], names) == "sat"


def test_arrhenius_1999_audit_rejects_misapplied_conditions() -> None:
    from research.p7_arrhenius1999 import CORE, GRID, audit

    by_name = {i.principle.removeprefix("arrhenius-1999:"): i for i in CORE}
    qa = by_name["quality-addition"]
    # The added group must be the declared very-high witness, not an extra low life.
    assert not audit(replace(qa, args=(qa.args[0] + (1,), qa.args[1])), GRID)
    mia = by_name["minimal-inequality-aversion"]
    # MIA's witness m = r fixes the number of worst-off lives.
    assert not audit(replace(mia, args=(mia.args[0][:-1], mia.args[1][1:])), GRID)
    ed = by_name["egalitarian-dominance"]
    # Egalitarian Dominance needs the better population to be perfectly equal.
    assert not audit(replace(ed, args=((6,) + ed.args[0][1:], ed.args[1])), GRID)


def test_known_ground_isolates_r6_new_steps_and_ignores_relabeling() -> None:
    from research.known import known_ground, novelty_rank
    from research.p7_arrhenius1999 import R6_CORE

    kg = known_ground(R6_CORE)
    assert kg["exact_known"] == "project-r6-gapped"
    assert kg["uncovered_by_catalogue"] == []
    assert kg["per_known"]["arrhenius-1999"] == "4/5"
    # Two maximum embeddings of the 2000 skeleton exist; together they cover Addition and
    # Repugnance avoidance, leaving only the second MNEP bridge and the 7⁷ ≻ 6⁷ step.
    assert sorted(kg["uncovered_by_published"]) == [
        "dominance([7, 7, 7, 7, 7, 7, 7], [6, 6, 6, 6, 6, 6, 6])",
        "mnep([-1, 6, 6, 6, 6, 6, 14], [6, 6, 6, 6, 6, 6, 6])",
    ]

    perm = list(range(7))
    random.Random(7).shuffle(perm)
    relabeled = [replace(i, args=tuple((perm[x[0]],) for x in i.args)) for i in BASELINE_SKELETON]
    assert known_ground(relabeled)["exact_known"] == "arrhenius-2000-ep"
    # Same shape after normalization, different role: must not count as the known skeleton.
    swapped = [
        Instance("non-sadism", (i.args[1], i.args[0])) if i.principle == "mnep" else i
        for i in BASELINE_SKELETON
    ]
    assert known_ground(swapped)["exact_known"] is None

    def entry(exact: str | None, uncovered: list[str], size: int) -> dict[str, Any]:
        kg = {"exact_known": exact, "uncovered_by_catalogue": uncovered}
        return {"known_ground": kg, "instances": size, "relata": size}

    small_known = entry("x", [], 3)
    small_covered = entry(None, [], 4)
    large_new = entry(None, ["step"], 9)
    order = sorted([small_known, small_covered, large_new], key=novelty_rank)
    assert order == [large_new, small_covered, small_known]


def test_review_gate_rejects_missing_and_unreviewed_readings_and_blocks_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import research.schema as schema
    from research.readings import UnreviewedPrinciple, load, parse, require_reviewed

    readings = load()
    assert set(schema.SHAPE) <= set(readings), "every schema principle needs a reading"
    require_reviewed(schema.SHAPE)
    downgraded = {**readings, "mnep": replace(readings["mnep"], review_state="agent-read")}
    with pytest.raises(UnreviewedPrinciple, match="mnep"):
        require_reviewed(["dominance", "mnep"], downgraded)
    with pytest.raises(UnreviewedPrinciple, match="no reading"):
        require_reviewed(["not-a-principle"], readings)
    monkeypatch.setattr(schema, "require_reviewed", lambda ps: require_reviewed(ps, downgraded))
    with pytest.raises(UnreviewedPrinciple):
        schema.instances(RELAXED, 2, 1, 1)
    row = {
        "principle": "x",
        "work": "w",
        "printed_page": "1",
        "name": "X",
        "excerpt": "e",
        "formal_reading": "f",
        "deviations": "",
        "reader": "a",
        "cross_reader": "b",
        "cross_verdict": "disagree: scope",
        "review_state": "agent-cross-read",
    }
    with pytest.raises(ValueError, match="without cross-reader agreement"):
        parse({"readings": [row]})


def _relabel(core: list[Instance], rng: random.Random) -> list[Instance]:
    nodes = sorted({x for inst in core for x in inst.args})
    image = rng.sample(range(100, 100 + 3 * len(nodes)), len(nodes))
    mapping = {x: (v,) for x, v in zip(nodes, image, strict=True)}
    shuffled = [Instance(i.principle, tuple(mapping[x] for x in i.args)) for i in core]
    rng.shuffle(shuffled)
    return shuffled


def test_canonical_form_is_relabeling_invariant_and_agrees_with_brute_force() -> None:
    from research.canon import canonical
    from research.p7_arrhenius1999 import CORE, R6_CORE
    from research.schema import canonical_skeleton

    rng = random.Random(5)
    fixtures = [list(BASELINE_SKELETON), list(CORE), list(R6_CORE)]
    for core in fixtures:
        for level in ("L0", "L1", "principle"):
            forms = {canonical(_relabel(core, rng), level) for _ in range(20)}
            assert forms == {canonical(core, level)}
    assert len({canonical(c, "L1") for c in fixtures}) == 3
    # Random small cores: exact form equality must coincide with brute-force isomorphism.
    principles = ["dominance", "mnep", "non-sadism", "addition", "non-anti-egalitarianism"]
    pool: list[list[Instance]] = []
    for _ in range(60):
        k = rng.randint(3, 6)
        core = []
        for _ in range(rng.randint(2, 6)):
            p = rng.choice(principles)
            arity = 3 if p == "addition" else 2
            core.append(Instance(p, tuple((v,) for v in rng.sample(range(k), arity))))
        pool += [core, _relabel(core, rng)]
    brute = [canonical_skeleton(c, principle_colors=True) for c in pool]
    exact = [canonical(c, "principle") for c in pool]
    matches = 0
    for i in range(len(pool)):
        for j in range(i + 1, len(pool)):
            assert (brute[i] == brute[j]) == (exact[i] == exact[j]), (pool[i], pool[j])
            matches += brute[i] == brute[j]
    assert matches >= 60  # every relabelled copy matches its original


def test_canonical_form_separates_what_colour_refinement_cannot() -> None:
    from research.canon import canonical
    from research.schema import canonical_skeleton

    # A directed 12-cycle and two directed 6-cycles of MNEP edges: every relatum has one in-
    # and one out-edge, so colour refinement (used above 9 relata) cannot tell them apart.
    big = [Instance("mnep", ((i,), ((i + 1) % 12,))) for i in range(12)]
    two = [Instance("mnep", ((i,), (6 * (i // 6) + (i + 1) % 6,))) for i in range(12)]
    assert canonical_skeleton(big, principle_colors=True) == canonical_skeleton(
        two, principle_colors=True
    )
    assert canonical(big, "L0") != canonical(two, "L0")


LADDER_WITNESS = {
    "quantity": {"step": 1},
    "quality": {"u": 4, "v": 6, "y": 3, "n": 1},
    "inequality-aversion": {"step": 1},
    "non-extreme-priority": {"x": 4, "y": -1, "z": 3, "n": 1},
    "weak-quality-addition": {"x": 4, "w": 6, "y": 3, "n": 1},
    "non-elitism": {"n": 1},
    "general-non-extreme-priority": {"u": 4, "y": 3, "n": 1},
    "weak-non-sadism": {"x": -1, "n": 1},
    "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
    "weak-quality-addition-negative": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
    "condition-beta": {"step": 1},
    "condition-delta": {"u": 4, "y": 3, "n": 1},
    "restricted-quality-addition": {"x": 4, "y": 3, "n": 1, "m": 1},
}


GROWING_WITNESS = {
    **LADDER_WITNESS,
    "quantity": {"step": 1, "mult": 2},
    "inequality-aversion": {"step": 1, "mult": 2},
    "condition-beta": {"step": 2},
    "condition-delta": {"u": 4, "y": 3, "n": 1, "n_per_m": 1},
}


GROWING_PRINCIPLES = [
    "thesis:quantity",
    "thesis:inequality-aversion",
    "thesis:condition-beta",
    "arrhenius-2003:condition-beta",
    "thesis:condition-delta",
]


@pytest.mark.parametrize(
    ("params", "negative", "lives", "only"),
    [(LADDER_WITNESS, 2, 3, None), (GROWING_WITNESS, 1, 4, GROWING_PRINCIPLES)],
)
def test_ladder_audit_accepts_exactly_the_generated_instances(
    params: dict[str, Any], negative: int, lives: int, only: list[str] | None
) -> None:
    from research.ladder import FORM, Ladder, Witness, audit, domain, instances_over

    ladder, witness = Ladder(negative, 6), Witness(params)
    pops = domain(ladder, lives)
    for principle in only or FORM:
        generated = {i.args for i in instances_over(pops, ladder, witness, [principle])}
        assert generated, f"{principle} generates nothing on this domain"
        audited = {
            (x, y)
            for x in pops
            for y in pops
            if audit(Instance(principle, (x, y)), ladder, witness)
        }
        assert audited == generated, (principle, sorted(audited ^ generated)[:5])


def test_ladder_generation_is_nested_and_rejects_bad_witnesses() -> None:
    from research.ladder import FORM, Ladder, Witness, domain, instances_over

    ladder, witness = Ladder(1, 6), Witness(LADDER_WITNESS)
    small = set(instances_over(domain(ladder, 3), ladder, witness, FORM))
    large = set(instances_over(domain(ladder, 4), ladder, witness, FORM))
    assert small < large
    bad = {
        "quality": {"u": 3, "v": 6, "y": 3, "n": 1},  # R(u, v) must lie above R(1, y)
        "non-extreme-priority": {"x": 4, "y": 1, "z": 3, "n": 1},  # W_y must be negative
        "general-non-extreme-priority": {"u": 4, "y": 2, "n": 1},  # R(1, 2) has two levels
        "vrc-avoidance": {"x": -1, "u": 5, "v": 6, "y": 3, "n": 1, "m": 1},  # R(5, 6) too short
    }
    for family, params in bad.items():
        principle = next(p for p, f in FORM.items() if f.startswith(family))
        with pytest.raises(ValueError, match="witness violates"):
            instances_over(
                domain(ladder, 3),
                ladder,
                Witness({**LADDER_WITNESS, family: params}),
                [principle],
            )


def test_frozen_theorems_are_audited_and_match_their_catalogue_entries() -> None:
    from research.known import CATALOGUE, known_ground
    from research.ladder import audit
    from research.p8_catalogue import FROZEN, LADDER, WITNESS

    ids = {k.id for k in CATALOGUE}
    same_as_1999 = {
        "arrhenius-thesis-theorem-3",
        "arrhenius-thesis-theorem-4",
        "arrhenius-2009-one-more",
    }
    for frozen in FROZEN:
        core = frozen.instances()
        assert all(audit(i, LADDER, WITNESS) for i in core), frozen.id
        expected = "arrhenius-1999" if frozen.id in same_as_1999 else frozen.id
        assert expected in ids
        assert known_ground(core)["exact_known"] == expected, frozen.id


def test_every_realization_example_is_audited_and_entailed_without_completeness() -> None:
    from research.realizations import load, verify_example

    checked = 0
    for realization in load():
        assert realization.examples, realization.id
        for variant in realization.variants:
            for example in realization.examples:
                result = verify_example(example, variant)
                assert all(result.values()), (realization.id, variant.target, result)
                checked += 1
    assert checked == 7


def _chain(principle: str, ends: tuple[Pop, ...], internal: int, tag: int) -> list[Instance]:
    nodes = [ends[0], *[(1000 * tag + k,) for k in range(internal)], ends[1]]
    return [Instance(principle, (nodes[k], nodes[k + 1])) for k in range(len(nodes) - 1)]


def test_l2_contracts_lemma_chains_back_to_the_lemma_level_skeleton() -> None:
    from research.canon import canonical, canonical_l2
    from research.p8_catalogue import THEOREM_4

    core = THEOREM_4.instances()
    beta = next(i for i in core if i.principle == "thesis:condition-beta")
    delta = next(i for i in core if i.principle == "thesis:condition-delta")
    primitive = [i for i in core if i not in (beta, delta)]
    primitive += _chain("thesis:non-elitism", beta.args, internal=1, tag=1)
    primitive += _chain("thesis:general-non-extreme-priority", delta.args, internal=3, tag=2)
    assert canonical(primitive, "L1") != canonical(core, "L1")
    assert canonical_l2(primitive) == (canonical(core, "L1"),)
    # A relatum inside the chain that touches another edge blocks contraction there.
    blocked = [*primitive, Instance("thesis:non-sadism", ((1000,), (4, 4, 4)))]
    assert canonical(core, "L1") not in canonical_l2(blocked)


def test_l2_recovers_the_1999_skeleton_from_the_primitive_2009_proof() -> None:
    from research.canon import canonical, canonical_l2
    from research.known import known_ground
    from research.p8_catalogue import THEOREM_2009

    core = THEOREM_2009.instances()
    by = {i.principle.split(":")[1]: i for i in core}
    rqa, delta, beta = (
        by["restricted-quality-addition"],
        by["condition-delta"],
        by["condition-beta"],
    )
    middle = (9999,)
    primitive = [by["weak-non-sadism"], by["egalitarian-dominance"]]
    primitive += _chain("arrhenius-2009:non-elitism", beta.args, internal=2, tag=3)
    primitive += _chain(
        "arrhenius-2009:general-non-extreme-priority", delta.args, internal=2, tag=4
    )
    # Lemma 3: Weak Quality Addition to a middle population, then δ (itself a GNEP run).
    primitive.append(Instance("arrhenius-2009:weak-quality-addition", (rqa.args[0], middle)))
    primitive += _chain(
        "arrhenius-2009:general-non-extreme-priority", (middle, rqa.args[1]), internal=3, tag=5
    )
    forms = canonical_l2(primitive)
    # Lemma 3's δ may be taken from either GNEP run, so two contractions exist; the one that
    # follows the source is the lemma-level skeleton, which is the 1999 skeleton at L1.
    assert canonical(core, "L1") in forms
    assert known_ground(core)["exact_known"] == "arrhenius-1999"


def test_universe_generation_matches_domain_generation_and_filters_exactly() -> None:
    from research.schema import instances_over

    for n in (2, 3):
        pops = domain(RELAXED, n)
        assert set(instances_over(pops, RELAXED, 1, 1)) == set(instances(RELAXED, n, 1, 1))
    rng = random.Random(3)
    pops = rng.sample(domain(RELAXED, 3), 40)
    universe = set(pops)
    expected = {i for i in instances(RELAXED, 3, 1, 1) if all(x in universe for x in i.args)}
    assert set(instances_over(pops, RELAXED, 1, 1)) == expected


def test_marco_over_ranks_finds_exactly_the_brute_force_muses() -> None:
    from itertools import combinations

    insts = list(instances(RELAXED, 2, 1, 1))
    rng = random.Random(9)
    triangle = [
        i
        for i in insts
        if (i.principle, i.args)
        in {
            ("dominance", ((6, 6), (5, 5))),
            ("non-anti-egalitarianism", ((-1, 8), (5, 5))),
            ("mnep", ((-1, 8), (6, 6))),
        }
    ]
    chosen = triangle + rng.sample([i for i in insts if i not in triangle], 9)
    pops = sorted({x for i in chosen for x in i.args})
    engine = RankEngine(pops, chosen)
    muses, _ = marco(engine)  # type: ignore[arg-type]
    unsat = {
        frozenset(s)
        for k in range(1, len(chosen) + 1)
        for s in combinations(range(len(chosen)), k)
        if engine.check(list(s))[0] == "unsat"
    }
    brute = {s for s in unsat if not any(t < s for t in unsat)}
    assert {frozenset(int(c[1:]) for c in m) for m in muses} == brute
    assert frozenset(chosen.index(i) for i in triangle) in brute


def test_ladder_generation_over_a_sparse_universe_keeps_every_instance() -> None:
    from research.ladder import FORM, Ladder, Witness, domain, instances_over

    ladder, witness = Ladder(1, 6), Witness(LADDER_WITNESS)
    full = domain(ladder, 4)
    universe = set(random.Random(4).sample(full, 300))
    expected = {
        i for i in instances_over(full, ladder, witness, FORM) if all(x in universe for x in i.args)
    }
    assert set(instances_over(universe, ladder, witness, FORM)) == expected


def test_rank_sat_agrees_with_z3_on_random_shape_hypergraphs() -> None:
    from research.census import rank_sat

    rng = random.Random(21)
    for trial in range(300):
        n = rng.randint(3, 5)
        edges = []
        for _ in range(rng.randint(1, 6)):
            shape = rng.choice("WWSI")
            args = tuple(rng.sample(range(n), 3 if shape == "I" else 2))
            edges.append((shape, args))
        pops: list[Pop] = [(k,) for k in range(n)]
        principle = {"W": "mnep", "S": "dominance", "I": "addition"}
        insts = [Instance(principle[s], tuple(pops[a] for a in args)) for s, args in edges]
        expected = RankEngine(pops, insts).check(list(range(len(insts))))[0] == "sat"
        assert rank_sat(n, edges) == expected, (trial, edges)


def test_minimal_cores_are_strict_cycles_and_fork_motifs_with_necklace_counts() -> None:
    from research.census import is_fork_motif, is_simple_cycle, minimal_cores
    from research.p9_census import necklaces_with_a_strict_edge

    cycles = minimal_cores(5, frozenset({"W", "S"}))
    counts = Counter(len(c[1]) for c in cycles.minimal)
    assert all(is_simple_cycle(c) for c in cycles.minimal)
    assert [counts[n] for n in range(2, 6)] == [
        necklaces_with_a_strict_edge(n) for n in range(2, 6)
    ]
    assert [necklaces_with_a_strict_edge(n) for n in range(2, 7)] == [2, 3, 5, 7, 13]
    forks = [c for c in minimal_cores(4, max_forks=1).minimal if any(s == "I" for s, _ in c[1])]
    assert len(forks) == 36 and all(is_fork_motif(c) for c in forks)
    # A fork with one strict path only is satisfiable, so it is never reported.
    assert not is_fork_motif((4, (("I", (0, 1, 2)), ("S", (0, 1)), ("W", (2, 3)))))


def test_cycle_census_agrees_with_marco_and_rediscovers_theorem_1() -> None:
    from research.census import cycle_words
    from research.ladder import domain as ladder_domain
    from research.ladder import instances_over as ladder_over
    from research.p8_catalogue import LADDER, THEOREM_1, WITNESS
    from research.p9_census import _cycle_order, _mus_words

    principles = sorted({p for p, _, _ in THEOREM_1.core})
    universe = set(random.Random(8).sample(ladder_domain(LADDER, 4), 80))
    universe |= set(THEOREM_1.populations.values())
    insts = ladder_over(universe, LADDER, WITNESS, principles)
    bottom_up, kinds, count = _mus_words(insts)
    top_down = {w.word for w in cycle_words(insts, 16)}
    assert count >= 1 and set(kinds) == {"cycle"}
    assert bottom_up == top_down
    source = tuple(i.principle for i in _cycle_order(THEOREM_1.instances()))
    assert min(source[i:] + source[:i] for i in range(5)) in top_down


@pytest.mark.parametrize(
    ("n_per_m", "step", "fires"), [(0, 1, True), (2, 1, False), (0, 3, True), (1, 3, False)]
)
def test_triangle_firing_condition_matches_the_census(n_per_m: int, step: int, fires: bool) -> None:
    from research.census import cycle_words
    from research.ladder import Witness, domain, instances_over
    from research.p8_catalogue import LADDER, WITNESS
    from research.p10_witness_families import triangle_predicted

    delta = {"u": 4, "y": 3, "n": 1, "n_per_m": n_per_m}
    beta = {"step": step}
    witness = Witness({**WITNESS.params, "condition-delta": delta, "condition-beta": beta})
    pops = [p for p in domain(LADDER, 5) if max(p) <= 4]
    principles = [
        "arrhenius-2003:condition-delta",
        "arrhenius-2003:condition-beta",
        "arrhenius-2003:egalitarian-dominance",
    ]
    found = any(
        len(w.word) == 3 for w in cycle_words(instances_over(pops, LADDER, witness, principles), 3)
    )
    assert triangle_predicted(LADDER, delta, beta, "any", 5) == found == fires


def test_one_tier_lexadd_verdicts_equal_exact_additive_verdicts() -> None:
    import z3

    from research.additive import CONDITIONS, AdditiveEngine
    from research.ladder import Ladder
    from research.lexadd import CHECKS, LexAxiology, tiers_of

    ladder = Ladder(1, 6)
    for name, g in (("total", lambda v: v), ("critical-level-3", lambda v: v - 3)):
        ax = LexAxiology(name, name, tiers_of(ladder, g))
        for principle in CONDITIONS:
            engine = AdditiveEngine(ladder, [principle])
            for level, var in engine.g.items():
                engine.solver.add(var == z3.RealVal(ax.tiers[0][level]))
            additive = engine.require([principle]).decision == "sat"
            assert (CHECKS[principle](ax, ladder) is None) == additive, (name, principle)


def test_lexadd_counterexamples_are_audited_instances_the_axiology_fails() -> None:
    from research.ladder import Ladder, Witness, audit
    from research.lexadd import (
        LexAxiology,
        dominance_addition_thesis,
        egalitarian_dominance,
        non_sadism,
        tiers_of,
    )

    ladder = Ladder(1, 6)
    cases = [
        (non_sadism, "thesis:non-sadism", LexAxiology("cl", "", tiers_of(ladder, lambda v: v - 3))),
        (
            dominance_addition_thesis,
            "thesis:dominance-addition",
            LexAxiology("cl", "", tiers_of(ladder, lambda v: v - 3)),
        ),
        (
            egalitarian_dominance,
            "thesis:egalitarian-dominance",
            LexAxiology("flat", "", tiers_of(ladder, lambda v: min(v, 2))),
        ),
    ]
    for check, principle, ax in cases:
        v = check(ax, ladder)
        assert v is not None, principle
        inst = Instance(principle, (v.left, v.right))
        assert audit(inst, ladder, Witness({})), (principle, v)
        a, b = ax.key(v.left), ax.key(v.right)
        holds = {"W": a >= b, "S": a > b, "N": not a > b}[v.shape]
        assert not holds, (principle, v)


def test_additive_classification_is_the_quality_positivity_dichotomy() -> None:
    from research.additive import classify
    from research.ladder import Ladder
    from research.possibility import PRIMITIVE

    quality = {
        "thesis:quality",
        "thesis:weak-quality-addition",
        "arrhenius-2003:vrc-avoidance",
        "arrhenius-2009:weak-quality-addition",
    }
    positivity = {
        "thesis:quantity",
        "thesis:dominance-addition",
        "arrhenius-2003:dominance-addition",
        "thesis:non-sadism",
        "thesis:weak-non-sadism",
    }
    result = classify(Ladder(1, 6), PRIMITIVE)
    muses = {frozenset(m) for m in result["minimal_unrealizable"]}
    expected = {
        frozenset({"thesis:egalitarian-dominance", q, p}) for q in quality for p in positivity
    }
    assert muses == expected


def test_negative_then_critical_level_realizes_a_set_no_lexical_threshold_view_does() -> None:
    from fractions import Fraction

    from research.ladder import Ladder
    from research.lexadd import CHECKS, LexAxiology, tiers_of

    ladder = Ladder(1, 6)
    ax = LexAxiology(
        "nl-cl",
        "",
        tiers_of(ladder, lambda v: min(v, 0), lambda v: Fraction(v) - Fraction(7, 2), lambda v: v),
    )
    wanted = [
        "thesis:egalitarian-dominance",
        "thesis:inequality-aversion",
        "thesis:non-sadism",
        "thesis:quality",
    ]
    assert all(CHECKS[p](ax, ladder) is None for p in wanted)
    assert CHECKS["thesis:non-extreme-priority"](ax, ladder) is not None  # the escape from T3


def test_support_abstraction_covers_every_concrete_instance() -> None:
    from research.certify import support_edges
    from research.ladder import FORM, WITNESS_OF, Ladder, Witness, domain, instances_over
    from research.possibility import PRIMITIVE

    ladder = Ladder(1, 6)
    witness = Witness(LADDER_WITNESS)
    pops = domain(ladder, 3)
    for principle in PRIMITIVE:
        family = WITNESS_OF.get(FORM[principle])
        levels = LADDER_WITNESS.get(family, {}) if family else {}
        edges = support_edges(principle, ladder, levels)
        concrete = instances_over(pops, ladder, witness, [principle])
        assert concrete, principle
        for inst in concrete:
            a, b = (inst.args[1], inst.args[0]) if inst.shape == "N" else inst.args
            assert (frozenset(a), frozenset(b), inst.shape == "S") in edges, (principle, inst)


def test_certifier_proves_the_vrc_gap_consistent_and_never_a_known_theorem() -> None:
    from research.certify import Certifier
    from research.ladder import Ladder
    from research.lexadd import battery
    from research.possibility import KNOWN_THEOREMS

    ladder = Ladder(2, 7)
    certifier = Certifier(
        ladder, [a for a in battery(ladder) if a.id in {"total", "negative-then-total"}]
    )
    gap = [
        "thesis:egalitarian-dominance",
        "thesis:non-extreme-priority",
        "thesis:quantity",
        "arrhenius-2003:vrc-avoidance",
    ]
    cert = certifier.certify(gap)
    assert cert is not None and cert.inert == ("arrhenius-2003:vrc-avoidance",)
    assert cert.axiology == "total"
    for name, theorem in KNOWN_THEOREMS.items():
        assert certifier.certify(theorem) is None, name


def test_component_restriction_reduces_to_the_full_and_the_empty_check() -> None:
    from itertools import combinations

    from research.ladder import Ladder
    from research.lexadd import Restriction, battery, check_at, check_restricted

    ladder = Ladder(1, 6)
    levels = tuple(ladder.levels)
    every = [frozenset(c) for k in range(1, len(levels) + 1) for c in combinations(levels, k)]
    one = {s: 0 for s in every}
    apart = {s: i for i, s in enumerate(every)}
    axes = {a.id: a for a in battery(ladder)}
    cases = [
        ("thesis:non-sadism", "critical-level-3", None, None),
        ("thesis:quantity", "threshold-4", (), None),
        ("thesis:inequality-aversion", "threshold-4", (), None),
        ("thesis:quality", "total", (), {"u": 4, "v": 6, "y": 3}),
        ("thesis:non-extreme-priority", "negative-then-total", None, {"x": 4, "y": -1, "z": 3}),
    ]
    for principle, ax_id, bg, lv in cases:
        full = check_at(principle, axes[ax_id], ladder, lv)
        assert full is not None, (principle, ax_id)  # each case is a real violation
        same = check_restricted(principle, axes[ax_id], ladder, lv, Restriction(one, levels, bg))
        assert same is not None, principle
        none = check_restricted(principle, axes[ax_id], ladder, lv, Restriction(apart, levels, bg))
        # Distinct components for distinct supports leave only instances with equal supports,
        # which a background-free condition never has.
        if bg == ():
            assert none is None, principle


def test_hybrid_certifier_keeps_plain_certificates_and_rejects_theorem_1() -> None:
    from research.certify import HybridCertifier
    from research.ladder import Ladder
    from research.lexadd import battery
    from research.possibility import KNOWN_THEOREMS

    ladder = Ladder(2, 7)
    models = [a for a in battery(ladder) if a.id in {"total", "negative-then-total"}]
    hybrid = HybridCertifier(ladder, models, per_gap=2)
    gap = [
        "thesis:egalitarian-dominance",
        "thesis:non-extreme-priority",
        "thesis:quantity",
        "arrhenius-2003:vrc-avoidance",
    ]
    cert = hybrid.certify(gap)
    assert cert is not None and "arrhenius-2003:vrc-avoidance" in cert.inert
    assert hybrid.certify(KNOWN_THEOREMS["thesis-theorem-1"]) is None
