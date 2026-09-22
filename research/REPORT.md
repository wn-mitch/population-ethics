# Breakthrough Search — Turn 1 Report

The labels follow the plan:
- **Result scope:** finite computational result, bounded conjecture, unrestricted conjecture, or
  checked theorem.
- **Formalization tier:**
  - frozen source-reviewed witness;
  - source-constrained fixed-skeleton generalization;
  - rational-cardinal spacing sensitivity;
  - logical mutation;
  - unreviewed schema generalization.
- **Novelty.** Ledger rows carry the solver-side status `candidate-new-result`. The literature
  verdicts in `corpus/literature.toml` override it; see "Literature collision" below.

Unless a result says otherwise, it is about the frozen instance `arrhenius-2000.selected-witness/v1`
(problem `eef25016…`) restricted to its seven active relata:
- **A**: one very-high life (8)
- **AB**: A plus 3 lives at 4
- **AC**: A plus 21 lives at 3
- **AAE**: A plus 2 more very-high lives plus 1 life at −1
- **AAF**: A plus 2 more very-high lives plus 19 lives at 1
- **D**: 22 lives at 4
- **G**: 22 lives at 2

The Phase 1 restriction/extension lemma makes the results on these seven relata valid for the
full 12-name instance. Phase 2 checked the 66-pair domain directly: its MUS and MCS families and
k_min are identical.

## Executive result

Two results lead. Both are about the incompleteness boundary and the weakest sufficient
assumptions of the frozen instance. Both are finite computational results backed by two
independent decision procedures.

1. **Exactly what incompleteness buys.** Take any reflexive, transitive relation on the seven
   populations that satisfies the seven Arrhenius instances.
   - **Minimum.** It leaves at least **4** of the 21 comparisons unresolved.
   - **Unique minimum pattern.** Only one pattern attains 4: AAF is incomparable to AAE, AB, AC,
     and G, and every other pair is comparable. Eight labeled relations realize it, differing
     only in ties.
   - **Where the gap must fall.** Every escape leaves at least one of the four avoidance
     comparisons unresolved.
   - **Same-number comparisons settled.** Then the cheapest escape is again unique: A, the single
     very-high life, becomes incomparable to all six others.
   - **Completeness alone.** Completeness restricted to same-number pairs is consistent with all
     seven instances. Completeness restricted to different-number pairs is not.

   So the contradiction is driven by comparability across different population sizes.
2. **A strictly weaker sufficient set of assumptions (C1)** is still inconsistent:
   - reflexivity is not needed;
   - transitivity;
   - completeness only on the four pairs the avoidance principles talk about (A:D, AC:D,
     AAE:AAF, AAF:G);
   - Addition weakened to "not better" form.

   A 78-node natural-deduction certificate checks with the production checker. C1 is locally
   irreducible relative to the frozen mutation catalogue v1. The curated certificate's fifth
   completeness premise (AB:AC) is redundant.

The witness and schema phases are mostly negative or diagnostic, and useful as such:
- On its own grid the source witness is tight: |D| = |G| = 7(p+q)+1, which is 22 at p=1, q=2.
- Under the unreviewed v0 principle schemas on the baseline grid, with W(p=1, q=1) and
  W(p=1, q=2), no contradiction exists among populations of at most 8 lives. That is up to
  3,002 populations and 342k instances, with every SAT model checked.
- On a grid that blocks the triangle but lets the AC-versus-D clause bind, the search found a
  **structurally different proof skeleton** (R6). It needs 7 lives where the baseline skeleton
  needs 9, and uses Non-Anti-Egalitarianism once instead of twice.
- With order-only categories, a trivial 3-instance contradiction of MNEP, Dominance, and
  Non-Anti-Egalitarianism appears. It fires exactly when the MNEP bundle averages below a
  non-top very-low level. This shows that the category formalization must carry a gap condition
  that the source leaves implicit.

No breakthrough in the strong sense. Nothing here refutes, or strengthens beyond known forms,
the unrestricted theorem.

## Baseline reproduction

- `just check` passed before any change: 24 tests.
- A fresh `run` reproduces `problem_id`, `run_key`, decision, grounded core, and the checked
  proof. `artifact_id` differs, as expected, because it hashes wall time.
- `verify` accepts both the stored and the fresh artifact.
- The stored artifact (`results/arrhenius.json`, sha256 `e2798da6…`) is untouched.
- Labels are unchanged: `bounded-proof-instance` and `human-reviewed-selected-instance`.

**Reproducibility.** `just research` regenerates every `research/results/p*.json` from a clean
state. Each file stores the mathematical payload separately from run observations such as
timing. The payload records z3 5.1.0, the `uv.lock` hash, and the baseline hashes; its
`result_sha256` is identical across repeated runs. No phase produced an `unknown`: every engine
raises on UNKNOWN, and all Z3 timeouts in research code are disabled.

Transcription of the curated certificate (75 nodes):
1. Avoidance plus completeness gives A⪰D, D⪰AC, G⪰AAF, and AAF⪰AAE.
2. Transitivity gives A⪰AC.
3. Reductio on AB⪰AC, using completeness on AB:AC, through A⪰AB and Addition.
4. MNEP gives AAE⪰AB. The chain G⪰AAF⪰AAE⪰AB⪰AC then contradicts Dominance (AC≻G).

The stored solver core uses a different 4-pair completeness set, a star at G: {A,G}, {AAF,G},
{AB,G}, {D,G}.

## Frontier structure

- **Principle level** (2^7 subsets): one minimal UNSAT set, all seven groups. Seven maximal SAT
  sets, one per dropped group. No unknowns.
- **Instance level** (2^8 subsets, completeness bundled): one MUS, all eight units. Eight maximal
  SAT sets.

The selected instance is therefore irreducibly inconsistent relative to reflexivity and
transitivity. That is *not* logical independence of the principles.

The group-level picture hides structure inside completeness:
- 339 minimal completeness cores over the 21 active pairs: 335 of size 4 and 4 of size 5. Their
  intersection is empty.
- 110 minimal correction sets, of sizes 4 to 12.
- The MCS family equals the inclusion-minimal incomparability patterns found by exhaustive
  enumeration. This independently checks MUS/MCS duality.

Ground minimization of the full MUS gives the stored 22-constraint core (deletion trace
persisted). Each maximal SAT set has a checked model. The model's restriction to the seven
relata satisfies the restricted theory, and its universal-top extension is a preorder on all
12 names.

## Completeness and incomparability

Without completeness the problem is SAT. Exhaustive enumeration of all 9,535,241 preorders on
the seven labeled relata finds **20,169 escape models**.

Pair classification:
- AAE:AB and AC:G are forced comparable, by MNEP and Dominance respectively.
- No pair is forced incomparable.
- The other 19 pairs are comparable in some escapes and incomparable in others.

Incomparability counts:
- The count K of unresolved pairs ranges from **4 to 19**.
- Distribution of models by K: 8, 22, 135, 153, 457, … for K = 4, 5, 6, 7, 8, ….

The unique minimum, K = 4, is the **AAF star**: AAF ∥ AAE, AB, AC, G.
- In all eight minimum models, A⪰D sit above the chain AAE⪰AB⪰AC≻G.
- AAF sits below A and D but is unrelated to that chain.

Human reconstruction of why this star is forced when everything else is comparable. The rest of
the proof yields AAE⪰AB⪰AC≻G.
- **AAF vs AB or AC.** If AAF is comparable to either, it lands above AC or below AB.
  - Above AC: then AAF≻G, which violates Non-Anti-Egalitarianism.
  - Below AB: then AAE≻AAF, which violates Non-Sadism.
- **AAF vs AAE or G.** The same argument applies. Comparing AAF with either lets the chain force
  one of the two strict comparisons.

Both avoidance instances that mention AAF are then satisfied vacuously. The analytical
"tie the sole gap" lemma gives only K ≥ 2. The gap from 2 to 4 comes from AAF needing
incomparability with every population in the forced chain between AAE and G.

Escaping through one avoidance route while the other three avoidance comparisons stay resolved
costs:

| Route (unresolved avoidance pair) | min K | Unique MCS |
|---|---|---|
| A:D (Repugnance) | 6 | A incomparable to all six |
| AC:D (Anti-Egalitarianism 1) | 10 | 10 pairs |
| AAE:AAF (Sadism) | 10 | 10 pairs |
| AAF:G (Anti-Egalitarianism 2) | 12 | 12 pairs |

The global minimum of 4 uses two routes at once: AAE:AAF and AAF:G.

Structural conjectures tested exhaustively on all 20,169 escapes:
- **Hold:**
  - some population is incomparable to at least two others;
  - A or AAF is incomparable to something;
  - some different-number comparison is unresolved;
  - some avoidance comparison is unresolved.
- **Fail:**
  - the incomparability graph is connected (4 counterexamples);
  - AAF is incomparable to G or to AAE (134 counterexamples, for example escapes that isolate D).

## Witness minimization

The skeleton is fixed; only numbers vary. Applicability is checked by exact clauses derived from
role populations (`research/lab.py::applicability`).

**Grid track** (source-constrained; levels {−1, 1, 2, 3, 4, 8} with the declared categories;
exhaustive search):
- The categories force f=1, g=2, c=3, b=d=4.
- The average clause avg(AAF) < g alone binds: m_min = 6(p+q)+1 and |D| = |G| = 7(p+q)+1.
- The baseline (p=1, q=2, m=19, |D|=22) is **optimal** for its witness. Every objective depends
  on p+q only.
- Distinct levels: 6 in every solution.
- Pareto fronts are single points.
- Relation atoms (144), ground instances (1,813), and certificate size (75) are fixed by
  construction.
- p=q=1 gives |D|=15. That is a different MNEP witness, not a smaller witness for q=2.

**Six-level lemma** (checked theorem for the fixed skeleton). The applicability clauses force
e < 0 < f < g < c < b < a:
- Dominance gives c > g.
- Addition gives c < b < a.
- avg(AAF) < g together with a, a′ > g gives f < g.

At least 6 levels are therefore required, and the baseline attains 6. The content is the
forcing, not the count.

**Closed form** (verified against brute force on 858 spacing cases):

m_min = max(2, ⌊p(a−d)/(d−c) − q⌋ + 1, ⌊(p(a−g) + q(a′−g))/(g−f)⌋ + 1)

The largest population is p+q+m_min. Addition's |C| > |B| forces m ≥ 2, so |D| ≥ p+q+2 for any
spacing.

**Spacing sensitivity** (not a source witness). With order-only categories the witness collapses
to p+q+2 lives: 4 at p=q=1 (levels 8/7/6/5/1) and 5 at p=1, q=2. These were materialized, run,
and verified through the CLI with the curated proof. Witness size tracks the ratio
(a−g)/(g−f):
- 1/4 gives 5 lives;
- 1 gives 7;
- 6 gives 22, the baseline;
- 12 gives 40.

Distance between the categories does real work in the source witness. It does not create the
contradiction, which is propositional.

## Candidate new results

### R1. Unique minimum escape

- **Statement.** Every reflexive, transitive relation on {A, AB, AC, AAE, AAF, D, G} that satisfies
  the seven frozen instances leaves at least 4 of the 21 pairs unresolved. Equality holds only
  for AAF ∥ {AAE, AB, AC, G}.
- **Scope.** Finite computational result on the frozen source-reviewed witness. The propositional
  structure is identical for every witness (p, q) of the skeleton.
- **Evidence.** Z3 cardinality sweep plus projection-blocked enumeration, and exhaustive
  enumeration of 9,535,241 preorders. A test pins the result.
- **Why interesting.** It gives an exact answer to "what does incompleteness buy". The cheapest
  escape floats the population that carries both Non-Sadism and the second Non-Anti-Egalitarianism
  instance.
- **Falsification attempts.** Incomparability-graph connectivity fails. "AAF is always involved"
  fails. Both were recorded.
- **Gap.** This is one skeleton. Whether other skeletons have a similar unique star is open.
- **Status.** Partial collision. The qualitative point is Arrhenius's own; the count and the
  unique pattern were not found in prior work.

### R2. Different-number comparability drives the contradiction

- **Statement.**
  - The seven instances are consistent with completeness on all same-number pairs.
  - They are inconsistent with completeness on the different-number pairs alone.
  - With same-number pairs settled, the unique cheapest escape makes A incomparable to all six
    others.
  - Every escape leaves at least two different-number pairs unresolved.
- **Scope.** Finite computational result on the frozen witness.
- **Evidence.** Z3 plus DPLL; enumeration.
- **Why interesting.** It connects to views that accept same-number comparability but doubt
  different-number comparability.
- **Gap.** Unrestricted form: "Arrhenius's conditions plus same-number completeness are
  consistent" is an unrestricted conjecture. Proving it needs an explicit model on all
  populations. It is untested.
- **Status.** Partial collision. The same-number-complete escape is an established program; the
  different-number-only UNSAT half was not found.

### R3. Weaker sufficient assumptions (C1)

- **Statement.** No transitive relation satisfies the seven instances, with Addition in the form
  "(A ≻ AB) → ¬(AC ≻ AB)", while settling the four avoidance comparisons. Reflexivity and the
  remaining completeness are unused.
- **Scope.** Finite computational result. The propositional core is checked. Because the skeleton
  exists for every witness (p, q) (closed form above), this is an **unrestricted conjecture with
  a clear path**. What remains is human review that the v0 applicability clauses match the
  source for all (p, q).
- **Evidence.** Z3, DPLL, and a 78-node `check_proof` certificate. The certificate is checked at
  script level; `verify` does not see it.
- **Local irreducibility** (catalogue v1). Each of these makes the set SAT:
  - dropping any avoidance pair;
  - quasi-transitivity instead of transitivity;
  - Suzumura consistency instead of transitivity;
  - weak MNEP;
  - weak Dominance.
- **Gap.** The positive form of the avoidance conditions (M2) needs no completeness at all.
  Arrhenius's later theorems may already be stated in that form, so novelty is doubtful.
- **Status.** Collides. The no-completeness positive form is Arrhenius's method from 1999 on; only
  the four-pair version for the exact 2000 condition set is unrecorded.

### R4. The minimum transitivity core depends on completeness

- **Statement.** With full completeness the contradiction needs only 5 transitivity instances;
  there are 10 minimum cores. With completeness restricted to the four avoidance pairs it needs
  7; there are 4 minimum cores.
- **Recognized weakenings.**
  - Quasi-transitivity and strict acyclicity escape even with full completeness.
  - Suzumura consistency does not escape with full completeness (it is equivalent to
    transitivity there), but escapes under the four-pair restriction.
- **Evidence.** Implicit-hitting-set minimum cores (complete enumeration); Z3 plus DPLL.
- **Status.** Finite computational result. Partial collision: the qualitative relation theory is
  standard; the core sizes and counts were not found.

### R6. A second proof skeleton using Non-Anti-Egalitarianism once

- **Statement.** Take the unreviewed v0 schema with W(p=1, q=1) on the "gapped" grid:
  - levels −1, 1, 5, 6, 7, 14;
  - very-high {14}; very-low {1, 5, 6, 7}; slightly negative {−1}.

  The following 8 instances over 8 populations are inconsistent with a complete preorder:
  - Dominance: 7⁷ ≻ 6⁷ and 6⁷ ≻ 5⁷.
  - Non-Anti-Egalitarianism: ¬((1⁵,14,14) ≻ 5⁷).
  - Non-Repugnance: ¬(7⁷ ≻ (14)).
  - Non-Sadism on background (14,14): ¬((−1,14,14) ≻ (1⁵,14,14)).
  - MNEP on background (14): (−1,14,14) ⪰ (7,7,14).
  - MNEP on background 6⁵: (−1,6⁵,14) ⪰ 6⁷.
  - Addition with base (14), added (7,7), and lower group (6⁵, −1):
    (14) ≻ (7,7,14) → (7,7,14) ⪰ (−1,6⁵,14).

  Only 3 completeness pairs are needed (the minimum core size is 3, against 4 for the baseline).
  The largest population is 7; the baseline skeleton needs 9 on this grid. The skeleton is not
  isomorphic to the baseline, either logically or semantically.
- **Human reconstruction.** Addition gives a case split on A ≻ AB, where A = (14) and
  AB = (7,7,14).
  - If A ≻ AB: Addition gives AB ⪰ AC = (−1,6⁵,14). Then MNEP and Dominance give
    AC ⪰ 6⁷ ≻ 5⁷.
  - Otherwise: AB ⪰ A, and Repugnance with completeness gives A ⪰ 7⁷ ≻ 6⁷ ≻ 5⁷.

  Either way AB ≻ 5⁷, so AAE = (−1,14,14) ≻ 5⁷. With completeness, Non-Sadism and
  Non-Anti-Egalitarianism give 5⁷ ⪰ AAF ⪰ AAE, a contradiction.

  Where the baseline gets AC ≻ G from Dominance, this skeleton puts the slightly negative life
  into Addition's lower group. It then links AC to G through a second MNEP instance and a
  dominance chain, so the AC-versus-D Anti-Egalitarianism instance is not needed.
- **Size law** (derived for p=q=1, and matched by the search). The largest population n must
  satisfy n > 2(a−f)/(g−f), where g is the equal comparison level. That is the same form as the
  baseline's AAF clause, minus the AC-versus-D clause. The two skeletons therefore tie on the
  baseline grid (15 lives at q=1) and differ where (a−d)/(d−c) is large.
- **Scope.** Finite computational result. Solver-discovered proof skeleton under an unreviewed
  schema, for a fixed witness W.
- **Evidence.** Three decision procedures:
  - Z3 with rank encoding;
  - the production CLI with atom encoding (`research/experiments/schema-gapped-p1q1-N7-skeleton0.toml`,
    verify accepted);
  - exhaustive enumeration of all 545,835 complete preorders on its 8 relata, none of which
    satisfy the core.

  Every instance passes the independent applicability audit.
- **Fidelity questions** that decide whether this is an Arrhenius proof at all:
  - Does Arrhenius's Addition allow the "even lower" group to contain a negative life?
  - Does MNEP quantify over arbitrary backgrounds?
  - Is 7 "very low" when 14 is "very high"? (The grid is still a sensitivity choice.)
- **Escape structure.** Minimum incomparability is 5, and the minimum escape again isolates the
  population where Non-Sadism and Non-Anti-Egalitarianism meet, (1⁵,14,14). This supports U3.
- **Status.** Partial collision, pending fidelity review. The outer frame is Arrhenius 1999; only
  the closing link is unrecorded.

### R5. Triangle gap condition

This is a diagnosis of the formalization, not a claim about Arrhenius.

- **Statement.** In v0 schemas, let the MNEP bundle be q very-high lives plus one slightly
  negative life, on an empty background. Suppose it averages below a very-low level c that has a
  very-low level b > c above it:

  (q·a + e)/(q+1) < c < b

  Then MNEP, Dominance, Non-Anti-Egalitarianism, and transitivity are jointly inconsistent. No
  completeness, Addition, Sadism, or Repugnance is involved. The proof is
  bundle ⪰ (q+1)·b ≻ (q+1)·c, contradicting ¬(bundle ≻ (q+1)·c).
- **Consequence.** Any transitive relation satisfying v0 Dominance and Non-Anti-Egalitarianism
  forces MNEP's witness to satisfy n ≥ (c − e)/(a − c) for every such c.
- **Scope.** Checked theorem for the schema instance, with a three-line proof. The core is
  verified by the CLI and by enumeration. Search results match the closed-form predicate on every
  grid tested.
- **Why interesting.** Order-only categories make the schema trivially inconsistent. The source's
  implicit distance between "very high" and "very low" is exactly what blocks this. The triangle
  cannot fire on the baseline grid for any q.
- **Status.** Formalization finding. Too simple to be a discovery.

## Failed conjectures

1. **The curated five completeness pairs are minimal.** False. The four avoidance pairs form a
   MUS. 335 MUSes have size 4.
2. **Some pair is forced incomparable in every escape.** False. The MUS intersection is empty.
3. **The minimum escape is not unique.** False. It is unique.
4. **Same-number completeness suffices for UNSAT.** False, with a checked SAT model.
5. **A smaller grid witness exists for p=1, q=2.** False. 22 is optimal.
6. **Weak MNEP survives local completeness.** False (SAT). It needs AAE:AB as well.
7. **Suzumura consistency suffices under local completeness.** False (SAT).
8. **The escape incomparability graph is always connected.** False, 4 counterexamples. Smallest:
   A ∥ D together with the AAF star.
9. **AAF is always incomparable to G or AAE.** False, 134 counterexamples. In these D is isolated
   instead.

## Emerging structural patterns

- **Completeness does exactly one job in this proof:** it turns each "not better" avoidance into
  "at least as good".
  - Each positive-form avoidance substitutes for exactly its own completeness pair (M2s).
  - All four positive forms remove completeness entirely (M2, 39-node certificate).
- **Escapes are organized by which avoidance principle is made vacuous.**
  - The cheapest single-route escape is through Repugnance.
  - The global minimum combines Sadism with the second Anti-Egalitarianism instance.
- **The SAT regions obtained by dropping one principle are small and rigid.**
  - Dropping Addition leaves 32 complete models with 12 of 21 pairs forced.
  - Dropping Repugnance leaves 32 with 10 forced.
  - Dropping MNEP leaves 64 with 12 forced.
  - Dropping Dominance leaves 416 with no pair forced.
- **Completeness and transitivity trade off:** fewer settled comparisons require longer chains
  (5 versus 7 instances).
- **Witness size depends only on p+q** on the source grid, and on gap ratios in general.

## Strongest unrestricted conjectures suggested by the data

- **U1.** Arrhenius's 2000 theorem remains valid with completeness replaced by "avoidance
  comparability". Whenever an avoidance condition says X is not better than Y, X and Y are
  comparable. Addition may also be in "not better" form. The propositional part is checked, and
  witnesses exist for every (p, q). Fidelity review is outstanding, and the result may be known.
- **U2.** Arrhenius's conditions are jointly consistent with same-number completeness plus
  transitivity. This needs a uniform model, and the search here was bounded.
- **U3.** In every Arrhenius-type skeleton, the minimum escape isolates the population on which
  Non-Sadism and Non-Anti-Egalitarianism meet. Support so far:
  - AAF in the baseline skeleton (minimum 4, unique).
  - (1⁵,14,14) in both R6-type skeletons (minimum 5). One of them also has an A-isolating
    minimum.
  - (1,8,8) in the 4-instance relaxed skeleton (minimum 3).

  This is a bounded conjecture supported by four skeletons.

## Phase 6: schema-level skeleton search

Formalization: `arrhenius-2000.schema/v0-unreviewed` (`research/schema.py`).
- **Instantiation.** Every universal principle is instantiated over D_N, the nonempty multisets
  of at most N lives over the grid levels.
- **Witness.** Existentials are fixed by W: the Repugnance witness is A = one life at the top
  very-high level, and MNEP uses n = q.
- **Transfer.** UNSAT over D_N refutes "v0 + W" only. It refutes neither Arrhenius nor v0 with
  another witness.
- **Encoding.** The complete branch uses the rank encoding, which was cross-checked against the
  atom encoding in the tests.
- **Nesting.** D_N ⊆ D_{N+1}, and the instance sets were checked to be nested.

| Grid | W | Result | Skeleton |
|---|---|---|---|
| baseline {−1,1,2,3,4,8} | p=1, q=1 | SAT for all N ≤ 8 (342k instances at N=8) | none; baseline skeleton needs 15 |
| baseline | p=1, q=2 | SAT for all N ≤ 8 | none; baseline skeleton needs 22 |
| relaxed {−1,1,5,6,7,8} | q=1 | UNSAT at N=2 | triangle (3 instances, no completeness) |
| relaxed | q=2 | UNSAT at N=3 | triangle; also a 4-instance variant with Non-Sadism |
| relaxed | q=3 | UNSAT at N=4 | triangle (predicted) |
| relaxed | q=4 | SAT for all N ≤ 6 | triangle predicted not to fire; baseline skeleton needs 9 |
| gapped {−1,1,5,6,7,14} | q=1 | UNSAT at N=7 | R6 (8 instances, 8 relata) |
| gapped | q=2 | SAT for all N ≤ 8 | R6-type needs 10; baseline needs 10 |

- **Triangle closed form.** The predicate (q·min VH + min SN)/(q+1) < second-highest VL predicted
  firing correctly in all eight runs, including the q=3 and q=4 runs added as a falsification
  test.
- **Coverage.** Skeleton coverage is a diversified search capped at 12 cores per run, not full
  MUS enumeration. "Smallest skeleton found" is not "minimum skeleton".
- **Bounded negative result.** On the baseline grid no skeleton of any shape fits within 8 lives.
  This is a finite computational result under the unreviewed schema.

## Literature collision

Source: `corpus/literature.toml`, which records each work, what was read firsthand, and a
verdict per result. The check covered Arrhenius's theorem papers from 1999 to 2022, his thesis,
Thomas's reconstruction of the book theorems, Thomas 2018, Thornley, the critical-band and
critical-range literature, and a search for machine-reasoning treatments. The book manuscript
and Arrhenius (2016, Theoria) were not obtained.

- **Arrhenius had already moved past completeness.** The 2000 paper says the theorem fails
  without completeness (p. 264, fn 31) and points to the 1999 theorem. Every Arrhenius theorem
  from 1999 on is stated over a quasi-ordering, with at-least-as-good conditions and one strict
  Egalitarian Dominance step.
- **R6 reuses the 1999 frame.** At p = q = 1, r = 5 the 1999 populations are (−1,14,14),
  (7,7,14), (1⁵,14,14), and 5⁷. The MNEP step, the Non-Sadism step, and the single inequality
  step match R6 exactly. Arrhenius's 2009 and 2011 Lemma 3 already puts negative lives in the
  added low group and removes them with an MNEP-type bridge. What remains is the closing link:
  E&P 2000 Addition with a Repugnance case split, in place of Quality Addition.
- **No prior computational analysis of Arrhenius was found.** The nearest is Parent & Benzmüller
  (2024), an Isabelle/HOL treatment of Parfit's three-population Mere Addition Paradox, which
  finds that acyclicity and quasi-transitivity escape it.
- **R2 may have a known model.** Critical-Band Utilitarianism is complete within each size and is
  reported to avoid the Repugnant and Sadistic Conclusions. A research agent derived that it
  satisfies all five 2000 conditions. That derivation has not been verified.

## Next research turn

1. **Gap-constrained schema v1 on larger domains**, plus fidelity review of R6's two
   quantifier readings.
   - Add an explicit, source-justified gap axiom.
   - Generate instances lazily so N can reach 10–15; Non-Sadism instances dominate the counts.
   - Test whether any skeleton smaller than the baseline exists once the triangle is blocked.
   - Highest information gain: R6 shows that the baseline skeleton is not the unique small proof.
     The open question is whether a skeleton beats the AAF clause's bound, which both known
     skeletons share.
2. **Uniform model for U2.** Look for a closed-form relation, for example lexicographic by
   population size, that is complete within each size. Test it against the v0 schema on bounded
   domains before attempting a proof.
3. **Remaining literature gaps.** Read Arrhenius (2016, Theoria) before any R2 claim. Get
   firsthand copies of Blackorby, Bossert & Donaldson (1996, 1997) and check whether
   Critical-Band Utilitarianism satisfies the 2000 conditions; if it does, U2 is settled by a
   known model. The `[[wanted]]` list in `corpus/literature.toml` names the rest.
4. **Encode the 1999 theorem and thesis Theorem 3** as frozen instances. R6 should then appear as
   a hybrid of the 1999 and 2000 skeletons, and the escape analysis can be rerun on a theorem
   that Arrhenius proved without completeness.

## Ledger

Machine-readable: `research/ledger.json`. The rows below are rendered from it by
`research/render_ledger.py`.

<!-- ledger:start -->
| candidate | status | scope label | tier | result |
|---|---|---|---|---|
| C1-combined-weakening | confirmed | finite computational result | logical mutation | unsat; certificate 78 nodes; dropping any avoidance pair: SAT (all 4); quasi-transitivity: SAT; Suzumura: SAT; weak MNEP: SAT; weak Dominance: SAT; dropping reflexivity: UNSAT (reflexivity unused) |
| M1-local-completeness-avoidance | confirmed | finite computational result | logical mutation | unsat; certificate 71 nodes (curated: 75 nodes, 5 pairs) |
| M1c-same-number-completeness | refuted | finite computational result | logical mutation | same-number: sat; different-number only: unsat |
| M2-reverse-weak-avoidance | confirmed | finite computational result | logical mutation | all four: unsat with no completeness; certificate 39 nodes; single positive avoidance + other three pairs: UNSAT for each; single positive avoidance alone: SAT for each |
| M3-transitivity | confirmed | finite computational result | logical mutation | min transitivity instances: 5 under full completeness (10 minimum cores), 7 under M1 (4 cores); quasi-transitivity: sat; acyclicity: sat; Suzumura: unsat (full completeness), sat (M1) |
| M4-M6-premise-weakenings | confirmed | finite computational result | logical mutation | weak Dominance: sat; weak Addition: full unsat, M1 unsat, none sat; weak MNEP: full unsat, M1 sat, M1+AAE:AB unsat |
| P0-baseline | confirmed | finite computational result | frozen source-reviewed witness | {"artifact_id (expected to differ: hashes wall time)": false, "checked_proof": true, "claim_kind": true, "grounded_core": true, "outcome": true, "problem_id": true, "run_key": true, "source_fidelity": true} |
| P1-active-reduction | confirmed | finite computational result | frozen source-reviewed witness | 0 of 47,293 complete preorders satisfy all seven instances; DPLL=unsat; extensions preorder=True |
| P1-frontier | confirmed | finite computational result | frozen source-reviewed witness | principle: 1 MUS [['completeness', 'repugnance-avoidance', 'anti-egalitarianism-avoidance', 'sadism-avoidance', 'minimal-non-extreme-priority', 'dominance', 'addition']], 7 maximal SAT; instance: 1 MUS, 8 maximal SAT;... |
| P2-avoidance-necessity | confirmed | finite computational result | frozen source-reviewed witness | confirmed (avoidance pairs form a MUS: True); single-route minimum K: {'completeness:A:D': 6, 'completeness:AAE:AAF': 10, 'completeness:AAF:G': 12, 'completeness:AC:D': 10} |
| P2-core-structure | refuted | finite computational result | frozen source-reviewed witness | 339 MUSes {4: 335, 5: 4}, intersection empty; 110 MCSes {4: 1, 6: 6, 7: 12, 8: 26, 9: 33, 10: 18, 11: 6, 12: 8}; forced comparable ['completeness:AAE:AB', 'completeness:AC:G']; forced incomparable none; curated 5-pair... |
| P2-escape-sat | confirmed | finite computational result | frozen source-reviewed witness | SAT; 20169 escape preorders on the 7 labeled relata |
| P2-min-incomparability | confirmed | finite computational result | frozen source-reviewed witness | k_min=4 (enumeration 4); unique minimum pattern ['AAE/AAF', 'AAF/AB', 'AAF/AC', 'AAF/G']; 8 labeled minimum models |
| P2-same-number-escape | confirmed | finite computational result | frozen source-reviewed witness | min K = 6; patterns [['A/AAE', 'A/AAF', 'A/AB', 'A/AC', 'A/D', 'A/G']]; min unresolved different-number pairs overall = 2 |
| P3-grid-minimum | refuted | finite computational result | source-constrained fixed-skeleton generalization | min largest population by (p,q): {'p=1,q=1': 15, 'p=1,q=2': 22, 'p=1,q=3': 29, 'p=1,q=4': 36, 'p=1,q=5': 43, 'p=2,q=1': 22, 'p=2,q=2': 29, 'p=2,q=3': 36, 'p=2,q=4': 43, 'p=2,q=5': 50, 'p=3,q=1': 29, 'p=3,q=2': 36, 'p=... |
| P3-six-level-lemma | confirmed | checked theorem (fixed skeleton) | source-constrained fixed-skeleton generalization | grid: distinct levels [6] |
| P3-spacing-collapse | confirmed | finite computational result | rational-cardinal spacing sensitivity | closed form agrees on 858 cases: True; largest population collapses to p+q+2 (4 for p=q=1, 5 for p=1,q=2) when (a-g)/(g-f) is small |
| P5-conjecture-E1 | confirmed | finite computational result | frozen source-reviewed witness | holds on every escape |
| P5-conjecture-E2 | confirmed | finite computational result | frozen source-reviewed witness | holds on every escape |
| P5-conjecture-E3 | refuted | finite computational result | frozen source-reviewed witness | false: 4 counterexamples |
| P5-conjecture-E4 | confirmed | finite computational result | frozen source-reviewed witness | holds on every escape |
| P5-conjecture-E5 | confirmed | finite computational result | frozen source-reviewed witness | holds on every escape |
| P5-conjecture-E6 | refuted | finite computational result | frozen source-reviewed witness | false: 134 counterexamples |
| P5-conjecture-E7 | confirmed | finite computational result | frozen source-reviewed witness | holds on every escape |
| P5-maximal-sat-census | confirmed | finite computational result | frozen source-reviewed witness | (models, forced pairs of 21) per dropped group: {'drop repugnance-avoidance': (32, 10), 'drop anti-egalitarianism-avoidance': (624, 1), 'drop sadism-avoidance': (104, 10), 'drop minimal-non-extreme-priority': (64, 12)... |
| P6-baseline-p1q1 | confirmed | finite computational result | unreviewed schema generalization | SAT for every N <= 8 (3002 populations, 341831 instances at N=8); every SAT rank model checked against all instances; triangle closed form predicts firing: False |
| P6-baseline-p1q2 | confirmed | finite computational result | unreviewed schema generalization | SAT for every N <= 8 (3002 populations, 341831 instances at N=8); every SAT rank model checked against all instances; triangle closed form predicts firing: False |
| P6-gapped-p1q1 | confirmed | finite computational result | unreviewed schema generalization + rational-cardinal spacing sensitivity | smallest UNSAT N = 7; 7 cores, 6 distinct skeletons; smallest: ['dominance(P_6_6_6_6_6_6_6, P_5_5_5_5_5_5_5)', 'dominance(P_7_7_7_7_7_7_7, P_6_6_6_6_6_6_6)', 'non-anti-egalitarianism(P_1_1_1_1_1_14_14, P_5_5_5_5_5_5_5... |
| P6-gapped-p1q2 | confirmed | finite computational result | unreviewed schema generalization + rational-cardinal spacing sensitivity | SAT for every N <= 8 (3002 populations, 342300 instances at N=8); every SAT rank model checked against all instances; triangle closed form predicts firing: False |
| P6-relaxed-p1q1 | confirmed | finite computational result | unreviewed schema generalization + rational-cardinal spacing sensitivity | smallest UNSAT N = 2; 4 cores, 2 distinct skeletons; smallest: ['dominance(P_6_6, P_5_5)', 'non-anti-egalitarianism(P_m1_8, P_5_5)', 'mnep(P_m1_8, P_6_6)'] (CLI unsat, enumerator models 0); triangle closed form predic... |
| P6-relaxed-p1q2 | confirmed | finite computational result | unreviewed schema generalization + rational-cardinal spacing sensitivity | smallest UNSAT N = 3; 2 cores, 2 distinct skeletons; smallest: ['dominance(P_7_7_7, P_6_6_6)', 'non-anti-egalitarianism(P_m1_8_8, P_6_6_6)', 'mnep(P_m1_8_8, P_7_7_7)'] (CLI unsat, enumerator models 0); triangle closed... |
| P6-relaxed-p1q3 | confirmed | finite computational result | unreviewed schema generalization + rational-cardinal spacing sensitivity | smallest UNSAT N = 4; 1 cores, 1 distinct skeletons; smallest: ['dominance(P_7_7_7_7, P_6_6_6_6)', 'non-anti-egalitarianism(P_m1_8_8_8, P_6_6_6_6)', 'mnep(P_m1_8_8_8, P_7_7_7_7)'] (CLI unsat, enumerator models 0); tri... |
| P6-relaxed-p1q4 | confirmed | finite computational result | unreviewed schema generalization + rational-cardinal spacing sensitivity | SAT for every N <= 6 (923 populations, 46118 instances at N=6); every SAT rank model checked against all instances; triangle closed form predicts firing: False |
| P6-skeleton-gapped-p1q1-0 | confirmed | finite computational result | solver-discovered proof skeleton (unreviewed schema) | 8 instances over 8 relata ({'addition': 1, 'dominance': 2, 'mnep': 2, 'non-anti-egalitarianism': 1, 'non-repugnance': 1, 'non-sadism': 1}); largest population 7; CLI unsat, enumerator models 0, completeness MUS sizes ... |
| P6-skeleton-gapped-p1q1-1 | confirmed | finite computational result | solver-discovered proof skeleton (unreviewed schema) | 8 instances over 8 relata ({'addition': 1, 'dominance': 2, 'mnep': 2, 'non-anti-egalitarianism': 1, 'non-repugnance': 1, 'non-sadism': 1}); largest population 7; CLI unsat, enumerator models 0, completeness MUS sizes ... |
| P6-skeleton-gapped-p1q1-2 | confirmed | finite computational result | solver-discovered proof skeleton (unreviewed schema) | 9 instances over 9 relata ({'addition': 1, 'dominance': 2, 'mnep': 2, 'non-anti-egalitarianism': 1, 'non-repugnance': 1, 'non-sadism': 2}); largest population 7; CLI unsat, enumerator models None, completeness MUS siz... |
| P6-skeleton-gapped-p1q1-3 | confirmed | finite computational result | solver-discovered proof skeleton (unreviewed schema) | 10 instances over 10 relata ({'addition': 1, 'dominance': 2, 'mnep': 2, 'non-anti-egalitarianism': 2, 'non-repugnance': 1, 'non-sadism': 2}); largest population 7; not re-verified (ranked below top 3); core: ['dominan... |
| P6-skeleton-gapped-p1q1-4 | confirmed | finite computational result | solver-discovered proof skeleton (unreviewed schema) | 14 instances over 14 relata ({'addition': 1, 'dominance': 2, 'mnep': 4, 'non-anti-egalitarianism': 3, 'non-repugnance': 1, 'non-sadism': 3}); largest population 7; not re-verified (ranked below top 3); core: ['dominan... |
| P6-skeleton-gapped-p1q1-5 | confirmed | finite computational result | solver-discovered proof skeleton (unreviewed schema) | 15 instances over 15 relata ({'addition': 1, 'dominance': 2, 'mnep': 4, 'non-anti-egalitarianism': 3, 'non-repugnance': 1, 'non-sadism': 4}); largest population 7; not re-verified (ranked below top 3); core: ['dominan... |
| P6-skeleton-relaxed-p1q1-1 | confirmed | finite computational result | solver-discovered proof skeleton (unreviewed schema) | 4 instances over 4 relata ({'dominance': 2, 'mnep': 1, 'non-anti-egalitarianism': 1}); largest population 2; CLI unsat, enumerator models 0, completeness MUS sizes {0: 1}, escape k_min None; core: ['dominance(P_6_6, P... |
| P6-skeleton-relaxed-p1q2-1 | confirmed | finite computational result | solver-discovered proof skeleton (unreviewed schema) | 4 instances over 4 relata ({'dominance': 1, 'mnep': 1, 'non-anti-egalitarianism': 1, 'non-sadism': 1}); largest population 3; CLI unsat, enumerator models 0, completeness MUS sizes {1: 3}, escape k_min 3; core: ['domi... |
<!-- ledger:end -->
