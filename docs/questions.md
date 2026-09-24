# Open questions

Conjectures and unresolved fidelity questions. Each entry says what would settle it. When one is
settled, mark it closed and point to the decision entry or ledger row that closed it; do not
delete it.

## Q-001. U1: avoidance comparability replaces completeness

- **Status:** open.
- **Claim:** the 2000 theorem stays valid with completeness replaced by "avoidance
  comparability": whenever an avoidance condition says X is not better than Y, X and Y are
  comparable. Addition may also be in "not better" form.
- **Known:** the propositional part is checked, and witnesses exist for every (p, q).
- **Settles it:** a source-grounded review of the v0 applicability clauses for all (p, q), then a
  literature check. It may be known (compare R3).

## Q-002. U2: same-number completeness is consistent

- **Status:** open.
- **Claim:** Arrhenius's 2000 conditions are jointly consistent with same-number completeness
  plus transitivity.
- **Known:** bounded search only. Critical-Band Utilitarianism is reported to avoid the
  Repugnant and Sadistic Conclusions; a literature agent derived, but did not find stated, that it
  satisfies all five 2000 conditions.
- **Settles it:** a uniform model checked against the conditions, or a firsthand check of
  Blackorby, Bossert & Donaldson (1996, 1997) that Critical-Band Utilitarianism satisfies them.

## Q-003. U3: the minimum escape isolates the Sadism/Anti-Egalitarianism meeting point

- **Status:** open; bounded conjecture.
- **Claim:** in every Arrhenius-type skeleton, the minimum escape isolates the population on
  which Non-Sadism and Non-Anti-Egalitarianism meet.
- **Known:** holds for AAF in the baseline skeleton (minimum 4, unique), (1⁵,14,14) in both
  R6-type skeletons (minimum 5; one also has an A-isolating minimum), and (1,8,8) in the
  4-instance relaxed skeleton (minimum 3).
- **Settles it:** escape numbers for every class in the motif census.

## Q-004. How far apart must very high and very low be?

- **Status:** open.
- **Question:** the 2000 paper declares the categories and requires four ordered very-low levels
  but sets no minimum gap between very low and very high. Is 7 a fair very-low level when 14 is
  very high (the gapped grid, R6)? Order-only categories admit the R5 triangle.
- **Settles it:** a source-justified gap axiom. The thesis replaces the categories with ranges
  R(u,v) above R(1,y), each at least three consecutive levels (D-014). That settles the gap for
  the thesis family; the 1999 and 2000 statements still set none.

## Q-005. MNEP wording: n or n+1 very-low lives

- **Status:** closed by D-012: the formal statements say n+1.
- **Question:** the paraphrase in `corpus/sources.toml` (source_wording, 2000) and
  `SOURCE_CLAUSES["mnep"]` in `research/schema.py` say one slightly negative life is offset
  "against the same number of very-low-positive lives". The generator in `research/schema.py`
  pits n very-high lives plus one slightly negative life against n+1 very-low lives, which
  matches the 1999 wording (n+1). The human-reviewed 2000 witness also uses n+1 (q = 2 against 3
  lives at level 4).
- **Settles it:** the verbatim formal MNEP on p. 261 of the 2000 paper. If it says n+1, the
  paraphrases are wrong and the code is right.

## Q-006. The cycle/fork hypothesis

- **Status:** closed by P9-l0-cycle-motif and P9-l0-fork-motif. Fork-free minimal cores are
  exactly simple strict cycles (a standard difference-constraint fact; enumeration to 6 edges
  matches the necklace counts). One-fork cores are the fork plus two strict paths converging on
  its middle argument (enumeration to 5 edges; the general proof is Q-008). Every thesis-family
  condition is fork-free, so all of its minimal cores are cycles.
- **Claim:** under completeness every principle shape is a difference constraint over ranks (W,
  S, or the disjunction I), so a skeleton's unsatisfiability depends only on its shape
  hypergraph. Minimal cores are then simple cycles with at least one strict edge (no I edge) or
  forced-comparability forks (with I edges).
- **Settles it:** exhaustive enumeration of minimal UNSAT shape hypergraphs up to a bound in the
  motif census.

## Q-007. R7: the priority triangle recurs in the thesis family

- **Status:** open; formalization diagnostic, literature unchecked.
- **Claim:** Condition δ, Condition β (or Inequality Aversion) and Egalitarian Dominance close a
  3-cycle whenever δ's witness n for (z, m) satisfies m ≥ m_β(n), where m_β(n) is β's witness for
  n. The census finds it on the Phase 8 witness inside the 2003, Theorem 4 and 2009 condition
  sets (for example (−1⁵, 4) ⪰_δ 3⁶ ≻_ED (−1³, 0³) ⪰_β (−1⁵, 4)), and the known-ground
  matcher identifies it with the R5 triangle at the role level. So a satisfying axiology must let
  δ's n grow with m, as the GNEP realization of δ does (n = 4 for z = −1).
- **Firing condition (P10-triangle-firing-condition).** The only rotation that closes is
  δ(X ⪰ Y), ED(Y ≻ Z), β(Z ⪰ X). ED forces Y to be n+m lives at W_3 and Z to lie below W_3, so
  β's background holds only δ's negative lives. The triangle fires iff some m with n = n_δ(m)
  has m_β(n) ≤ m (= m for Inequality Aversion), within the bound, given a level strictly
  between the negative level and W_3. The prediction matches the census on all 108 witnesses of
  the Phase 10 grid (24 fire).
- **Settles it:** a written proof of necessity at every size, and a check whether Arrhenius
  states the growth requirement (thesis Lemma 5.2, 2009 Lemma 2).

## Q-008. The fork motif in general

- **Status:** open.
- **Claim:** every minimal rank-inconsistent hypergraph with exactly one Addition fork is the
  fork plus two strict paths converging on its middle argument, at any size.
- **Settles it:** a written proof (each disjunct must close its own strict cycle, and minimality
  forces the union of two such paths), then extension to two forks.

## Q-009. Exchange rates, not growth: repeated δ steps

- **Status:** open.
- **Observation (P10-safe-census-arrhenius-2003-vrc):** with δ's n growing by 5 per negative
  life, the triangle disappears, but over {δ, 2003 β, Egalitarian Dominance} a 5-cycle
  δ, δ, ED, β, β survives with β's step 1:
  (−1², 3, 4²) ⪰_δ (−1, 3³, 4) ⪰_δ 3⁵ ≻_ED 1⁵ ⪰_β (0³, 4²) ⪰_β (−1², 3, 4²).
  It applies δ twice with m = 1. Growth in m cannot protect against repeating the cheapest δ
  step, so the constraint is on the exchange rate δ allows per negative life against the rate β
  demands. With β's step 2 or 3 no cycle of length ≤ 5 survives at ≤ 6 lives.
- **Settles it:** a characterization of the cycles δ^a β^b ED in terms of both witnesses'
  rates, tested against the census over a witness grid; then whether any witness family avoids
  every such cycle while keeping the source proofs.

## Q-010. Gaps in the possibility map

- **Status:** open (3 of 58 sets).
- **Setup (P11-possibility-map):** the additive class is decided exactly, and 57
  lexicographic-additive axiologies are checked exactly (D-021). 58 minimal condition sets are
  realized by none of them. 37 are explained by a known or project theorem via the recorded
  implications; 21 are not. Every unexplained set has 4 or 5 conditions.
- **Certificates (P12-gap-certificates, D-019):** 18 of the 21 are proved consistent. Two
  mechanisms cover them. (1) The background-free quality condition (Quality or VRC avoidance)
  is inert and total utilitarianism covers the rest, so the backgrounds in Weak Quality Addition
  are load-bearing in thesis Theorems 3 and 4 and the 2009 theorem. (2) With NEP rather than
  GNEP, a first tier that makes only W_−2 lexically bad separates NEP's single negative life at
  W_−1, which high lives outweigh, from Weak Quality Addition's negatives at W_−2, which nothing
  outweighs. That closes {Egalitarian Dominance, NEP, Quantity, 2009 Weak Quality Addition} and
  the NEP variants of the Dominance Addition and Non-Sadism gaps. GNEP defeats (2): it trades
  one level at every level, so no level can be lexically bad.
- **Project theorems explain eleven former gaps:**
  - P13-bounce-theorem: {Egalitarian Dominance, GNEP, Quantity, 2009 Weak Quality Addition}
    (research/p13_bounce.py).
  - P14-gnep-theorem-3: thesis Theorem 3 with GNEP for NEP, with Weak Non-Sadism or Non-Sadism
    and either form of Weak Quality Addition (research/p14_gnep_theorem_3.py). GNEP raises each
    negative life to W_3 one level at a time, and Inequality Aversion supplies enough lives to
    absorb any witness. The bounded census missed it because the cycle needs more than 6 lives.
  - P16-top-gnep-ne-and-ia: five Dominance Addition gaps with GNEP, repaired 2009 Weak
    Quality Addition, and Inequality Aversion or either Non-Elitism form. Its audited cycles
    need no welfare level above the GNEP witness (research/p16_ne_top.py; Q-013).
- **Still open: 3.** Each contains Egalitarian Dominance, GNEP, VRC avoidance, a Non-Elitism
  form and a Dominance Addition form (Q-011). VRC avoidance has no arbitrary background,
  so the P16 Weak Quality Addition construction does not apply.
- **Settles it:** for each of the three, a certificate from a background-sensitive or
  count-sensitive model class, or a contradiction for every valid top-level witness.

## Q-011. Is the 2003 theorem stronger than stated?

- **Status:** open at the source-general welfare-level domain; the weakest variant now has an
  all-population-size model on the finite ladder `W_-1…W_6` (P21).
- **Candidates:** the 2003 conditions {Egalitarian Dominance, Non-Elitism, GNEP, VRC avoidance,
  Dominance Addition}, with Dominance Addition weakened to the thesis's not-worse form, or
  Non-Elitism weakened to its ranged background, or both. P21 realizes **both** weakenings
  together on one finite ladder at one legal witness. The two singly weakened variants remain
  without a model; no source-general model or contradiction is established for any variant.
- **What the proof would need:** the published 2003 proof uses Condition β with a negative
  background while β's own low level is `W_1`. Thesis Non-Elitism yields β with background in
  `R(z, y+1)`: that excludes negatives for the published levels, but permits them if β's low
  level `z` is negative (D-022). The published Dominance Addition edge also has a mixed positive
  addition, unavailable to thesis Dominance Addition. The thesis not-worse clause is N-shaped,
  not a reverse weak edge in isolation; it can nevertheless close a suitable weak cycle.
- **Evidence so far (lemma level, derived β and δ, ≤ 6 lives, δ's n growing by 5 per negative
  life):**
  - The control holds: the 2003 conditions reproduce their source word.
  - With ranged β (the 2009 Lemma 1 form that ranged Non-Elitism yields) there are no cycles at
    all.
  - With not-worse Dominance Addition, no cycle uses Dominance Addition. The only cycles are
    Q-009 exchange-rate cycles over β, δ and Egalitarian Dominance, and those are witness
    artifacts: total utilitarianism satisfies Egalitarian Dominance, Non-Elitism and GNEP
    together once δ's base n is at least 4 on this ladder.

- **Source-instance diagnostic (P17-vrc-source-boundary):** at the Phase 8 fixed witness, on only
  the five frozen 2003 proof populations (each at most six lives), the original and ranged-NE
  sets each generate 1 Egalitarian Dominance, 2 VRC-avoidance and 2 Dominance Addition instances;
  the thesis-DA sets generate the first 3 but no DA instance. No primitive Non-Elitism or GNEP
  instance has both endpoints among these five populations. All four focused preorders are SAT
  without completeness, with no W/S cycle of at most 8 edges. The original published *derived*
  β/δ proof remains independently UNSAT: its β edge has a negative background unavailable to
  ranged NE, and its mixed-addition DA edge is unavailable to thesis DA. This narrow diagnostic
  neither tests all six-life populations nor settles any variant; see `research/results/p17_vrc_boundary.json`.

  This bounded diagnostic does not establish consistency for either weakening.

- **Primitive control and bounded search (P18-vrc-primitive-control-and-bounded-search,
  `research/p18_vrc_certificate.py`):** the 2003 Lemma 3 chain is rebuilt from primitive
  applications: 42 edges over 42 populations — 35 Non-Elitism, four GNEP, one each Egalitarian
  Dominance, Dominance Addition and VRC avoidance — every edge replayed from its own serialized
  decomposition (principle, shape, count vectors, background, added parts, existential lookup,
  source page), and every edge also passing the exhaustive ladder audit. Condition β's realized
  target (n = 5, m = 35, C = 40 lives at W_3, from the Lemma 1.2 counts 5, 10, 20) and Condition
  δ's (four GNEP applications at z = −1, 0, 1, 2 with δ's n = 4 at m = 1) are audited as source
  instances, so both derived conditions are targets of the trace rather than premises. The chain is
  UNSAT with no completeness through mentioned-atom transitivity alone, and the separately labelled
  P8 derived β/δ control stays UNSAT. On the fixed 32- and 64-population foci (≤ three lives per
  relatum, the 11 mandatory seeds, 218 and 511 instances, all audited, all seven principles
  covered) all four variants are SAT at both caps with no W/S cycle of at most 8 edges, the scan
  being partial only where thesis Dominance Addition's N-shape is present. Fixing a cap-32
  assignment's weak atoms and extending it to the 64-relatum focus is UNSAT for all four variants
  on this run, each with a minimal conflicting set of two or three primitive clauses; an
  independent run of the same query found original and ranged-NE extending SAT instead, so that
  decision is a property of the recorded 32-relatum assignment, not of the focus. A bounded SAT
  table bounds nothing beyond its focus and no source-general witness construction or full
  finite-ladder model is discharged here, so Q-011 stays open; see
  `research/results/p18_vrc_certificate.json`.
- **Phase 19 dual-route pass (P19-vrc-universal-routes, `research/p19_vrc_universal.py`):** both
  routes were pushed as far as the evidence allows; neither reaches a certificate, and Q-011 stays
  open.
  - *Reading.* Thesis Condition β quantifies over `D ⊂ R(z, y+1)`, a closed range, so ranged
    Non-Elitism **does** supply a negative background whenever β's own low level is negative
    (D-022). The phase-18 losing edge is therefore a level-choice artefact, and the repair is
    available; the phase replays the rule in both directions.
  - *Mechanics.* With the repair the written chain ED, δ, β, VRC closes as an UNSAT chain under
    reflexivity and the cycle's own transitivity, for **both** Dominance Addition forms. The
    not-worse (N-shaped) thesis form does not block the closure: the weak chain already entails
    `P2 ⪰ M1`, so `¬(P2 ≻ M1)` forces `M1 ⪰ P2`, contradicting the strict Egalitarian Dominance
    link. This corrects the phase-17 note that the not-worse clause gives no reverse weak edge:
    locally true, globally irrelevant inside a cycle. Dropping the Dominance Addition link restores
    satisfiability, and every chain edge passes the phase-18 manifest replay plus the new ranged-β
    replayer at this chain's own witness.
  - *Obstruction.* A derived-witness instance closes, but arbitrary source-order witnesses do
    not force this repaired chain. In the shared population, high lives must either sit at β's
    single A level with δ's high population nested there (`n_β = n_δ + n_v`), or δ's A lives
    must fall inside β's permitted background
    (`x_δ ≤ y_β + 1 ≤ y_v + 1`, a bound on the axiology's GNEP witness level relative to its own
    VRC range top that no source condition supplies). The nesting branch is closed by the source's
    own count identities: thesis Lemma 5.2.2's `n_δ = m_δ·n_χ` with `n_χ ≥ 1`, β's `m_β > n_β`,
    and the negative lives `m_δ = m_β + m_v` give the unsatisfiable
    `n_β = n_δ + n_v ≥ n_δ ≥ m_δ > m_β > n_β`. The phase proves that branch UNSAT over the
    integers, and shows the same system without the nesting equation is satisfiable, so the
    obstruction is exactly the nesting. The independent template scan in
    `research/p19_impossibility_ranged_ne.py` reports the same tension on 88 repaired templates
    (`n_δ = 4·n_g·(m_β + m_v) > n_β`); the bounded scans in
    `research/p19_impossibility_not_worse_da.py` (96-population focus, ≤ 8 lives, ≤ 6 edges) find
    no cycle and no contradiction for any variant; and the phase-18 42-edge control still replays
    and closes UNSAT at its own fixed witness.
  - *Models.* Six explicit count-sensitive total preorders were checked
    (`research/p19_vrc_model.py`; the two decisive counterexamples are re-verified by the phase
    with `ladder.audit`): critical-level and exponential additive orders fail VRC avoidance through
    arbitrary-size `B`; level-count lexicographic fails Non-Elitism for every pair `(x, y)` and
    every witness `n`; count-first and thresholded orders fail Egalitarian Dominance or
    Non-Elitism. No candidate certifies the five conditions for all finite sizes, and no
    candidate's failure proves inconsistency. The three requirements pull in different directions,
    and each class isolates one of them: critical-level total at the VRC threshold and `Σ2^level`
    satisfy everything but VRC avoidance (arbitrary-size `B`); level-count lexicographic and the
    count-first orders tested satisfy everything but Non-Elitism (one `W_x` life outranks any
    number at `W_{x-1}`); critical-level total with its critical level above the added lives
    satisfies everything but thesis Dominance Addition (enough added low lives sink the uniformly
    higher side).
  - *Background-sensitive and structural checks.* Three non-additive relations with
    background-dependent comparisons were checked in `research/p19_vrc_model_background.py`.
    Each satisfies some source conditions for all finite sizes on the ladder but fails another
    with an independently audited source instance; none models the five-condition set.
    A separate first-tier coefficient proof in `research/p19_vrc_translation_invariant.py`
    excludes every lexicographic-linear, translation-invariant order on `W_-1…W_6`, regardless
    of its existential witnesses. VRC's arbitrary-size low bag and thesis DA force zero weights
    at positive levels; NE propagates zero to the remaining positive levels; ED and GNEP force
    zero at neutral and negative levels. The necessary-coefficient solver is UNSAT and becomes
    SAT when VRC's unbounded-bag restriction is removed. This class exclusion is ladder-relative,
    not a consistency or unrestricted impossibility certificate.
  - *Verdicts at the phase-19 ladder and placement.* Route A: **unresolved** for the three
    weakenings (no source-general contradiction; the nested placement is obstructed, while the
    bound placement was not instantiated on the frozen ladder). Route B: **unresolved** for the
    three weakenings (no certified model at any stated domain). The
    original variant is not in question: for {Egalitarian Dominance, 2003 Non-Elitism, GNEP, VRC
    avoidance, 2003 Dominance Addition} the published 2003 theorem is the source-general
    impossibility, and this phase's contribution there is only the fixed-witness chain mechanics
    (both Dominance Addition forms) plus the phase-18 primitive control, not an independent
    parameterized primitive proof. The initial six route-B orders cancel shared backgrounds
    (D-018), whereas three genuinely background-sensitive orders still fail audited source
    instances. The translation-invariant class exclusion leaves only background-dependent
    relations as model candidates on this ladder. Nothing here promotes a bounded table to
    consistency or a fixed witness to a source-general claim.
    What is checked here: β's background is a level
    question (D-022), the not-worse clause does not block a closure, and the nesting count identity
    obstructs one placement of the repaired template; see
    `research/results/p19_vrc_universal.json`. A phase-20 fixed-witness construction reaches the
    bound placement one level above the frozen ladder; it does not make that placement source-general.
- **Phase 20 independent routes (P20-vrc-dual-routes, `research/p20_vrc_dual_routes.py`):**
  three contradiction constructions and three model approaches sharpen the boundary without
  settling any weakened set.
  - *Primitive cycles at chosen witnesses.* On the extended ladder `W_-1…W_9`, a direct
    23-edge cycle uses one Egalitarian Dominance, one VRC avoidance, eight GNEP, twelve
    Non-Elitism and one Dominance Addition instance. At VRC `(x,u,v,y,n,m)=(-1,5,7,4,1,2)`,
    GNEP `(u,y,n)=(4,3,1)` and Non-Elitism `n=1`, all edges pass the frozen source manifest
    and independent ladder audit, including the ranged backgrounds and single-level addition.
    Both Dominance Addition forms close without completeness; the same primitive instances
    therefore refute all four variants **at this witness only**. A separate β/δ placement puts
    the GNEP high lives in β's ranged background and expands into 82 primitive audited edges
    (15 Non-Elitism, 64 GNEP, three closing edges). Its smallest top is `W_7`, explaining why
    the phase-19 `W_6` ladder missed it. Neither cycle works for arbitrary source witnesses:
    the direct reservoir needs VRC's low range to reach GNEP's fuel level, which the source
    does not require. A distinct adversarial search found no instantiable bare cycle among
    3,762 motifs with at most three weak path edges and four levels per population; this
    bounded absence proves nothing about longer chains.
  - *Model exclusions, not a model.* On `W_-1…W_6`, an exact support-quotient cycle excludes
    every total preorder determined only by occupied levels, for every Non-Elitism witness.
    All-size inequalities exclude anchored level-separable count potentials via Egalitarian
    Dominance + ranged Non-Elitism + VRC, and strictly total-welfare-monotone
    cardinality-normalized orders via thesis Dominance Addition + VRC. A context-state
    linear-score design is refuted at its specified Non-Elitism/GNEP/VRC witness by a
    21-instance audited core at six lives; other witness choices are not excluded. Raw
    total-preorder feasibility at size eight (size eleven with the optional `--full` scan)
    is only a bounded control, not a model.
  - *Verdict.* All three weakenings remain **open** at the source-general welfare-level domain:
    no source-general primitive cycle and no source-general model. At phase 20's own fixed
    witnesses and model families, no exact all-size model was found; the both-weakened variant
    later got one on the frozen ladder (P21 below). The original is the published 2003 theorem.
    The source comparison and result scopes are in `corpus/literature.toml` and
    `research/results/p20_vrc_dual_routes.json`.
- **All-size finite-ladder model (P21-least-preorder-both-weakened,
  `research/p21_least_preorder.py`):** on all nonempty finite multisets of `W_-1…W_6`, take the
  reflexive/transitive closure of the primitive ED, thesis ranged NE, 2003 GNEP and 2003 VRC
  weak edges. Witnesses are NE `n=1`, GNEP `(u,y,n)=(5,3,1)`, VRC
  `(x,u,v,y,n,m)=(-1,4,6,3,1,1)`. Thesis DA is an N-shaped condition to verify, **not** a
  reverse weak edge. Every edge preserves cardinality except VRC, which increases it from a
  singleton when its bag is nonempty (with an empty bag it is size-preserving and holds along
  the single-life ED chain down to `W_-1`). The exact potential `Σ(20t−t²)` strictly decreases on
  each cardinality-preserving edge (the GNEP high/low drop is at least 24, against a maximum
  adjacent-level gain of 21), so the closure is a partial order and ED is strict. Every VRC
  target and subsequent reachable larger population satisfies `I(P)=#{t≤0}−#{t≥5}≥1`: ED and
  GNEP preserve it, and the only negative-delta ranged NE cases either retain slack or have an
  impossible invariant-bearing source. DA's larger target is unreachable from any nonsingleton,
  and a singleton cannot reach its all-positive DA target by VRC without violating `I≥1`; a
  same-size DA target (C empty, which the reading leaves open) is excluded by the strictly
  increasing potential; see the module's complete case proof. Because the readings leave VRC's
  bag and DA's `C` unconstrained, those two empty families are treated as source instances and
  discharged rather than dropped: the ladder generators and `ladder.audit` require nonempty
  sub-populations, which only ever drops instances and is therefore unsound for a
  model-existence claim. All level-parameter checks are size-uniform; the separately audited
  bounded instance/closure scan is only a diagnostic
  (`research/results/p21_least_preorder.json`). This is a consistency model for **one finite
  ladder**, not for unrestricted welfare levels or either singly weakened set. The
  source-general Q-011 question remains open.
- **Settles it:** an exact model over the source's unrestricted welfare-level domain for a
  weakened set, or a contradiction for every valid source witness. P21 settles only the
  both-weakened variant on one finite ladder. On `W_-1…W_6`, no translation-invariant
  additive or lexicographic-linear order supplies that model; the least-preorder construction
  uses the reachability relation rather than such a score.

## Q-012. Is the bounce theorem known?

- **Status:** closed by collision P13 in `corpus/literature.toml`: partial. Under full
  comparability it is thesis Theorem 1 plus Appendix B (pp. 205–206). The completeness-free
  bounce appears in none of the 28 works read firsthand or in part (Arrhenius 1999–2025, Thomas 2016 and 2018,
  Thornley, Baker, Nebel and others). The corollary needs Weak Quality Addition in Thornley's
  repaired form, because Arrhenius's Restricted Quality Addition derivation has an error (Thomas
  2018 fn. 4). Still unread: the forthcoming book, Arrhenius 2016, Jensen 2008/2020, Handfield &
  Rabinowicz 2018, and Arrhenius & Rabinowicz 2005.
- **Claim:** Egalitarian Dominance, Quantity and Restricted Quality Addition are jointly
  inconsistent. It suffices that some n lives at one level are at least as good as every
  population of at least m lives in R(1, y). Corollary: Egalitarian Dominance, GNEP, Quantity and
  2009 Weak Quality Addition are inconsistent.
- **Why it might be known:** the proof is short. Arrhenius introduced Restricted Quality Addition
  himself (2009 Lemma 3), and Theorem 1 uses the same chain.
- **Settles it:** check Arrhenius 2011 (Lemmas 1.1–1.4), the book manuscript, Thomas
  (reconstruction), and later Arrhenius papers for a size-restricted form of Theorem 1.

## Q-013. Do the Dominance Addition gaps close on an unbounded ladder?

- **Status:** closed by the unconditional P16 cycle in `research/p16_ne_top.py`. The five
  W_-2…W_7 top-GNEP-witness gaps are inconsistent even on that finite ladder; the conditional
  headroom construction in `research/p15_dominance_addition.py` is not needed.
- **Claim:** Egalitarian Dominance, GNEP, repaired 2009 Weak Quality Addition, Inequality
  Aversion and thesis Dominance Addition are inconsistent for every valid fixed witness on a
  consecutive ladder. The 2003 Dominance Addition form implies the thesis form. The thesis
  and 2003 Non-Elitism variants supply the needed Inequality Aversion instances; P16 also
  audits direct Non-Elitism paths. No completeness or level above the GNEP high witness is
  required.
- **Cycle:** let h = max(5, GNEP.u, WQA.u), q < 0, and g, a, m be the GNEP high, WQA high
  and WQA negative counts. Put H = gm(2−q), T = a+H. Choose IA witness M1 > T,
  K = T+M1, IA witness M2 > K, Q = K+M2 and b = a+M2−m > 0.
  Egalitarian Dominance gives 4^K ≻ 3^K. IA gives 3^K ⪰ h^T ∪ 2^M1. WQA over
  h^H ∪ 2^M1 gives h^H ∪ 2^(M1+b) ∪ q^m. Exactly m(2−q) GNEP steps spend H
  high lives to raise q^m to level 2, yielding 2^Q. IA gives
  2^Q ⪰ h^K ∪ 1^M2. Thus 4^K ≻ h^K ∪ 1^M2, directly contradicting thesis
  Dominance Addition's not-better clause. The 2003 form supplies the reverse weak edge.
- **Scope:** WQA's fixed witnesses and arbitrary background are the repaired uniform
  reading, stronger than the published background-first quantifier order. The literature
  collision is partial, not a claim that the exact theorem is printed in a checked source.
  The three VRC-avoidance gaps remain Q-011.

