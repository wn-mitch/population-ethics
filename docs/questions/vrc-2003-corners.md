# VRC and the 2003 corners

Detailed entries of the [open-questions register](../questions.md). Each entry keeps its
original heading, status, citations and cross-references verbatim, and carries an explicit
`q-nnn` anchor so the index and other pages can link straight to it. The index
([docs/questions.md](../questions.md)) lists every entry's heading.

<a id="q-011"></a>

## Q-011. Is the 2003 theorem stronger than stated?

- **Status:** the original 2003 conjunction is impossible. Unrestricted
  2003 NE with thesis not-worse DA is also impossible at every legal
  existential witness on the reviewed indexed chains (P26); this is
  source-known, not a new priority claim. Ranged NE with positive 2003 DA
  has an all-size model on the full integer chain (P27), as does the
  both-weakened set (P21). Off-chain source fidelity remains open (Q-014).
- **Candidates:** the 2003 conditions {Egalitarian Dominance, Non-Elitism,
  GNEP, VRC avoidance, Dominance Addition}, weakening Non-Elitism to a
  ranged background, Dominance Addition to thesis not-worse, or both.
  The original set is impossible by the published 2003 theorem. Consistency
  needs only one legal witness and a model of every instance on its domain;
  impossibility needs a contradiction for every legal existential witness.
- **Earlier proof boundary:** the published 2003 proof uses Condition β with a negative
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
  - *Verdict at phase 20.* No source-general primitive cycle or model had been established
    for any weakened set. At that phase's fixed witnesses and model families no exact
    all-size model was found. P21 below supplies a both-weakened model on a single
    unbounded chain; it does not generalize to every possible welfare quasi-order.
    The original five-condition impossibility remains the published 2003 theorem.
    The source comparison and result scopes are in `corpus/literature.toml` and
    `research/results/p20_vrc_dual_routes.json`.
- **All-size integer-chain model (P21-integer-chain-both-weakened,
  `research/p21_least_preorder.py`, D-023):** the welfare universe is exactly
  `{W_i : i ∈ Z}`, and the populations have every finite multiset of its levels,
  including `∅`. The relation pulls back from level multisets to distinct finite
  sets of lives, treating equal welfare profiles as indifferent. Take the
  reflexive/transitive closure of the primitive ED, thesis
  ranged NE, 2003 GNEP and 2003 VRC weak edges; leave `∅` isolated. Witnesses are
  NE `n=1`, GNEP `(u,y,n)=(5,3,1)`, VRC `(x,u,v,y,n,m)=(-1,4,6,3,1,1)`.
  Thesis DA is an N-shaped condition checked on this closure, **not** a reverse
  weak edge. Define `F(0)=0`, `F(t+1)−F(t)=g(t)=1+1/(1+2^t)` for every integer `t`,
  and the exact potential `Σ F(t)`. Since `1<g(t)<2`, `g` strictly decreases and
  `g(3)+g(4)>2`, every cardinality-preserving primitive edge decreases this
  potential strictly; only reflexive steps preserve it. In
  particular ED cannot reverse. VRC with a nonempty bag is the only
  cardinality-increasing primitive edge; its targets satisfy
  `I(P)=#{t≤0}−#{t≥5}≥1`, and all further edges preserve that invariant.
  A larger DA target cannot be reached from a nonsingleton, while the only
  singleton source that can grow has level at least 4; every corresponding
  DA target has invariant at most −1 and every reachable grown profile has
  invariant at least 1. DA with an empty added bag is same-size and excluded
  by the potential; `A=B=∅` is reflexive. VRC with an empty low bag is
  discharged by ED, without changing size.
  The independent `research/p21_machine_check.py` discharges the universal
  gain, invariant and DA-target inequalities with exact SMT and checks the
  finite-sum and abstract path inductions with Spacer CHCs. Its source-to-edge
  translation is still a reviewed reading, tested on an extended finite
  window only as a diagnostic.
  The proof uses the written source quantifiers: NE has a ranged background, GNEP
  an arbitrary one, and ED, DA and VRC have no additional universally quantified
  common background. It does not prove a separability-strengthened variant.
  This is one source-permitted unbounded welfare structure, **not** a
  construction on every richer quasi-order with additional off-chain
  levels. P23 below establishes the ranged-NE model separately; P26
  settles the not-worse-DA-only set by contradiction.
- **Finite-ladder specialization (P21-least-preorder-both-weakened):** on
  `W_-1…W_6` the same primitive closure has the exact potential
  `Σ(20t−t²)` and the same invariant; it covers all nonempty population
  sizes plus `∅`. This score does **not** extend to the full integer
  chain. The original source-level generators omit the empty low bag,
  empty added bag, and `∅`, so the separate source-instance checks are
  required; a bounded generator's success alone does not prove either model.
- **Witness and literature boundary:** the named phase-17, phase-18 and
  phase-20 contextual witnesses have GNEP high floor `u=4`; at that
  witness, thesis NE and GNEP admit the weak cycle
  `(2,4) ⪰ (3,3) ⪰ (2,4)`. P20's other direct-route UNSAT chains
  use different VRC ranges and are not defeated just by changing that
  floor. With weak DA and unrestricted-background NE, the 2016
  reconstruction derives `¬(high ⪰ negative+positive)`, directly
  contradicting the 2003 VRC-avoidance comparison at matching relata.
  P26 settles that DA-only indexed-chain corner. P21 uses ranged NE,
  so this unrestricted-background derivation does not refute its
  both-weakened model. The source and premise comparison is certified
  in `corpus/literature.toml`; unchecked texts leave P21's priority open.
- **P23 singly weakened square (`research/p23_vrc_corners.py`):** with
  ranged thesis NE and positive 2003 DA, the least closure of all five
  primitive W/S edge families is a partial order on every finite profile
  over W_-1..W_k (k ≥ 6), including the one-sided chain unbounded above.
  Use P21's integer potential for size-preserving edges and
  `Ψ(P)=#{negative lives}−#{lives at W_5 or above}` after VRC. Every VRC
  target has Ψ=1. Ranged NE cannot decrease Ψ while a negative life is
  present: its shared background must then contain W_-1 and force y=-1.
  GNEP cannot decrease Ψ in that state either. Each 2003 DA source is
  nonnegative on a chain beginning at W_-1, so no DA edge follows VRC.
  Only nonempty-bag VRC increases size, only nonempty-addition DA decreases
  it, and all same-size edges strictly lower the integer potential. This
  excludes every nontrivial cycle, for arbitrary finite population sizes
  and finite path lengths. Source-legal VRC with B empty and DA with C
  empty descend in the potential; DA with A=B=empty sends positive C to
  the empty sink. The module checks the unbounded NE/GNEP Ψ inequalities
  with SMT; finite scans and instance audits are diagnostics.
- **P23 not-worse-DA probe:** with unrestricted 2003 NE at P21's witness,
  a legal background W_-1 outside thesis NE's range takes
  (-1,4,4) ⪰ (-1,1,5) and lowers P21's invariant from 1 to 0.
  An independent audited primitive chain reaches the same legal thesis-DA
  target (6,1⁷) from both (4,) and (5,). The N-shaped DA clause plus
  transitivity forces (4,) ⪰ (5,), contradicting ED's (5,) ≻ (4,);
  the induced fixed-witness theory is UNSAT without completeness.
  This refutes only this legal witness, not every source witness. A bounded
  six-witness census includes surviving candidate witnesses and resolves
  nothing beyond its caps.
- **P25 repaired scanner and two-source frontier (`research/p25_q011_frontier.py`):**
  the P23 forward generator now respects GNEP's `n` high lives and all size-`n`
  low bags, and VRC's perfectly equal high source. Tiny exhaustive instances
  match the independent ladder generator and audit. Its regenerated cap-eight
  census has no singleton obstruction at `ne-n2`, `gnep-n2`, `vrc-m2` or
  `vrc-n2`; any prior invalid GNEP/VRC path is superseded. For every `r≥1`,
  two primitive paths from equal `W_a^r` and `W_a'^r` (`a<a'<b`) into one
  legal `W_b^r ∪ W_c^k` (`c>0`, `k≥1`) contradict ED and thesis not-worse
  DA without completeness. This conditional lemma does not construct paths
  at every witness. At caps eight and ten, the three surviving controls have
  no such target for `r=1` or, for `vrc-n2`, `r=2`; absence is bounded.
  The `ne-n2` least primitive closure is acyclic by a symbolic potential and
  finite-path induction, but P25 did not prove the all-size DA-return
  exclusion. P26 below constructs a legal target beyond the scanned caps
  and supersedes this candidate. The source-permitted empty clauses do not
  affect the contradiction because P26 uses only nonempty instances.
- **P26 source-general contradiction (`research/p26_q011_unrestricted.py`):**
  for arbitrary legal VRC `(x,u,v,y,n,m)`, NE's pair-dependent counts
  `n(j+1,1)` and GNEP's carrier-dependent triples at `z=x..0`, choose
  `b=max(u+2,max_z u_z)`, `M=∏_{j=3}^{b-1}(n(j+1,1)+1)`,
  `H=n+m Σ_{z=x}^0 n_z`, and a VRC low bag of `K=M H` lives at W_3.
  Both `W_u^n` and `W_{u+1}^n` reach `W_b^n ∪ W_1^(K+m-n)`:
  unrestricted NE lifts all W_3 lives to W_b while leaving only W_1
  drops, then GNEP raises every negative carrier to W_1 using
  `m Σ n_z` high lives. Thesis DA at `W_{u+1}^n` and strict ED
  contradict without completeness. All eight finite instantiations
  replay and audit their edges; the count identity is symbolic.
  The `ne-n2` target has 82 lives, beyond P25's caps. The 2016
  reconstruction, p. 10, already states the weak-DA conclusion
  `not(high ⪰ negative+positive)`, directly opposite VRC avoidance;
  the earlier P25 literature note reversed this comparison.
- **P27 full-integer ranged-NE model (`research/p27_ranged_ne_integer.py`):**
  at P23's fixed witness the least primitive preorder remains acyclic
  on every finite profile over all W_i (`i∈Z`). After any VRC edge,
  `N=#{negative lives}≥1` and `N−H≥1` for `H=#{lives at W_5 or above}`;
  all non-VRC edges preserve both inequalities, including ranged NE
  at negative levels and 2003 weak DA with a negative source.
  No later VRC source is reachable. Without VRC, cardinality cannot
  increase and every size-preserving edge lowers P21's full-chain
  potential `F`, whose adjacent gains are `1+1/(1+2^i)`.
  SMT checks the edge obligations and finite-path induction; bounded
  source audits are diagnostics. Empty VRC bags and DA additions are
  checked in a separate source-fidelity branch. This is one model,
  not a representation of every richer welfare quasi-order.
- **Indexed-domain corollary (P24-convex-chain-restriction):** restrict P21's
  *full-chain relation* to all finite profiles over any convex integer-indexed
  J containing W_-1..W_6, retaining the fixed legal witness. Every
  restricted source instance was already satisfied on Z. Reflexivity,
  transitivity and strict ED persist under restriction; the empty profile
  remains included. This covers arbitrarily long finite intervals, one-sided
  infinite intervals and the full chain, but not off-chain extensions.
  Restricting the relation is not the same as recomputing the primitive
  closure solely from J, since paths could leave J.
