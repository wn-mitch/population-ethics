# Formalization decisions

Settled and open choices about how the sources are formalized. Each entry has a status
(settled or open), the sources it rests on, and what depends on it. A decision is changed by
adding a new entry that supersedes the old one; the old entry stays, marked superseded.

Sources are backticked `corpus/literature.toml` work ids or repository paths. A test checks that
every one resolves.

## D-001. Result labels and formalization tiers

- **Status:** settled.
- **Sources:** `docs/journal/2026-09-22-turn-1.md`.
- **Decision:** every result carries a scope label (finite computational result, bounded
  conjecture, unrestricted conjecture, checked theorem) and a formalization tier (frozen
  source-reviewed witness, source-constrained fixed-skeleton generalization, rational-cardinal
  spacing sensitivity, logical mutation, unreviewed schema generalization).
- **Consequences:** the ledger has since used tiers outside this list (solver-discovered proof
  skeleton, frozen agent-read witness, role correspondence). New tiers are allowed but must be
  named in the ledger row.

## D-002. Literature verdicts override solver-side novelty

- **Status:** settled.
- **Sources:** `corpus/literature.toml`, `research/render_ledger.py`.
- **Decision:** ledger rows default to `novelty_status = candidate-new-result`. A
  `[[collisions]]` entry lists the ledger rows it covers in `ledger`, and its verdict replaces
  the novelty column in `docs/results.md`.

## D-003. The frozen 2000 witness

- **Status:** settled.
- **Sources:** `arrhenius-2000-ep`, `corpus/sources.toml`.
- **Decision:** `arrhenius-2000.selected-witness/v1` (problem `eef25016…`) is the
  human-source-reviewed finite instance: grid {−1, 1, 2, 3, 4, 8}, very high 8, p=1, q=2, m=19.
  Turn-1 results are about its seven active relata A, AB, AC, AAE, AAF, D, G unless stated
  otherwise. The Phase 1 restriction lemma carries them to all 12 names.

## D-004. Category membership is declared, not derived

- **Status:** settled for v0; revisited by Q-004.
- **Sources:** `arrhenius-2000-ep`, `research/p6_schema.py`.
- **Decision:** grids declare which levels are very high, very low and slightly negative. The
  integers carry order, averages and category membership only. The v0 grids are baseline
  {−1,1,2,3,4,8}, relaxed {−1,1,5,6,7,8} and gapped {−1,1,5,6,7,14}.
- **Consequences:** order-only categories admit the R5 triangle; the source's implicit gap
  between very high and very low is not encoded.

## D-005. Schema v0 instantiation and witness

- **Status:** settled for v0; superseded when schema v1 lands.
- **Sources:** `research/schema.py`, `docs/journal/2026-09-22-turn-1.md`.
- **Decision:** universal principles are instantiated over D_N, the nonempty multisets of at most
  N lives over the grid levels. Existentials are fixed by W: the Repugnance witness is one life
  at the top very-high level, and MNEP uses n = q. UNSAT over D_N refutes "v0 + W" only.
- **Consequences:** v0 is unreviewed. No v0 result is a claim about Arrhenius's unrestricted
  theorem.

## D-006. R6 Addition reading

- **Status:** settled.
- **Sources:** `arrhenius-2000-ep` (p. 261).
- **Decision:** formal Addition requires a_i > b_j > c_h and m > n, with no positivity condition
  on the lower group, so it may contain the slightly negative life.
  `research/schema.py` implements exactly these three conditions.

## D-007. MNEP backgrounds

- **Status:** settled.
- **Sources:** `arrhenius-2000-ep` (p. 261).
- **Decision:** formal MNEP appends the same background D_k, k ≥ 0, to both sides, so MNEP
  instances range over every background, including the empty one.

## D-008. The 1999 witness

- **Status:** settled; agent-read, not human-reviewed.
- **Sources:** `arrhenius-1999-weak-ordering`, `corpus/sources.toml`, `research/p7_arrhenius1999.py`.
- **Decision:** `arrhenius-1999.selected-witness/v1` fixes p = q = 1, r = 5 on the gapped grid,
  with very-low levels 1 < 5 < 7, very high 14 and slightly negative −1. Its five principles
  exist only as frozen instances with a dedicated audit, not as generators.

## D-009. Role correspondences

- **Status:** settled as a project judgment.
- **Sources:** `research/known.py`, `arrhenius-1999-weak-ordering`, `arrhenius-2000-ep`.
- **Decision:** principles from different papers share a role when they occupy the same place
  in a proof: Non-Anti-Egalitarianism and Minimal Inequality Aversion are
  `inequality-aversion`; Non-Repugnance is `quality` (Quality Addition on an empty background).
  Shapes are normalized for the complete branch, where ¬(X ≻ Y) is Y ⪰ X.
- **Consequences:** a known-ground match says two proofs have the same dependency shape, not
  that their conditions are equivalent. Matches are meaningful only for complete-branch cores.

## D-010. Principle readings pass a review-first gate

- **Status:** settled.
- **Sources:** project decision.
- **Decision:** no principle enters instance generation or the known-ground catalogue until it
  has a reading in `corpus/readings.toml` with a verbatim source excerpt and page, written by
  one agent and independently confirmed by a second agent that reads the source cold
  (`agent-cross-read`). The user may upgrade a reading to `human-reviewed`. Disagreement blocks
  the reading until a decision entry resolves it.
- **Consequences:** v0 principles and the five 1999 principles must be re-read under the gate
  before schema v1 replaces v0.

## D-011. Edge realizations are recorded data

- **Status:** settled.
- **Sources:** project decision.
- **Decision:** a judgment that a lemma chain realizes an abstract edge (for example, 2009
  Lemma 3 realizing Restricted Quality Addition) is recorded once, with source and reason, and
  verified by test for entailment and realizability. It is never re-judged per session.

## D-012. MNEP adds n very-high lives and one slightly negative life against n+1 very-low lives

- **Status:** settled.
- **Sources:** `arrhenius-2000-ep` (p. 261), `arrhenius-1999-weak-ordering` (p. 16),
  `corpus/readings.toml`.
- **Decision:** both formal statements compare A_n ∪ B_1 ∪ D_k with C_{n+1} ∪ D_k. The
  informal "the same number of people" means the n+1 added lives on each side. The generator in
  `research/schema.py` already encodes n+1; the paraphrases in `corpus/sources.toml` and
  `SOURCE_CLAUSES` were ambiguous, not the code. Closes Q-005.

## D-013. The v0 and 1999 encodings match their formal statements

- **Status:** settled; agent-cross-read.
- **Sources:** `corpus/readings.toml`.
- **Decision:** every v0 principle and every 1999 principle matches its cross-read formal
  statement. The encodings deviate in two ways. They drop instances where the source is
  silent (empty populations, an empty Addition base), which only weakens the encoded theory.
  They fix each existential by the witness W, which strengthens it, so an UNSAT result still
  refutes "source conditions + W" only (D-005). Each reading's `deviations` field records the
  specifics.
- **Consequences:** supersedes D-005's "v0 is unreviewed"; the v0 principles are now
  agent-cross-read.

## D-014. Thesis-family conditions are ordinal over a ladder of consecutive levels

- **Status:** settled.
- **Sources:** `arrhenius-2000-thesis` (pp. 152–157), `arrhenius-2003-vrc` (pp. 169–172),
  `arrhenius-2009-one-more` (pp. 25–30).
- **Decision:** from the thesis on, the formal conditions refer to indexed consecutive levels
  (W_{x−1}, W_{z+1}, W_3) and to ranges R(x, y) of at least three consecutive levels; "very
  high" and "very low" are replaced by non-fixed ranges R(u, v) above R(1, y), and no condition
  uses averages. Schema v1 therefore represents a grid for these principles as a finite ladder
  of consecutive levels W_{−a} … W_{−1}, W_1 … W_b, and only its index order matters. The 1999
  and 2000 conditions keep numeric levels because Non-Anti-Egalitarianism compares averages.
- **Consequences:** a thesis-family instance needs enough consecutive positive levels for
  R(1, y) and R(u, v) to hold at least three levels each, so b ≥ 6. The single very-high level
  of the gapped grid does not form a range (see Q-004).

## D-015. Known-ground coverage counts only substantial embeddings

- **Status:** settled.
- **Sources:** `research/known.py`.
- **Decision:** a catalogued skeleton's maximum embedding covers core instances only when it
  maps at least 3 edges and a strict majority of the skeleton's edges. Two-edge fragments of
  the 4- and 5-edge thesis and 2003 skeletons embed into R6 by role alone and would have
  "covered" its two new steps; with this rule R6 keeps exactly those two uncovered instances.
- **Consequences:** `uncovered_by_published` no longer shrinks just because the catalogue grows.
  Coverage by a small fragment is still visible in `per_known`.

## D-016. The ladder includes the neutral level W_0

- **Status:** settled; supersedes D-014's "W_−a … W_−1, W_1 … W_b".
- **Sources:** `arrhenius-2000-thesis` (pp. 152–155).
- **Decision:** the thesis indexes W_0 as the neutral level and assumes a possible population of
  n people at every welfare level, so lives at W_0 exist. `research/ladder.py` includes W_0 by
  default. Without it, GNEP (which moves one life up one level) cannot step from W_−1 to W_1, and
  Condition δ is underivable from GNEP on any ladder.

## D-017. Realizations contract principle paths, not role paths

- **Status:** settled.
- **Sources:** `research/realizations.toml`, `research/canon.py`.
- **Decision:** a realization maps a series path of specific principles to the derived
  principle its source lemma proves (a run of Non-Elitism steps to Condition β, a run of GNEP
  steps to δ, Weak Quality Addition plus δ to Restricted Quality Addition). Role-level rules
  would be wrong: "priority then quality" occurs inside the 1999 cycle itself, and contracting it
  would merge the 1999 skeleton with a 4-cycle. Only paths whose internal relata touch no other
  edge are contracted, and every distinct full contraction is reported (L2).
- **Consequences:** L2 recognizes only recorded realizations. Each realization carries a
  solver-found example chain that a test re-verifies (audit, and entailment in every preorder).
  The 2000 derivation of the 1999 Quality Addition edge uses Addition's fork and completeness,
  so it is not a path and is not yet a realization.

## D-018. Consistency evidence comes only from exact model checks

- **Status:** settled.
- **Sources:** `research/additive.py`, `research/lexadd.py`, `research/possibility.py`.
- **Decision:** a condition set counts as realized only when an axiology satisfies it for every
  population size. Two classes are decided exactly: additive axiologies (quantifiers over sizes
  eliminated in closed form, every g), and lexicographic-additive axiologies (per axiology, with
  counterexamples of any size searched by z3; only outer existential witnesses are grid-bounded).
  Bounded model checking over a finite universe is not used as consistency evidence. Existential
  witnesses let a condition's hard instances fall outside any finite universe, and in practice it
  reported total utilitarianism as avoiding the Very Repugnant Conclusion.
- **Consequences:** the lexicographic-additive class cancels backgrounds, so it cannot separate
  background-sensitive conditions (Weak Quality Addition, GNEP) from their background-free
  counterparts. Gaps involving that difference stay open (Q-010) until a background-sensitive
  class is checked exactly.
