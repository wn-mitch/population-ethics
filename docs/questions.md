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

- **Status:** open.
- **Setup (P11-possibility-map):** the additive class is decided exactly, and 38
  lexicographic-additive axiologies are checked exactly. 90 minimal condition sets are realized by
  none of them. Twenty-seven are explained by a known theorem via the recorded implications; 63
  are not. Every unexplained set has 4 or 5 conditions.
- **The leading gaps:**
  - Theorem 3 with Quality or VRC avoidance in place of Weak Quality Addition.
  - Theorem 4 with Quality in place of Weak Quality Addition.
  - The 2003 theorem with NEP or Inequality Aversion in place of GNEP or Non-Elitism.
  - The 4-set {Egalitarian Dominance, NEP or GNEP, Quantity, VRC avoidance}.

  The census finds no strict cycle for the first and last of these under the Phase 8 witness at
  ≤ 6 lives.
- **Reading so far:** most gaps trade a background-sensitive condition for one the
  lexicographic-additive class cannot distinguish from it. For the 4-set: Quantity with
  Egalitarian Dominance makes high lives worth finitely many low lives, VRC avoidance makes a few
  negative lives outweigh any number of low lives, and NEP lets finitely many high lives offset a
  negative. A contradiction would need to move negatives between levels inside a background,
  which none of the four conditions provides.
- **Certificates (P12-gap-certificates, D-019):** 34 of the 63 gaps are proved consistent. Each
  certificate makes the background-free quality condition (Quality or VRC avoidance) inert and
  covers the rest with total utilitarianism. So the backgrounds in Weak Quality Addition are
  load-bearing in thesis Theorems 3 and 4 and the 2009 theorem. That includes the 4-set
  {Egalitarian Dominance, NEP or GNEP, Quantity, VRC avoidance} and Theorem 3 with Quality.
- **Still open: 29.** Twenty-six contain a background-carrying quality condition (5 thesis Weak
  Quality Addition, 21 2009 Weak Quality Addition), so a certificate needs a background-sensitive
  axiology. The other three are Q-011.
- **Why they resist (D-020):** a certificate's axiology must be background-sensitive, because
  every lexicographic-additive tier cancels backgrounds. Worked case: {Egalitarian Dominance,
  GNEP, Quantity, 2009 Weak Quality Addition}. GNEP yields δ (2009 Lemma 2), and δ with Weak
  Quality Addition yields Restricted Quality Addition (2009 Lemma 3). That looks as if it should
  drive Theorem 1's Quantity chain, but Restricted Quality Addition covers only low populations of
  at least m lives, with m chosen by the axiology. The Quantity chain ends near n plus the number
  of levels, so a large m escapes. A model would need to disregard small low populations.
- **Settles it:** an exact check of a background-sensitive axiology class that realizes a gap, or
  a proof. Each proof would be a new impossibility theorem strictly stronger than a known one.

## Q-011. Is the 2003 theorem stronger than stated?

- **Status:** open; the most concrete candidates for strengthening a known theorem.
- **Candidates:** the 2003 conditions {Egalitarian Dominance, Non-Elitism, GNEP, VRC avoidance,
  Dominance Addition}, with Dominance Addition weakened to the thesis's not-worse form, or
  Non-Elitism weakened to its ranged background, or both. No checked axiology realizes any of
  them, no certificate exists at the level witnesses tried, and no known theorem explains them.
- **What the proof would need:** the 2003 proof uses Condition β with a negative background (D₂).
  Ranged Non-Elitism only yields β with a background in R(z, y+1), which excludes negatives. The
  proof also chains Dominance Addition's ⪰. The not-worse form gives that only under
  completeness, which is how the census and certifier read it.
- **Evidence so far (lemma level, derived β and δ, ≤ 6 lives, δ's n growing by 5 per negative
  life):**
  - The control holds: the 2003 conditions reproduce their source word.
  - With ranged β (the 2009 Lemma 1 form that ranged Non-Elitism yields) there are no cycles at
    all.
  - With not-worse Dominance Addition, no cycle uses Dominance Addition. The only cycles are
    Q-009 exchange-rate cycles over β, δ and Egalitarian Dominance, and those are witness
    artifacts: total utilitarianism satisfies Egalitarian Dominance, Non-Elitism and GNEP
    together once δ's base n is at least 4 on this ladder.

  Both weakenings therefore look consistent, not like stronger versions of the 2003 theorem.
- **Settles it:** a background-sensitive or lexicographic model certified with the certifier's
  method, which would close them; or a cycle under every witness family.
