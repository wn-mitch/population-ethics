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

- **Status:** open (8 of 58 sets).
- **Setup (P11-possibility-map):** the additive class is decided exactly, and 57
  lexicographic-additive axiologies are checked exactly (D-021). 58 minimal condition sets are
  realized by none of them. 32 are explained by a known or project theorem via the recorded
  implications; 26 are not. Every unexplained set has 4 or 5 conditions.
- **Certificates (P12-gap-certificates, D-019):** 18 of the 26 are proved consistent. Two
  mechanisms cover them. (1) The background-free quality condition (Quality or VRC avoidance)
  is inert and total utilitarianism covers the rest, so the backgrounds in Weak Quality Addition
  are load-bearing in thesis Theorems 3 and 4 and the 2009 theorem. (2) With NEP rather than
  GNEP, a first tier that makes only W_−2 lexically bad separates NEP's single negative life at
  W_−1, which high lives outweigh, from Weak Quality Addition's negatives at W_−2, which nothing
  outweighs. That closes {Egalitarian Dominance, NEP, Quantity, 2009 Weak Quality Addition} and
  the NEP variants of the Dominance Addition and Non-Sadism gaps. GNEP defeats (2): it trades
  one level at every level, so no level can be lexically bad.
- **Project theorems explain six former gaps:**
  - P13-bounce-theorem: {Egalitarian Dominance, GNEP, Quantity, 2009 Weak Quality Addition}
    (research/p13_bounce.py).
  - P14-gnep-theorem-3: thesis Theorem 3 with GNEP for NEP, with Weak Non-Sadism or Non-Sadism
    and either form of Weak Quality Addition (research/p14_gnep_theorem_3.py). GNEP raises each
    negative life to W_3 one level at a time, and Inequality Aversion supplies enough lives to
    absorb any witness. The bounded census missed it because the cycle needs more than 6 lives.
- **Still open: 8.** Each contains GNEP, Egalitarian Dominance and a Dominance Addition form.
  - Five also contain 2009 Weak Quality Addition and Inequality Aversion or a Non-Elitism form.
    They have a proof that needs one level above W_h = max(Weak Quality Addition's very high
    level, GNEP's W_u) (Q-013). On W_−2 … W_7 a witness with W_u at the top escapes that proof.
  - Three contain VRC avoidance and a Non-Elitism form (Q-011). VRC avoidance has no
    background, so the Q-013 construction does not apply.
- **Settles it:** for each of the 8, a certificate from a background-sensitive or
  count-sensitive model class, or a proof that works when W_u is the top level.

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

- **Status:** open; this is where the possibility map becomes ladder-relative.
- **Claim:** {Egalitarian Dominance, GNEP, 2009 Weak Quality Addition, Inequality Aversion, a
  Dominance Addition form} is inconsistent whenever W_{h+1} exists, where W_h = max(Weak
  Quality Addition's very high level, GNEP's W_u). Non-Elitism implies Inequality Aversion
  (thesis Lemma 5.1), so the claim covers the five Q-010 gaps with 2009 Weak Quality Addition.
- **Construction (written, not yet mechanized):** let T be a + |H| lives at W_h, with |H| =
  n_G·m_W·(3 − q) for Weak Quality Addition's m_W lives at W_q.
  1. Weak Quality Addition, background H: T ⪰ H ∪ C ∪ (m_W at W_q), with C at W_3.
  2. GNEP raises each negative life to W_3, spending H.
  3. The result is K lives at W_3, which Egalitarian Dominance makes ≻ K lives at W_2.
  4. Inequality Aversion: K at W_2 ⪰ |T| at W_{h+1} ∪ M at W_1.
  5. Dominance Addition: that is ⪰ T (in the 2003 form; the thesis not-worse form forbids
     T ≻ it).

  |C| = a + M − m_W > 2a absorbs any Inequality Aversion witness. Completeness is not used.
- **Why the ladder matters:** step 4 needs a level above W_h. On a finite ladder the witness may
  put GNEP's W_u at the top level. Then GNEP's high lives sit only at the top, only Inequality
  Aversion can create lives there, and its M > N lowered lives cannot all be raised again.
  If the gaps are consistent at W_u = top, the finite-ladder classification differs from the
  unbounded one.
- **Settles it:** mechanize the construction (as in `p14_gnep_theorem_3.cycle`) with a
  headroom precondition. Then either certify the gaps on W_−2 … W_7 at W_u = W_7, or prove them
  without headroom.

