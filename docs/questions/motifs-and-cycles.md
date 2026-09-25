# Motifs and cycles

Detailed entries of the [open-questions register](../questions.md). Each entry keeps its
original heading, status, citations and cross-references verbatim, and carries an explicit
`q-nnn` anchor so the index and other pages can link straight to it. The index
([docs/questions.md](../questions.md)) lists every entry's heading.

<a id="q-003"></a>

## Q-003. U3: the minimum escape isolates the Sadism/Anti-Egalitarianism meeting point

- **Status:** open; bounded conjecture.
- **Claim:** in every Arrhenius-type skeleton, the minimum escape isolates the population on
  which Non-Sadism and Non-Anti-Egalitarianism meet.
- **Known:** holds for AAF in the baseline skeleton (minimum 4, unique), (1⁵,14,14) in both
  R6-type skeletons (minimum 5; one also has an A-isolating minimum), and (1,8,8) in the
  4-instance relaxed skeleton (minimum 3).
- **Settles it:** escape numbers for every class in the motif census.
---

<a id="q-006"></a>

## Q-006. The cycle/fork hypothesis

- **Status:** closed by P9-l0-cycle-motif and P9-l0-fork-motif. Fork-free minimal cores are
  exactly simple strict cycles (a standard difference-constraint fact; enumeration to 6 edges
  matches the necklace counts). One-fork cores are the fork plus two strict paths converging on
  their middle argument (enumeration to 5 edges); P22 proves the one-fork implication at every
  finite length. Every thesis-family condition is fork-free, so all its minimal cores are cycles.
- **Claim:** under completeness every principle shape is a difference constraint over ranks (W,
  S, or the disjunction I), so a skeleton's unsatisfiability depends only on its shape
  hypergraph. Minimal cores are then simple cycles with at least one strict edge (no I edge) or
  forced-comparability forks (with I edges).
- **Settles it:** exhaustive enumeration of minimal UNSAT shape hypergraphs up to a bound in the
  motif census.
---

<a id="q-007"></a>

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
---

<a id="q-008"></a>

## Q-008. The fork motif in general

- **Status:** one-fork claim closed by P22-complete-shape-branch-cycles; multi-fork
  parameterized motif compression open.
- **Claim (proved for one fork):** every deletion-minimal rank-inconsistent hypergraph
  with exactly one Addition fork I(a,b,c) is that fork plus the union of two simple
  strict paths a ⇝ b and c ⇝ b. The paths may overlap (or coincide if a=c).
  Deleting the fork leaves a satisfiable W/S graph. Each of the two failing branches
  must use its added weak edge, so removing it leaves a strict path. Every other
  base edge must lie on the two paths, or deleting it would leave both branch
  contradictions intact. This proves the necessity checked by `is_fork_motif`;
  the path-union form by itself does not certify deletion minimality.
- **Multi-fork evidence:** the four-edge set I(3,1,2), I(0,3,2), S(0,1),
  W(2,0) is deletion-minimal UNSAT and contains no one-fork obstruction.
  The exact branch-cycle decision covers any finite number of forks, but no
  finite family of parameterized minimal motifs and converse is proved.
- **Settles the remainder:** a general parameterized motif-family theorem with
  both directions, or a counterexample to a proposed family. Finite lists of
  fixed-size forbidden graphs cannot suffice because simple strict cycles have
  unbounded length.
---

<a id="q-009"></a>

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
