# Gaps and precedence

Detailed entries of the [open-questions register](../questions.md). Each entry keeps its
original heading, status, citations and cross-references verbatim, and carries an explicit
`q-nnn` anchor so the index and other pages can link straight to it. The index
([docs/questions.md](../questions.md)) lists every entry's heading.

<a id="q-010"></a>

## Q-010. Gaps in the possibility map

- **Status:** one VRC-avoidance gap remains open: unrestricted 2003 Non-Elitism
  with thesis not-worse Dominance Addition (Q-011). P21 and P23 realize the
  both-weakened and ranged-NE sets, respectively.
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
- **Still open: 1.** The unrestricted-NE plus thesis not-worse-DA set has ED,
  GNEP and VRC avoidance. P21 realizes both thesis weakenings on the full
  integer chain; P23 realizes ranged NE plus positive 2003 DA on a chain
  bounded below at W_-1. P23 refutes the remaining set at a chosen legal
  witness but not at every legal witness. VRC avoidance has no arbitrary
  background, so P16's Weak Quality Addition construction does not apply.
- **Settles it:** a full-domain model at another legal witness, or audited
  contradictions for every valid top-level witness.
---

<a id="q-012"></a>

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
---

<a id="q-013"></a>

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
  The remaining singly weakened VRC-avoidance gaps are tracked under Q-011.
