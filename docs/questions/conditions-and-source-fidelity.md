# Conditions and source fidelity

Detailed entries of the [open-questions register](../questions.md). Each entry keeps its
original heading, status, citations and cross-references verbatim, and carries an explicit
`q-nnn` anchor so the index and other pages can link straight to it. The index
([docs/questions.md](../questions.md)) lists every entry's heading.

<a id="q-001"></a>

## Q-001. U1: avoidance comparability replaces completeness

- **Status:** open.
- **Claim:** the 2000 theorem stays valid with completeness replaced by "avoidance
  comparability": whenever an avoidance condition says X is not better than Y, X and Y are
  comparable. Addition may also be in "not better" form.
- **Known:** the propositional part is checked, and witnesses exist for every (p, q).
- **Settles it:** a source-grounded review of the v0 applicability clauses for all (p, q), then a
  literature check. R3 records shared positive comparison directions but not an exact
  published M1, M2 or C1 mutation.
---

<a id="q-002"></a>

## Q-002. U2: same-number completeness is consistent

- **Status:** open.
- **Claim:** Arrhenius's 2000 conditions are jointly consistent with same-number completeness
  plus transitivity.
- **Known:** bounded search only. Critical-Band Utilitarianism is reported to avoid the
  Repugnant and Sadistic Conclusions; a literature agent derived, but did not find stated, that it
  satisfies all five 2000 conditions.
- **Settles it:** a uniform model checked against the conditions, or a firsthand check of
  Blackorby, Bossert & Donaldson (1996, 1997) that Critical-Band Utilitarianism satisfies them.
---

<a id="q-004"></a>

## Q-004. How far apart must very high and very low be?

- **Status:** open.
- **Question:** the 2000 paper declares the categories and requires four ordered very-low levels
  but sets no minimum gap between very low and very high. Is 7 a fair very-low level when 14 is
  very high (the gapped grid, R6)? Order-only categories admit the R5 triangle.
- **Settles it:** a source-justified gap axiom. The thesis replaces the categories with ranges
  R(u,v) above R(1,y), each at least three consecutive levels (D-014). That settles the gap for
  the thesis family; the 1999 and 2000 statements still set none.
---

<a id="q-005"></a>

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
---

<a id="q-014"></a>

## Q-014. How do the source clauses treat off-chain welfare levels?

- **Status:** open source-fidelity question (P24-off-chain-fidelity-probes).
- **Inserted-level probe:** a new level strictly between indexed W_4 and W_5
  contradicts the reviewed definition that adjacent indexed levels are
  consecutive if their names remain fixed. Reindexing would change NE/GNEP
  successor instances and P21's chosen threshold `u=5`. The source does
  not fix how to reindex an added level; no primitive closure was inferred.
- **Incomparable-level probe:** the life quasi-order allows levels outside
  the selected W_i chain. Exact indexed ranges exclude a life at a level
  incomparable with every W_i, but unrestricted GNEP backgrounds can
  include it. The reviewed text leaves the indexing of other levels
  unstated, as well as how the informal welfare-comparison clauses apply
  to mixed off-chain populations. Neither a numerical index nor a
  comparability rule was invented to force a verdict.
- **Settles it:** an independent primary-source reading that determines
  indexing and the universal quantifiers for the additional level, then
  an audited full mixed-profile source instance generator and closure
  proof or counterexample. P21/P23 prove indexed-chain existence only.
