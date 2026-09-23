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
- **Settles it:** a source-justified gap axiom. Thesis §10.2 (pp. 153–157) replaces the
  categories with ranges R(u,v) and R(1,y), u > y, and is the first place to look.

## Q-005. MNEP wording: n or n+1 very-low lives

- **Status:** open; resolve in the schema v1 reading of MNEP.
- **Question:** the paraphrase in `corpus/sources.toml` (source_wording, 2000) and
  `SOURCE_CLAUSES["mnep"]` in `research/schema.py` say one slightly negative life is offset
  "against the same number of very-low-positive lives". The generator in `research/schema.py`
  pits n very-high lives plus one slightly negative life against n+1 very-low lives, which
  matches the 1999 wording (n+1). The human-reviewed 2000 witness also uses n+1 (q = 2 against 3
  lives at level 4).
- **Settles it:** the verbatim formal MNEP on p. 261 of the 2000 paper. If it says n+1, the
  paraphrases are wrong and the code is right.

## Q-006. The cycle/fork hypothesis

- **Status:** open.
- **Claim:** under completeness every principle shape is a difference constraint over ranks (W,
  S, or the disjunction I), so a skeleton's unsatisfiability depends only on its shape
  hypergraph. Minimal cores are then simple cycles with at least one strict edge (no I edge) or
  forced-comparability forks (with I edges).
- **Settles it:** exhaustive enumeration of minimal UNSAT shape hypergraphs up to a bound in the
  motif census.
