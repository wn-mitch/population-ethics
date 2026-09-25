# Population ethics laboratory

A solver-backed lab for finite experiments and all-size certificates in population ethics. The library in `src/population_ethics/` checks instances, models, and proof evidence. The scripts in `research/` compare reviewed source readings with proof skeletons, countermodels, and known results. A passing solver check establishes a fact about its encoding; it does not by itself establish that the encoding matches its source.

## The P21 consistency model

The current all-size result concerns **two specific weakenings** of the conditions in Arrhenius's 2003 Very Repugnant Conclusion impossibility theorem, on one integer-indexed welfare chain rather than every possible welfare structure:

| Condition | Form used here |
| --- | --- |
| Egalitarian Dominance, General Non-Extreme Priority, VRC avoidance | 2003 exact formulations; strict ED implicitly requires a nonempty population |
| Non-Elitism | Thesis formulation, with the common background restricted to `R(y,x)` |
| Dominance Addition | Thesis's “not worse” consequent, `¬(A ≻ B∪C)`, not the 2003 weak-preference consequent |

Existential parameters are instantiated by a single uniform witness, even where the source permits them to depend on a level or level pair. This is stronger than the source's existential requirement, not a change to its universal clauses.

Take every integer-indexed welfare level `W_i` (`i ∈ ℤ`, including neutral `W_0`) and every finite population over those levels, including the empty population. Populations with the same multiset of welfare levels are treated as indifferent, even when they contain different people. At the fixed legal witnesses NE `n=1`, GNEP `(u,y,n)=(5,3,1)`, and VRC `(x,u,v,y,n,m)=(-1,4,6,3,1,1)`, form the reflexive–transitive closure of the ED, ranged-NE, GNEP, and VRC comparisons. Dominance Addition is an obligation checked against that closure, **not** an additional reverse edge.

The all-integer argument uses a potential `Φ(P)=Σ F(i)` with adjacent gains
`F(i+1)−F(i)=1+1/(1+2^i)`. These gains are strictly decreasing and lie between 1 and 2. They make every size-preserving primitive comparison descend in potential and prevent a reverse ED comparison. VRC is the only source of population growth, and it grows only from a singleton. Every such target has `I(P)=#{i≤0}−#{i≥5}≥1`; the other primitive comparisons preserve this bound. A larger Dominance Addition target cannot be reached from a nonsingleton, and the bound excludes the targets reachable after singleton growth. Empty added bags are ruled out by the potential; an empty VRC low bag is already covered by ED. The empty population is an isolated reflexive point.

This is a solver-checked **compositional certificate** over one unbounded, discrete welfare chain, not a proof assistant's verification of the source prose. [`research/p21_machine_check.py`](research/p21_machine_check.py) checks universal gain, NE/GNEP descent, invariant, and DA-target inequalities with exact SMT for arbitrary integer levels. Background bags are handled by composing per-level sign checks with a Spacer finite-sum induction. Another Spacer induction checks every finite path of an abstract transition system; its edge properties are assembled from the local checks and the monotonicity of `F`, but that assembly is not itself an SMT obligation. A bounded source-instance audit tests the source-to-edge translation; it cannot prove that translation correct. The result does **not** extend to arbitrary incomparable off-chain welfare levels, either singly weakened set, or the original 2003 five-condition set. The literal size-zero instance of strict ED would demand `∅ ≻ ∅`; the model follows the implicitly nonempty reading necessary for ED to be consistent at all. The source's VRC condition specifies `x<0`; the model fixes `x=-1`, and whether that level adequately captures “very negative” remains a source-fidelity question. The model follows the written source background quantifiers, not a stronger global separability principle. Independent publication of this exact conjunction has not been established.

The construction is in [`research/p21_least_preorder.py`](research/p21_least_preorder.py), with its independent [machine certificate](research/p21_machine_check.py). [Q-011](docs/questions.md) states the result and open questions; [D-023](docs/decisions.md) records its domain and empty-population choices. The source readings are in [`corpus/readings.toml`](corpus/readings.toml), and the incomplete literature comparison is in [`corpus/literature.toml`](corpus/literature.toml).

## Run the checks

Requires Python 3.14, `uv`, and `just`:

```sh
uv sync
just check
uv run python -m research.p21_least_preorder
```

The last command writes [`research/results/p21_least_preorder.json`](research/results/p21_least_preorder.json) and updates the P21 rows in `research/ledger.json`. Its finite-window diagnostic audits 18,273 instances on `W_-3…W_10` with at most three lives; that count is **not** the all-integer proof. `just research` reruns every research phase, and `just docs` regenerates `docs/results.md` from the ledger and literature verdicts. For the library CLI, run `uv run population-ethics --help`.

## Repository map

- `src/population_ethics/`: finite specification, solver, relation, proof, and CLI code.
- `research/`: phase scripts, exact model checks, canonical proof skeletons, and the ledger.
- `corpus/`: source readings, source authority, and literature-collision records.
- `docs/decisions.md`, `docs/questions.md`: formalization decisions and unresolved claims.
- `docs/results.md`: generated results register; do not edit it by hand.
- `tests/`: library and research regression tests.
