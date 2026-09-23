"""Phase 10: witness families. Where does the census change as existential witnesses grow?

Phase 9 ran one witness. Here each "∃ m > n" witness is a rule m = mult·n + step and Condition
δ's n may grow with its number of negative lives, n(m) = n + n_per_m·(m − 1)
(research/ladder.py). Three sweeps:

- **Triangle (Q-007).** Over {δ, a β-type condition, Egalitarian Dominance}, the census's 3-cycles
  are compared with a closed-form prediction. The only rotation that can close is
  δ(X ⪰ Y), ED(Y ≻ Z), β(Z ⪰ X). ED forces Y = (n+m) lives at W_3 and Z entirely below W_3, so
  β's background holds only δ's negative lives. The triangle therefore fires iff for some
  negative level z with a ladder level strictly between z and W_3, and some m with
  n = n_δ(m) and n + m within the bound, β's witness m_β(n) is at most m (β over any background
  or over R(z, y+1)) or equals m (Inequality Aversion, which has no background).
- **Theorem 1 length law.** With Quality ranges R(u, v) above R(1, y), the shortest strict cycle
  over {Quality, Quantity, Egalitarian Dominance} has u − y + 3 edges: Quality, u − y + 1
  Quantity steps, one Egalitarian Dominance step. It exists iff the Quantity chain's final size
  fits the population bound.
- **Safe witnesses.** The Phase 8 theorems' condition sets re-censused with δ's n growing fast
  enough that the triangle cannot fire: which short cycles remain, and is the source word still
  there?
"""

from __future__ import annotations

import json
import time
from itertools import combinations_with_replacement, product
from typing import Any

from research.census import cycle_words
from research.lab import LedgerEntry, record, write_result
from research.ladder import Ladder, Witness, delta_n, domain, instances_over, larger
from research.p8_catalogue import FROZEN, LADDER, WITNESS
from research.p9_census import _cycle_order, _rotation_min

TRIANGLE_LIVES = 6
LAW_MAX_LIVES = 8  # Quantity chains that outgrow this are skipped, not extrapolated
BETA_VARIANTS = {
    "arrhenius-2003:condition-beta": "any",
    "thesis:condition-beta": "ranged",
    "thesis:inequality-aversion": "none",
}


def triangle_predicted(
    ladder: Ladder, delta: dict[str, int], beta: dict[str, int], background: str, lives: int
) -> bool:
    for z in (v for v in ladder.levels if v < 0):
        if not any(z < y < 3 for y in ladder.levels):
            continue
        for m in range(1, lives + 1):
            n = delta_n(delta, m)
            if n + m > lives:
                continue
            mb = larger(beta, n)
            if (mb == m) if background == "none" else (mb <= m):
                return True
    return False


def triangle_sweep() -> list[dict[str, Any]]:
    rows = []
    # Levels above W_u = W_4 cannot change whether the triangle fires (δ needs one level >= u),
    # so the universe stops there; this keeps the 36 regenerations within memory.
    pops = [p for p in domain(LADDER, TRIANGLE_LIVES) if max(p) <= 4]
    for (beta_id, background), n0, per_m, step, mult in product(
        BETA_VARIANTS.items(), (1, 2), (0, 1, 2), (1, 2, 3), (1, 2)
    ):
        delta = {"u": 4, "y": 3, "n": n0, "n_per_m": per_m}
        beta = {"step": step, "mult": mult}
        family = "inequality-aversion" if background == "none" else "condition-beta"
        witness = Witness({**WITNESS.params, "condition-delta": delta, family: beta})
        principles = [
            "arrhenius-2003:condition-delta",
            beta_id,
            "arrhenius-2003:egalitarian-dominance",
        ]
        insts = instances_over(pops, LADDER, witness, principles)
        found = [w for w in cycle_words(insts, 3) if len(w.word) == 3]
        predicted = triangle_predicted(LADDER, delta, beta, background, TRIANGLE_LIVES)
        rows.append(
            {
                "beta": beta_id,
                "delta": delta,
                "beta_witness": beta,
                "predicted": predicted,
                "found": bool(found),
                "example": [[i.principle, [list(p) for p in i.args]] for i in found[0].example]
                if found
                else None,
            }
        )
    return rows


def length_law_sweep() -> list[dict[str, Any]]:
    rows = []
    ladder = Ladder(1, 9)
    for y, u, mult in product((3, 4, 5), range(4, 8), (1, 2)):
        if u <= y or u + 2 > ladder.positive:
            continue
        quantity = {"step": 1, "mult": mult}
        size, sizes = 1, [1]
        for _ in range(u - y + 1):
            size = larger(quantity, size)
            sizes.append(size)
        if size > LAW_MAX_LIVES:
            continue
        for lives in (size - 1, size):
            witness = Witness(
                {"quality": {"u": u, "v": u + 2, "y": y, "n": 1}, "quantity": quantity}
            )
            principles = ["thesis:quality", "thesis:quantity", "thesis:egalitarian-dominance"]
            # Levels above W_u never shorten the chain, and no step uses a negative level.
            pops = [
                tuple(c)
                for k in range(1, lives + 1)
                for c in combinations_with_replacement(range(1, u + 1), k)
            ]
            words = cycle_words(instances_over(pops, ladder, witness, principles), u - y + 3)
            shortest = min((len(w.word) for w in words), default=None)
            predicted = u - y + 3 if lives >= size else None
            rows.append(
                {
                    "u": u,
                    "y": y,
                    "quantity": quantity,
                    "lives": lives,
                    "chain_sizes": sizes,
                    "predicted_shortest": predicted,
                    "shortest": shortest,
                    "agree": shortest == predicted,
                }
            )
    return rows


def safe_census() -> list[dict[str, Any]]:
    """Phase 8 theorems whose conditions include δ, with δ's n growing by 5 per negative life."""
    rows = []
    for frozen in FROZEN:
        principles = sorted({p for p, _, _ in frozen.core})
        if not any("condition-delta" in p for p in principles):
            continue
        delta = {**WITNESS.params["condition-delta"], "n_per_m": 5}
        witness = Witness({**WITNESS.params, "condition-delta": delta})
        lives = max(len(p) for p in frozen.populations.values())
        started = time.monotonic()
        insts = instances_over(domain(LADDER, lives), LADDER, witness, principles)
        words = cycle_words(insts, len(frozen.core))
        source = _rotation_min(tuple(i.principle for i in _cycle_order(frozen.instances())))
        rows.append(
            {
                "theorem": frozen.id,
                "delta": delta,
                "lives": lives,
                "words_by_length": {
                    k: sum(1 for w in words if len(w.word) == k)
                    for k in sorted({len(w.word) for w in words})
                },
                "shortest": min((len(w.word) for w in words), default=None),
                "source_word_rediscovered": source in {w.word for w in words},
                "shortest_words": [
                    [p.split(":")[1] for p in w.word]
                    for w in words
                    if len(w.word) == min(len(v.word) for v in words)
                ],
                "seconds": round(time.monotonic() - started, 1),
            }
        )
    return rows


def main() -> None:
    started = time.monotonic()
    data = {"triangle": triangle_sweep(), "length_law": length_law_sweep(), "safe": safe_census()}
    write_result(
        "p10_witness_families", data, {"wall_time_s": round(time.monotonic() - started, 1)}
    )
    _ledger(data)
    tri = data["triangle"]
    print(
        f"triangle: {sum(r['predicted'] == r['found'] for r in tri)}/{len(tri)} agree, {sum(r['found'] for r in tri)} fire"
    )
    law = data["length_law"]
    print(f"length law: {sum(r['agree'] for r in law)}/{len(law)} agree")
    print(json.dumps(data["safe"], indent=1))


def _ledger(data: dict[str, Any]) -> None:
    tri, law, safe = data["triangle"], data["length_law"], data["safe"]
    tri_ok = all(r["predicted"] == r["found"] for r in tri)
    law_ok = all(r["agree"] for r in law)
    entries = [
        LedgerEntry(
            candidate_id="P10-triangle-firing-condition",
            hypothesis="δ, a β-type condition and Egalitarian Dominance close a 3-cycle iff some m has m_β(n_δ(m)) <= m (= m for Inequality Aversion) within the bound.",
            motivation="Q-007: the R5 triangle in the thesis family.",
            exact_formal_change=f"{len(tri)} witnesses: δ n ∈ {{1,2}}, n_per_m ∈ {{0,1,2}}; β step ∈ {{1,2,3}}, mult ∈ {{1,2}}; three β variants; ladder W_-1..W_6, <= {TRIANGLE_LIVES} lives",
            scope="finite witness grid",
            search_method="closed-form prediction vs exhaustive 3-cycle search",
            result=f"prediction matches the census in {sum(r['predicted'] == r['found'] for r in tri)}/{len(tri)} witnesses; the triangle fires in {sum(r['found'] for r in tri)}",
            evidence_type="exhaustive search against a derived predicate",
            checked=tri_ok,
            minimal="every 3-cycle is a minimal core",
            interpretation="A satisfying axiology must let δ's n grow with m so that β's witness for it always exceeds m. The R5 triangle is the same constraint on MNEP's witness in the 2000 family.",
            next_experiment="literature check (thesis Lemma 5.2, 2009 Lemma 2)",
            result_scope="bounded conjecture",
            formalization_tier="unreviewed witness family over cross-read conditions",
            witness_conditions="research/p10_witness_families.py triangle_sweep",
            status="confirmed" if tri_ok else "refuted",
        ),
        LedgerEntry(
            candidate_id="P10-theorem-1-length-law",
            hypothesis="The shortest strict cycle over Quality, Quantity and Egalitarian Dominance has u − y + 3 edges and exists iff the Quantity chain's final size fits the bound.",
            motivation="Phase 9 found Theorem 1 shortening to 4 edges under its witness.",
            exact_formal_change=f"{len(law)} (u, y, Quantity rule, bound) cases on ladder W_-1..W_9",
            scope="finite witness grid",
            search_method="closed-form prediction vs exhaustive cycle search",
            result=f"{sum(r['agree'] for r in law)}/{len(law)} cases agree",
            evidence_type="exhaustive search against a derived predicate",
            checked=law_ok,
            minimal="every simple strict cycle is a minimal core",
            interpretation="The proof's length is set by the gap between the high and low Quality ranges, not by Quantity's growth rule, which only sets the populations' size.",
            next_experiment="length laws for the other theorems",
            result_scope="bounded conjecture",
            formalization_tier="unreviewed witness family over cross-read conditions",
            witness_conditions="research/p10_witness_families.py length_law_sweep",
            status="confirmed" if law_ok else "refuted",
        ),
    ]
    for r in safe:
        entries.append(
            LedgerEntry(
                candidate_id=f"P10-safe-census-{r['theorem']}",
                hypothesis="With δ's n growing fast enough, the triangle disappears and the source word remains.",
                motivation="Separate witness artifacts from the theorems' own structure.",
                exact_formal_change=f"δ {r['delta']}; <= {r['lives']} lives",
                scope="finite universe",
                search_method="exhaustive simple-cycle search",
                result=f"words by length {r['words_by_length']}; shortest {r['shortest']} ({r['shortest_words'][:4]}); source rediscovered: {r['source_word_rediscovered']}",
                evidence_type="exhaustive search",
                checked=r["source_word_rediscovered"],
                minimal="every simple strict cycle is a minimal core",
                interpretation="Cycles shorter than the source proof that survive are candidate shortcuts to examine.",
                next_experiment="inspect surviving short words",
                result_scope="finite computational result",
                formalization_tier="unreviewed witness family over cross-read conditions",
                witness_conditions="research/p10_witness_families.py safe_census",
                status="confirmed" if r["source_word_rediscovered"] else "refuted",
            )
        )
    record(entries)


if __name__ == "__main__":
    main()
