"""Route B: explicit ladder-relative candidate relations for Q-011.

This module is a proof ledger, not a search for a hidden preorder.  Each candidate is a small total
preorder on finite multisets of the frozen ladder W_-1,...,W_6.  The symbolic obligations cover
arbitrary finite multiplicities; the executable driver only double-checks a fixed small set of source
instances with ``research.ladder.audit``.

Scope: every positive claim is ladder-relative and covers all finite population sizes on that ladder.
No candidate here is promoted to a source-general (all integer levels) model.
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

from research.ladder import Witness, audit, domain, instances_over
from research.p8_catalogue import LADDER
from research.schema import Instance, Pop

ED = "arrhenius-2003:egalitarian-dominance"
GNEP = "arrhenius-2003:general-non-extreme-priority"
VRC = "arrhenius-2003:vrc-avoidance"
NE_2003 = "arrhenius-2003:non-elitism"
NE_THESIS = "thesis:non-elitism"
DA_2003 = "arrhenius-2003:dominance-addition"
DA_THESIS = "thesis:dominance-addition"

CONDITIONS: tuple[str, ...] = (ED, NE_THESIS, GNEP, VRC, DA_THESIS)
STRONGER: tuple[str, ...] = (NE_2003, DA_2003)
ALL_CONDITIONS: tuple[str, ...] = CONDITIONS + STRONGER

SHORT: dict[str, str] = {
    ED: "ED",
    NE_THESIS: "NE_THESIS (ranged background)",
    GNEP: "GNEP",
    VRC: "VRC avoidance",
    DA_THESIS: "DA_THESIS (not-worse)",
    NE_2003: "NE_2003 (any background)",
    DA_2003: "DA_2003 (mixed positive C)",
}


# ---------------------------------------------------------------------------------------------
# Candidate relations


class Candidate:
    """A total preorder represented by a comparable score tuple or number."""

    name: str
    definition: str

    def score(self, population: Pop) -> Any:
        raise NotImplementedError

    def weak(self, left: Pop, right: Pop) -> bool:
        return bool(self.score(left) >= self.score(right))

    def strict(self, left: Pop, right: Pop) -> bool:
        return bool(self.score(left) > self.score(right))

    def relation_description(self) -> str:
        return "P ⪰ Q iff score(P) >= score(Q); P ≻ Q iff score(P) > score(Q)."


class CriticalLevelSum(Candidate):
    """Critical-level total utility: U_c(P) = Σ_{l in P}(l-c)."""

    def __init__(self, c: int = 1) -> None:
        self.c = c
        self.name = f"critical-level sum (c={c})"
        self.definition = f"U_c(P) = sum(l - {c}) over every life l in P."

    def score(self, population: Pop) -> int:
        return sum(level - self.c for level in population)


class LevelCountLex(Candidate):
    """Lexicographic level-count order, highest level first."""

    def __init__(self) -> None:
        self.name = "level-count lexicographic"
        self.definition = (
            "score(P) = (N_6(P), N_5(P), ..., N_-1(P)); compare tuples lexicographically."
        )
        self._levels = tuple(reversed(LADDER.levels))

    def score(self, population: Pop) -> tuple[int, ...]:
        counts = Counter(population)
        return tuple(counts[level] for level in self._levels)


class TwoTierCount(Candidate):
    """Count lives at or above a cut first, then level-count lexicographic."""

    def __init__(self, u: int = 4) -> None:
        self.u = u
        self.secondary = LevelCountLex()
        self.name = f"two-tier count >= {u}, then count-lex"
        self.definition = (
            f"score(P) = (N_>={u}(P), N_6(P), ..., N_-1(P)); compare lexicographically."
        )

    def score(self, population: Pop) -> tuple[int, ...]:
        return (sum(level >= self.u for level in population), *self.secondary.score(population))


class LexCountCritical(Candidate):
    """Lexicographic pair (count above u, critical-level total)."""

    def __init__(self, u: int = 4, c: int = 1) -> None:
        self.u, self.c = u, c
        self.name = f"lex (count >= {u}, critical sum c={c})"
        self.definition = (
            f"score(P) = (N_>={u}(P), sum(l - {c})); compare the pair lexicographically."
        )

    def score(self, population: Pop) -> tuple[int, int]:
        return (
            sum(level >= self.u for level in population),
            sum(level - self.c for level in population),
        )


class ThresholdedSum(Candidate):
    """Additive utility that ignores lives below ``cut``."""

    def __init__(self, cut: int = 4) -> None:
        self.cut = cut
        self.name = f"thresholded sum (cut={cut})"
        self.definition = f"U(P) = sum(max(0, l - {cut} + 1)); levels below {cut} have weight zero."

    def score(self, population: Pop) -> int:
        return sum(max(0, level - self.cut + 1) for level in population)


class ExponentialSum(Candidate):
    """A justified count-sensitive additive family: positive exponential level weights."""

    def __init__(self) -> None:
        self.name = "positive exponential weighted sum"
        self.definition = (
            "U(P) = sum(2^l); this is an additive, strictly increasing, positive-weight order."
        )

    def score(self, population: Pop) -> Fraction:
        return sum((Fraction(2) ** level for level in population), Fraction(0))


# ---------------------------------------------------------------------------------------------
# Source witnesses and exact premise checker


def witness_for(candidate: Candidate) -> Witness:
    """Existential choices used in the holding proofs and executable audit.

    NE's n and GNEP's (u,y,n) are choices for the source's existential quantifiers.  They are not
    silently treated as one universal source witness: the proof text records where a choice is made.
    """

    if isinstance(candidate, ExponentialSum):
        ne_n = 2  # the worst adjacent-gap case on this finite ladder
        gnep = {"u": 6, "y": 3, "n": 1}
    elif isinstance(candidate, (LevelCountLex, TwoTierCount, LexCountCritical, ThresholdedSum)):
        ne_n = 1
        gnep = {"u": 6, "y": 3, "n": 2}
    else:
        ne_n = 1
        gnep = {"u": 4, "y": 3, "n": 1}
    return Witness(
        {
            "non-elitism": {"n": ne_n},
            "general-non-extreme-priority": gnep,
            "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
        }
    )


def condition_premise(
    left: Sequence[int], right: Sequence[int], condition: str, witness: Witness | None = None
) -> bool:
    """Decide a source condition's premise from its population pair.

    The decomposition is not guessed here: ``research.ladder.audit`` independently recovers all
    allowed shared backgrounds, sizes, ranges, and source shapes from the reading formalization.
    A witness is needed only for conditions with an existential numeric choice.  Thus this function
    answers the exact fixed-witness premise, while the surrounding proof handles source existential
    quantification symbolically.
    """

    if condition not in ALL_CONDITIONS:
        raise ValueError(f"unknown source condition {condition!r}")
    if witness is None:
        witness = Witness({})
    try:
        return audit(
            Instance(condition, (tuple(sorted(left)), tuple(sorted(right)))), LADDER, witness
        )
    except KeyError, ValueError:
        return False


# ---------------------------------------------------------------------------------------------
# Exact counterexamples and symbolic proof obligations


@dataclass(frozen=True)
class Counterexample:
    condition: str
    left: Pop
    right: Pop
    witness: Mapping[str, int]
    reason: str
    universal_obstruction: str = ""

    def text(self) -> str:
        left = format_population(self.left)
        right = format_population(self.right)
        witness = (
            ", ".join(f"{key}={value}" for key, value in sorted(self.witness.items())) or "none"
        )
        suffix = (
            f" Universal obstruction: {self.universal_obstruction}"
            if self.universal_obstruction
            else ""
        )
        return f"{SHORT[self.condition]}: left={left}, right={right}; witness {{{witness}}}; {self.reason}.{suffix}"


@dataclass(frozen=True)
class Verdict:
    holds: bool
    proof: str = ""
    counterexample: Counterexample | None = None


def format_population(population: Pop) -> str:
    counts = Counter(population)
    if not counts:
        return "empty"
    return "{" + ", ".join(f"W_{level}^{count}" for level, count in sorted(counts.items())) + "}"


def _ne_counterexample(condition: str, *, lowest_level_pair: bool = False) -> Counterexample:
    # C = (n+1) lives at W_(x-1), A = one W_x, B = n lives at W_y; D is empty.
    if lowest_level_pair:
        left, right = (0, 0), (-1, 1)
        x, y = 1, -1
        high, low, middle = "W_1", "W_-1", "W_0"
    else:
        left, right = (3, 3), (2, 4)
        x, y = 4, 2
        high, low, middle = "W_4", "W_2", "W_3"
    return Counterexample(
        condition,
        left,
        right,
        {"x": x, "y": y, "n": 1},
        f"the premise holds with D empty, but the right has one {high} and the left has none",
        f"for every n>0, the right has one {high} while the left has only {middle}^(n+1); "
        f"no existential n can repair this (the B lives are at {low}).",
    )


def _ne_counterexample_for(candidate: Candidate, condition: str) -> Counterexample:
    return _ne_counterexample(
        condition,
        lowest_level_pair=isinstance(candidate, (LevelCountLex, TwoTierCount)),
    )


def _vrc_counterexample(candidate: Candidate) -> Counterexample:
    if isinstance(candidate, CriticalLevelSum):
        b_count = 3
    elif isinstance(candidate, ExponentialSum):
        b_count = 2
    else:
        raise AssertionError("only additive candidates use the VRC counterexample")
    right = tuple(sorted((-1,) + (3,) * b_count))
    return Counterexample(
        VRC,
        (4,),
        right,
        {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
        f"the premise holds with B=W_3^{b_count}, but score(left)={candidate.score((4,))!s} < "
        f"score(right)={candidate.score(right)!s}",
        "for every valid VRC witness, fix A=W_u^n and C=W_-1^m and let B be K copies of W_3; its positive weight makes the right side exceed the fixed left for sufficiently large K.",
    )


def _threshold_ed_counterexample() -> Counterexample:
    return Counterexample(
        ED,
        (1,),
        (0,),
        {},
        "the premise holds with equal population size and B below A, but both levels are ignored and score(left)=score(right)=0",
    )


def verdicts(candidate: Candidate) -> dict[str, Verdict]:
    """Symbolic verdict ledger, including both weakened and stronger source forms."""

    if isinstance(candidate, (CriticalLevelSum, ExponentialSum)):
        additive = isinstance(candidate, CriticalLevelSum)
        if additive:
            ne_proof = (
                "For x-1>y and equal shared D, additive cancellation gives "
                "U(C)-U(A+B)=n*(x-1-y)-1; n=1 is nonnegative on the integer ladder."
            )
        else:
            ne_proof = (
                "For x-1>y and equal shared D, exponential cancellation gives "
                "U(C)-U(A+B)=n*(2^(x-1)-2^y)-2^(x-1).  The smallest gap is y=x-2, "
                "where n=2 makes this zero; n=2 is therefore a uniform finite-ladder choice."
            )
        if additive:
            g_proof = (
                "Choose GNEP (u,y,n)=(4,3,1).  After cancelling E, "
                "U(A+C)-U(B+D)=x-b-1>=0 for x>=4 and b<=3, for every z and every finite E."
            )
        else:
            g_proof = (
                "Choose GNEP (u,y,n)=(6,3,1).  The only x is 6; the worst z=5,b=3 gives "
                "2^6+2^5-(2^3+2^6)>0, and all other z or b are easier.  Additive cancellation "
                "handles every finite E."
            )
        da_proof = (
            "For DA_THESIS, every B life is strictly above every A life and c=1 makes every "
            "positive C life nonnegative; hence U(B+C)>=U(A).  For DA_2003 the same argument "
            "allows arbitrary mixed positive C."
            if additive
            else "All exponential weights are positive and strictly increasing: B's equal-sized "
            "lives strictly dominate A's lives, and arbitrary positive C only increases the right."
        )
        return {
            ED: Verdict(
                True,
                "Equal-sized A=W_x and lower B have strictly larger additive weight at every life; backgrounds are absent.",
            ),
            NE_THESIS: Verdict(True, ne_proof),
            GNEP: Verdict(True, g_proof),
            VRC: Verdict(False, counterexample=_vrc_counterexample(candidate)),
            DA_THESIS: Verdict(True, da_proof),
            NE_2003: Verdict(
                True,
                ne_proof
                + " The argument cancels any unrestricted shared D, so it also covers NE_2003.",
            ),
            DA_2003: Verdict(True, da_proof),
        }

    if isinstance(candidate, ThresholdedSum):
        g_proof = (
            "Choose GNEP (u,y,n)=(6,3,2).  Two W_6 lives on the left outweigh at most one "
            "counted D life on the right; all B lives are below the cut and common E cancels."
        )
        da_proof = (
            "Every threshold weight is nonnegative and nondecreasing.  In DA, B is at levels "
            "strictly above A and has equal size, while C is positive; therefore thresholded "
            "score(B+C)>=score(A), including the all-ignored case."
        )
        return {
            ED: Verdict(False, counterexample=_threshold_ed_counterexample()),
            NE_THESIS: Verdict(False, counterexample=_ne_counterexample(NE_THESIS)),
            GNEP: Verdict(True, g_proof),
            VRC: Verdict(
                True,
                "Choose VRC x=-1,u=4,v=6,y=3,n=m=1.  A is counted; arbitrary B<=W_3 and C=W_-1 are ignored.",
            ),
            DA_THESIS: Verdict(True, da_proof),
            NE_2003: Verdict(False, counterexample=_ne_counterexample(NE_2003)),
            DA_2003: Verdict(True, da_proof + " Mixed positive C remains nonnegative."),
        }

    if isinstance(candidate, (LevelCountLex, TwoTierCount, LexCountCritical)):
        if isinstance(candidate, LevelCountLex):
            vrc = "With VRC x=-1,u=4,v=6,y=3,n=m=1, A has one W_4 while B+C has no W_4 or higher, regardless of B's size."
            gnep = (
                "Choose GNEP (u,y,n)=(6,3,2).  The left has two W_6 lives; the right has at most "
                "one W_6 (D), so the first lexicographic coordinate at which they differ favors left."
            )
            da = "In DA, B has the same size as A and every B level is above every A level; the highest B level gives a positive first differing count, and C cannot reverse it."
            ed = "At the highest level in A, no B life occurs; equal sizes and strict level separation make the first differing count favor A."
        elif isinstance(candidate, TwoTierCount):
            vrc = "With VRC x=-1,u=4,v=6,y=3,n=m=1, A contributes one >=4 life and B+C contributes zero, regardless of B's finite size."
            gnep = (
                "Choose GNEP (u,y,n)=(6,3,2).  Left has at least two lives >=4 and right has at most "
                "one (D), so the first tier strictly favors left for every z, B, and E."
            )
            da = "If A has fewer >=4 lives than B+C the first tier favors right; if tied, every B level is above A and the count-lex secondary favors right."
            ed = "Either A has more lives at or above 4, or the secondary count-lex sees A's highest level before every lower B level."
        else:
            vrc = "With VRC x=-1,u=4,v=6,y=3,n=m=1, the first tier gives left count 1 and right count 0, regardless of B's finite size."
            gnep = (
                "Choose GNEP (u,y,n)=(6,3,2).  The first tier gives left at least two >=4 lives and "
                "right at most one; any shared E cancels from both coordinates."
            )
            da = "The >=4 count cannot favor A when B is at/above its threshold; on a tie, c=1 critical total strictly favors B, while positive C is nonnegative."
            ed = "The first-tier count is no smaller for A; on a tie, the critical total is strictly larger because A is at the higher equal level."
        return {
            ED: Verdict(True, ed),
            NE_THESIS: Verdict(False, counterexample=_ne_counterexample_for(candidate, NE_THESIS)),
            GNEP: Verdict(True, gnep),
            VRC: Verdict(True, vrc),
            DA_THESIS: Verdict(True, da),
            NE_2003: Verdict(False, counterexample=_ne_counterexample_for(candidate, NE_2003)),
            DA_2003: Verdict(True, da + " The same dominance argument covers mixed positive C."),
        }

    raise TypeError(f"unhandled candidate {candidate!r}")


# ---------------------------------------------------------------------------------------------
# Machine-checked small driver


def candidate_set() -> tuple[Candidate, ...]:
    return (
        CriticalLevelSum(c=1),
        LevelCountLex(),
        TwoTierCount(u=4),
        LexCountCritical(u=4, c=1),
        ThresholdedSum(cut=4),
        ExponentialSum(),
    )


def relation_holds(candidate: Candidate, instance: Instance) -> bool:
    """Evaluate the consequent with the source shape, not one guessed edge direction."""

    left, right = instance.args
    if instance.principle == ED:
        return candidate.strict(left, right)
    if instance.principle == DA_THESIS:
        # Thesis DA is N-shaped: it forbids A ≻ B∪C, rather than asserting a weak edge.
        return not candidate.strict(left, right)
    return candidate.weak(left, right)


def _cex_audit(candidate: Candidate, verdict: Verdict) -> bool:
    if verdict.counterexample is None:
        return True
    cex = verdict.counterexample
    witness = witness_for(candidate)
    # Counterexample witnesses explicitly override the candidate's witness for the tested form.
    if cex.condition in {NE_THESIS, NE_2003}:
        witness = Witness({"non-elitism": dict(cex.witness)})
    elif cex.condition == VRC:
        witness = Witness({"vrc-avoidance": dict(cex.witness)})
    return condition_premise(cex.left, cex.right, cex.condition, witness)


def audit_driver(candidate: Candidate) -> dict[str, Any]:
    """Audit all generated premises over a fixed small population set.

    This is a sanity check on the symbolic ledger, not a bounded consistency claim.  The generated
    populations have at most two lives; the separately listed counterexamples are replayed too.
    """

    focus = domain(LADDER, 2)
    witness = witness_for(candidate)
    generated = instances_over(focus, LADDER, witness, ALL_CONDITIONS)
    premise_failures = [
        instance
        for instance in generated
        if not condition_premise(instance.args[0], instance.args[1], instance.principle, witness)
    ]
    relation_violations = [
        instance for instance in generated if not relation_holds(candidate, instance)
    ]
    violations_by_condition = Counter(instance.principle for instance in relation_violations)
    checked_cex = 0
    for result in verdicts(candidate).values():
        if result.counterexample is not None:
            if not _cex_audit(candidate, result):
                raise AssertionError(f"counterexample did not audit: {result.counterexample}")
            checked_cex += 1
    if premise_failures:
        raise AssertionError(f"audit rejected generated instances: {premise_failures[:2]}")
    return {
        "fixed_population_count": len(focus),
        "generated_instance_count": len(generated),
        "premise_checks_failed": len(premise_failures),
        "relation_violations_on_fixed_set": len(relation_violations),
        "relation_violations_by_condition": dict(sorted(violations_by_condition.items())),
        "counterexamples_replayed": checked_cex,
    }


def run() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for candidate in candidate_set():
        table = verdicts(candidate)
        driver = audit_driver(candidate)
        rows.append(
            {
                "candidate": candidate.name,
                "definition": candidate.definition,
                "relation": candidate.relation_description(),
                "scope": "ladder-relative, all finite sizes",
                "verdicts": {
                    SHORT[key]: {
                        "holds": value.holds,
                        "proof": value.proof,
                        "counterexample": value.counterexample.text()
                        if value.counterexample is not None
                        else None,
                    }
                    for key, value in table.items()
                },
                "driver": driver,
                "certified_model": all(table[key].holds for key in CONDITIONS),
            }
        )
    return {"scope": "ladder-relative, all finite sizes", "candidates": rows, "survivor": None}


def main() -> None:
    data = run()
    print("Route B explicit model analysis (Q-011)")
    print("Scope: ladder-relative, all finite sizes; no unrestricted-domain claim.")
    for row in data["candidates"]:
        print(f"\nCandidate: {row['candidate']}")
        print(f"  Definition: {row['definition']}")
        print(f"  Relation: {row['relation']}")
        for condition, result in row["verdicts"].items():
            status = "HOLDS" if result["holds"] else "FAILS"
            print(f"  {condition}: {status}")
            if result["holds"]:
                print(f"    Proof obligations discharged: {result['proof']}")
            else:
                print(f"    Exact counterexample: {result['counterexample']}")
        print(f"  Machine checker: {row['driver']}")
        print(
            "  Certified model for {ED, NE_THESIS, GNEP, VRC, DA_THESIS}: "
            + str(row["certified_model"])
        )
    print("\nConclusion: no listed candidate certifies the weakest five-condition variant.")
    print(
        "All failures are explicit; this is neither a source-general consistency proof nor an inconsistency proof."
    )


if __name__ == "__main__":
    main()
