"""Route B rerun: background-sensitive, non-additive ladder relations for Q-011.

This module is deliberately ladder-relative (W_-1, ..., W_6).  The symbolic rows below are
all-size arguments over finite populations on that ladder; the finite driver is only a premise
and replay sanity check.  It is not used as consistency evidence (D-018).
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from typing import Any

from research.ladder import Witness, audit, domain, instances_over
from research.p8_catalogue import LADDER
from research.p19_vrc_model import (
    ALL_CONDITIONS,
    DA_2003,
    DA_THESIS,
    ED,
    GNEP,
    NE_2003,
    NE_THESIS,
    VRC,
)
from research.schema import Instance, Pop

SHORT = {
    ED: "ED",
    NE_THESIS: "NE_THESIS",
    NE_2003: "NE_2003",
    GNEP: "GNEP",
    VRC: "VRC avoidance",
    DA_THESIS: "DA_THESIS",
    DA_2003: "DA_2003",
}

ORDER: tuple[str, ...] = (ED, NE_THESIS, NE_2003, GNEP, VRC, DA_THESIS, DA_2003)

# Every existential source witness used by this rerun is explicit.  The chosen ranges exist on
# LADDER: R(4,6) and R(1,3), and x=-1 is negative.  A proof may use a different witness, but the
# driver below checks only the displayed witness and never promotes that check to an all-size claim.
BASE_WITNESS = Witness(
    {
        "non-elitism": {"n": 1},
        "general-non-extreme-priority": {"u": 4, "y": 3, "n": 1},
        "vrc-avoidance": {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
    }
)


class Candidate:
    """A complete preorder on nonempty finite ladder populations."""

    name: str
    definition: str

    def score(self, population: Pop) -> tuple[Any, ...]:
        raise NotImplementedError

    def weak(self, left: Pop, right: Pop) -> bool:
        return self.score(left) >= self.score(right)

    def strict(self, left: Pop, right: Pop) -> bool:
        return self.score(left) > self.score(right)

    def relation_description(self) -> str:
        return "P ⪰ Q iff score(P) >= score(Q); P ≻ Q iff score(P) > score(Q)."

    def background_demo(self) -> str:
        return ""


class MinimumLevel(Candidate):
    """Support-conditioned rank: the worst occupied level is decisive."""

    def __init__(self) -> None:
        self.name = "minimum occupied level"
        self.definition = "score(P)=(min(P), max(P), -N(P)); compare lexicographically."

    def score(self, population: Pop) -> tuple[Any, ...]:
        if not population:
            return (-(10**9), -(10**9), 0)
        return (min(population), max(population), -len(population))

    def background_demo(self) -> str:
        return (
            "Background-sensitive: {W_1} ≻ {W_0,W_2} because its minimum is higher, but "
            "after shared D={W_-1} the minima tie and the second population has the higher "
            "maximum. The comparison reverses, so common backgrounds do not cancel."
        )


class SpanLex(Candidate):
    """Support-conditioned rank: prefer a narrower occupied support, then its upper endpoint."""

    def __init__(self) -> None:
        self.name = "narrow-support span lex"
        self.definition = "score(P)=(-(max(P)-min(P)), max(P), min(P)); compare lexicographically."

    def score(self, population: Pop) -> tuple[Any, ...]:
        if not population:
            return (-(10**9), -(10**9), -(10**9))
        lo, hi = min(population), max(population)
        return (-(hi - lo), hi, lo)

    def background_demo(self) -> str:
        return (
            "Background-sensitive: {W_1} ≻ {W_0}, but adding shared D={W_-1} reverses the "
            "comparison because their spans become 2 and 1."
        )


class HighCountMax(Candidate):
    """Unbounded high-block count, with a non-additive maximum tie-break."""

    def __init__(self, cut: int = 4) -> None:
        self.cut = cut
        self.name = f"high-count then maximum (cut={cut})"
        self.definition = (
            f"score(P)=(N_{{>={cut}}}(P), max(P)); compare lexicographically. "
            "The first tier counts high lives; the tie-break is support-sensitive max."
        )

    def score(self, population: Pop) -> tuple[Any, ...]:
        if not population:
            return (0, -(10**9))
        return (sum(level >= self.cut for level in population), max(population))

    def background_demo(self) -> str:
        return (
            "Background-sensitive despite its first additive tier: {W_1} ≻ {W_0}, while shared "
            "D={W_6} makes both high-count 1 and max W_6, hence a tie. The max tie-break is not "
            "additive, so the whole order is not a fixed additive/lexicographic-additive order."
        )


@dataclass(frozen=True)
class Counterexample:
    condition: str
    instance: Instance
    witness: Witness
    reason: str
    cap: int

    @property
    def left(self) -> Pop:
        return self.instance.args[0]

    @property
    def right(self) -> Pop:
        return self.instance.args[1]

    def text(self) -> str:
        def fmt(pop: Pop) -> str:
            counts = Counter(pop)
            if not counts:
                return "empty"
            return "{" + ", ".join(f"W_{k}^{v}" for k, v in sorted(counts.items())) + "}"

        family = self.witness.params.get("non-elitism")
        if self.condition in {NE_THESIS, NE_2003}:
            witness = family
        elif self.condition == GNEP:
            witness = self.witness.params.get("general-non-extreme-priority")
        elif self.condition == VRC:
            witness = self.witness.params.get("vrc-avoidance")
        else:
            witness = {}
        return (
            f"{SHORT[self.condition]}: left={fmt(self.left)}, right={fmt(self.right)}; "
            f"witness={witness}; cap={self.cap}; ladder.audit=True; {self.reason}"
        )


@dataclass(frozen=True)
class Verdict:
    holds: bool
    proof: str = ""
    counterexample: Counterexample | None = None


def relation_holds(candidate: Candidate, instance: Instance) -> bool:
    """Evaluate the source consequent using the source shape (S, W, or N)."""
    left, right = instance.args
    if instance.principle == ED:
        return candidate.strict(left, right)
    if instance.principle == DA_THESIS:
        # Thesis DA is N-shaped: it forbids A ≻ B∪C.
        return not candidate.strict(left, right)
    return candidate.weak(left, right)


def smallest_counterexample(
    candidate: Candidate, condition: str, witness: Witness
) -> Counterexample:
    """Find the first audited relation violation, increasing the population-size cap.

    This search is only for a replayable source counterexample.  Absence from the bounded search
    is never interpreted as a proof; holding rows come from the separate symbolic ledger below.
    """
    for cap in range(1, 5):
        focus = domain(LADDER, cap)
        generated = instances_over(focus, LADDER, witness, [condition])
        for instance in sorted(generated, key=lambda i: (sum(map(len, i.args)), i.args)):
            if not audit(instance, LADDER, witness):
                continue
            if not relation_holds(candidate, instance):
                reason = failure_reason(candidate, condition, instance)
                return Counterexample(condition, instance, witness, reason, cap)
    raise AssertionError(f"no small audited counterexample found for {candidate.name}/{condition}")


def failure_reason(candidate: Candidate, condition: str, instance: Instance) -> str:
    left, right = instance.args
    return (
        f"candidate scores left={candidate.score(left)!r}, right={candidate.score(right)!r}, "
        "so the required consequent is false"
    )


def _minimum_verdicts() -> dict[str, str]:
    return {
        ED: (
            "For ED, min(A)=x while every B life is below x, so min(A)>min(B); equal size is "
            "irrelevant."
        ),
        # A negative shared background can tie the minima while the right's W_x raises its
        # maximum.  The all-size NE obligations therefore need an audited counterexample below.
        VRC: (
            "The left has only z>=u>y>0, whereas the right contains m>0 lives at the negative "
            "level x<0; therefore min(left)>min(right), for every finite B size."
        ),
    }


def _span_verdicts() -> dict[str, str]:
    return {
        ED: (
            "A is homogeneous, hence span(A)=0. If B has more than one occupied level its span "
            "is positive; if B is homogeneous, max(A)=x>max(B)."
        ),
        NE_THESIS: (
            "Put a=x−1>y. For any finite D, max(D∪{a})<=max(D∪{x}) and "
            "min(D∪{a})>=min(D∪{y}), hence span(left)<=span(right). Equality can occur only "
            "with equal upper endpoints, so the (−span,max,min) tuple favors left. This covers "
            "every ranged background and every finite n."
        ),
        NE_2003: (
            "The preceding extrema argument never used the range restriction on D; it therefore "
            "proves the same span inequality for every finite unrestricted background."
        ),
        VRC: (
            "With no shared background, the left is homogeneous positive (span 0), while the "
            "right contains both a negative and a positive life (positive span); left wins."
        ),
    }


def _high_count_verdicts() -> dict[str, str]:
    return {
        ED: ("If A's high-count tier exceeds B's, A wins immediately; if tied, max(A)=x>max(B)."),
        GNEP: (
            "With (u,y,n)=(4,3,1), after any shared E cancels in the high-count difference, "
            "left-minus-right is n+1[z>=4]−1[z+1>=4]>=0. It is strict except the only tie "
            "case n=1,z=3; there max(left)>=max(right) because x>=4 and B<=3. Thus the "
            "unbounded E and every finite z are covered."
        ),
        VRC: (
            "A contributes n high lives at z>=4; B is confined to 1..3 and C is negative, so "
            "the high-count tier strictly favors A for every finite B and m."
        ),
        DA_THESIS: (
            "Every B life is above every A life. Therefore B contributes at least as many high "
            "lives as A; if tied, max(B)>max(A), and adding positive C cannot lower either tier."
        ),
        DA_2003: (
            "The same high-count and maximum argument allows C to be any finite nonempty mixture "
            "of positive levels, so it proves the 2003 weak edge as well."
        ),
    }


def _existential_failures(candidate: Candidate) -> dict[str, str]:
    if isinstance(candidate, MinimumLevel):
        return {
            NE_THESIS: "At (x,y)=(1,-1), D={W_-1}, the minima tie and the right has "
            "maximum 1 versus 0 on the left for every n>=1.",
            NE_2003: "The same unrestricted D={W_-1} refutes every n>=1.",
            GNEP: "At z=-1 and E empty, the left minimum is -1 while the right minimum "
            "is at least 0 for every permitted (u,y,n).",
        }
    if isinstance(candidate, SpanLex):
        return {
            GNEP: "At z=-1 and E empty, the left span is at least u+1, while the "
            "right span is at most y<u for every permitted (u,y,n).",
        }
    if isinstance(candidate, HighCountMax):
        return {
            NE_THESIS: "At (x,y)=(1,-1), D empty, both sides have zero high lives "
            "and the right maximum is 1 versus 0 on the left for every n>=1.",
            NE_2003: "The same unrestricted empty D refutes every n>=1.",
        }
    return {}


def verdicts(candidate: Candidate) -> dict[str, Verdict]:
    if isinstance(candidate, MinimumLevel):
        proofs = _minimum_verdicts()
    elif isinstance(candidate, SpanLex):
        proofs = _span_verdicts()
    elif isinstance(candidate, HighCountMax):
        proofs = _high_count_verdicts()
    else:  # pragma: no cover - candidate_set is closed below
        raise TypeError(candidate)

    failures = _existential_failures(candidate)
    out: dict[str, Verdict] = {}
    witness = BASE_WITNESS
    for condition in ORDER:
        if condition in proofs:
            out[condition] = Verdict(True, proofs[condition])
        else:
            out[condition] = Verdict(
                False,
                failures.get(condition, ""),
                smallest_counterexample(candidate, condition, witness),
            )
    return out


def candidate_set() -> tuple[Candidate, ...]:
    return (MinimumLevel(), SpanLex(), HighCountMax())


def audit_driver(candidate: Candidate) -> dict[str, Any]:
    """Run the bounded premise/relation sanity driver and replay symbolic counterexamples."""
    focus = domain(LADDER, 2)
    generated = instances_over(focus, LADDER, BASE_WITNESS, ALL_CONDITIONS)
    premise_failures = [
        instance for instance in generated if not audit(instance, LADDER, BASE_WITNESS)
    ]
    relation_violations = [
        instance for instance in generated if not relation_holds(candidate, instance)
    ]
    by_condition = Counter(instance.principle for instance in relation_violations)
    replayed = 0
    for result in verdicts(candidate).values():
        if result.counterexample is not None:
            if not audit(result.counterexample.instance, LADDER, result.counterexample.witness):
                raise AssertionError(f"counterexample failed audit: {result.counterexample.text()}")
            replayed += 1
    return {
        "fixed_population_count": len(focus),
        "generated_instance_count": len(generated),
        "premise_checks_failed": len(premise_failures),
        "relation_violations_on_fixed_set": len(relation_violations),
        "relation_violations_by_condition": dict(sorted(by_condition.items())),
        "counterexamples_replayed": replayed,
        "bounded_scope_only": True,
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
                "background_sensitivity": candidate.background_demo(),
                "scope": "ladder-relative, all finite sizes only where a lemma is printed",
                "verdicts": {
                    SHORT[key]: {
                        "holds": value.holds,
                        "proof": value.proof if value.holds else "",
                        "no_witness_reason": value.proof if not value.holds else "",
                        "counterexample": value.counterexample.text()
                        if value.counterexample is not None
                        else None,
                    }
                    for key, value in table.items()
                },
                "driver": driver,
                "weakest_five_all_proved": all(
                    table[key].holds for key in (ED, NE_THESIS, GNEP, VRC, DA_THESIS)
                ),
            }
        )
    return {"scope": "ladder-relative", "candidates": rows}


def main() -> None:
    data = run()
    print("Route B background-sensitive candidate rerun (Q-011)")
    print("Scope: ladder W_-1..W_6; all-size claims are proved lemmas, not bounded scans.")
    for row in data["candidates"]:
        print(f"\nCandidate: {row['candidate']}")
        print(f"  Definition: {row['definition']}")
        print(f"  {row['background_sensitivity']}")
        for condition in ORDER:
            result = row["verdicts"][SHORT[condition]]
            if result["holds"]:
                print(f"  {SHORT[condition]}: proved for all finite sizes (ladder)")
                print(f"    Lemma: {result['proof']}")
            else:
                print(f"  {SHORT[condition]}: fails: audited instance {result['counterexample']}")
                if result["no_witness_reason"]:
                    print(f"    Every witness fails: {result['no_witness_reason']}")
        print(f"  Machine checker: {row['driver']}")
        print(f"  Weakest five all proved: {row['weakest_five_all_proved']}")
    print("\nFinal variant status (a)-(d):")
    print("  (a) NE_2003 + DA_2003: remains without a candidate in this rerun.")
    print("  (b) NE_THESIS + DA_2003: remains without a candidate in this rerun.")
    print("  (c) NE_2003 + DA_THESIS: remains without a candidate in this rerun.")
    print(
        "  (d) ED + NE_THESIS + GNEP + VRC avoidance + DA_THESIS: remains without a candidate in this rerun."
    )
    print(
        "Candidates-in-hand but unproved: none; each displayed exploratory relation has a genuine audited source counterexample."
    )
    print(
        "The fixed-set counts are premise/precondition sanity checks only, never all-size evidence."
    )


if __name__ == "__main__":
    main()
