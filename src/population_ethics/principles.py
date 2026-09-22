from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from itertools import product

from population_ethics.domain import ValidationError
from population_ethics.relations import Formula, Implies, conjunction, disjunction, weak


@dataclass(frozen=True, slots=True)
class PrincipleMetadata:
    id: str
    title: str
    description: str
    source_id: str | None = None

    def __post_init__(self) -> None:
        if not self.id or not self.title or not self.description:
            raise ValidationError("principle metadata fields must be non-empty")


@dataclass(frozen=True, slots=True)
class GroundConstraint:
    id: str
    principle_id: str
    formula: Formula
    populations: tuple[str, ...]
    source_locator: str | None
    formalization_id: str
    explanation: str

    def __post_init__(self) -> None:
        if not self.id or not self.principle_id or not self.formalization_id:
            raise ValidationError("ground constraint identifiers must be non-empty")
        if not self.explanation:
            raise ValidationError("ground constraint explanation must be non-empty")
        if not self.populations or any(not population for population in self.populations):
            raise ValidationError("ground constraint populations must be non-empty identifiers")


def _population_ids(populations: Iterable[str]) -> tuple[str, ...]:
    result = tuple(populations)
    if any(not isinstance(population, str) or not population for population in result):
        raise ValidationError("population identifiers must be non-empty strings")
    if len(set(result)) != len(result):
        raise ValidationError("population identifiers must be unique")
    return tuple(sorted(result))


def compile_reflexivity(populations: Iterable[str]) -> tuple[GroundConstraint, ...]:
    return tuple(
        GroundConstraint(
            id=f"reflexivity:{population}",
            principle_id="reflexivity",
            formula=weak(population, population),
            populations=(population,),
            source_locator=None,
            formalization_id="background.reflexivity/v1",
            explanation=f"{population} is weakly at least as good as itself.",
        )
        for population in _population_ids(populations)
    )


def compile_transitivity(populations: Iterable[str]) -> tuple[GroundConstraint, ...]:
    population_ids = _population_ids(populations)
    return tuple(
        GroundConstraint(
            id=f"transitivity:{left}:{middle}:{right}",
            principle_id="transitivity",
            formula=Implies(
                conjunction(weak(left, middle), weak(middle, right)), weak(left, right)
            ),
            populations=(left, middle, right),
            source_locator=None,
            formalization_id="background.transitivity/v1",
            explanation=(
                f"If {left} is weakly at least as good as {middle}, and {middle} is weakly "
                f"at least as good as {right}, then {left} is weakly at least as good as {right}."
            ),
        )
        for left, middle, right in product(population_ids, repeat=3)
    )


def compile_completeness(populations: Iterable[str]) -> tuple[GroundConstraint, ...]:
    population_ids = _population_ids(populations)
    return tuple(
        GroundConstraint(
            id=f"completeness:{left}:{right}",
            principle_id="completeness",
            formula=disjunction(weak(left, right), weak(right, left)),
            populations=(left, right),
            source_locator=None,
            formalization_id="background.completeness/v1",
            explanation=f"Either {left} is weakly at least as good as {right}, or conversely.",
        )
        for index, left in enumerate(population_ids)
        for right in population_ids[index + 1 :]
    )
