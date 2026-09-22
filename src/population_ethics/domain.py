from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from itertools import combinations_with_replacement
from math import comb
from types import MappingProxyType
from typing import cast

type Population = tuple[int, ...]


class ValidationError(ValueError):
    """Input violates a declared experiment invariant."""


def _integer(value: object, *, field_name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValidationError(f"{field_name} must be an integer, got {value!r}")
    return value


def canonical_population(values: Iterable[int]) -> Population:
    checked = tuple(_integer(value, field_name="welfare") for value in values)
    return tuple(sorted(checked))


@dataclass(frozen=True, slots=True)
class PopulationGroup:
    welfare: int
    count: int

    def __post_init__(self) -> None:
        _integer(self.welfare, field_name="welfare")
        count = _integer(self.count, field_name="count")
        if count <= 0:
            raise ValidationError(f"count must be positive, got {count}")


type PopulationInput = Sequence[int] | PopulationGroup | Sequence[PopulationGroup]


def population_size(value: PopulationInput) -> int:
    if isinstance(value, PopulationGroup):
        return value.count
    if all(isinstance(item, PopulationGroup) for item in value):
        return sum(item.count for item in cast(Sequence[PopulationGroup], value))
    if any(isinstance(item, PopulationGroup) for item in value):
        raise ValidationError("population cannot mix welfare integers and compact groups")
    return len(value)


def expand_population(value: PopulationInput) -> Population:
    if isinstance(value, PopulationGroup):
        return (value.welfare,) * value.count
    if all(isinstance(item, PopulationGroup) for item in value):
        return canonical_population(
            welfare
            for item in value
            for welfare in (item.welfare,) * item.count  # type: ignore[union-attr]
        )
    if any(isinstance(item, PopulationGroup) for item in value):
        raise ValidationError("population cannot mix welfare integers and compact groups")
    return canonical_population(cast(Sequence[int], value))


def parse_population(value: object) -> PopulationInput:
    if isinstance(value, Mapping):
        return _parse_group(value)
    if not isinstance(value, list):
        raise ValidationError("population must be an integer list or compact welfare/count groups")
    if all(isinstance(item, Mapping) for item in value):
        return tuple(_parse_group(item) for item in value)
    if any(isinstance(item, Mapping) for item in value):
        raise ValidationError("population cannot mix welfare integers and compact groups")
    return tuple(_integer(item, field_name="welfare") for item in value)


def _parse_group(value: Mapping[object, object]) -> PopulationGroup:
    if set(value) != {"welfare", "count"}:
        raise ValidationError("compact population group requires exactly welfare and count")
    return PopulationGroup(
        welfare=_integer(value["welfare"], field_name="welfare"),
        count=_integer(value["count"], field_name="count"),
    )


@dataclass(frozen=True, slots=True)
class WelfareCategories:
    values: Mapping[str, frozenset[int]]
    disjoint: bool = True

    def __post_init__(self) -> None:
        normalized: dict[str, frozenset[int]] = {}
        seen: dict[int, str] = {}
        for name, members in self.values.items():
            if not isinstance(name, str) or not name:
                raise ValidationError("category names must be non-empty strings")
            checked = frozenset(_integer(value, field_name=f"category {name}") for value in members)
            if not checked:
                raise ValidationError(f"category {name!r} must not be empty")
            if self.disjoint:
                for member in checked:
                    if member in seen:
                        raise ValidationError(
                            f"welfare {member} overlaps categories {seen[member]!r} and {name!r}"
                        )
                    seen[member] = name
            normalized[name] = checked
        object.__setattr__(self, "values", MappingProxyType(normalized))

    def contains(self, category: str, welfare: int) -> bool:
        try:
            return welfare in self.values[category]
        except KeyError as error:
            raise ValidationError(f"unknown welfare category {category!r}") from error


@dataclass(frozen=True, slots=True)
class GeneratedDomainSpec:
    welfare_levels: tuple[int, ...]
    max_population_size: int

    def __post_init__(self) -> None:
        levels = tuple(_integer(value, field_name="welfare level") for value in self.welfare_levels)
        if not levels:
            raise ValidationError("generated welfare levels must not be empty")
        if len(set(levels)) != len(levels):
            raise ValidationError("generated welfare levels must be unique")
        bound = _integer(self.max_population_size, field_name="max_population_size")
        if bound < 0:
            raise ValidationError("max_population_size must not be negative")
        object.__setattr__(self, "welfare_levels", tuple(sorted(levels)))


@dataclass(frozen=True, slots=True)
class NamedPopulation:
    name: str
    values: PopulationInput
    parts: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise ValidationError("population name must be a non-empty string")
        if any(not isinstance(part, str) or not part for part in self.parts):
            raise ValidationError(f"population {self.name!r} has an invalid composite part")


@dataclass(frozen=True, slots=True)
class ExplicitDomainSpec:
    populations: tuple[NamedPopulation, ...]

    def __post_init__(self) -> None:
        names = [entry.name for entry in self.populations]
        duplicate = next((name for name in names if names.count(name) > 1), None)
        if duplicate is not None:
            raise ValidationError(f"duplicate explicit population name {duplicate!r}")


@dataclass(frozen=True, slots=True)
class ResourcePolicy:
    max_populations: int = 10_000
    max_expanded_lives: int = 1_000_000
    max_relation_atoms: int = 1_000_000
    max_ground_constraints: int = 1_000_000
    max_subsets: int = 65_536
    timeout_ms: int = 10_000

    def __post_init__(self) -> None:
        for name in (
            "max_populations",
            "max_expanded_lives",
            "max_relation_atoms",
            "max_ground_constraints",
            "max_subsets",
            "timeout_ms",
        ):
            value = _integer(getattr(self, name), field_name=name)
            if value < 0:
                raise ValidationError(f"{name} must not be negative")

    def preflight(self, usage: ResourceUsage) -> None:
        limits = {
            "populations": self.max_populations,
            "expanded_lives": self.max_expanded_lives,
            "relation_atoms": self.max_relation_atoms,
            "ground_constraints": self.max_ground_constraints,
            "subsets": self.max_subsets,
        }
        prospective = {
            "populations": usage.populations,
            "expanded_lives": usage.expanded_lives,
            "relation_atoms": usage.relation_atoms,
            "ground_constraints": usage.ground_constraints,
            "subsets": usage.subsets,
        }
        exceeded = [
            f"{name}={prospective[name]} exceeds max_{name}={limit}"
            for name, limit in limits.items()
            if prospective[name] > limit
        ]
        if exceeded:
            raise ValidationError("resource preflight failed: " + "; ".join(exceeded))


@dataclass(frozen=True, slots=True)
class ResourceUsage:
    populations: int
    expanded_lives: int
    relation_atoms: int = 0
    ground_constraints: int = 0
    subsets: int = 0


@dataclass(frozen=True, slots=True)
class PopulationUniverse:
    populations: tuple[Population, ...]
    names: Mapping[str, Population]
    aliases: Mapping[Population, tuple[str, ...]]
    usage: ResourceUsage

    def __post_init__(self) -> None:
        expected = tuple(
            sorted(set(self.populations), key=lambda population: (len(population), population))
        )
        if self.populations != expected:
            raise ValidationError("population universe is not canonical")
        object.__setattr__(self, "names", MappingProxyType(dict(self.names)))
        object.__setattr__(self, "aliases", MappingProxyType(dict(self.aliases)))


def prospective_usage(
    spec: GeneratedDomainSpec | ExplicitDomainSpec,
    *,
    relation_atoms: int = 0,
    ground_constraints: int = 0,
    subsets: int = 0,
) -> ResourceUsage:
    relation_atoms = _integer(relation_atoms, field_name="relation_atoms")
    ground_constraints = _integer(ground_constraints, field_name="ground_constraints")
    subsets = _integer(subsets, field_name="subsets")
    if min(relation_atoms, ground_constraints, subsets) < 0:
        raise ValidationError("prospective resource counts must not be negative")
    if isinstance(spec, GeneratedDomainSpec):
        level_count = len(spec.welfare_levels)
        populations = sum(
            comb(level_count + size - 1, size) for size in range(spec.max_population_size + 1)
        )
        expanded_lives = sum(
            size * comb(level_count + size - 1, size)
            for size in range(spec.max_population_size + 1)
        )
    else:
        populations = len(spec.populations)
        expanded_lives = sum(population_size(entry.values) for entry in spec.populations)
    return ResourceUsage(
        populations=populations,
        expanded_lives=expanded_lives,
        relation_atoms=relation_atoms,
        ground_constraints=ground_constraints,
        subsets=subsets,
    )


def build_population_universe(
    spec: GeneratedDomainSpec | ExplicitDomainSpec,
    policy: ResourcePolicy,
    *,
    relation_atoms: int = 0,
    ground_constraints: int = 0,
    subsets: int = 0,
) -> PopulationUniverse:
    usage = prospective_usage(
        spec,
        relation_atoms=relation_atoms,
        ground_constraints=ground_constraints,
        subsets=subsets,
    )
    policy.preflight(usage)
    if isinstance(spec, GeneratedDomainSpec):
        populations = tuple(
            tuple(population)
            for size in range(spec.max_population_size + 1)
            for population in combinations_with_replacement(spec.welfare_levels, size)
        )
        return PopulationUniverse(populations, {}, {}, usage)

    names = {entry.name: expand_population(entry.values) for entry in spec.populations}
    for entry in spec.populations:
        if not entry.parts:
            continue
        try:
            combined = canonical_population(value for part in entry.parts for value in names[part])
        except KeyError as error:
            raise ValidationError(
                f"population {entry.name!r} references unknown part {error.args[0]!r}"
            ) from error
        if names[entry.name] != combined:
            raise ValidationError(
                f"population {entry.name!r} does not concatenate declared parts {entry.parts!r}"
            )

    aliases: dict[Population, list[str]] = {}
    for name, population in names.items():
        aliases.setdefault(population, []).append(name)
    ordered = tuple(sorted(aliases, key=lambda population: (len(population), population)))
    frozen_aliases = {
        population: tuple(sorted(source_names)) for population, source_names in aliases.items()
    }
    return PopulationUniverse(ordered, names, frozen_aliases, usage)
