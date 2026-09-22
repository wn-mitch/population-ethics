from fractions import Fraction

from population_ethics.domain import Population, ValidationError


def total(population: Population) -> Fraction:
    return Fraction(sum(population))


def average(population: Population) -> Fraction:
    if not population:
        raise ValidationError("average welfare is undefined for the empty population")
    return Fraction(sum(population), len(population))


def critical_level(population: Population, critical_level: Fraction) -> Fraction:
    return sum((Fraction(welfare) - critical_level for welfare in population), start=Fraction())
