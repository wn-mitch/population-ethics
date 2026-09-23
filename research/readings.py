"""The review-first gate: source readings of principles, from corpus/readings.toml.

A principle may enter instance generation or the known-ground catalogue only when its reading
is at least ``agent-cross-read``: one agent transcribed the source and a second agent, reading
the same source cold, agreed (docs/decisions.md D-010). ``human-reviewed`` is the stronger
state. Anything else, or a missing reading, is rejected.
"""

from __future__ import annotations

import tomllib
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import Any

from research.lab import ROOT

READINGS_PATH = ROOT / "corpus" / "readings.toml"
STATES = ("agent-read", "agent-cross-read", "human-reviewed")
REVIEWED = frozenset({"agent-cross-read", "human-reviewed"})
REQUIRED = (
    "principle",
    "work",
    "printed_page",
    "name",
    "excerpt",
    "formal_reading",
    "deviations",
    "reader",
    "cross_reader",
    "cross_verdict",
    "review_state",
)


class UnreviewedPrinciple(ValueError):
    """A principle was used before its reading passed the review-first gate."""


@dataclass(frozen=True)
class Reading:
    principle: str
    work: str
    printed_page: str
    name: str
    excerpt: str
    formal_reading: str
    deviations: str
    reader: str
    cross_reader: str
    cross_verdict: str
    review_state: str
    extra: Mapping[str, Any]


def parse(data: Mapping[str, Any]) -> dict[str, Reading]:
    readings: dict[str, Reading] = {}
    for raw in data.get("readings", ()):
        missing = [k for k in REQUIRED if k not in raw]
        if missing:
            raise ValueError(f"reading {raw.get('principle', '?')} lacks {', '.join(missing)}")
        if raw["review_state"] not in STATES:
            raise ValueError(f"{raw['principle']}: unknown review_state {raw['review_state']}")
        if raw["principle"] in readings:
            raise ValueError(f"{raw['principle']}: two readings")
        if raw["review_state"] in REVIEWED and raw["cross_verdict"] != "agree":
            raise ValueError(f"{raw['principle']}: reviewed state without cross-reader agreement")
        extra = {k: v for k, v in raw.items() if k not in REQUIRED}
        readings[raw["principle"]] = Reading(**{k: raw[k] for k in REQUIRED}, extra=extra)
    return readings


@cache
def load(path: Path = READINGS_PATH) -> dict[str, Reading]:
    return parse(tomllib.loads(path.read_text()))


def require_reviewed(
    principles: Iterable[str], readings: Mapping[str, Reading] | None = None
) -> None:
    """Raise UnreviewedPrinciple unless every principle has a reviewed reading."""
    table = load() if readings is None else readings
    bad = sorted(
        p for p in set(principles) if p not in table or table[p].review_state not in REVIEWED
    )
    if bad:
        states = ", ".join(
            f"{p} ({table[p].review_state if p in table else 'no reading'})" for p in bad
        )
        raise UnreviewedPrinciple(f"principles not past the review-first gate: {states}")
