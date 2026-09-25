"""Render research/ledger.json and the literature verdicts as the docs/results.md register.

``docs/results.md`` is a short generated index. The full named-collision table is generated at
``docs/results/named.md``; the ledger rows are split by phase into ``docs/results/ledger-early.md``
(C/M mutations and P0-P9) and ``docs/results/ledger-later.md`` (P10 onward). The literature
verdict of a result (corpus/literature.toml ``[[collisions]]``) overrides the solver-side
``novelty_status`` of every ledger row it lists. ``render_pages()`` returns every generated page
keyed by path; ``--check`` exits non-zero when any generated file on disk differs from a fresh
render.
"""

from __future__ import annotations

import json
import re
import sys
import tomllib
from itertools import product
from pathlib import Path
from typing import Any

from research.lab import LEDGER_PATH, ROOT

RESULTS = ROOT / "docs" / "results.md"
NAMED = ROOT / "docs" / "results" / "named.md"
LEDGER_EARLY = ROOT / "docs" / "results" / "ledger-early.md"
LEDGER_LATER = ROOT / "docs" / "results" / "ledger-later.md"
LITERATURE = ROOT / "corpus" / "literature.toml"
JOURNAL = "journal/2026-09-22-turn-1.md"

_LEDGER_HEADER = [
    "| candidate | status | scope label | tier | novelty | result |",
    "|---|---|---|---|---|---|",
]


def _cell(text: str, limit: int | None = None) -> str:
    text = text.replace("|", "/").replace("\n", " ")
    if limit is not None and len(text) > limit:
        text = text[: limit - 3] + "..."
    return text


def _models(formula: str) -> frozenset[tuple[bool, bool]]:
    """Two-population preorder states satisfying a directed source claim."""
    match = re.fullmatch(r"(¬\()?([XY]) (⪰|≻) ([XY])(\))?", formula)
    if not match or bool(match[1]) != bool(match[5]) or match[2] == match[4]:
        raise ValueError(f"invalid directed formula {formula!r}")
    result = set()
    for xy, yx in product((False, True), repeat=2):
        forward = xy if match[2] == "X" else yx
        backward = yx if match[2] == "X" else xy
        holds = forward if match[3] == "⪰" else forward and not backward
        if holds != bool(match[1]):
            result.add((xy, yx))
    return frozenset(result)


def validate_literature(corpus: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Reject unchecked or directionally inconsistent literature comparisons."""
    if corpus.get("schema") != "population-ethics.literature/v2":
        raise ValueError("literature corpus needs source certificates (v2)")
    works = {w["id"]: w for w in corpus["works"]}
    claims: dict[str, dict[str, Any]] = {}
    for claim in corpus["source_claims"]:
        name = claim["id"]
        if name in claims:
            raise ValueError(f"duplicate source claim {name}")
        work = works.get(claim["work"])
        if work is None or work["read"] not in {"firsthand", "partial"}:
            raise ValueError(f"{name}: source must have been read firsthand or in part")
        for key in ("printed_page", "excerpt", "X", "Y", "reader", "cross_reader"):
            if not isinstance(claim.get(key), str) or not claim[key].strip():
                raise ValueError(f"{name}: missing {key}")
        if claim["reader"] == claim["cross_reader"] or claim.get("cross_verdict") != "agree":
            raise ValueError(f"{name}: source comparison lacks independent agreement")
        _models(claim["formula"])
        claims[name] = claim

    used: set[str] = set()
    for collision in corpus["collisions"]:
        name = collision["result"]
        directional = collision.get("directional")
        if not isinstance(directional, bool):
            raise ValueError(f"{name}: classify directional source comparison")
        comparisons = collision.get("comparisons", [])
        if directional != bool(comparisons):
            raise ValueError(f"{name}: directional comparison needs a source certificate")
        if not directional and re.search(
            r"[⪰≻]|(?:not )?at least as good|not worse|not better",
            collision["known"],
            re.IGNORECASE,
        ):
            raise ValueError(f"{name}: directional claim is marked non-directional")
        matched = False
        for comparison in comparisons:
            source = comparison["source_claim"]
            if source not in claims or claims[source]["work"] not in collision["sources"]:
                raise ValueError(f"{name}: unknown or unlisted source claim {source}")
            used.add(source)
            left = _models(claims[source]["formula"])
            right = _models(comparison["project_formula"])
            actual = (
                "same" if left == right else "contradicts" if left.isdisjoint(right) else "overlaps"
            )
            if comparison.get("relationship") != actual:
                raise ValueError(
                    f"{name}: {source} comparison is {actual}, not {comparison.get('relationship')}"
                )
            if (
                not isinstance(comparison.get("premises_match"), bool)
                or not comparison.get("premise_comparison", "").strip()
            ):
                raise ValueError(f"{name}: compare domain, witness and premise dependencies")
            matched |= comparison["premises_match"] and actual in {"same", "contradicts"}
        if collision["verdict"] == "collides" and not matched:
            raise ValueError(f"{name}: collision requires a matching-premise source comparison")
    if used != set(claims):
        raise ValueError(f"unreferenced source claims: {sorted(set(claims) - used)}")
    return claims


def _load() -> tuple[
    list[dict[str, Any]], list[dict[str, Any]], dict[str, str], dict[str, dict[str, Any]]
]:
    entries = json.loads(LEDGER_PATH.read_text())["entries"]
    corpus = tomllib.loads(LITERATURE.read_text())
    claims = validate_literature(corpus)
    collisions = corpus["collisions"]
    known = {e["candidate_id"] for e in entries}
    verdict_of: dict[str, str] = {}
    for c in collisions:
        for candidate in c["ledger"]:
            if candidate not in known:
                raise ValueError(f"{c['result']} lists unknown ledger row {candidate}")
            if candidate in verdict_of:
                raise ValueError(f"{candidate} is listed by two results")
            verdict_of[candidate] = f"{c['result']}: {c['verdict']}"
    return entries, collisions, verdict_of, claims


def is_later_phase(candidate_id: str) -> bool:
    """A ledger row belongs to the later page when its phase is P10 or above."""
    token = candidate_id.split("-", 1)[0]
    return token.startswith("P") and token[1:].isdigit() and int(token[1:]) >= 10


def _named_rows(collisions: list[dict[str, Any]], claims: dict[str, dict[str, Any]]) -> list[str]:
    rows = ["| result | verdict | ledger rows | known | open |", "|---|---|---|---|---|"]
    rows += [
        f"| {c['result']} | {c['verdict']} | {', '.join(c['ledger'])} | "
        f"{_cell(c['known'])} | {_cell(c['open'])} |"
        for c in collisions
    ]
    rows += ["", "## Cross-read source passages", ""]
    for name, source in claims.items():
        rows += [
            f"### {name}",
            "",
            f"{source['work']}, p. {source['printed_page']}: “{source['excerpt']}”",
            "",
            f"X = {source['X']}; Y = {source['Y']}. Formula: `{source['formula']}`.",
            "",
        ]
        if source.get("ambiguity"):
            rows += [f"Source ambiguity: {source['ambiguity']}", ""]
    rows += ["## Result comparisons", ""]
    for collision in collisions:
        if not collision.get("comparisons"):
            continue
        rows += [f"### {collision['result']}", ""]
        for comparison in collision["comparisons"]:
            rows += [
                f"- `{comparison['source_claim']}`: source "
                f"`{claims[comparison['source_claim']]['formula']}`; project "
                f"`{comparison['project_formula']}` ({comparison['relationship']}). "
                f"Premises match: {comparison['premises_match']}. "
                f"{comparison['premise_comparison']}",
            ]
        rows.append("")
    return rows


def _ledger_rows(entries: list[dict[str, Any]], verdict_of: dict[str, str]) -> list[str]:
    rows = []
    for e in entries:
        novelty = _cell(verdict_of.get(e["candidate_id"], e["novelty_status"]))
        rows.append(
            f"| {e['candidate_id']} | {e['status']} | {e['result_scope']} | "
            f"{e['formalization_tier']} | {novelty} | {_cell(e['result'], 220)} |"
        )
    return rows


def _detail(title: str, intro: str, table: list[str]) -> str:
    lines = [
        f"# {title}",
        "",
        "Generated by `just docs` from `research/ledger.json` and `corpus/literature.toml`.",
        "Do not edit by hand. Part of the [results register](../results.md).",
        "",
        intro,
        "",
    ]
    return "\n".join(lines + table) + "\n"


def render_pages() -> dict[Path, str]:
    entries, collisions, verdict_of, claims = _load()
    early = [e for e in entries if not is_later_phase(e["candidate_id"])]
    later = [e for e in entries if is_later_phase(e["candidate_id"])]
    index = [
        "# Results register",
        "",
        "Generated by `just docs` from `research/ledger.json` and `corpus/literature.toml`.",
        "Do not edit by hand. The R-numbered results are written up in",
        f"[{JOURNAL}]({JOURNAL}).",
        "",
        "## Named results",
        "",
        f"[results/named.md](results/named.md) holds the collision table: {len(collisions)} "
        f"named results over the {len(entries)} ledger rows below.",
        "",
        "## Ledger",
        "",
        "Novelty is the literature verdict where one exists, otherwise the solver-side status.",
        f"The rows are split by phase: [results/ledger-early.md](results/ledger-early.md) "
        f"(C/M mutations and P0-P9, {len(early)} rows) and "
        f"[results/ledger-later.md](results/ledger-later.md) (P10 onward, {len(later)} rows).",
    ]
    return {
        RESULTS: "\n".join(index) + "\n",
        NAMED: _detail(
            "Named results",
            "Literature collisions and their verdicts.",
            _named_rows(collisions, claims),
        ),
        LEDGER_EARLY: _detail(
            "Ledger: C/M mutations and P0-P9",
            "Novelty is the literature verdict where one exists, otherwise the solver-side status.",
            _LEDGER_HEADER + _ledger_rows(early, verdict_of),
        ),
        LEDGER_LATER: _detail(
            "Ledger: P10 onward",
            "Novelty is the literature verdict where one exists, otherwise the solver-side status.",
            _LEDGER_HEADER + _ledger_rows(later, verdict_of),
        ),
    }


def main(argv: list[str]) -> int:
    pages = render_pages()
    if "--check" in argv:
        stale = [p for p, text in pages.items() if not p.exists() or p.read_text() != text]
        for path in stale:
            print(f"{path.relative_to(ROOT)} is stale; run `just docs`", file=sys.stderr)
        return 1 if stale else 0
    for path, text in pages.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
