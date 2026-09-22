"""Render research/ledger.json as the human-readable ledger table inside REPORT.md."""

from __future__ import annotations

import json

from research.lab import LEDGER_PATH, ROOT

REPORT = ROOT / "research" / "REPORT.md"
START, END = "<!-- ledger:start -->", "<!-- ledger:end -->"


def main() -> None:
    entries = json.loads(LEDGER_PATH.read_text())["entries"]
    rows = [
        "| candidate | status | scope label | tier | result |",
        "|---|---|---|---|---|",
    ]
    for e in entries:
        result = e["result"].replace("|", "/").replace("\n", " ")
        if len(result) > 220:
            result = result[:217] + "..."
        rows.append(
            f"| {e['candidate_id']} | {e['status']} | {e['result_scope']} | "
            f"{e['formalization_tier']} | {result} |"
        )
    text = REPORT.read_text()
    head, rest = text.split(START, 1)
    _, tail = rest.split(END, 1)
    REPORT.write_text(head + START + "\n" + "\n".join(rows) + "\n" + END + tail)


if __name__ == "__main__":
    main()
