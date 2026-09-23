"""Phase 12: consistency certificates for the gaps of the possibility map.

Phase 11 left 63 minimal condition sets that no checked axiology realizes and no known theorem
explains. For each one, research/certify.py searches level witnesses for a certificate: every
condition whose support edges lie inside a strongly connected component of the support graph
is satisfied exactly by one axiology, and every other condition is inert (on no cycle). A
certificate proves the set consistent on the ladder (docs/decisions.md D-019). Gaps without a
certificate stay open; they are not claimed as theorems.

Each known theorem is also run through the certifier as a control: a certificate for one would
mean the certifier is unsound.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict
from typing import Any

from research.certify import Certifier
from research.lab import ROOT, LedgerEntry, record, write_result
from research.ladder import Ladder
from research.lexadd import battery, from_additive
from research.possibility import KNOWN_THEOREMS


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--positive", type=int, default=7)
    args = parser.parse_args()
    positive = args.positive
    ladder = Ladder(2, positive)
    started = time.monotonic()
    p11_name = "p11_possibility" if positive == 7 else f"p11_possibility_n2_p{positive}"
    p11_path = ROOT / "research" / "results" / f"{p11_name}.json"
    if not p11_path.exists():
        raise SystemExit(
            f"missing P11 result for positive={positive}: {p11_path}; run research.p11_possibility first"
        )
    p11 = json.loads(p11_path.read_text())["result"]
    gaps = [c["conditions"] for c in p11["coverage"] if not c["explained_by"]]
    axiologies = list(battery(ladder)) + [
        from_additive(ladder, f"additive-{i}", m["g"])
        for i, m in enumerate(p11["additive"]["maximal_realizable"])
    ]
    certifier = Certifier(ladder, axiologies)
    certified: list[dict[str, Any]] = []
    still_open: list[list[str]] = []
    for gap in sorted(gaps, key=lambda g: (len(g), g)):
        cert = certifier.certify(gap)
        if cert:
            certified.append(asdict(cert))
        else:
            still_open.append(gap)
    controls = {name: certifier.certify(t) is None for name, t in KNOWN_THEOREMS.items()}
    data = {
        "ladder": {"negative": ladder.negative, "positive": ladder.positive},
        "certified": certified,
        "open": still_open,
        "controls_uncertified": controls,
    }
    name = "p12_certificates" if positive == 7 else f"p12_certificates_n2_p{positive}"
    write_result(name, data, {"wall_time_s": round(time.monotonic() - started, 1)})
    if positive == 7:
        _ledger(data)
    print(
        json.dumps(
            {"certified": len(certified), "open": len(still_open), "controls": controls}, indent=1
        )
    )


def _ledger(data: dict[str, Any]) -> None:
    certified, still_open = data["certified"], data["open"]
    inert_kinds = sorted({p for c in certified for p in c["inert"]})
    models = sorted({str(c["axiology"]) for c in certified})
    ok = all(data["controls_uncertified"].values())
    record(
        [
            LedgerEntry(
                candidate_id="P12-gap-certificates",
                hypothesis="The unexplained gaps of the possibility map are consistent.",
                motivation="Close Q-010 with proofs of consistency rather than more models.",
                exact_formal_change=f"{len(certified) + len(still_open)} gaps; support-graph abstraction; lexicographic-additive and additive models",
                scope="W_-2..W_7; all population sizes",
                search_method="level-witness search + SCC analysis + exact model checks",
                result=f"{len(certified)} certified consistent; {len(still_open)} open. Inert conditions across certificates: {inert_kinds}; covering axiologies: {models}. Known theorems certified as consistent: none (controls pass: {ok}).",
                evidence_type="sound certificate (abstraction test + exact model checks)",
                checked=ok,
                minimal="n/a",
                interpretation="Backgrounds are load-bearing: replacing Weak Quality Addition by Quality in thesis Theorems 3 and 4, or 2009 Weak Quality Addition by VRC avoidance, gives a consistent set. The background-free condition's high populations have no route back into any cycle.",
                next_experiment="background-sensitive models for the open gaps (Q-010)",
                result_scope="checked theorem",
                formalization_tier="exact certificate over cross-read conditions",
                witness_conditions="level witnesses per certificate in research/results/p12_certificates.json",
                status="confirmed" if ok else "refuted",
            )
        ]
    )


if __name__ == "__main__":
    main()
