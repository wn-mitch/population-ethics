"""Download source PDFs into the gitignored corpus/cache/ and verify them against their hashes.

A work is fetchable when ``corpus/literature.toml`` or ``corpus/sources.toml`` gives both a
``pdf_url`` and a ``pdf_sha256`` for it. A cached file whose hash matches is kept; a mismatch,
from the cache or from the network, is an error and the bad bytes are not kept.

Usage: ``python -m research.fetch [work-id ...]`` (all fetchable works when none are given).
"""

from __future__ import annotations

import hashlib
import sys
import tomllib
import urllib.request
from pathlib import Path

from research.lab import ROOT

CACHE = ROOT / "corpus" / "cache"
# sources.toml ids that differ from their literature.toml work ids.
SOURCE_ALIASES = {
    "arrhenius-2000": "arrhenius-2000-ep",
    "arrhenius-1999": "arrhenius-1999-weak-ordering",
}


def fetchable() -> dict[str, tuple[str, str]]:
    """Work id -> (pdf_url, pdf_sha256) for every work with both fields."""
    found: dict[str, tuple[str, str]] = {}
    literature = tomllib.loads((ROOT / "corpus" / "literature.toml").read_text())["works"]
    sources = tomllib.loads((ROOT / "corpus" / "sources.toml").read_text())["sources"]
    records = [(w["id"], w) for w in literature] + [
        (SOURCE_ALIASES.get(s["id"], s["id"]), s) for s in sources
    ]
    for work_id, record in records:
        if "pdf_url" not in record or "pdf_sha256" not in record:
            continue
        entry = (record["pdf_url"], record["pdf_sha256"])
        if found.setdefault(work_id, entry)[1] != entry[1]:
            raise ValueError(f"{work_id}: conflicting pdf_sha256 between corpus files")
    return found


def cached_path(work_id: str) -> Path:
    return CACHE / f"{work_id}.pdf"


def fetch(work_id: str, url: str, sha256: str) -> Path:
    path = cached_path(work_id)
    if path.exists():
        if hashlib.sha256(path.read_bytes()).hexdigest() == sha256:
            return path
        raise ValueError(f"{work_id}: cached file does not match pdf_sha256; delete {path}")
    request = urllib.request.Request(url, headers={"User-Agent": "population-ethics-lab"})
    with urllib.request.urlopen(request, timeout=60) as response:
        data = response.read()
    digest = hashlib.sha256(data).hexdigest()
    if digest != sha256:
        raise ValueError(f"{work_id}: downloaded bytes hash to {digest}, expected {sha256}")
    CACHE.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return path


def main(argv: list[str]) -> int:
    works = fetchable()
    wanted = argv or sorted(works)
    unknown = [w for w in wanted if w not in works]
    if unknown:
        print(f"not fetchable (no pdf_url and pdf_sha256): {', '.join(unknown)}", file=sys.stderr)
        return 2
    failures = 0
    for work_id in wanted:
        try:
            print(f"ok  {fetch(work_id, *works[work_id]).relative_to(ROOT)}")
        except (OSError, ValueError) as error:
            failures += 1
            print(f"err {work_id}: {error}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
