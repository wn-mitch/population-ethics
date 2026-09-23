test:
    uv run pytest

lint:
    uv run ruff format --check .
    uv run ruff check .

typecheck:
    uv run mypy src tests research

check:
    uv run ruff format --check .
    uv run ruff check .
    uv run mypy src tests research
    uv run pytest

# Rerun every breakthrough-search phase; each writes research/results/pN_*.json.
research:
    uv run python -m research.p0_baseline
    uv run python -m research.p1_frontier
    uv run python -m research.p2_escape
    uv run python -m research.p3_witness
    uv run python -m research.p4_mutations
    uv run python -m research.p5_sat_structure
    uv run python -m research.p6_schema
    uv run python -m research.p7_arrhenius1999
    uv run python -m research.p8_catalogue
    uv run python -m research.p9_census
    uv run python -m research.p10_witness_families
    uv run python -m research.p11_possibility
    uv run python -m research.p12_certificates
    uv run python -m research.p13_bounce
    uv run python -m research.p14_gnep_theorem_3
    uv run python -m research.p15_dominance_addition
    uv run python -m research.p16_ne_top
    uv run python -m research.render_ledger

# Regenerate docs/results.md from the ledger and literature verdicts.
docs:
    uv run python -m research.render_ledger

# Download source PDFs into corpus/cache/ and verify their hashes.
fetch-sources *works:
    uv run python -m research.fetch {{works}}
