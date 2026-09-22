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
