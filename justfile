test:
    uv run pytest

lint:
    uv run ruff format --check .
    uv run ruff check .

typecheck:
    uv run mypy src tests

check:
    uv run ruff format --check .
    uv run ruff check .
    uv run mypy src tests
    uv run pytest
