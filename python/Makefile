.PHONY: sync surface-viscosity thin-shell literature check finite-elements/build finite-elements/check

sync:
	uv sync --frozen --extra dev

surface-viscosity:
	uv run --frozen python -m experiments surface-viscosity

thin-shell:
	uv run --frozen python -m experiments thin-shell

literature:
	uv run --frozen python -m reproductions

check:
	uv run --frozen ruff check .
	uv run --frozen pytest
	uv run --frozen python -m reproductions
	uv run --frozen python -m experiments surface-viscosity --samples 2
	uv run --frozen python -m experiments thin-shell --samples 2

finite-elements/build:
	docker build -f Dockerfile.fenicsx -t riemannian-fluids-fenicsx .

finite-elements/check: finite-elements/build
	docker run --rm riemannian-fluids-fenicsx
