.PHONY: python/sync python/check lean/sync lean/check lean/statements lean/progress claims/check check

python/sync:
	$(MAKE) -C python sync

python/check:
	$(MAKE) -C python check

lean/sync:
	cd lean && lake update && lake exe cache get

lean/check:
	cd lean && lake build RiemannianFluids
	cd python && uv run --frozen python ../tools/validate_lean.py check
	cd lean && lake env lean RiemannianFluids/AxiomAudit.lean

lean/statements: lean/check

lean/progress: lean/check
	cd python && uv run --frozen python ../tools/validate_lean.py progress

claims/check:
	cd python && uv run --frozen python ../tools/validate_claims.py

check: claims/check python/check lean/check
