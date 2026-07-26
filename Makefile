.PHONY: python/sync python/check lean/sync lean/check claims/check check

python/sync:
	$(MAKE) -C python sync

python/check:
	$(MAKE) -C python check

lean/sync:
	cd lean && lake update && lake exe cache get

lean/check:
	cd lean && lake --wfail build RiemannianFluids
	@if rg -n '\b(sorry|admit|axiom)\b' lean/RiemannianFluids.lean lean/RiemannianFluids -g '*.lean'; then \
		echo 'Lean placeholder audit failed'; exit 1; \
	fi

claims/check:
	cd python && uv run --frozen python ../tools/validate_claims.py

check: claims/check python/check lean/check

