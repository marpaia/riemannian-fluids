.PHONY: python/sync python/check python/finite-elements/check lean/sync lean/check lean/statements claims/check check

python/sync:
	$(MAKE) -C python sync

python/check:
	$(MAKE) -C python check

python/finite-elements/check:
	$(MAKE) -C python finite-elements/check

lean/sync:
	cd lean && lake update && lake exe cache get

lean/check:
	cd lean && lake build RiemannianFluids
	pixi run --locked lean-contracts-check
	cd lean && lake env lean RiemannianFluids/AxiomAudit.lean

lean/statements: lean/check

claims/check:
	pixi run --locked claims-check

check: claims/check python/check lean/check
