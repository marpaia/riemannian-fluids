.PHONY: sync surface-viscosity surface-stokes navier-stokes thin-shell resolved-shell wall-selection literature check finite-elements/check finite-elements/check/mpi finite-elements/build/docker finite-elements/check/docker

PIXI_MANIFEST := ../pixi.toml

sync:
	pixi install --manifest-path $(PIXI_MANIFEST) --locked

surface-viscosity:
	pixi run --manifest-path $(PIXI_MANIFEST) --locked surface-viscosity

surface-stokes:
	pixi run --manifest-path $(PIXI_MANIFEST) --locked surface-stokes

navier-stokes:
	pixi run --manifest-path $(PIXI_MANIFEST) --locked navier-stokes

thin-shell:
	pixi run --manifest-path $(PIXI_MANIFEST) --locked thin-shell

resolved-shell:
	pixi run --manifest-path $(PIXI_MANIFEST) --locked resolved-shell

wall-selection:
	pixi run --manifest-path $(PIXI_MANIFEST) --locked wall-selection

literature:
	pixi run --manifest-path $(PIXI_MANIFEST) --locked literature

check:
	pixi run --manifest-path $(PIXI_MANIFEST) --locked check

finite-elements/check:
	pixi run --manifest-path $(PIXI_MANIFEST) --locked fenicsx-check

finite-elements/check/mpi:
	pixi run --manifest-path $(PIXI_MANIFEST) --locked finite-elements-mpi

finite-elements/build/docker:
	docker build -f Dockerfile.fenicsx -t riemannian-fluids-fenicsx ..

finite-elements/check/docker: finite-elements/build/docker
	docker run --rm riemannian-fluids-fenicsx
