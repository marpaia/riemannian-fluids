import RiemannianFluids

/-!
# Axiom audit for the expository kernel

Formal exposition is useful only if the reader can tell which parts Lean has checked and which parts the theorem merely assumes. A successful
elaboration is not enough: Lean can elaborate a declaration containing an unfinished proof placeholder, whose proof then depends on an unsafe
primitive.

Each command below asks Lean for the logical axioms used by one representative milestone in the argument, in dependency order:

    covariant derivative
      → musical inverse laws
      → scalar gradient and divergence
      → tensor lowering, transpose, and symmetrization
      → Def and codifferential
      → divergence-free correction
      → CCD17 operator identities
      → abstract pressure and energy cancellations.

`make lean/check` executes this file and rejects `sorryAx`. The accepted output consists only of standard Lean/mathlib foundations such as `propext`,
`Classical.choice`, and `Quot.sound`.

This audit does **not** turn explicit hypotheses into proved geometry. For example, `ccd17_divfree_def_hodge` receives the Weitzenböck and
symmetric-gradient identities as arguments. The audit establishes the more precise claim that the conclusion follows from those visible hypotheses
with no hidden project postulate or unfinished proof. That distinction is exactly the formal boundary described in `docs/formal-analysis.md`.
-/

#print axioms RiemannianFluids.LeviCivitaConnection.covariantDerivative_apply
#print axioms RiemannianFluids.sharp_flat
#print axioms RiemannianFluids.flat_sharp
#print axioms RiemannianFluids.gradient_characterization
#print axioms RiemannianFluids.isDivergenceFree_iff_pointwise
#print axioms RiemannianFluids.covariantDerivativeTensor_apply
#print axioms RiemannianFluids.transposeCovariantTwoTensor_apply
#print axioms RiemannianFluids.symmetrizeCovariantTwoTensor_apply
#print axioms RiemannianFluids.deformationTensor_apply
#print axioms RiemannianFluids.deformationTensor_symmetric
#print axioms RiemannianFluids.codifferentialOne_flat
#print axioms RiemannianFluids.exactCodifferentialCorrection_eq_zero_of_divergenceFree
#print axioms RiemannianFluids.ccd17_positive_full
#print axioms RiemannianFluids.ccd17_divfree_def_hodge
#print axioms RiemannianFluids.pressure_work_eq_zero
#print axioms RiemannianFluids.navierStokes_energy_identity
