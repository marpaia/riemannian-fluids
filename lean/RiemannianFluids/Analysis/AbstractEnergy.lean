import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Abstract energy interfaces

The classical Navier--Stokes energy calculation is shorter than the analysis needed to justify it. Formally test the momentum equation against the
velocity `u`. Two terms disappear:

    ⟨grad p,u⟩ = -⟨p,div u⟩ = 0,
    ⟨∇_u u,u⟩ = 0.

The first uses integration by parts and incompressibility. The second uses the skew/transport structure of advection together with incompressibility
and appropriate boundary behavior. What remains is the balance between kinetic energy, viscous dissipation, and forcing.

## Why begin abstractly

An end-to-end analytic theorem would have to specify a manifold, volume form, boundary conditions, function spaces, weak derivatives, and the domains
of unbounded operators before proving either cancellation. None of that should be smuggled into an algebraic proof by suggestive naming. This file
instead states the exact interfaces consumed by the energy calculation.

`ScalarVectorCalculus` contains a divergence/gradient pair and their adjoint relation. `EnergyConservingAdvection` contains the nonlinear operation
and its diagonal energy cancellation on an explicitly supplied incompressible class. These fields are assumptions a future concrete geometric theory
must instantiate; they are not asserted axioms and they do not claim the Sobolev theory is already present.

This abstraction has expository value. It reveals that the later energy identity uses no coordinate formula and no special choice among the competing
viscosity operators. Once the two cancellations are available, the remaining proof is inner-product algebra.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/--
An abstract divergence/gradient pair with the duality required by the energy method. The identity includes all domain and boundary hypotheses.
-/
structure ScalarVectorCalculus where
  /-- Abstract divergence from velocities to scalar constraints. -/
  divergence : V →ₗ[ℝ] Q
  /-- Abstract gradient from scalar pressures to velocity forces. -/
  gradient : Q →ₗ[ℝ] V
  /--
  Integration by parts with all boundary/domain hypotheses already included:
  `⟪grad p,u⟫ = -⟪p,div u⟫`.
  -/
  gradient_divergence_duality : ∀ p u,
    inner ℝ (gradient p) u = -inner ℝ p (divergence u)

/-- Abstract advection equipped with its incompressible energy cancellation. -/
structure EnergyConservingAdvection (incompressible : V → Prop) where
  /-- The bilinear-looking transport operation `(u,v) ↦ ∇_u v`. -/
  advect : V → V → V
  /-- The kinetic-energy cancellation `⟪∇_u u,u⟫ = 0`. -/
  energy_cancel : ∀ u, incompressible u → inner ℝ (advect u u) u = 0

/-- Korn's inequality for a concrete first derivative and deformation operator between normed
spaces.  The lower-order `‖u‖` term is retained for manifolds with Killing fields. -/
def KornInequality
    {Velocity FullGradient SymmetricGradient : Type*}
    [NormedAddCommGroup Velocity] [NormedSpace ℝ Velocity]
    [NormedAddCommGroup FullGradient] [NormedSpace ℝ FullGradient]
    [NormedAddCommGroup SymmetricGradient] [NormedSpace ℝ SymmetricGradient]
    (covariantDerivative : Velocity →L[ℝ] FullGradient)
    (deformation : Velocity →L[ℝ] SymmetricGradient) : Prop :=
  ∃ constant : ℝ, 0 < constant ∧ ∀ velocity,
    ‖covariantDerivative velocity‖ ≤
      constant * (‖deformation velocity‖ + ‖velocity‖)

/-- Gaffney's inequality controlling the first derivative of a form by `d`, `d*`, and its
lower-order norm. -/
def GaffneyInequality
    {Form FullGradient ExteriorDerivative Codifferential : Type*}
    [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    [NormedAddCommGroup FullGradient] [NormedSpace ℝ FullGradient]
    [NormedAddCommGroup ExteriorDerivative] [NormedSpace ℝ ExteriorDerivative]
    [NormedAddCommGroup Codifferential] [NormedSpace ℝ Codifferential]
    (covariantDerivative : Form →L[ℝ] FullGradient)
    (exteriorDerivative : Form →L[ℝ] ExteriorDerivative)
    (codifferential : Form →L[ℝ] Codifferential) : Prop :=
  ∃ constant : ℝ, 0 < constant ∧ ∀ form,
    ‖covariantDerivative form‖ ≤
      constant * (‖exteriorDerivative form‖ + ‖codifferential form‖ + ‖form‖)

/-- Ladyzhenskaya's two-dimensional interpolation inequality, stated for the actual norms supplied
by a function-space realization. -/
def LadyzhenskayaInequality
    {FunctionSpace : Type*}
    (l2Norm h1Norm l4Norm : FunctionSpace → ℝ) : Prop :=
  ∃ constant : ℝ, 0 < constant ∧ ∀ function,
    l4Norm function ^ 2 ≤
      constant * l2Norm function * h1Norm function

end RiemannianFluids
