import RiemannianFluids.Geometry.Manifolds

/-!
# Covariant calculus interface

This module corresponds to `riemannian_fluids/tensors/calculus.py` in the
executable sibling project.  At the current proof rung it packages only the
global identities used by incompressible energy analysis.  Concrete gradient,
divergence, deformation, and covariant-advection constructions come later.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/--
The divergence and scalar-gradient fragment of Riemannian calculus.

`gradient_divergence_duality` incorporates the integration domain and boundary
conditions required for integration by parts.
-/
structure ScalarVectorCalculus where
  divergence : V →ₗ[ℝ] Q
  gradient : Q →ₗ[ℝ] V
  gradient_divergence_duality : ∀ p u,
    inner ℝ (gradient p) u = -inner ℝ p (divergence u)

/-- Covariant advection with the cancellation used by the energy method. -/
structure EnergyConservingAdvection (incompressible : V → Prop) where
  advect : V → V → V
  energy_cancel : ∀ u, incompressible u → inner ℝ (advect u u) u = 0

end RiemannianFluids

