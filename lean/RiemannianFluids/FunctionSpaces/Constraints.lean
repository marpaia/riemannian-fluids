import RiemannianFluids.Analysis.AbstractEnergy

/-!
# Incompressibility and pressure constraints

Incompressibility is the constraint

    div u = 0.

Its most immediate analytical consequence is that pressure performs no work:

    ⟨grad p,u⟩
      = -⟨p,div u⟩          by integration by parts,
      = 0                       by incompressibility.

The proof below is precisely these two lines. `rw` invokes the duality stored in `ScalarVectorCalculus`; unfolding `IsIncompressible` exposes `div u =
0`; and simplification evaluates the inner product with the zero scalar field.

## The current level of abstraction

`V` and `Q` are arbitrary real inner-product spaces. They should eventually be instantiated by velocity and pressure spaces with the correct manifold,
regularity, boundary, and gauge conditions. The present theorem records only the algebra those spaces must support. It is therefore the theorem-level
counterpart of `riemannian_fluids/function_spaces/constraints.py`, not a claim that a paper-specific `L²` or Sobolev construction has already been
completed.

The concrete smooth predicate `IsDivergenceFree` lives in `Tensors.VectorCalculus`. Connecting it to this abstract interface will require an actual
integrated inner product and integration-by-parts theorem.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/--
A velocity is incompressible when its divergence vanishes. This is the abstract-space analogue of the concrete `IsDivergenceFree` predicate on smooth
Riemannian vector fields.
-/
def IsIncompressible (calculus : ScalarVectorCalculus V Q) (u : V) : Prop :=
  calculus.divergence u = 0

/--
Scalar gradients perform no work on incompressible velocities: `⟪grad p,u⟫ = 0` when `div u = 0`. This is the pressure cancellation used in the
Navier--Stokes energy identity.
-/
theorem pressure_work_eq_zero (calculus : ScalarVectorCalculus V Q)
    {u : V} (hu : IsIncompressible V Q calculus u) (p : Q) :
    inner ℝ (calculus.gradient p) u = 0 := by
  -- Replace pressure work by the divergence pairing using the packaged integration-by-parts identity.
  rw [calculus.gradient_divergence_duality]
  -- Expose the definition of incompressibility in the hypothesis.
  change calculus.divergence u = 0 at hu
  -- Substitute `div u = 0`; the inner product with zero vanishes.
  simp [hu]

end RiemannianFluids
