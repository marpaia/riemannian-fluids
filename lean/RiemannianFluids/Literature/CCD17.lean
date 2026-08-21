import RiemannianFluids.Operators.ConstructedHodge

/-!
# CCD17: curvature comparison of viscosity operators

The literature namespace exposes the fully constructed divergence-free comparison.  Its geometric
hypotheses remain visible in the inferred theorem type and are documented in the claim crosswalk.
-/

namespace RiemannianFluids.Literature.CCD17

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The constructed divergence-free identity between deformation and Hodge viscosity. -/
abbrev divergenceFree_deformation_eq_hodge_sub_two_ricci
    [IsManifold I 3 M]
    (regularity : ℕ∞ω) (hreg : (2 : ℕ∞ω) ≤ regularity + 1)
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection.connection x)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    (hdiv : IsDivergenceFree I connection regularity smooth field)
    (x : M) (w : TangentSpace I x) :=
  _root_.RiemannianFluids.ccd17_divfree_def_hodge_constructed I regularity hreg
    connection smooth regular field hdiv x w

end RiemannianFluids.Literature.CCD17
