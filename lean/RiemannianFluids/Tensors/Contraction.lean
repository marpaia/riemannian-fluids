import Mathlib.LinearAlgebra.Trace
import RiemannianFluids.Geometry.Manifolds
import RiemannianFluids.Tensors.SmoothSections

/-!
# Smooth contraction of tangent endomorphisms

The trace of a tangent-valued one-form is coordinate independent and varies
smoothly.  This module proves that fact through bundle coordinates and packages
it as a linear map on regularity-indexed sections.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

/-- Trace as a continuous linear functional on model-space endomorphisms. -/
noncomputable def continuousEndomorphismTrace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : (E →L[ℝ] E) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ E).comp
      (LinearMap.toContinuousLinearMap :
        (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).symm.toLinearMap)

@[simp]
theorem continuousEndomorphismTrace_apply
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (endomorphism : E →L[ℝ] E) :
    continuousEndomorphismTrace E endomorphism =
      LinearMap.trace ℝ E endomorphism.toLinearMap :=
  rfl

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The algebraic trace on a tangent fiber. -/
noncomputable def tangentTrace (x : M) :
    (TangentSpace I x →L[ℝ] TangentSpace I x) →ₗ[ℝ] ℝ :=
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    tangentFiniteDimensional I x
  (LinearMap.trace ℝ (TangentSpace I x)).comp
    (LinearMap.toContinuousLinearMap :
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x) ≃ₗ[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x)).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
/--
Smooth fiberwise trace
`C^k(Hom(TM, TM)) → C^k(M, ℝ)`.

The coordinate proof uses invariance of trace under conjugation; this is the
step that makes the result intrinsic rather than dependent on a chart.
-/
noncomputable def traceVectorOneForm (regularity : ℕ∞ω) :
    SmoothVectorOneForm (M := M) I regularity →ₗ[ℝ]
      SmoothScalarField (M := M) I regularity where
  toFun field :=
    { val := fun x => tangentTrace I x (field x)
      property := by
        intro x₀
        have hfield :
            ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) regularity
              (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x (field x)) x₀ :=
          field.contMDiff.contMDiffAt
        rw [contMDiffAt_hom_bundle] at hfield
        have hcoordinateTrace : ContMDiffAt I 𝓘(ℝ) regularity
            (fun x : M => continuousEndomorphismTrace E
              (ContinuousLinearMap.inCoordinates
                E (TangentSpace I : M → Type _)
                E (TangentSpace I : M → Type _)
                x₀ x x₀ x (field x))) x₀ :=
          (continuousEndomorphismTrace E).contDiff.comp_contMDiffAt hfield.2
        apply hcoordinateTrace.congr_of_eventuallyEq
        have htrivialization :
            (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ 𝓝 x₀ :=
          (trivializationAt _ _ _).open_baseSet.mem_nhds
            (FiberBundle.mem_baseSet_trivializationAt' _)
        filter_upwards [htrivialization] with x hx
        rw [ContinuousLinearMap.inCoordinates_eq hx hx]
        change tangentTrace I x (field x) = LinearMap.trace ℝ E
          (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt
            ℝ x hx).toLinearEquiv.conj (field x).toLinearMap)
        rw [LinearMap.trace_conj']
        rfl }
  map_add' first second := by
    ext x
    simp [tangentTrace]
  map_smul' scalar field := by
    ext x
    simp [tangentTrace]

omit [CompleteSpace E] in
@[simp]
theorem traceVectorOneForm_apply (regularity : ℕ∞ω)
    (field : SmoothVectorOneForm (M := M) I regularity) (x : M) :
    traceVectorOneForm I regularity field x = tangentTrace I x (field x) :=
  rfl

end RiemannianFluids
