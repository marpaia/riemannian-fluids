import Mathlib.LinearAlgebra.Trace
import RiemannianFluids.Geometry.Manifolds
import RiemannianFluids.Tensors.SmoothSections

/-!
# Smooth contraction of tangent endomorphisms

Contraction is how a covariant derivative becomes divergence. At a point, `∇u` is the endomorphism

    T_xM → T_xM,       X ↦ ∇_X u.

Its trace is the coordinate-free scalar

    div u = tr(∇u),

which a local frame writes as `∇ᵢuⁱ`. This file isolates the contraction step so the later definition of divergence is literally “differentiate, then
trace.”

## Why a coordinate proof appears

Trace is algebraic in each individual tangent space, but a smooth scalar field must vary smoothly from point to point. Around a base point, a
tangent-bundle trivialization represents an intrinsic endomorphism `A_x` by

    P_x ∘ A_x ∘ P_x⁻¹ : E → E.

The model-space trace is a continuous linear functional, so its composition with a smooth coordinate endomorphism field is smooth. What makes this the
*intrinsic* trace is the familiar similarity-invariance identity

    tr(P A P⁻¹) = tr(A).

That identity is the conceptual heart of `traceVectorOneForm`. The local trivialization and `ContMDiffAt` plumbing merely put Lean in a position to
use it.

## The argument encoded below

We first turn mathlib's algebraic `LinearMap.trace` into a continuous linear functional on the finite-dimensional model endomorphisms. We then define
trace independently on each tangent fiber. Finally, in a local trivialization, we compose the smooth coordinate field with model-space trace and use
`trace_conj'` to identify that coordinate scalar with the intrinsic fiber trace.

The result is not yet divergence; no connection appears here. It is the coordinate-natural contraction operation that `VectorCalculus` will compose
with `∇`.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

/--
Trace as a continuous linear functional on model-space endomorphisms. Mathlib defines trace on ordinary linear maps; the two conversions in the
definition move between continuous and ordinary linear maps in finite dimension.
-/
noncomputable def continuousEndomorphismTrace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : (E →L[ℝ] E) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ E).comp
      (LinearMap.toContinuousLinearMap :
        (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).symm.toLinearMap)

/-- The continuous wrapper evaluates to mathlib's algebraic trace. -/
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

/--
The algebraic trace on a tangent fiber. The explicit local `FiniteDimensional` instance prevents this central contraction from depending on fragile
typeclass inference through the tangent-bundle implementation.
-/
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
Smooth fiberwise trace `C^k(Hom(TM, TM)) → C^k(M, ℝ)`.

The coordinate proof uses invariance of trace under conjugation; this is the step that makes the result intrinsic rather than dependent on a chart.
-/
noncomputable def traceVectorOneForm (regularity : ℕ∞ω) :
    SmoothVectorOneForm (M := M) I regularity →ₗ[ℝ]
      SmoothScalarField (M := M) I regularity where
  toFun field :=
    -- The scalar value at `x` is the trace of the tangent endomorphism `field x`.
    { val := fun x => tangentTrace I x (field x)
      property := by
        -- Smoothness of a scalar field is local; fix a base point for bundle coordinates.
        intro x₀
        -- The bundled hypothesis says the original endomorphism field is smooth as a section of `Hom(TM,TM)`.
        have hfield :
            ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) regularity
              (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x (field x)) x₀ :=
          field.contMDiff.contMDiffAt
        -- Rewrite that statement as smoothness of its coordinate endomorphism.
        rw [contMDiffAt_hom_bundle] at hfield
        -- Trace is a continuous linear functional, so composing it with the smooth coordinate field gives a smooth scalar function.
        have hcoordinateTrace : ContMDiffAt I 𝓘(ℝ) regularity
            (fun x : M => continuousEndomorphismTrace E
              (ContinuousLinearMap.inCoordinates
                E (TangentSpace I : M → Type _)
                E (TangentSpace I : M → Type _)
                x₀ x x₀ x (field x))) x₀ :=
          (continuousEndomorphismTrace E).contDiff.comp_contMDiffAt hfield.2
        -- We now prove that this coordinate trace equals the intrinsic fiber trace on a neighborhood of `x₀`.
        apply hcoordinateTrace.congr_of_eventuallyEq
        -- Restrict to the base set of the tangent trivialization.
        have htrivialization :
            (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ 𝓝 x₀ :=
          (trivializationAt _ _ _).open_baseSet.mem_nhds
            (FiberBundle.mem_baseSet_trivializationAt' _)
        filter_upwards [htrivialization] with x hx
        -- On this set, the coordinate endomorphism is conjugation by the chart equivalence.
        rw [ContinuousLinearMap.inCoordinates_eq hx hx]
        -- State the remaining goal as invariance of ordinary linear-map trace under conjugation.
        change tangentTrace I x (field x) = LinearMap.trace ℝ E
          (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt
            ℝ x hx).toLinearEquiv.conj (field x).toLinearMap)
        -- `trace(P A P⁻¹) = trace(A)` is exactly the coordinate-independence theorem needed here.
        rw [LinearMap.trace_conj']
        -- The definitions of `tangentTrace` and the continuous-map conversion now coincide.
        rfl }
  map_add' first second := by
    -- Trace is additive, checked pointwise on the scalar output.
    ext x
    simp [tangentTrace]
  map_smul' scalar field := by
    -- Trace is homogeneous over `ℝ`.
    ext x
    simp [tangentTrace]

omit [CompleteSpace E] in
/-- Evaluating smooth contraction at `x` is the intrinsic trace in `T_xM`. -/
@[simp]
theorem traceVectorOneForm_apply (regularity : ℕ∞ω)
    (field : SmoothVectorOneForm (M := M) I regularity) (x : M) :
    traceVectorOneForm I regularity field x = tangentTrace I x (field x) :=
  rfl

end RiemannianFluids
