import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
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

/-! ## Ricci contraction of a trilinear curvature tensor -/

section RicciForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- For fixed `Y` and `Z`, view `X ↦ R(X,Y)Z` as an endomorphism. -/
noncomputable def curvatureFirstSlotEndomorphism
    (curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) (second field : V) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap {
    toFun := fun first ↦ curvature first second field
    map_add' := by simp
    map_smul' := by simp
  }

/-- The Ricci form obtained by tracing the first and output indices of `R(X,Y)Z`.

Thus `ricciFormOfCurvatureTensor R Y Z = tr (X ↦ R(X,Y)Z)`. The algebraic trace
makes this definition independent of any chosen basis. -/
noncomputable def ricciFormOfCurvatureTensor
    (curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun second ↦ LinearMap.toContinuousLinearMap {
      toFun := fun field ↦
        continuousEndomorphismTrace V
          (curvatureFirstSlotEndomorphism curvature second field)
      map_add' := by
        intro firstField secondField
        calc
          continuousEndomorphismTrace V
              (curvatureFirstSlotEndomorphism curvature second
                (firstField + secondField)) =
              continuousEndomorphismTrace V
                (curvatureFirstSlotEndomorphism curvature second firstField +
                  curvatureFirstSlotEndomorphism curvature second secondField) := by
            congr 1
            ext first
            simp [curvatureFirstSlotEndomorphism]
          _ = _ := map_add _ _ _
      map_smul' := by
        intro scalar field
        calc
          continuousEndomorphismTrace V
              (curvatureFirstSlotEndomorphism curvature second (scalar • field)) =
              continuousEndomorphismTrace V
                (scalar • curvatureFirstSlotEndomorphism curvature second field) := by
            congr 1
            ext first
            simp [curvatureFirstSlotEndomorphism]
          _ = _ := map_smul _ _ _
    }
    map_add' := by
      intro firstSecond secondSecond
      ext field
      calc
        continuousEndomorphismTrace V
            (curvatureFirstSlotEndomorphism curvature (firstSecond + secondSecond) field) =
            continuousEndomorphismTrace V
              (curvatureFirstSlotEndomorphism curvature firstSecond field +
                curvatureFirstSlotEndomorphism curvature secondSecond field) := by
          congr 1
          ext first
          simp [curvatureFirstSlotEndomorphism]
        _ = _ := map_add _ _ _
    map_smul' := by
      intro scalar second
      ext field
      calc
        continuousEndomorphismTrace V
            (curvatureFirstSlotEndomorphism curvature (scalar • second) field) =
            continuousEndomorphismTrace V
              (scalar • curvatureFirstSlotEndomorphism curvature second field) := by
          congr 1
          ext first
          simp [curvatureFirstSlotEndomorphism]
        _ = _ := map_smul _ _ _
  }

@[simp]
theorem ricciFormOfCurvatureTensor_apply
    (curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) (second field : V) :
    ricciFormOfCurvatureTensor curvature second field =
      LinearMap.trace ℝ V
        (curvatureFirstSlotEndomorphism curvature second field).toLinearMap :=
  rfl

set_option maxHeartbeats 800000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Ricci contraction as a continuous linear operation on trilinear curvature tensors. -/
noncomputable def ricciContractionLinearMap (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    (V →L[ℝ] V →L[ℝ] V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V ↦
      ricciFormOfCurvatureTensor curvature
    map_add' := by
      intro firstCurvature secondCurvature
      apply DFunLike.ext _ _
      intro second
      apply DFunLike.ext _ _
      intro field
      change continuousEndomorphismTrace V
          (curvatureFirstSlotEndomorphism (firstCurvature + secondCurvature) second field) = _
      calc
        _ = continuousEndomorphismTrace V
            (curvatureFirstSlotEndomorphism firstCurvature second field +
              curvatureFirstSlotEndomorphism secondCurvature second field) := by
          congr 1
        _ = _ := map_add _ _ _
    map_smul' := by
      intro scalar curvature
      apply DFunLike.ext _ _
      intro second
      apply DFunLike.ext _ _
      intro field
      change continuousEndomorphismTrace V
          (curvatureFirstSlotEndomorphism (scalar • curvature) second field) = _
      calc
        _ = continuousEndomorphismTrace V
            (scalar • curvatureFirstSlotEndomorphism curvature second field) := by
          congr 1
        _ = _ := map_smul _ _ _
  }

/-! ### A native continuous-trilinear model for curvature regularity -/

private noncomputable def curriedBilinearToMultilinear
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : V →L[ℝ] V →L[ℝ] F) : V [×2]→L[ℝ] F :=
  (((continuousMultilinearCurryFin1 ℝ V F).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    f).uncurryLeft

omit [FiniteDimensional ℝ V] in
@[simp]
private theorem curriedBilinearToMultilinear_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : V →L[ℝ] V →L[ℝ] F) (v : Fin 2 → V) :
    curriedBilinearToMultilinear f v = f (v 0) (v 1) := by
  simp [curriedBilinearToMultilinear, ContinuousLinearMap.uncurryLeft_apply,
    continuousMultilinearCurryFin1_symm_apply]
  congr 1

/-- Repackage the final two slots of a triple-curried map as a native continuous bilinear map. -/
noncomputable def curriedTrilinearToLeftCurriedMultilinear
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : V →L[ℝ] V →L[ℝ] V →L[ℝ] F) : V →L[ℝ] V [×2]→L[ℝ] F :=
  LinearMap.toContinuousLinearMap {
    toFun := fun first ↦ curriedBilinearToMultilinear (f first)
    map_add' := by
      intro first second
      ext v
      simp
    map_smul' := by
      intro scalar first
      ext v
      simp
  }

@[simp]
theorem curriedTrilinearToLeftCurriedMultilinear_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : V →L[ℝ] V →L[ℝ] V →L[ℝ] F) (first : V) (v : Fin 2 → V) :
    curriedTrilinearToLeftCurriedMultilinear f first v = f first (v 0) (v 1) := by
  simp [curriedTrilinearToLeftCurriedMultilinear]

/-- Repackage a triple-curried continuous linear map as Mathlib's native continuous trilinear
map. -/
noncomputable def curriedTrilinearToMultilinear
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : V →L[ℝ] V →L[ℝ] V →L[ℝ] F) : V [×3]→L[ℝ] F :=
  (curriedTrilinearToLeftCurriedMultilinear f).uncurryLeft

@[simp]
theorem curriedTrilinearToMultilinear_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : V →L[ℝ] V →L[ℝ] V →L[ℝ] F) (v : Fin 3 → V) :
    curriedTrilinearToMultilinear f v = f (v 0) (v 1) (v 2) := by
  rfl

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private lemma updateVec3_zero (first second field : V) :
    Function.update ![0, second, field] 0 first = ![first, second, field] := by
  funext i
  fin_cases i <;> rfl

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private lemma updateVec3_one (first second field : V) :
    Function.update ![first, 0, field] 1 second = ![first, second, field] := by
  funext i
  fin_cases i <;> rfl

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private lemma updateVec3_two (first second field : V) :
    Function.update ![first, second, 0] 2 field = ![first, second, field] := by
  funext i
  fin_cases i <;> rfl

/-- For a native continuous trilinear curvature tensor, freeze its last two slots and retain the
first-slot endomorphism whose trace is Ricci. -/
noncomputable def multilinearCurvatureFirstSlotEndomorphism
    (curvature : V [×3]→L[ℝ] V) (second field : V) : V →L[ℝ] V :=
  curvature.toContinuousLinearMap ![0, second, field] 0

omit [FiniteDimensional ℝ V] in
@[simp]
theorem multilinearCurvatureFirstSlotEndomorphism_apply
    (curvature : V [×3]→L[ℝ] V) (first second field : V) :
    multilinearCurvatureFirstSlotEndomorphism curvature second field first =
      curvature ![first, second, field] := by
  simp [multilinearCurvatureFirstSlotEndomorphism,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, updateVec3_zero]

/-- Ricci contraction of a native continuous trilinear curvature tensor. -/
noncomputable def ricciFormOfMultilinearCurvatureTensor
    (curvature : V [×3]→L[ℝ] V) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun second ↦ LinearMap.toContinuousLinearMap {
      toFun := fun field ↦ continuousEndomorphismTrace V
        (multilinearCurvatureFirstSlotEndomorphism curvature second field)
      map_add' := by
        intro firstField secondField
        change continuousEndomorphismTrace V _ =
          continuousEndomorphismTrace V _ + continuousEndomorphismTrace V _
        rw [← map_add]
        congr
        ext first
        simp only [multilinearCurvatureFirstSlotEndomorphism_apply, add_apply]
        simpa [updateVec3_two] using
          curvature.map_update_add ![first, second, 0] 2 firstField secondField
      map_smul' := by
        intro scalar field
        change continuousEndomorphismTrace V _ =
          scalar • continuousEndomorphismTrace V _
        rw [← map_smul]
        congr
        ext first
        simp only [multilinearCurvatureFirstSlotEndomorphism_apply, smul_apply]
        simpa [updateVec3_two] using
          curvature.map_update_smul ![first, second, 0] 2 scalar field
    }
    map_add' := by
      intro firstSecond secondSecond
      ext field
      change continuousEndomorphismTrace V _ =
        continuousEndomorphismTrace V _ + continuousEndomorphismTrace V _
      rw [← map_add]
      congr
      ext first
      simp only [multilinearCurvatureFirstSlotEndomorphism_apply, add_apply]
      simpa [updateVec3_one] using
        curvature.map_update_add ![first, 0, field] 1 firstSecond secondSecond
    map_smul' := by
      intro scalar second
      ext field
      change continuousEndomorphismTrace V _ =
        scalar • continuousEndomorphismTrace V _
      rw [← map_smul]
      congr
      ext first
      simp only [multilinearCurvatureFirstSlotEndomorphism_apply, smul_apply]
      simpa [updateVec3_one] using
        curvature.map_update_smul ![first, 0, field] 1 scalar second
  }

omit [FiniteDimensional ℝ V] in
private lemma multilinearCurvatureFirstSlotEndomorphism_norm
    (curvature : V [×3]→L[ℝ] V) (second field : V) :
    ‖multilinearCurvatureFirstSlotEndomorphism curvature second field‖ ≤
      (‖curvature‖ * ‖second‖) * ‖field‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro first
  have h := curvature.le_opNorm ![first, second, field]
  simpa [multilinearCurvatureFirstSlotEndomorphism_apply, Fin.prod_univ_succ,
    mul_assoc, mul_left_comm, mul_comm] using h

omit [FiniteDimensional ℝ V] in
private lemma multilinearCurvatureFirstSlotEndomorphism_add
    (first second : V [×3]→L[ℝ] V) (y z : V) :
    multilinearCurvatureFirstSlotEndomorphism (first + second) y z =
      multilinearCurvatureFirstSlotEndomorphism first y z +
        multilinearCurvatureFirstSlotEndomorphism second y z := by
  ext x
  simp [multilinearCurvatureFirstSlotEndomorphism_apply]

omit [FiniteDimensional ℝ V] in
private lemma multilinearCurvatureFirstSlotEndomorphism_smul
    (scalar : ℝ) (curvature : V [×3]→L[ℝ] V) (y z : V) :
    multilinearCurvatureFirstSlotEndomorphism (scalar • curvature) y z =
      scalar • multilinearCurvatureFirstSlotEndomorphism curvature y z := by
  ext x
  simp [multilinearCurvatureFirstSlotEndomorphism_apply]

private lemma ricciFormOfMultilinearCurvatureTensor_norm
    (curvature : V [×3]→L[ℝ] V) :
    ‖ricciFormOfMultilinearCurvatureTensor curvature‖ ≤
      ‖continuousEndomorphismTrace V‖ * ‖curvature‖ := by
  refine (ricciFormOfMultilinearCurvatureTensor curvature).opNorm_le_bound (by positivity) ?_
  intro second
  refine ((ricciFormOfMultilinearCurvatureTensor curvature) second).opNorm_le_bound
    (by positivity) ?_
  intro field
  calc
    _ ≤ ‖continuousEndomorphismTrace V‖ *
          ‖multilinearCurvatureFirstSlotEndomorphism curvature second field‖ :=
      (continuousEndomorphismTrace V).le_opNorm _
    _ ≤ ‖continuousEndomorphismTrace V‖ *
          ((‖curvature‖ * ‖second‖) * ‖field‖) := by
      gcongr
      exact multilinearCurvatureFirstSlotEndomorphism_norm curvature second field
    _ = (‖continuousEndomorphismTrace V‖ * ‖curvature‖) *
          ‖second‖ * ‖field‖ := by ring

/-- Ricci contraction in the differentiability-friendly model with a linear first slot and a
native bilinear map in the remaining slots. -/
noncomputable def ricciFormOfLeftCurriedMultilinearCurvatureTensor
    (curvature : V →L[ℝ] V [×2]→L[ℝ] V) : V →L[ℝ] V →L[ℝ] ℝ :=
  ricciFormOfMultilinearCurvatureTensor curvature.uncurryLeft

set_option synthInstance.maxHeartbeats 100000 in
private noncomputable def multilinearRicciContractionPointwiseLinearMap :
    (V [×3]→L[ℝ] V) →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) :=
  LinearMap.mkContinuous {
    toFun := fun curvature : V [×3]→L[ℝ] V ↦
      ricciFormOfMultilinearCurvatureTensor curvature
    map_add' := by
      intro first second
      ext y z
      change continuousEndomorphismTrace V
          (multilinearCurvatureFirstSlotEndomorphism (first + second) y z) =
        continuousEndomorphismTrace V
            (multilinearCurvatureFirstSlotEndomorphism first y z) +
          continuousEndomorphismTrace V
            (multilinearCurvatureFirstSlotEndomorphism second y z)
      rw [multilinearCurvatureFirstSlotEndomorphism_add, map_add]
    map_smul' := by
      intro scalar curvature
      ext y z
      change continuousEndomorphismTrace V
          (multilinearCurvatureFirstSlotEndomorphism (scalar • curvature) y z) =
        scalar • continuousEndomorphismTrace V
          (multilinearCurvatureFirstSlotEndomorphism curvature y z)
      rw [multilinearCurvatureFirstSlotEndomorphism_smul, map_smul]
  } ‖continuousEndomorphismTrace V‖ ricciFormOfMultilinearCurvatureTensor_norm

/-- Ricci trace is a bounded linear operation on the left-curried multilinear curvature model. -/
noncomputable def leftCurriedMultilinearRicciContractionLinearMap :
    (V →L[ℝ] V [×2]→L[ℝ] V) →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) :=
  multilinearRicciContractionPointwiseLinearMap.comp
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 ↦ V) V).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The same bounded contraction with the norm-induced topologies made explicit. This wrapper is
the form consumed by the differentiability API, avoiding the pointwise-topology instances carried
by bundled spaces of continuous maps. -/
noncomputable def normedLeftCurriedMultilinearRicciContractionLinearMap :
    let Source := V →L[ℝ] V [×2]→L[ℝ] V
    let Target := V →L[ℝ] V →L[ℝ] ℝ
    let sourceNorm : NormedAddCommGroup Source := ContinuousLinearMap.toNormedAddCommGroup
    let sourceSpace : NormedSpace ℝ Source := ContinuousLinearMap.toNormedSpace
    let targetNorm : NormedAddCommGroup Target := ContinuousLinearMap.toNormedAddCommGroup
    let targetSpace : NormedSpace ℝ Target := ContinuousLinearMap.toNormedSpace
    letI : NormedAddCommGroup Source := sourceNorm
    letI : NormedSpace ℝ Source := sourceSpace
    letI : TopologicalSpace Source :=
      sourceNorm.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : AddCommMonoid Source := sourceNorm.toAddCommMonoid
    letI : Module ℝ Source := sourceSpace.toModule
    letI : NormedAddCommGroup Target := targetNorm
    letI : NormedSpace ℝ Target := targetSpace
    letI : TopologicalSpace Target :=
      targetNorm.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : AddCommMonoid Target := targetNorm.toAddCommMonoid
    letI : Module ℝ Target := targetSpace.toModule
    Source →L[ℝ] Target :=
  let Source := V →L[ℝ] V [×2]→L[ℝ] V
  let Target := V →L[ℝ] V →L[ℝ] ℝ
  let sourceNorm : NormedAddCommGroup Source := ContinuousLinearMap.toNormedAddCommGroup
  let sourceSpace : NormedSpace ℝ Source := ContinuousLinearMap.toNormedSpace
  let targetNorm : NormedAddCommGroup Target := ContinuousLinearMap.toNormedAddCommGroup
  let targetSpace : NormedSpace ℝ Target := ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup Source := sourceNorm
  letI : NormedSpace ℝ Source := sourceSpace
  letI : TopologicalSpace Source :=
    sourceNorm.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommMonoid Source := sourceNorm.toAddCommMonoid
  letI : Module ℝ Source := sourceSpace.toModule
  letI : NormedAddCommGroup Target := targetNorm
  letI : NormedSpace ℝ Target := targetSpace
  letI : TopologicalSpace Target :=
    targetNorm.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommMonoid Target := targetNorm.toAddCommMonoid
  letI : Module ℝ Target := targetSpace.toModule
  LinearMap.mkContinuous
    (leftCurriedMultilinearRicciContractionLinearMap (V := V)).toLinearMap
    ‖leftCurriedMultilinearRicciContractionLinearMap (V := V)‖
    (leftCurriedMultilinearRicciContractionLinearMap (V := V)).le_opNorm

set_option synthInstance.maxHeartbeats 100000 in
/-- Ricci contraction is `C^n` as a map between the normed curvature and bilinear-form model
spaces. Keeping this Euclidean-calculus fact separate lets manifold composition choose its own
canonical self-chart instances. -/
theorem contDiff_ricciFormOfLeftCurriedMultilinearCurvatureTensor (n : ℕ∞ω) :
    ContDiff ℝ n (fun curvature : V →L[ℝ] V [×2]→L[ℝ] V ↦
      ricciFormOfLeftCurriedMultilinearCurvatureTensor curvature) := by
  let Source := V →L[ℝ] V [×2]→L[ℝ] V
  let Target := V →L[ℝ] V →L[ℝ] ℝ
  let sourceNorm : NormedAddCommGroup Source := ContinuousLinearMap.toNormedAddCommGroup
  let sourceSpace : NormedSpace ℝ Source := ContinuousLinearMap.toNormedSpace
  let targetNorm : NormedAddCommGroup Target := ContinuousLinearMap.toNormedAddCommGroup
  let targetSpace : NormedSpace ℝ Target := ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup Source := sourceNorm
  letI : NormedSpace ℝ Source := sourceSpace
  letI : TopologicalSpace Source :=
    sourceNorm.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommMonoid Source := sourceNorm.toAddCommMonoid
  letI : Module ℝ Source := sourceSpace.toModule
  letI : NormedAddCommGroup Target := targetNorm
  letI : NormedSpace ℝ Target := targetSpace
  letI : TopologicalSpace Target :=
    targetNorm.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommMonoid Target := targetNorm.toAddCommMonoid
  letI : Module ℝ Target := targetSpace.toModule
  exact (normedLeftCurriedMultilinearRicciContractionLinearMap (V := V)).contDiff.of_le le_top

@[simp]
theorem leftCurriedMultilinearRicciContractionLinearMap_apply
    (curvature : V →L[ℝ] V [×2]→L[ℝ] V) :
    leftCurriedMultilinearRicciContractionLinearMap (V := V) curvature =
      ricciFormOfLeftCurriedMultilinearCurvatureTensor curvature := by
  rfl

/-- The left-curried contraction agrees with the established triple-curried Ricci interface. -/
theorem ricciFormOfLeftCurriedMultilinearCurvatureTensor_curried
    (curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) :
    ricciFormOfLeftCurriedMultilinearCurvatureTensor
        (curriedTrilinearToLeftCurriedMultilinear curvature) =
      ricciFormOfCurvatureTensor curvature := by
  ext second field
  change continuousEndomorphismTrace V _ = continuousEndomorphismTrace V _
  congr

/-- The native-trilinear contraction agrees with the established triple-curried Ricci interface. -/
theorem ricciFormOfMultilinearCurvatureTensor_curried
    (curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) :
    ricciFormOfMultilinearCurvatureTensor
        (curriedTrilinearToMultilinear curvature) =
      ricciFormOfCurvatureTensor curvature := by
  ext second field
  change continuousEndomorphismTrace V _ = continuousEndomorphismTrace V _
  congr

/-- Transport a trilinear curvature tensor through a continuous linear equivalence. -/
noncomputable def curvatureTensorInCoordinates
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (equiv : V ≃L[ℝ] W)
    (curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) :
    W →L[ℝ] W →L[ℝ] W →L[ℝ] W :=
  LinearMap.toContinuousLinearMap {
    toFun := fun first ↦ LinearMap.toContinuousLinearMap {
      toFun := fun second ↦ LinearMap.toContinuousLinearMap {
        toFun := fun field ↦ equiv (curvature (equiv.symm first)
          (equiv.symm second) (equiv.symm field))
        map_add' := by simp
        map_smul' := by simp
      }
      map_add' := by
        intro first second
        ext field
        simp
      map_smul' := by
        intro scalar second
        ext field
        simp
    }
    map_add' := by
      intro first second
      ext innerSecond field
      simp
    map_smul' := by
      intro scalar first
      ext second field
      simp
  }

/-- Transport a covariant two-tensor through a continuous linear equivalence. -/
noncomputable def covariantTwoTensorInCoordinates
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (equiv : V ≃L[ℝ] W)
    (tensor : V →L[ℝ] V →L[ℝ] ℝ) : W →L[ℝ] W →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun first ↦ LinearMap.toContinuousLinearMap {
      toFun := fun second ↦ tensor (equiv.symm first) (equiv.symm second)
      map_add' := by simp
      map_smul' := by simp
    }
    map_add' := by
      intro first second
      ext field
      simp
    map_smul' := by
      intro scalar first
      ext second
      simp
  }

/-- Ricci contraction commutes with a simultaneous change of coordinates in every curvature slot. -/
theorem ricciForm_curvatureTensorInCoordinates
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (equiv : V ≃L[ℝ] W)
    (curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) :
    ricciFormOfCurvatureTensor (curvatureTensorInCoordinates equiv curvature) =
      covariantTwoTensorInCoordinates equiv (ricciFormOfCurvatureTensor curvature) := by
  ext second field
  rw [ricciFormOfCurvatureTensor_apply]
  change LinearMap.trace ℝ W
      (curvatureFirstSlotEndomorphism
        (curvatureTensorInCoordinates equiv curvature) second field).toLinearMap =
    ricciFormOfCurvatureTensor curvature (equiv.symm second) (equiv.symm field)
  rw [ricciFormOfCurvatureTensor_apply]
  have hconj :
      (curvatureFirstSlotEndomorphism
        (curvatureTensorInCoordinates equiv curvature) second field).toLinearMap =
      equiv.toLinearEquiv.conj
        (curvatureFirstSlotEndomorphism curvature (equiv.symm second)
          (equiv.symm field)).toLinearMap := by
    ext first
    simp [curvatureFirstSlotEndomorphism, curvatureTensorInCoordinates]
  rw [hconj, LinearMap.trace_conj']

end RicciForm

section RicciAction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Raise the second covector index of the Ricci form using the inner product. -/
noncomputable def ricciActionOfCurvatureTensor
    (curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) : V →L[ℝ] V :=
  InnerProductSpace.continuousLinearMapOfBilin (ricciFormOfCurvatureTensor curvature)

@[simp]
theorem ricciActionOfCurvatureTensor_inner
    (curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) (second field : V) :
    inner ℝ (ricciActionOfCurvatureTensor curvature second) field =
      ricciFormOfCurvatureTensor curvature second field := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply
    (ricciFormOfCurvatureTensor curvature) second field

/-- In every orthonormal basis, the intrinsic Ricci trace is the familiar contracted sum. -/
theorem ricciFormOfCurvatureTensor_eq_sum_inner
    {ι : Type*} [Fintype ι]
    (curvature : V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (basis : OrthonormalBasis ι ℝ V) (second field : V) :
    ricciFormOfCurvatureTensor curvature second field =
      ∑ i, inner ℝ (basis i) (curvature (basis i) second field) := by
  rw [ricciFormOfCurvatureTensor_apply, LinearMap.trace_eq_sum_inner _ basis]
  rfl

end RicciAction

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
