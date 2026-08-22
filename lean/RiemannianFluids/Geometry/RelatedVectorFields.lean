import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Lie brackets of related vector fields

The naturality statement needed by submanifold geometry is more general than pullback invariance
under a local diffeomorphism: if `V̄` and `W̄` are `f`-related to `V` and `W`, then their Lie
brackets are also `f`-related.  This file proves the model-space calculus at the heart of that
statement without any invertibility assumption on `df`.

The manifold lift belongs in this same layer.  It will transport the theorem through source and
target charts and will therefore apply to genuine lower-dimensional immersions, unlike
Mathlib's `mpullback_mlieBracket`, whose pullback uses an inverse derivative.
-/

namespace RiemannianFluids

open Filter Function
open scoped ContDiff Manifold Topology

noncomputable section

variable
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace VectorField

/-- Lie brackets preserve `f`-relatedness in normed vector spaces, with no injectivity,
surjectivity, or invertibility assumption on `df`.

The two relatedness hypotheses are germ equalities because the bracket only sees first germs.
The `C²` hypothesis on `f` is exactly what cancels its symmetric second derivative in the
commutator. -/
theorem lieBracket_eq_fderiv_lieBracket_of_related
    {f : E → F} {V W : E → E} {Vbar Wbar : F → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hVbar : DifferentiableAt ℝ Vbar (f x))
    (hWbar : DifferentiableAt ℝ Wbar (f x))
    (relatedV : Vbar ∘ f =ᶠ[𝓝 x] fun y ↦ fderiv ℝ f y (V y))
    (relatedW : Wbar ∘ f =ᶠ[𝓝 x] fun y ↦ fderiv ℝ f y (W y)) :
    VectorField.lieBracket ℝ Vbar Wbar (f x) =
      fderiv ℝ f x (VectorField.lieBracket ℝ V W x) := by
  have hfDiff := hf.differentiableAt (by norm_num)
  have hVvalue := relatedV.self_of_nhds
  have hWvalue := relatedW.self_of_nhds
  have hVvalue' : Vbar (f x) = fderiv ℝ f x (V x) := by
    simpa only [Function.comp_apply] using hVvalue
  have hWvalue' : Wbar (f x) = fderiv ℝ f x (W x) := by
    simpa only [Function.comp_apply] using hWvalue
  have hVcomp := hVbar.comp x hfDiff
  have hWcomp := hWbar.comp x hfDiff
  have derivativeV :
      fderiv ℝ (Vbar ∘ f) x =
        fderiv ℝ (fun y ↦ fderiv ℝ f y (V y)) x :=
    Filter.EventuallyEq.fderiv_eq relatedV
  have derivativeW :
      fderiv ℝ (Wbar ∘ f) x =
        fderiv ℝ (fun y ↦ fderiv ℝ f y (W y)) x :=
    Filter.EventuallyEq.fderiv_eq relatedW
  rw [VectorField.lieBracket]
  rw [VectorField.fderiv_apply_lieBracket hf (by norm_num) hW hV]
  rw [← derivativeV, ← derivativeW]
  rw [fderiv_comp x hWbar hfDiff, fderiv_comp x hVbar hfDiff]
  simp only [ContinuousLinearMap.comp_apply, hVvalue', hWvalue']

end VectorField

section Manifold

variable
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [CompleteSpace E] [CompleteSpace F]
  [IsManifold I 2 M] [IsManifold I' 2 N]
  [I.Boundaryless] [I'.Boundaryless]

namespace VectorField

/-- Lie brackets preserve relatedness for vector fields on boundaryless manifolds.  In
particular, the map may be a genuine lower-dimensional immersion: its derivative is never
inverted. -/
theorem mlieBracket_eq_mfderiv_mlieBracket_of_related
    {f : M → N}
    {V W : (y : M) → TangentSpace I y}
    {Vbar Wbar : (z : N) → TangentSpace I' z} {x : M}
    (hf : CMDiff 2 f)
    (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x)
    (hVbar : MDiffAt (T% Vbar) (f x))
    (hWbar : MDiffAt (T% Wbar) (f x))
    (relatedV : ∀ y, Vbar (f y) = mfderiv I I' f y (V y))
    (relatedW : ∀ y, Wbar (f y) = mfderiv I I' f y (W y)) :
    VectorField.mlieBracket I' Vbar Wbar (f x) =
      mfderiv I I' f x (VectorField.mlieBracket I V W x) := by
  let sourceChart := extChartAt I x
  let targetChart := extChartAt I' (f x)
  let coordinateMap : E → F := (targetChart ∘ f) ∘ sourceChart.symm
  let sourceV := VectorField.mpullbackWithin 𝓘(ℝ, E) I sourceChart.symm V Set.univ
  let sourceW := VectorField.mpullbackWithin 𝓘(ℝ, E) I sourceChart.symm W Set.univ
  let targetV := VectorField.mpullbackWithin 𝓘(ℝ, F) I' targetChart.symm Vbar Set.univ
  let targetW := VectorField.mpullbackWithin 𝓘(ℝ, F) I' targetChart.symm Wbar Set.univ
  have sourceVdiff : DifferentiableAt ℝ sourceV (sourceChart x) := by
    rw [← mdifferentiableWithinAt_univ] at hV
    have h := hV.differentiableWithinAt_mpullbackWithin_vectorField
    rw [Set.preimage_univ, ModelWithCorners.Boundaryless.range_eq_univ,
      Set.inter_univ, differentiableWithinAt_univ] at h
    exact h
  have sourceWdiff : DifferentiableAt ℝ sourceW (sourceChart x) := by
    rw [← mdifferentiableWithinAt_univ] at hW
    have h := hW.differentiableWithinAt_mpullbackWithin_vectorField
    rw [Set.preimage_univ, ModelWithCorners.Boundaryless.range_eq_univ,
      Set.inter_univ, differentiableWithinAt_univ] at h
    exact h
  have targetVdiff : DifferentiableAt ℝ targetV (targetChart (f x)) := by
    rw [← mdifferentiableWithinAt_univ] at hVbar
    have h := hVbar.differentiableWithinAt_mpullbackWithin_vectorField
    rw [Set.preimage_univ, ModelWithCorners.Boundaryless.range_eq_univ,
      Set.inter_univ, differentiableWithinAt_univ] at h
    exact h
  have targetWdiff : DifferentiableAt ℝ targetW (targetChart (f x)) := by
    rw [← mdifferentiableWithinAt_univ] at hWbar
    have h := hWbar.differentiableWithinAt_mpullbackWithin_vectorField
    rw [Set.preimage_univ, ModelWithCorners.Boundaryless.range_eq_univ,
      Set.inter_univ, differentiableWithinAt_univ] at h
    exact h
  have coordinateC2 : ContDiffAt ℝ 2 coordinateMap (sourceChart x) := by
    have hsymmWithin :=
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 2) x
    rw [ModelWithCorners.Boundaryless.range_eq_univ] at hsymmWithin
    have hsymm : CMDiffAt 2 sourceChart.symm (sourceChart x) := by
      simpa only [contMDiffWithinAt_univ] using hsymmWithin
    have hfcomp : CMDiffAt 2 (f ∘ sourceChart.symm) (sourceChart x) := by
      exact (hf.contMDiffAt.comp (sourceChart x) hsymm)
    have htarget : CMDiffAt 2 targetChart
        ((f ∘ sourceChart.symm) (sourceChart x)) := by
      simpa [sourceChart, targetChart] using
        (contMDiffAt_extChartAt : CMDiffAt 2 (extChartAt I' (f x)) (f x))
    have hall : CMDiffAt 2 coordinateMap (sourceChart x) := by
      simpa [coordinateMap, Function.comp_assoc] using
        htarget.comp (sourceChart x) hfcomp
    exact hall.contDiffAt
  have coordinateValue : coordinateMap (sourceChart x) = targetChart (f x) := by
    simp [coordinateMap, sourceChart, targetChart]
  have relatedCoordinate
      (Y : (y : M) → TangentSpace I y)
      (Ybar : (z : N) → TangentSpace I' z)
      (related : ∀ y, Ybar (f y) = mfderiv I I' f y (Y y)) :
      (VectorField.mpullbackWithin 𝓘(ℝ, F) I' targetChart.symm Ybar Set.univ) ∘
          coordinateMap =ᶠ[𝓝 (sourceChart x)]
        fun z ↦ fderiv ℝ coordinateMap z
          (VectorField.mpullbackWithin 𝓘(ℝ, E) I sourceChart.symm Y Set.univ z) := by
    have sourceSymmContinuous : ContinuousAt sourceChart.symm (sourceChart x) := by
      have hsymmWithin :=
        contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 1) x
      rw [ModelWithCorners.Boundaryless.range_eq_univ] at hsymmWithin
      have hsymm : CMDiffAt 1 sourceChart.symm (sourceChart x) := by
        simpa only [sourceChart, contMDiffWithinAt_univ] using hsymmWithin
      exact hsymm.continuousAt
    have fSourceSymmContinuous : ContinuousAt (f ∘ sourceChart.symm) (sourceChart x) :=
      (hf.contMDiffAt.continuousAt.comp sourceSymmContinuous)
    have targetSourceEventually :
        (f ∘ sourceChart.symm) ⁻¹' targetChart.source ∈ 𝓝 (sourceChart x) := by
      apply fSourceSymmContinuous.preimage_mem_nhds
      simpa [sourceChart, targetChart] using extChartAt_source_mem_nhds (I := I') (f x)
    filter_upwards [extChartAt_target_mem_nhds (I := I) x,
      targetSourceEventually] with z hz htarget
    have hy : sourceChart.symm z ∈ sourceChart.source :=
      sourceChart.map_target hz
    have hfy : f (sourceChart.symm z) ∈ targetChart.source := htarget
    have hsourceInverse :
        (mfderiv 𝓘(ℝ, E) I sourceChart.symm z).IsInvertible := by
      simpa [sourceChart, ModelWithCorners.Boundaryless.range_eq_univ,
        mfderivWithin_univ] using
        (isInvertible_mfderivWithin_extChartAt_symm (I := I) hz)
    have htargetInverse :
        (mfderiv 𝓘(ℝ, F) I' targetChart.symm
          (targetChart (f (sourceChart.symm z)))).IsInvertible := by
      simpa [targetChart, ModelWithCorners.Boundaryless.range_eq_univ,
        mfderivWithin_univ] using
        (isInvertible_mfderivWithin_extChartAt_symm (I := I')
          (targetChart.map_source hfy))
    have targetPullback_eq :
        (mfderiv 𝓘(ℝ, F) I' targetChart.symm
            (targetChart (f (sourceChart.symm z)))).inverse
            (Ybar (f (sourceChart.symm z))) =
          mfderiv I' 𝓘(ℝ, F) targetChart (f (sourceChart.symm z))
            (Ybar (f (sourceChart.symm z))) := by
      apply htargetInverse.inverse_apply_eq.mpr
      rw [← ContinuousLinearMap.comp_apply]
      have hcomp :=
        mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
          (I := I') hfy
      rw [ModelWithCorners.Boundaryless.range_eq_univ,
        mfderivWithin_univ] at hcomp
      convert! (congrArg
        (fun L : TangentSpace I' (f (sourceChart.symm z)) →L[ℝ]
            TangentSpace I' (f (sourceChart.symm z)) ↦
          L (Ybar (f (sourceChart.symm z)))) hcomp).symm <;>
        exact targetChart.left_inv hfy
    have hsourceSymm : MDiffAt sourceChart.symm z := by
      have hwithin :=
        (contMDiffWithinAt_extChartAt_symm_range
          (I := I) (n := 1) x hz).mdifferentiableWithinAt (by norm_num)
      rw [ModelWithCorners.Boundaryless.range_eq_univ,
        mdifferentiableWithinAt_univ] at hwithin
      simpa [sourceChart] using hwithin
    have hfAt : MDiffAt f (sourceChart.symm z) :=
      (hf.contMDiffAt.mdifferentiableAt (by norm_num))
    have htargetChart : MDiffAt targetChart (f (sourceChart.symm z)) := by
      simpa [targetChart] using
        mdifferentiableAt_extChartAt (I := I')
          (show f (sourceChart.symm z) ∈ (chartAt H' (f x)).source by
            simpa [targetChart] using hfy)
    have coordinateDerivative :
        fderiv ℝ coordinateMap z
            ((mfderiv 𝓘(ℝ, E) I sourceChart.symm z).inverse
              (Y (sourceChart.symm z))) =
          mfderiv I' 𝓘(ℝ, F) targetChart (f (sourceChart.symm z))
            (mfderiv I I' f (sourceChart.symm z) (Y (sourceChart.symm z))) := by
      rw [← mfderiv_eq_fderiv]
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F)
          ((targetChart ∘ f) ∘ sourceChart.symm) z _ = _
      rw [mfderiv_comp_apply z (htargetChart.comp _ hfAt) hsourceSymm]
      rw [hsourceInverse.self_apply_inverse]
      rw [mfderiv_comp_apply _ htargetChart hfAt]
    simp only [Function.comp_apply, VectorField.mpullbackWithin_apply,
      mfderivWithin_univ, coordinateMap]
    calc
      _ = mfderiv I' 𝓘(ℝ, F) targetChart (f (sourceChart.symm z))
          (Ybar (f (sourceChart.symm z))) := by
        convert targetPullback_eq using 1
        rw [targetChart.left_inv hfy]
      _ = mfderiv I' 𝓘(ℝ, F) targetChart (f (sourceChart.symm z))
          (mfderiv I I' f (sourceChart.symm z) (Y (sourceChart.symm z))) := by
        rw [related]
      _ = _ := coordinateDerivative.symm
  have relatedCoordinateV :
      targetV ∘ coordinateMap =ᶠ[𝓝 (sourceChart x)]
        fun y ↦ fderiv ℝ coordinateMap y (sourceV y) := by
    exact relatedCoordinate V Vbar relatedV
  have relatedCoordinateW :
      targetW ∘ coordinateMap =ᶠ[𝓝 (sourceChart x)]
        fun y ↦ fderiv ℝ coordinateMap y (sourceW y) := by
    exact relatedCoordinate W Wbar relatedW
  have coordinateBracket :=
    VectorField.lieBracket_eq_fderiv_lieBracket_of_related
      coordinateC2 sourceVdiff sourceWdiff
      (coordinateValue ▸ targetVdiff) (coordinateValue ▸ targetWdiff)
      relatedCoordinateV relatedCoordinateW
  let sourceDerivative := mfderiv I 𝓘(ℝ, E) sourceChart x
  let targetDerivative := mfderiv I' 𝓘(ℝ, F) targetChart (f x)
  have sourceDerivativeInvertible : sourceDerivative.IsInvertible := by
    exact isInvertible_mfderiv_extChartAt (I := I) (mem_extChartAt_source x)
  have targetDerivativeInvertible : targetDerivative.IsInvertible := by
    exact isInvertible_mfderiv_extChartAt (I := I') (mem_extChartAt_source (f x))
  have sourceCoordinate :
      sourceDerivative (VectorField.mlieBracket I V W x) =
        VectorField.lieBracket ℝ sourceV sourceW (sourceChart x) := by
    dsimp only [sourceDerivative]
    rw [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply]
    simp only [ModelWithCorners.Boundaryless.range_eq_univ,
      Set.preimage_univ, Set.inter_self, VectorField.lieBracketWithin_univ]
    rw [sourceDerivativeInvertible.self_apply_inverse]
  have targetCoordinate :
      targetDerivative (VectorField.mlieBracket I' Vbar Wbar (f x)) =
        VectorField.lieBracket ℝ targetV targetW (targetChart (f x)) := by
    dsimp only [targetDerivative]
    rw [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply]
    simp only [ModelWithCorners.Boundaryless.range_eq_univ,
      Set.preimage_univ, Set.inter_self, VectorField.lieBracketWithin_univ]
    rw [targetDerivativeInvertible.self_apply_inverse]
  have coordinateDerivativeAtBracket :
      fderiv ℝ coordinateMap (sourceChart x)
          (VectorField.lieBracket ℝ sourceV sourceW (sourceChart x)) =
        targetDerivative
          (mfderiv I I' f x (VectorField.mlieBracket I V W x)) := by
    have hsourceSymm : MDiffAt sourceChart.symm (sourceChart x) := by
      have hwithin :=
        (contMDiffWithinAt_extChartAt_symm_range_self
          (I := I) (n := 1) x).mdifferentiableWithinAt (by norm_num)
      rw [ModelWithCorners.Boundaryless.range_eq_univ,
        mdifferentiableWithinAt_univ] at hwithin
      simpa [sourceChart] using hwithin
    have hfAt : MDiffAt f x :=
      hf.contMDiffAt.mdifferentiableAt (by norm_num)
    have htargetChart : MDiffAt targetChart (f x) := by
      simpa [targetChart] using
        mdifferentiableAt_extChartAt (I := I')
          (ChartedSpace.mem_chart_source (f x))
    have hsourceInverse :
        (mfderiv 𝓘(ℝ, E) I sourceChart.symm
          (sourceChart x)).IsInvertible := by
      simpa [sourceChart, ModelWithCorners.Boundaryless.range_eq_univ,
        mfderivWithin_univ] using
        (isInvertible_mfderivWithin_extChartAt_symm (I := I)
          (mem_extChartAt_target x))
    have sourceInverseChart (v : TangentSpace I x) :
        (mfderiv 𝓘(ℝ, E) I sourceChart.symm
            (sourceChart x)).inverse v =
          mfderiv I 𝓘(ℝ, E) sourceChart x v := by
      apply hsourceInverse.inverse_apply_eq.mpr
      rw [← ContinuousLinearMap.comp_apply]
      have hcomp :=
        mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
          (I := I) (mem_extChartAt_source x)
      rw [ModelWithCorners.Boundaryless.range_eq_univ,
        mfderivWithin_univ] at hcomp
      convert! congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x ↦
        L v) hcomp |>.symm <;> exact sourceChart.left_inv (mem_extChartAt_source x)
    have sourceCancel (v : TangentSpace I x) :
        mfderiv 𝓘(ℝ, E) I sourceChart.symm (sourceChart x)
            (sourceDerivative v) = v := by
      dsimp only [sourceDerivative]
      rw [← sourceInverseChart]
      exact hsourceInverse.self_apply_inverse v
    rw [← sourceCoordinate]
    rw [← mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F)
        ((targetChart ∘ f) ∘ sourceChart.symm) (sourceChart x)
          (sourceDerivative (VectorField.mlieBracket I V W x)) = _
    have sourceLeft : sourceChart.symm (sourceChart x) = x :=
      sourceChart.left_inv (mem_extChartAt_source x)
    have hfAtSource : MDiffAt f (sourceChart.symm (sourceChart x)) := by
      simpa [sourceLeft] using hfAt
    have htargetAtSource :
        MDiffAt targetChart (f (sourceChart.symm (sourceChart x))) := by
      simpa [sourceLeft] using htargetChart
    rw [mfderiv_comp_apply _ (htargetAtSource.comp _ hfAtSource) hsourceSymm]
    rw [mfderiv_comp_apply _ htargetAtSource hfAtSource]
    rw [sourceCancel]
    rw [sourceLeft]
  apply targetDerivativeInvertible.injective
  rw [targetCoordinate]
  rw [← coordinateValue, coordinateBracket, coordinateDerivativeAtBracket]
  rfl

end VectorField

end Manifold

end

end RiemannianFluids
