import Mathlib.Analysis.InnerProductSpace.Dual
import RiemannianFluids.Geometry.Manifolds
import RiemannianFluids.Tensors.SmoothSections

/-!
# Musical equivalence on smooth sections

The Riemannian metric lowers tangent vectors to covectors.  Finite-dimensional
Riesz representation supplies the inverse, and smoothness of the inverse
family is proved in bundle coordinates rather than assumed.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
  (regularity : ℕ∞ω)
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]

/-- The smooth metric tensor supplied by the Riemannian-bundle regularity class. -/
noncomputable def metricTensor (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  Classical.choose
    (IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := I) (n := regularity) (F := E)
      (E := (TangentSpace I : M → Type _))) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem metricTensor_contMDiff :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) regularity
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        (metricTensor I regularity x)) :=
  (Classical.choose_spec
    (IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := I) (n := regularity) (F := E)
      (E := (TangentSpace I : M → Type _)))).1

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
theorem metricTensor_apply (x : M) (v w : TangentSpace I x) :
    metricTensor I regularity x v w = inner ℝ v w :=
  (Classical.choose_spec
    (IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := I) (n := regularity) (F := E)
      (E := (TangentSpace I : M → Type _)))).2 x v w |>.symm

set_option backward.isDefEq.respectTransparency false in
/-- Metric lowering as a linear map on `C^k` sections. -/
noncomputable def flat :
    SmoothVectorField (M := M) I regularity →ₗ[ℝ]
      SmoothOneForm (M := M) I regularity where
  toFun field :=
    { toFun := fun x => metricTensor I regularity x (field x)
      contMDiff_toFun :=
        (metricTensor_contMDiff I regularity).clm_bundle_apply field.contMDiff }
  map_add' first second := by
    ext x direction
    simp
  map_smul' scalar field := by
    ext x direction
    simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
theorem flat_apply (field : SmoothVectorField (M := M) I regularity)
    (x : M) (direction : TangentSpace I x) :
    flat I regularity field x direction = inner ℝ (field x) direction :=
  metricTensor_apply I regularity x (field x) direction

/-- Lower the tangent-valued output of a fiber endomorphism with the metric. -/
noncomputable def lowerVectorOneFormFiber (x : M)
    (field : TangentSpace I x →L[ℝ] TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (metricTensor I regularity x).comp field

set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
/--
Metric lowering of tangent-valued one-forms as a smooth linear map
`C^k(Hom(TM, TM)) → C^k(T*M ⊗ T*M)`.
-/
noncomputable def lowerVectorOneForm :
    SmoothVectorOneForm (M := M) I regularity →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity where
  toFun field :=
    { toFun := fun x => lowerVectorOneFormFiber I regularity x (field x)
      contMDiff_toFun := by
        intro x₀
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_id, ?_⟩
        have hmetric :
            ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) regularity
              (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
                (metricTensor I regularity x)) x₀ :=
          (metricTensor_contMDiff I regularity).contMDiffAt
        rw [contMDiffAt_hom_bundle] at hmetric
        have hfield :
            ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) regularity
              (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x (field x)) x₀ :=
          field.contMDiff.contMDiffAt
        rw [contMDiffAt_hom_bundle] at hfield
        have hcomposition := hmetric.2.clm_comp hfield.2
        apply hcomposition.congr_of_eventuallyEq
        have htangent :
            (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ 𝓝 x₀ :=
          (trivializationAt _ _ _).open_baseSet.mem_nhds
            (FiberBundle.mem_baseSet_trivializationAt' _)
        have hcotangent :
            (trivializationAt (E →L[ℝ] ℝ)
              (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀).baseSet ∈ 𝓝 x₀ :=
          (trivializationAt _ _ _).open_baseSet.mem_nhds
            (FiberBundle.mem_baseSet_trivializationAt' _)
        filter_upwards [htangent, hcotangent] with x hx hxstar
        rw [ContinuousLinearMap.inCoordinates_eq hx hxstar,
          ContinuousLinearMap.inCoordinates_eq hx hxstar,
          ContinuousLinearMap.inCoordinates_eq hx hx]
        ext direction test
        simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
          lowerVectorOneFormFiber]
        let tangentCoordinates :=
          (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt
            ℝ x hx
        let cotangentCoordinates :=
          (trivializationAt (E →L[ℝ] ℝ)
            (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀).continuousLinearEquivAt
              ℝ x hxstar
        let value := field x (tangentCoordinates.symm direction)
        have hcancel : tangentCoordinates.symm (tangentCoordinates value) = value :=
          tangentCoordinates.symm_apply_apply value
        change cotangentCoordinates (metricTensor I regularity x value) test =
          cotangentCoordinates
            (metricTensor I regularity x
              (tangentCoordinates.symm (tangentCoordinates value))) test
        rw [hcancel] }
  map_add' first second := by
    ext x direction test
    simp [lowerVectorOneFormFiber]
  map_smul' scalar field := by
    ext x direction test
    simp [lowerVectorOneFormFiber]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
theorem lowerVectorOneForm_apply
    (field : SmoothVectorOneForm (M := M) I regularity)
    (x : M) (direction test : TangentSpace I x) :
    lowerVectorOneForm I regularity field x direction test =
      inner ℝ (field x direction) test := by
  rw [show lowerVectorOneForm I regularity field x =
    lowerVectorOneFormFiber I regularity x (field x) from rfl]
  exact metricTensor_apply I regularity x (field x direction) test

section Sharp

private noncomputable def metricEquiv (x : M) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  letI : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).toLinearEquiv.toContinuousLinearEquiv

omit [CompleteSpace E] in
private theorem metricEquiv_apply (x : M) (v : TangentSpace I x) :
    metricEquiv I x v = metricTensor I regularity x v := by
  ext w
  rw [metricTensor_apply]
  simp [metricEquiv]

omit [CompleteSpace E] in
private theorem metricTensor_isInvertible (x : M) :
    (metricTensor I regularity x).IsInvertible := by
  refine ⟨metricEquiv I x, ?_⟩
  ext v w
  exact metricEquiv_apply I regularity x v ▸ rfl

private noncomputable def sharpFiber (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x :=
  (metricTensor I regularity x).inverse

set_option backward.isDefEq.respectTransparency false in
private theorem sharpFiber_contMDiff :
    ContMDiff I (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)) regularity
      (fun x : M => TotalSpace.mk' ((E →L[ℝ] ℝ) →L[ℝ] E) x
        (sharpFiber I regularity x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hmetric : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) regularity
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        (metricTensor I regularity x)) x₀ :=
    (metricTensor_contMDiff I regularity).contMDiffAt
  rw [contMDiffAt_hom_bundle] at hmetric
  have hinverse : ContMDiffAt I 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E) regularity
      (ContinuousLinearMap.inverse ∘
        (fun x : M => ContinuousLinearMap.inCoordinates
          E (TangentSpace I : M → Type _)
          (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)
          x₀ x x₀ x (metricTensor I regularity x))) x₀ := by
    have hinverseAt :
        ContMDiffAt 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)
          regularity ContinuousLinearMap.inverse
          (ContinuousLinearMap.inCoordinates
            E (TangentSpace I : M → Type _)
            (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)
            x₀ x₀ x₀ x₀ (metricTensor I regularity x₀)) := by
      apply ContDiffAt.contMDiffAt
      apply ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
      rw [ContinuousLinearMap.inCoordinates_eq
        (FiberBundle.mem_baseSet_trivializationAt' x₀)
        (FiberBundle.mem_baseSet_trivializationAt' x₀)]
      exact ContinuousLinearMap.isInvertible_equiv.comp
        ((metricTensor_isInvertible I regularity x₀).comp
          ContinuousLinearMap.isInvertible_equiv)
    exact hinverseAt.comp x₀ hmetric.2
  apply hinverse.congr_of_eventuallyEq
  have hT :
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _)
  have hTstar :
      (trivializationAt (E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _)
  filter_upwards [hT, hTstar] with x hx hxstar
  simp only [Function.comp_apply]
  rw [ContinuousLinearMap.inCoordinates_eq hx hxstar,
    ContinuousLinearMap.inCoordinates_eq hxstar hx]
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv, ContinuousLinearEquiv.symm_symm, sharpFiber]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Metric raising as a linear map on `C^k` sections. -/
noncomputable def sharp :
    SmoothOneForm (M := M) I regularity →ₗ[ℝ]
      SmoothVectorField (M := M) I regularity where
  toFun form :=
    { toFun := fun x => sharpFiber I regularity x (form x)
      contMDiff_toFun :=
        (sharpFiber_contMDiff I regularity).clm_bundle_apply form.contMDiff }
  map_add' first second := by
    ext x
    simp [sharpFiber]
  map_smul' scalar form := by
    ext x
    simp [sharpFiber]

@[simp]
theorem sharp_flat (field : SmoothVectorField (M := M) I regularity) :
    sharp I regularity (flat I regularity field) = field := by
  ext x
  exact (metricTensor_isInvertible I regularity x).inverse_apply_self (field x)

@[simp]
theorem flat_sharp (form : SmoothOneForm (M := M) I regularity) :
    flat I regularity (sharp I regularity form) = form := by
  ext x direction
  rw [flat_apply, ← metricTensor_apply I regularity x]
  change metricTensor I regularity x (sharpFiber I regularity x (form x)) direction =
    form x direction
  rw [show sharpFiber I regularity x = (metricTensor I regularity x).inverse from rfl]
  rw [(metricTensor_isInvertible I regularity x).self_apply_inverse]

/-- The metric gives a linear equivalence between smooth vector fields and one-forms. -/
noncomputable def musicalEquiv :
    SmoothVectorField (M := M) I regularity ≃ₗ[ℝ]
      SmoothOneForm (M := M) I regularity where
  toFun := flat I regularity
  invFun := sharp I regularity
  map_add' := (flat I regularity).map_add
  map_smul' := (flat I regularity).map_smul
  left_inv := sharp_flat I regularity
  right_inv := flat_sharp I regularity

end Sharp

end RiemannianFluids
