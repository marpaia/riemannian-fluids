import Mathlib.Analysis.InnerProductSpace.Dual
import RiemannianFluids.Geometry.Manifolds
import RiemannianFluids.Tensors.SmoothSections

/-!
# Musical equivalence on smooth sections

On a Riemannian manifold the metric is more than a way to measure length. At each point it turns a tangent vector into the covector that takes an
inner product against it:

    flat_x(v) = v♭ = g_x(v,·).

Finite-dimensional Riesz representation says this map is an isomorphism. Its inverse is called `sharp`:

    sharp_x(α) = α♯,
    g_x(α♯,w) = α(w).

This identification is so conventional on paper that authors often use the same letter for a vector field and its metric-dual one-form. Immediately
after equation (1.3), Chan--Czubak--Disconzi explicitly adopt that convention when interpreting `d* v = 0`. Lean refuses the identification: sections
of `TM` and `T*M` have different types. That refusal is analytically helpful, because every passage between vector and form operators is now visible.

## The one real issue: a smooth inverse family

Pointwise invertibility is easy. Positive definiteness of `g_x` identifies `T_xM` with its dual. But defining `sharp` on *smooth sections* requires
more: the inverse maps `flat_x⁻¹` must themselves vary smoothly with `x`.

In local bundle coordinates the metric becomes a smooth family of invertible continuous linear maps

    G(x) : E → E*,

and inversion is smooth on the open set of invertible maps. Hence `x ↦ G(x)⁻¹` is smooth. The coordinate inverse still has to be related to the
intrinsic inverse in the moving fibers; that last calculation says that inverting a conjugated operator conjugates its inverse in the opposite order.

## The construction

The proof proceeds in four stages.

1. Extract from mathlib's `IsContMDiffRiemannianBundle` a smooth bilinear tensor `metricTensor` and record that it evaluates to the fiber inner
   product.
2. Apply it pointwise to construct `flat`. Smoothness follows from smooth application of a family of continuous linear maps.
3. Use finite-dimensional Riesz duality to prove each metric map invertible, then prove that its inverse family is smooth in local coordinates. This
   is the long proof `sharpFiber_contMDiff`.
4. Package that inverse family as `sharp` and check `sharp (flat u) = u` and `flat (sharp α) = α` from the two inverse laws.

The same metric-lowering idea is also applied to a tangent-valued one-form `A : TM → TM`. It produces the covariant tensor

    (X,Y) ↦ g(A X,Y).

With `A = ∇u`, this is the unsymmetrized tensor that the next layer turns into `Def u`. Thus the module explains two normally invisible paper moves:
identifying vectors with one-forms, and lowering the output index of `∇u`.
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

/--
The smooth metric tensor supplied by the Riemannian-bundle regularity class.

`IsContMDiffRiemannianBundle` states existence of a smooth bilinear form equal to the fiber inner product. `Classical.choose` selects that witness;
the next two theorems immediately recover its smoothness and pointwise meaning.
-/
noncomputable def metricTensor (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  Classical.choose
    (IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := I) (n := regularity) (F := E)
      (E := (TangentSpace I : M → Type _))) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The chosen representative of the metric is a `C^k` bilinear-form section. -/
theorem metricTensor_contMDiff :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) regularity
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        (metricTensor I regularity x)) :=
  -- The first component of the witness specification is smoothness.
  (Classical.choose_spec
    (IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := I) (n := regularity) (F := E)
      (E := (TangentSpace I : M → Type _)))).1

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Evaluating the chosen metric tensor recovers the tangent-fiber inner product. -/
@[simp]
theorem metricTensor_apply (x : M) (v w : TangentSpace I x) :
    metricTensor I regularity x v w = inner ℝ v w :=
  -- The second component identifies the chosen bilinear form with `g(v,w)`.
  (Classical.choose_spec
    (IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := I) (n := regularity) (F := E)
      (E := (TangentSpace I : M → Type _)))).2 x v w |>.symm

set_option backward.isDefEq.respectTransparency false in
/--
Metric lowering as a linear map on `C^k` sections: `u♭(X) = g(u,X)`. No derivative is taken, so regularity is preserved.
-/
noncomputable def flat :
    SmoothVectorField (M := M) I regularity →ₗ[ℝ]
      SmoothOneForm (M := M) I regularity where
  toFun field :=
    -- Lower the vector independently in each tangent fiber.
    { toFun := fun x => metricTensor I regularity x (field x)
      contMDiff_toFun :=
        -- Smooth application of a smooth family of continuous linear maps to a smooth section gives another smooth section.
        (metricTensor_contMDiff I regularity).clm_bundle_apply field.contMDiff }
  map_add' first second := by
    -- Fiberwise bilinearity of the metric proves additivity.
    ext x direction
    simp
  map_smul' scalar field := by
    -- Fiberwise bilinearity also proves compatibility with real scalars.
    ext x direction
    simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Pointwise, `flat` is evaluation of the Riemannian metric against the field. -/
@[simp]
theorem flat_apply (field : SmoothVectorField (M := M) I regularity)
    (x : M) (direction : TangentSpace I x) :
    flat I regularity field x direction = inner ℝ (field x) direction :=
  metricTensor_apply I regularity x (field x) direction

/--
Lower the tangent-valued output of a fiber endomorphism with the metric: `A ↦ ((X,Y) ↦ g(A X,Y))`. Applied to `A = ∇u`, this is the unsymmetrized
two-tensor used in CCD17 equation (1.2).
-/
noncomputable def lowerVectorOneFormFiber (x : M)
    (field : TangentSpace I x →L[ℝ] TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (metricTensor I regularity x).comp field

set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
/--
Metric lowering of tangent-valued one-forms as a smooth linear map `C^k(Hom(TM, TM)) → C^k(T*M ⊗ T*M)`.
-/
noncomputable def lowerVectorOneForm :
    SmoothVectorOneForm (M := M) I regularity →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity where
  toFun field :=
    -- The pointwise formula is the fiber construction just defined.
    { toFun := fun x => lowerVectorOneFormFiber I regularity x (field x)
      contMDiff_toFun := by
        -- Prove smoothness at an arbitrary base point in hom-bundle coordinates.
        intro x₀
        rw [contMDiffAt_hom_bundle]
        -- The section lies over the identity base map; prove smoothness of its coordinate value as the second component.
        refine ⟨contMDiffAt_id, ?_⟩
        -- Put the metric's global smoothness hypothesis at the chosen point.
        have hmetric :
            ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) regularity
              (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
                (metricTensor I regularity x)) x₀ :=
          (metricTensor_contMDiff I regularity).contMDiffAt
        -- Convert smoothness of the metric section to smoothness of its local continuous-bilinear-map coordinates.
        rw [contMDiffAt_hom_bundle] at hmetric
        -- Do the same for the tangent-valued one-form being lowered.
        have hfield :
            ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) regularity
              (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x (field x)) x₀ :=
          field.contMDiff.contMDiffAt
        rw [contMDiffAt_hom_bundle] at hfield
        -- Composition of the coordinate metric with the coordinate endomorphism is smooth. This is the local formula for `g ∘ A`.
        have hcomposition := hmetric.2.clm_comp hfield.2
        -- It remains to show that this coordinate composition agrees locally with the intrinsic pointwise definition.
        apply hcomposition.congr_of_eventuallyEq
        -- Choose neighborhoods where the tangent trivialization is valid.
        have htangent :
            (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ 𝓝 x₀ :=
          (trivializationAt _ _ _).open_baseSet.mem_nhds
            (FiberBundle.mem_baseSet_trivializationAt' _)
        -- Choose the analogous neighborhood for the cotangent bundle.
        have hcotangent :
            (trivializationAt (E →L[ℝ] ℝ)
              (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀).baseSet ∈ 𝓝 x₀ :=
          (trivializationAt _ _ _).open_baseSet.mem_nhds
            (FiberBundle.mem_baseSet_trivializationAt' _)
        -- Work at a point in both neighborhoods.
        filter_upwards [htangent, hcotangent] with x hx hxstar
        -- Replace abstract coordinate maps by the corresponding local linear equivalences on this neighborhood.
        rw [ContinuousLinearMap.inCoordinates_eq hx hxstar,
          ContinuousLinearMap.inCoordinates_eq hx hxstar,
          ContinuousLinearMap.inCoordinates_eq hx hx]
        -- Equality of bilinear maps is checked on two model-space vectors.
        ext direction test
        -- Expose the compositions as ordinary function application.
        simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
          lowerVectorOneFormFiber]
        -- Name the tangent and cotangent coordinate equivalences to keep the cancellation argument readable.
        let tangentCoordinates :=
          (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt
            ℝ x hx
        let cotangentCoordinates :=
          (trivializationAt (E →L[ℝ] ℝ)
            (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀).continuousLinearEquivAt
              ℝ x hxstar
        -- `value` is `A` applied to the intrinsic direction represented by the model vector `direction`.
        let value := field x (tangentCoordinates.symm direction)
        -- Changing `value` to coordinates and back does nothing.
        have hcancel : tangentCoordinates.symm (tangentCoordinates value) = value :=
          tangentCoordinates.symm_apply_apply value
        -- After spelling out the local charts, naturality reduces exactly to that inverse-law cancellation.
        change cotangentCoordinates (metricTensor I regularity x value) test =
          cotangentCoordinates
            (metricTensor I regularity x
              (tangentCoordinates.symm (tangentCoordinates value))) test
        rw [hcancel] }
  map_add' first second := by
    -- The fiber formula is additive in the endomorphism being lowered.
    ext x direction test
    simp [lowerVectorOneFormFiber]
  map_smul' scalar field := by
    -- The same fiber formula is homogeneous over `ℝ`.
    ext x direction test
    simp [lowerVectorOneFormFiber]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The section-level lowering map evaluates to `g(A X,Y)` in each fiber. -/
@[simp]
theorem lowerVectorOneForm_apply
    (field : SmoothVectorOneForm (M := M) I regularity)
    (x : M) (direction test : TangentSpace I x) :
    lowerVectorOneForm I regularity field x direction test =
      inner ℝ (field x direction) test := by
  -- Expose the fiberwise composition chosen by the bundled definition.
  rw [show lowerVectorOneForm I regularity field x =
    lowerVectorOneFormFiber I regularity x (field x) from rfl]
  -- The chosen metric tensor evaluates to the Riemannian inner product.
  exact metricTensor_apply I regularity x (field x direction) test

section Sharp

private noncomputable def metricEquiv (x : M) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  -- Riesz duality is an equivalence in a finite-dimensional complete inner product space; install those fiber instances explicitly.
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  letI : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).toLinearEquiv.toContinuousLinearEquiv

omit [CompleteSpace E] in
/-- Riesz lowering and the selected smooth metric tensor are the same fiber map. -/
private theorem metricEquiv_apply (x : M) (v : TangentSpace I x) :
    metricEquiv I x v = metricTensor I regularity x v := by
  -- Covectors are equal when they agree on every test vector.
  ext w
  -- Replace the chosen metric tensor by the inner product.
  rw [metricTensor_apply]
  -- Riesz duality is defined by the same inner product.
  simp [metricEquiv]

omit [CompleteSpace E] in
/-- Positive definiteness makes the metric-lowering map invertible in every fiber. -/
private theorem metricTensor_isInvertible (x : M) :
    (metricTensor I regularity x).IsInvertible := by
  -- Supply the Riesz continuous-linear equivalence as the inverse witness.
  refine ⟨metricEquiv I x, ?_⟩
  -- Equality of continuous bilinear maps is checked on two vectors.
  ext v w
  -- The preceding theorem identifies Riesz lowering with the chosen metric.
  exact metricEquiv_apply I regularity x v ▸ rfl

private noncomputable def sharpFiber (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x :=
  (metricTensor I regularity x).inverse

set_option backward.isDefEq.respectTransparency false in
/-- The pointwise inverse metric maps form a `C^k` hom-bundle section. -/
private theorem sharpFiber_contMDiff :
    ContMDiff I (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)) regularity
      (fun x : M => TotalSpace.mk' ((E →L[ℝ] ℝ) →L[ℝ] E) x
        (sharpFiber I regularity x)) := by
  -- Smoothness of the inverse family is local on the base.
  intro x₀
  -- Use the hom-bundle coordinate characterization of smooth sections.
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  -- Start with smoothness of the metric family at the chosen base point.
  have hmetric : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) regularity
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        (metricTensor I regularity x)) x₀ :=
    (metricTensor_contMDiff I regularity).contMDiffAt
  rw [contMDiffAt_hom_bundle] at hmetric
  -- In model coordinates, apply mathlib's smooth inverse-map theorem to the smooth family of invertible continuous linear maps.
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
      -- Move from ordinary differentiability on normed spaces to manifold differentiability on their identity models.
      apply ContDiffAt.contMDiffAt
      -- Matrix/operator inversion is smooth near an invertible operator.
      apply ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
      -- At the center of the chart, identify the coordinate metric with a conjugate of the intrinsic metric.
      rw [ContinuousLinearMap.inCoordinates_eq
        (FiberBundle.mem_baseSet_trivializationAt' x₀)
        (FiberBundle.mem_baseSet_trivializationAt' x₀)]
      exact ContinuousLinearMap.isInvertible_equiv.comp
        ((metricTensor_isInvertible I regularity x₀).comp
          ContinuousLinearMap.isInvertible_equiv)
    -- Compose inverse-map smoothness with smoothness of the metric family.
    exact hinverseAt.comp x₀ hmetric.2
  -- Relate the inverse computed in coordinates to the intrinsic `sharpFiber`.
  apply hinverse.congr_of_eventuallyEq
  -- Restrict to neighborhoods where tangent and cotangent charts are valid.
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
  -- Expand the function composition and rewrite coordinate changes as linear equivalences.
  simp only [Function.comp_apply]
  rw [ContinuousLinearMap.inCoordinates_eq hx hxstar,
    ContinuousLinearMap.inCoordinates_eq hxstar hx]
  -- Inverse of a conjugated equivalence is the oppositely conjugated inverse; mathlib's simplifier closes this naturality calculation.
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv, ContinuousLinearEquiv.symm_symm, sharpFiber]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Metric raising as a linear map on `C^k` sections. Pointwise this applies the inverse Riesz map, and `sharpFiber_contMDiff` is the nontrivial proof
that the inverse varies smoothly with the base point.
-/
noncomputable def sharp :
    SmoothOneForm (M := M) I regularity →ₗ[ℝ]
      SmoothVectorField (M := M) I regularity where
  toFun form :=
    -- Apply the inverse metric independently in each fiber.
    { toFun := fun x => sharpFiber I regularity x (form x)
      contMDiff_toFun :=
        -- Smooth family application preserves the section's regularity.
        (sharpFiber_contMDiff I regularity).clm_bundle_apply form.contMDiff }
  map_add' first second := by
    -- Inversion produced a continuous linear map, hence it preserves addition.
    ext x
    simp [sharpFiber]
  map_smul' scalar form := by
    -- The same continuous linear map preserves scalar multiplication.
    ext x
    simp [sharpFiber]

/-- Raising after lowering is the identity on smooth vector fields. -/
@[simp]
theorem sharp_flat (field : SmoothVectorField (M := M) I regularity) :
    sharp I regularity (flat I regularity field) = field := by
  -- Section equality reduces to equality in each tangent fiber.
  ext x
  -- Apply the left inverse law of the invertible metric tensor.
  exact (metricTensor_isInvertible I regularity x).inverse_apply_self (field x)

/-- Lowering after raising is the identity on smooth one-forms. -/
@[simp]
theorem flat_sharp (form : SmoothOneForm (M := M) I regularity) :
    flat I regularity (sharp I regularity form) = form := by
  -- One-forms are equal if they agree at every point and direction.
  ext x direction
  -- Express lowering through the chosen metric tensor.
  rw [flat_apply, ← metricTensor_apply I regularity x]
  -- Expose `sharpFiber` so the right inverse law has the expected shape.
  change metricTensor I regularity x (sharpFiber I regularity x (form x)) direction =
    form x direction
  rw [show sharpFiber I regularity x = (metricTensor I regularity x).inverse from rfl]
  -- Apply the right inverse law of the invertible metric tensor.
  rw [(metricTensor_isInvertible I regularity x).self_apply_inverse]

/--
The metric gives a linear equivalence between smooth vector fields and one-forms. The fields of the structure are exactly the two constructions and
inverse theorems proved above; no additional mathematics is hidden here.
-/
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
