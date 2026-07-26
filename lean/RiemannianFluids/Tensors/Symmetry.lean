import RiemannianFluids.Geometry.Manifolds
import RiemannianFluids.Tensors.SmoothSections

/-!
# Natural symmetry operations on covariant two-tensors

Transposition and symmetrization are defined fiberwise and proved smooth in
bundle coordinates.  The coordinate proof is the naturality step: changing
tangent coordinates and then transposing gives the same tensor as
transposing first and then changing coordinates.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]

set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
/-- Coordinate-natural transposition of a covariant two-tensor. -/
noncomputable def transposeCovariantTwoTensor (regularity : ℕ∞ω) :
    SmoothCovariantTwoTensor (M := M) I regularity →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity where
  toFun field :=
    { toFun := fun x => (field x).flip
      contMDiff_toFun := by
        intro x₀
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_id, ?_⟩
        have hfield :
            ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) regularity
              (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (field x)) x₀ :=
          field.contMDiff.contMDiffAt
        rw [contMDiffAt_hom_bundle] at hfield
        have hflip : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) regularity
            (fun x : M => ContinuousLinearMap.flip
              (ContinuousLinearMap.inCoordinates
                E (TangentSpace I : M → Type _)
                (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)
                x₀ x x₀ x (field x))) x₀ := by
          have hflipAt : ContMDiffAt 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)
              𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) regularity ContinuousLinearMap.flip
              (ContinuousLinearMap.inCoordinates
                E (TangentSpace I : M → Type _)
                (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)
                x₀ x₀ x₀ x₀ (field x₀)) := by
            apply ContDiffAt.contMDiffAt
            apply ContDiff.contDiffAt
            apply IsBoundedLinearMap.contDiff
            refine IsBoundedLinearMap.mk (IsLinearMap.mk ?_ ?_) ?_
            · exact ContinuousLinearMap.flip_add
            · exact ContinuousLinearMap.flip_smul
            · refine ⟨1, zero_lt_one, ?_⟩
              intro tensor
              rw [ContinuousLinearMap.opNorm_flip, one_mul]
          exact hflipAt.comp x₀ hfield.2
        apply hflip.congr_of_eventuallyEq
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
        rw [ContinuousLinearMap.inCoordinates_eq hx hxstar,
          ContinuousLinearMap.inCoordinates_eq hx hxstar]
        ext u v
        simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
        simp [ContinuousLinearMap.flip_apply, hom_trivializationAt,
          Bundle.Trivialization.continuousLinearMap_apply]
        rw [(trivializationAt E (TangentSpace I : M → Type _) x₀).symmL_apply hx v,
          (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL_apply hx u] }
  map_add' first second := by
    ext x u v
    simp
  map_smul' scalar field := by
    ext x u v
    simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
@[simp]
theorem transposeCovariantTwoTensor_apply (regularity : ℕ∞ω)
    (field : SmoothCovariantTwoTensor (M := M) I regularity)
    (x : M) (u v : TangentSpace I x) :
    transposeCovariantTwoTensor I regularity field x u v = field x v u :=
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
@[simp]
theorem transposeCovariantTwoTensor_involutive (regularity : ℕ∞ω)
    (field : SmoothCovariantTwoTensor (M := M) I regularity) :
    transposeCovariantTwoTensor I regularity
        (transposeCovariantTwoTensor I regularity field) = field := by
  ext x u v
  rfl

set_option synthInstance.maxHeartbeats 100000 in
/-- Fiberwise symmetrization `T ↦ (T + Tᵀ) / 2`. -/
noncomputable def symmetrizeCovariantTwoTensor (regularity : ℕ∞ω) :
    SmoothCovariantTwoTensor (M := M) I regularity →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity :=
  (2 : ℝ)⁻¹ • (LinearMap.id + transposeCovariantTwoTensor I regularity)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
set_option synthInstance.maxHeartbeats 100000 in
@[simp]
theorem symmetrizeCovariantTwoTensor_apply (regularity : ℕ∞ω)
    (field : SmoothCovariantTwoTensor (M := M) I regularity)
    (x : M) (u v : TangentSpace I x) :
    symmetrizeCovariantTwoTensor I regularity field x u v =
      (2 : ℝ)⁻¹ * (field x u v + field x v u) := by
  simp [symmetrizeCovariantTwoTensor, transposeCovariantTwoTensor_apply]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem symmetrizeCovariantTwoTensor_symmetric (regularity : ℕ∞ω)
    (field : SmoothCovariantTwoTensor (M := M) I regularity) :
    transposeCovariantTwoTensor I regularity
        (symmetrizeCovariantTwoTensor I regularity field) =
      symmetrizeCovariantTwoTensor I regularity field := by
  ext x u v
  rw [transposeCovariantTwoTensor_apply,
    symmetrizeCovariantTwoTensor_apply, symmetrizeCovariantTwoTensor_apply]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
@[simp]
theorem symmetrizeCovariantTwoTensor_idempotent (regularity : ℕ∞ω)
    (field : SmoothCovariantTwoTensor (M := M) I regularity) :
    symmetrizeCovariantTwoTensor I regularity
        (symmetrizeCovariantTwoTensor I regularity field) =
      symmetrizeCovariantTwoTensor I regularity field := by
  ext x u v
  rw [symmetrizeCovariantTwoTensor_apply, symmetrizeCovariantTwoTensor_apply,
    symmetrizeCovariantTwoTensor_apply]
  ring

end RiemannianFluids
