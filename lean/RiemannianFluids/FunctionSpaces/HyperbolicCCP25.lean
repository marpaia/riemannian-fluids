import RiemannianFluids.FunctionSpaces.HyperbolicScalarEnergy
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Exact CCP25 Hodge decomposition on the complete hyperbolic plane

The shifted scalar dense-range theorem is used first to identify the source harmonic remainder
with distributionally closed and coclosed forms.  Density of the concrete source embedding,
orthogonal projection, and the exact source norm then show that this identification is onto the
full harmonic `L²` sector.  The resulting inverse gives every harmonic `L²` form a canonical
source `H¹` representative and upgrades the abstract three-sector decomposition to the exact
canonical `N = 2`, `k = 1`, `a = 1` specialization of CCP25.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Set
open scoped NNReal RealInnerProductSpace

/-- The source exact closure maps into the concrete closed exact `L²` sector. -/
theorem hyperbolicOneFormH1ToL2_mem_exact
    (u : HyperbolicOneFormH1) (hu : u ∈ hyperbolicExactH1) :
    hyperbolicOneFormH1ToL2 u ∈ hyperbolicExactL2 := by
  change u ∈ hyperbolicExactCoreH1.topologicalClosure at hu
  have hle : hyperbolicExactCoreH1.topologicalClosure ≤
      hyperbolicExactL2.comap hyperbolicOneFormH1ToL2.toLinearMap :=
    hyperbolicExactCoreH1.topologicalClosure_minimal (by
      rintro _ ⟨f, rfl⟩
      change hyperbolicDZeroCoreL2 f ∈ hyperbolicExactL2
      exact Submodule.le_topologicalClosure
        (s := hyperbolicExactCoreL2) ⟨f, rfl⟩) (by
      exact isClosed_hyperbolicExactL2.preimage
        hyperbolicOneFormH1ToL2.continuous)
  exact hle hu

/-- The source coexact closure maps into the concrete closed coexact `L²` sector. -/
theorem hyperbolicOneFormH1ToL2_mem_coexact
    (u : HyperbolicOneFormH1) (hu : u ∈ hyperbolicCoexactH1) :
    hyperbolicOneFormH1ToL2 u ∈ hyperbolicCoexactL2 := by
  change u ∈ hyperbolicCoexactCoreH1.topologicalClosure at hu
  have hle : hyperbolicCoexactCoreH1.topologicalClosure ≤
      hyperbolicCoexactL2.comap hyperbolicOneFormH1ToL2.toLinearMap :=
    hyperbolicCoexactCoreH1.topologicalClosure_minimal (by
      rintro _ ⟨f, rfl⟩
      change hyperbolicDeltaTwoCoreL2 f ∈ hyperbolicCoexactL2
      exact Submodule.le_topologicalClosure
        (s := hyperbolicCoexactCoreL2) ⟨f, rfl⟩) (by
      exact isClosed_hyperbolicCoexactL2.preimage
        hyperbolicOneFormH1ToL2.continuous)
  exact hle hu

theorem hyperbolicOneFormH1ToL2_denseRange :
    DenseRange hyperbolicOneFormH1ToL2 := by
  apply DenseRange.of_comp (g := hyperbolicSmoothCompactOneFormToH1)
  have hcomp :
      (hyperbolicOneFormH1ToL2 ∘ hyperbolicSmoothCompactOneFormToH1) =
        (hyperbolicSmoothCompactToL2 :
          HyperbolicSmoothCompactOneForm → HyperbolicOneFormL2) := by
    funext alpha
    exact hyperbolicOneFormH1ToL2_core alpha
  rw [hcomp]
  exact hyperbolicSmoothCompactOneForm_dense

/-- No-hypothesis CCP25 Proposition 4.3 on the canonical hyperbolic plane. -/
theorem hyperbolicHarmonicH1_toL2_mem_harmonic
    (u : HyperbolicOneFormH1) (hu : u ∈ hyperbolicHarmonicH1) :
    hyperbolicOneFormH1ToL2 u ∈ hyperbolicHarmonicL2 :=
  hyperbolicHarmonicH1_toL2_mem_harmonic_of_shifted_denseRange'
    hyperbolicScalarShiftedHodgeCoreL2_denseRange u hu

noncomputable def hyperbolicHarmonicL2OrthogonalProjector :
    HyperbolicOneFormL2 →L[ℝ] hyperbolicHarmonicL2 :=
  ContinuousLinearMap.codRestrict hyperbolicHarmonicL2.starProjection
    hyperbolicHarmonicL2
    (fun u ↦ hyperbolicHarmonicL2.starProjection_apply_mem u)

theorem hyperbolicHarmonicL2OrthogonalProjector_surjective :
    Function.Surjective hyperbolicHarmonicL2OrthogonalProjector := by
  intro h
  refine ⟨(h : HyperbolicOneFormL2), ?_⟩
  apply Subtype.ext
  exact (Submodule.starProjection_eq_self_iff).2 h.property

/-- Project an arbitrary source `H¹` form onto its source harmonic remainder, then retain its
now-proved harmonic `L²` representative. -/
noncomputable def hyperbolicHarmonicH1ProjectedToHarmonicL2 :
    HyperbolicOneFormH1 →L[ℝ] hyperbolicHarmonicL2 :=
  ContinuousLinearMap.codRestrict
    (hyperbolicOneFormH1ToL2.comp hyperbolicHarmonicH1Projector)
    hyperbolicHarmonicL2
    (fun u ↦ hyperbolicHarmonicH1_toL2_mem_harmonic _
      (hyperbolicHarmonicH1Projector_mem u))

theorem hyperbolicHarmonicH1ProjectedToHarmonicL2_eq_projection
    (u : HyperbolicOneFormH1) :
    hyperbolicHarmonicH1ProjectedToHarmonicL2 u =
      hyperbolicHarmonicL2OrthogonalProjector
        (hyperbolicOneFormH1ToL2 u) := by
  let e := hyperbolicExactH1Projector u
  let c := hyperbolicCoexactH1Projector u
  let r := hyperbolicHarmonicH1Projector u
  have he : e ∈ hyperbolicExactH1 := hyperbolicExactH1Projector_mem u
  have hc : c ∈ hyperbolicCoexactH1 := hyperbolicCoexactH1Projector_mem u
  have hr : r ∈ hyperbolicHarmonicH1 := hyperbolicHarmonicH1Projector_mem u
  have heL2 : hyperbolicOneFormH1ToL2 e ∈ hyperbolicExactL2 :=
    hyperbolicOneFormH1ToL2_mem_exact e he
  have hcL2 : hyperbolicOneFormH1ToL2 c ∈ hyperbolicCoexactL2 :=
    hyperbolicOneFormH1ToL2_mem_coexact c hc
  have hrL2 : hyperbolicOneFormH1ToL2 r ∈ hyperbolicHarmonicL2 :=
    hyperbolicHarmonicH1_toL2_mem_harmonic r hr
  have hsum : u = e + c + r := hyperbolicH1_exact_add_coexact_add_harmonic u
  have hdiff : hyperbolicOneFormH1ToL2 u - hyperbolicOneFormH1ToL2 r ∈
      hyperbolicHarmonicL2.orthogonal := by
    have heq : hyperbolicOneFormH1ToL2 u - hyperbolicOneFormH1ToL2 r =
        hyperbolicOneFormH1ToL2 e + hyperbolicOneFormH1ToL2 c := by
      rw [hsum, map_add, map_add]
      abel
    rw [heq, Submodule.mem_orthogonal]
    intro z hz
    rw [inner_add_right]
    have hexact : inner ℝ z (hyperbolicOneFormH1ToL2 e) = 0 := by
      rw [real_inner_comm]
      exact hz.1 _ heL2
    have hcoexact : inner ℝ z (hyperbolicOneFormH1ToL2 c) = 0 := by
      rw [real_inner_comm]
      exact hz.2 _ hcL2
    rw [hexact, hcoexact, add_zero]
  have hprojection := hyperbolicHarmonicL2.eq_starProjection_of_mem_orthogonal
    hrL2 hdiff
  apply Subtype.ext
  exact hprojection.symm

theorem hyperbolicHarmonicH1ProjectedToHarmonicL2_denseRange :
    DenseRange hyperbolicHarmonicH1ProjectedToHarmonicL2 := by
  have hdenseProjection : DenseRange hyperbolicHarmonicL2OrthogonalProjector :=
    hyperbolicHarmonicL2OrthogonalProjector_surjective.denseRange
  have hcomp : DenseRange
      (hyperbolicHarmonicL2OrthogonalProjector ∘ hyperbolicOneFormH1ToL2) :=
    hdenseProjection.comp hyperbolicOneFormH1ToL2_denseRange
      hyperbolicHarmonicL2OrthogonalProjector.continuous
  have heq :
      (hyperbolicHarmonicL2OrthogonalProjector ∘ hyperbolicOneFormH1ToL2) =
        hyperbolicHarmonicH1ProjectedToHarmonicL2 := by
    funext u
    exact (hyperbolicHarmonicH1ProjectedToHarmonicL2_eq_projection u).symm
  rwa [heq] at hcomp

/-- The concrete map from the source harmonic remainder into the actual distributional harmonic
`L²` sector. -/
noncomputable def hyperbolicHarmonicH1ToHarmonicL2 :
    hyperbolicHarmonicH1 →L[ℝ] hyperbolicHarmonicL2 :=
  ContinuousLinearMap.codRestrict
    (hyperbolicOneFormH1ToL2.comp (Submodule.subtypeL hyperbolicHarmonicH1))
    hyperbolicHarmonicL2
    (fun u ↦ hyperbolicHarmonicH1_toL2_mem_harmonic u u.property)

@[simp] theorem hyperbolicHarmonicH1ToHarmonicL2_coe
    (u : hyperbolicHarmonicH1) :
    (hyperbolicHarmonicH1ToHarmonicL2 u : HyperbolicOneFormL2) =
      hyperbolicOneFormH1ToL2 u :=
  rfl

theorem hyperbolicHarmonicH1ToHarmonicL2_denseRange :
    DenseRange hyperbolicHarmonicH1ToHarmonicL2 := by
  let sourceProjection : HyperbolicOneFormH1 → hyperbolicHarmonicH1 :=
    fun u ↦ ⟨hyperbolicHarmonicH1Projector u,
      hyperbolicHarmonicH1Projector_mem u⟩
  apply DenseRange.of_comp (g := sourceProjection)
  have heq :
      (hyperbolicHarmonicH1ToHarmonicL2 ∘ sourceProjection) =
        hyperbolicHarmonicH1ProjectedToHarmonicL2 := by
    funext u
    apply Subtype.ext
    rfl
  rw [heq]
  exact hyperbolicHarmonicH1ProjectedToHarmonicL2_denseRange

/-- On the source harmonic remainder the exact CCP25 norm collapses to twice the `L²` norm. -/
theorem norm_sq_hyperbolicHarmonicH1ToHarmonicL2
    (u : hyperbolicHarmonicH1) :
    ‖u‖ ^ 2 = 2 * ‖hyperbolicHarmonicH1ToHarmonicL2 u‖ ^ 2 := by
  have hharmonic : hyperbolicOneFormH1ToL2 (u : HyperbolicOneFormH1) ∈
      hyperbolicHarmonicL2 :=
    hyperbolicHarmonicH1_toL2_mem_harmonic u u.property
  have hhodge : hyperbolicOneFormH1Hodge (u : HyperbolicOneFormH1) = 0 :=
    (hyperbolicOneFormH1ToL2_mem_harmonic_iff u).1 hharmonic
  change ‖(u : HyperbolicOneFormH1)‖ ^ 2 =
    2 * ‖hyperbolicOneFormH1ToL2 (u : HyperbolicOneFormH1)‖ ^ 2
  rw [norm_sq_hyperbolicOneFormH1, hhodge, norm_zero,
    zero_pow (by decide : 2 ≠ 0), add_zero]

theorem hyperbolicHarmonicH1ToHarmonicL2_injective :
    Function.Injective hyperbolicHarmonicH1ToHarmonicL2 := by
  intro u v huv
  apply Subtype.ext
  apply hyperbolicOneFormH1ToL2_injective
  exact congrArg Subtype.val huv

theorem hyperbolicHarmonicH1ToHarmonicL2_lower_bound
    (u : hyperbolicHarmonicH1) :
    (1 / 2 : ℝ) * ‖u‖ ≤ ‖hyperbolicHarmonicH1ToHarmonicL2 u‖ := by
  let x := ‖u‖
  let y := ‖hyperbolicHarmonicH1ToHarmonicL2 u‖
  have hsq : x ^ 2 = 2 * y ^ 2 :=
    norm_sq_hyperbolicHarmonicH1ToHarmonicL2 u
  have hx : 0 ≤ x := norm_nonneg u
  have hy : 0 ≤ y := norm_nonneg _
  have hxy : x ≤ 2 * y := by
    by_contra hnot
    have hlt : 2 * y < x := lt_of_not_ge hnot
    have hleft : 0 < x - 2 * y := sub_pos.mpr hlt
    have hright : 0 < x + 2 * y := by linarith
    have hproduct : 0 < (x - 2 * y) * (x + 2 * y) :=
      mul_pos hleft hright
    nlinarith
  dsimp [x, y] at hxy ⊢
  linarith

/-- The source harmonic remainder exhausts the full distributional harmonic `L²` sector. -/
theorem hyperbolicHarmonicH1ToHarmonicL2_surjective :
    Function.Surjective hyperbolicHarmonicH1ToHarmonicL2 := by
  have hantiExists : ∃ K : ℝ≥0,
      AntilipschitzWith K hyperbolicHarmonicH1ToHarmonicL2 :=
    (antilipschitzWith_iff_exists_mul_le_norm).2
      ⟨1 / 2, by norm_num, hyperbolicHarmonicH1ToHarmonicL2_lower_bound⟩
  obtain ⟨K, hanti⟩ := hantiExists
  have hclosed : IsClosed (Set.range hyperbolicHarmonicH1ToHarmonicL2) :=
    hanti.isClosed_range hyperbolicHarmonicH1ToHarmonicL2.uniformContinuous
  have hdense : Dense (Set.range hyperbolicHarmonicH1ToHarmonicL2) :=
    hyperbolicHarmonicH1ToHarmonicL2_denseRange
  have hrange : Set.range hyperbolicHarmonicH1ToHarmonicL2 = Set.univ := by
    rw [← hclosed.closure_eq]
    exact dense_iff_closure_eq.mp hdense
  exact Set.range_eq_univ.mp hrange

/-- Linear identification of the source harmonic remainder with the actual distributional
harmonic `L²` sector. -/
noncomputable def hyperbolicHarmonicH1EquivHarmonicL2 :
    hyperbolicHarmonicH1 ≃ₗ[ℝ] hyperbolicHarmonicL2 :=
  LinearEquiv.ofBijective hyperbolicHarmonicH1ToHarmonicL2.toLinearMap
    ⟨hyperbolicHarmonicH1ToHarmonicL2_injective,
      hyperbolicHarmonicH1ToHarmonicL2_surjective⟩

/-- Canonical source `H¹` representative of an actual harmonic `L²` form. -/
noncomputable def hyperbolicHarmonicL2ToH1 :
    hyperbolicHarmonicL2 →ₗ[ℝ] HyperbolicOneFormH1 :=
  (Submodule.subtype hyperbolicHarmonicH1).comp
    hyperbolicHarmonicH1EquivHarmonicL2.symm.toLinearMap

theorem hyperbolicHarmonicL2ToH1_mem_harmonic
    (h : hyperbolicHarmonicL2) :
    hyperbolicHarmonicL2ToH1 h ∈ hyperbolicHarmonicH1 :=
  (hyperbolicHarmonicH1EquivHarmonicL2.symm h).property

@[simp] theorem hyperbolicOneFormH1ToL2_harmonicL2ToH1
    (h : hyperbolicHarmonicL2) :
    hyperbolicOneFormH1ToL2 (hyperbolicHarmonicL2ToH1 h) =
      (h : HyperbolicOneFormL2) := by
  have happly := hyperbolicHarmonicH1EquivHarmonicL2.apply_symm_apply h
  exact congrArg Subtype.val happly

@[simp] theorem hyperbolicHarmonicL2ToH1_toHarmonicL2
    (u : hyperbolicHarmonicH1) :
    hyperbolicHarmonicL2ToH1 (hyperbolicHarmonicH1ToHarmonicL2 u) =
      (u : HyperbolicOneFormH1) := by
  have hsymm := hyperbolicHarmonicH1EquivHarmonicL2.symm_apply_apply u
  exact congrArg Subtype.val hsymm

/-- Exact source norm and hence the explicit CCP25 harmonic regularity estimate. -/
theorem norm_sq_hyperbolicHarmonicL2ToH1
    (h : hyperbolicHarmonicL2) :
    ‖hyperbolicHarmonicL2ToH1 h‖ ^ 2 = 2 * ‖h‖ ^ 2 := by
  let u := hyperbolicHarmonicH1EquivHarmonicL2.symm h
  have hnorm := norm_sq_hyperbolicHarmonicH1ToHarmonicL2 u
  have happly := hyperbolicHarmonicH1EquivHarmonicL2.apply_symm_apply h
  change ‖(u : HyperbolicOneFormH1)‖ ^ 2 = 2 * ‖h‖ ^ 2
  rw [← happly]
  exact hnorm

theorem hyperbolicHarmonicL2ToH1_hodge_eq_zero
    (h : hyperbolicHarmonicL2) :
    hyperbolicOneFormH1Hodge (hyperbolicHarmonicL2ToH1 h) = 0 :=
  (hyperbolicOneFormH1ToL2_mem_harmonic_iff _).1 (by
    rw [hyperbolicOneFormH1ToL2_harmonicL2ToH1]
    exact h.property)

/-- Set-level equality used by the source statement: the `L²` image of the source harmonic
remainder is exactly the actual harmonic sector. -/
theorem range_hyperbolicHarmonicH1ToL2_eq_harmonicL2 :
    Set.range (fun u : hyperbolicHarmonicH1 ↦
      hyperbolicOneFormH1ToL2 (u : HyperbolicOneFormH1)) =
      (hyperbolicHarmonicL2 : Set HyperbolicOneFormL2) := by
  ext h
  constructor
  · rintro ⟨u, rfl⟩
    exact hyperbolicHarmonicH1_toL2_mem_harmonic u u.property
  · intro hh
    let hs : hyperbolicHarmonicL2 := ⟨h, hh⟩
    refine ⟨hyperbolicHarmonicH1EquivHarmonicL2.symm hs, ?_⟩
    exact hyperbolicOneFormH1ToL2_harmonicL2ToH1 hs

/-- No-hypothesis CCP25 Theorem 1.3 in the canonical `N=2`, `k=1`, `a=1` case, with the
harmonic summand exhibited as an actual distributional harmonic `L²` form. -/
theorem hyperbolicH1_exact_add_coexact_add_actualHarmonic
    (u : HyperbolicOneFormH1) :
    let harmonicL2 : hyperbolicHarmonicL2 :=
      ⟨hyperbolicOneFormH1ToL2 (hyperbolicHarmonicH1Projector u),
        hyperbolicHarmonicH1_toL2_mem_harmonic _
          (hyperbolicHarmonicH1Projector_mem u)⟩
    u = hyperbolicExactH1Projector u + hyperbolicCoexactH1Projector u +
      hyperbolicHarmonicL2ToH1 harmonicL2 := by
  dsimp only
  change u = hyperbolicExactH1Projector u + hyperbolicCoexactH1Projector u +
    hyperbolicHarmonicL2ToH1
      (hyperbolicHarmonicH1ToHarmonicL2
        ⟨hyperbolicHarmonicH1Projector u,
          hyperbolicHarmonicH1Projector_mem u⟩)
  rw [hyperbolicHarmonicL2ToH1_toHarmonicL2]
  exact hyperbolicH1_exact_add_coexact_add_harmonic u

end RiemannianFluids.HyperbolicPlane
