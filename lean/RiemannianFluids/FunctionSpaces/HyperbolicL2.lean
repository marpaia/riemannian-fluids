import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import RiemannianFluids.Geometry.Instances.HyperbolicPlaneMeasure

/-!
# Concrete `L²` carriers on the hyperbolic plane

An `L²` space must identify almost-everywhere equal fields and must be complete.  The earlier
Sobolev interfaces only put `MemLp` predicates on raw dependent sections; this module supplies the
first actual quotient Hilbert carriers.

Scalars use Mathlib's `Lp ℝ 2 hyperbolicVolume` directly.  A one-form has a varying cotangent
fiber, so it is represented by its two coefficients in the global hyperbolic orthonormal frame
`(y·∂x, y·∂y)`.  Riesz duality and the orthonormal-basis representation give an isometric
equivalence between each intrinsic cotangent fiber and `EuclideanSpace ℝ (Fin 2)`.  Consequently
the one-form carrier is the genuine Hilbert space

    L²(ℝ², dvol_hyp),

not an opaque varying-section predicate and not an `Lp` space carrying the Euclidean coordinate
covector norm.
-/

noncomputable section

namespace RiemannianFluids
namespace HyperbolicPlane

open Bundle ENNReal Function MeasureTheory Pointwise Set
open scoped Bundle ContDiff ENNReal Manifold RealInnerProductSpace

/-- A tangent fiber of the project's real two-dimensional hyperbolic manifold. -/
abbrev HyperbolicTangentFiber (p : HyperbolicPlane) :=
  TangentSpace (modelWithCornersSelf ℝ ℂ) p

/-- The intrinsic continuous dual of one hyperbolic tangent fiber. -/
abbrev HyperbolicOneFormFiber (p : HyperbolicPlane) :=
  HyperbolicTangentFiber p →L[ℝ] ℝ

/-- Two coefficients in the global hyperbolic orthonormal coframe. -/
abbrev HyperbolicOneFormComponents := EuclideanSpace ℝ (Fin 2)

/-- Hyperbolic tangent fibers are finite dimensional.  This named instance makes the fact
available to Riesz duality and later fiberwise functional analysis. -/
noncomputable instance hyperbolicTangentFiniteDimensional (p : HyperbolicPlane) :
    FiniteDimensional ℝ (HyperbolicTangentFiber p) :=
  tangentFiniteDimensional (modelWithCornersSelf ℝ ℂ) p

/-- Each intrinsic tangent fiber is complete because it is finite dimensional. -/
noncomputable instance hyperbolicTangentCompleteSpace (p : HyperbolicPlane) :
    CompleteSpace (HyperbolicTangentFiber p) :=
  FiniteDimensional.complete ℝ (HyperbolicTangentFiber p)

/-- Intrinsic one-form coefficients in the orthonormal frame.  Riesz first turns the covector
into its representing tangent vector; `orthonormalFrame.repr` then records its two coefficients. -/
noncomputable def oneFormComponentsAt (p : HyperbolicPlane)
    (alpha : HyperbolicOneFormFiber p) : HyperbolicOneFormComponents :=
  (orthonormalFrame p).repr
    ((InnerProductSpace.toDual ℝ (HyperbolicTangentFiber p)).symm alpha)

/-- Reconstruct an intrinsic cotangent vector from its two orthonormal-frame coefficients. -/
noncomputable def oneFormOfComponentsAt (p : HyperbolicPlane)
    (components : HyperbolicOneFormComponents) : HyperbolicOneFormFiber p :=
  InnerProductSpace.toDual ℝ (HyperbolicTangentFiber p)
    ((orthonormalFrame p).repr.symm components)

@[simp] theorem oneFormOfComponentsAt_componentsAt (p : HyperbolicPlane)
    (alpha : HyperbolicOneFormFiber p) :
    oneFormOfComponentsAt p (oneFormComponentsAt p alpha) = alpha := by
  simp [oneFormOfComponentsAt, oneFormComponentsAt]

@[simp] theorem oneFormComponentsAt_ofComponentsAt (p : HyperbolicPlane)
    (components : HyperbolicOneFormComponents) :
    oneFormComponentsAt p (oneFormOfComponentsAt p components) = components := by
  simp [oneFormOfComponentsAt, oneFormComponentsAt]

/-- The `i`th stored coefficient is evaluation on the `i`th orthonormal tangent vector. -/
theorem oneFormComponentsAt_apply (p : HyperbolicPlane)
    (alpha : HyperbolicOneFormFiber p) (i : Fin 2) :
    oneFormComponentsAt p alpha i = alpha (orthonormalFrame p i) := by
  rw [oneFormComponentsAt, OrthonormalBasis.repr_apply_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]

theorem oneFormComponentsAt_zero (p : HyperbolicPlane)
    (alpha : HyperbolicOneFormFiber p) :
    oneFormComponentsAt p alpha 0 = alpha ((p.im : ℂ)) := by
  rw [oneFormComponentsAt_apply, orthonormalFrame_apply_zero]

theorem oneFormComponentsAt_one (p : HyperbolicPlane)
    (alpha : HyperbolicOneFormFiber p) :
    oneFormComponentsAt p alpha 1 = alpha ((p.im : ℂ) * Complex.I) := by
  rw [oneFormComponentsAt_apply, orthonormalFrame_apply_one]

/-- Orthonormal components preserve the intrinsic cotangent norm exactly. -/
@[simp] theorem norm_oneFormComponentsAt (p : HyperbolicPlane)
    (alpha : HyperbolicOneFormFiber p) :
    ‖oneFormComponentsAt p alpha‖ = ‖alpha‖ := by
  simp [oneFormComponentsAt]

/-- Reconstruction from orthonormal components is also norm preserving. -/
@[simp] theorem norm_oneFormOfComponentsAt (p : HyperbolicPlane)
    (components : HyperbolicOneFormComponents) :
    ‖oneFormOfComponentsAt p components‖ = ‖components‖ := by
  rw [oneFormOfComponentsAt,
    (InnerProductSpace.toDual ℝ (HyperbolicTangentFiber p)).norm_map,
    (orthonormalFrame p).repr.symm.norm_map]

/-- Raw intrinsic one-form sections, before measurability or integrability is imposed. -/
abbrev HyperbolicRawOneForm :=
  (p : HyperbolicPlane) → HyperbolicOneFormFiber p

/-- Take orthonormal components pointwise along a raw intrinsic one-form. -/
noncomputable def oneFormComponents (alpha : HyperbolicRawOneForm) :
    HyperbolicPlane → HyperbolicOneFormComponents :=
  fun p ↦ oneFormComponentsAt p (alpha p)

/-- Reconstruct a raw intrinsic one-form from a component field. -/
noncomputable def oneFormOfComponents
    (components : HyperbolicPlane → HyperbolicOneFormComponents) :
    HyperbolicRawOneForm :=
  fun p ↦ oneFormOfComponentsAt p (components p)

@[simp] theorem oneFormOfComponents_components (alpha : HyperbolicRawOneForm) :
    oneFormOfComponents (oneFormComponents alpha) = alpha := by
  funext p
  exact oneFormOfComponentsAt_componentsAt p (alpha p)

@[simp] theorem oneFormComponents_ofComponents
    (components : HyperbolicPlane → HyperbolicOneFormComponents) :
    oneFormComponents (oneFormOfComponents components) = components := by
  funext p
  exact oneFormComponentsAt_ofComponentsAt p (components p)

/-- The scalar `L²` Hilbert carrier on the complete measured hyperbolic plane. -/
abbrev HyperbolicScalarL2 :=
  Lp ℝ 2 hyperbolicVolume

/-- The intrinsic one-form `L²` Hilbert carrier, represented isometrically in the global
orthonormal coframe. -/
abbrev HyperbolicOneFormL2 :=
  Lp HyperbolicOneFormComponents 2 hyperbolicVolume

/-- The scalar carrier is complete; this theorem forces use of the actual `CompleteSpace`
instance rather than merely recording a completeness predicate. -/
theorem hyperbolicScalarL2_complete :
    IsComplete (Set.univ : Set HyperbolicScalarL2) :=
  complete_univ

/-- The one-form carrier is complete for the same concrete `Lp` reason. -/
theorem hyperbolicOneFormL2_complete :
    IsComplete (Set.univ : Set HyperbolicOneFormL2) :=
  complete_univ

/-- The scalar `L²` inner product is the integral of the pointwise product. -/
theorem hyperbolicScalarL2_inner (f g : HyperbolicScalarL2) :
    inner ℝ f g = ∫ p, f p * g p ∂hyperbolicVolume := by
  rw [L2.inner_def]
  simp only [Real.inner_apply]

/-- The one-form `L²` inner product is the integral of the Euclidean inner product of intrinsic
orthonormal components. -/
theorem hyperbolicOneFormL2_inner (alpha beta : HyperbolicOneFormL2) :
    inner ℝ alpha beta =
      ∫ p, inner ℝ (alpha p) (beta p) ∂hyperbolicVolume :=
  L2.inner_def alpha beta

/-- Put a square-integrable scalar representative into the actual `L²` quotient. -/
noncomputable def scalarToL2 (f : HyperbolicPlane → ℝ)
    (hf : MemLp f 2 hyperbolicVolume) : HyperbolicScalarL2 :=
  hf.toLp f

theorem scalarToL2_coe (f : HyperbolicPlane → ℝ)
    (hf : MemLp f 2 hyperbolicVolume) :
    scalarToL2 f hf =ᵐ[hyperbolicVolume] f :=
  hf.coeFn_toLp

/-- Intrinsic `L²` membership of a raw one-form, expressed through the norm-preserving global
orthonormal coframe. -/
def IsHyperbolicOneFormL2 (alpha : HyperbolicRawOneForm) : Prop :=
  MemLp (oneFormComponents alpha) 2 hyperbolicVolume

/-- Put an integrable raw intrinsic one-form into the actual one-form `L²` quotient. -/
noncomputable def oneFormToL2 (alpha : HyperbolicRawOneForm)
    (halpha : IsHyperbolicOneFormL2 alpha) : HyperbolicOneFormL2 :=
  halpha.toLp (oneFormComponents alpha)

theorem oneFormToL2_coe (alpha : HyperbolicRawOneForm)
    (halpha : IsHyperbolicOneFormL2 alpha) :
    oneFormToL2 alpha halpha =ᵐ[hyperbolicVolume] oneFormComponents alpha :=
  halpha.coeFn_toLp

/-- A chosen raw intrinsic representative of an `L²` one-form.  Different choices made by the
`Lp` quotient agree almost everywhere, which is the correct analytic equality. -/
noncomputable def oneFormL2ToRawOneForm
    (alpha : HyperbolicOneFormL2) : HyperbolicRawOneForm :=
  oneFormOfComponents fun p ↦ alpha p

theorem oneFormComponents_oneFormL2ToRawOneForm_ae
    (alpha : HyperbolicOneFormL2) :
    oneFormComponents (oneFormL2ToRawOneForm alpha) =ᵐ[hyperbolicVolume]
      (fun p ↦ alpha p) :=
  Filter.Eventually.of_forall fun p ↦ oneFormComponentsAt_ofComponentsAt p (alpha p)

/-! ## Smooth compact cores -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A compactly supported continuous field on the hyperbolic manifold can be approximated in
`Lᵖ` by a compactly supported smooth field.  Mathlib supplies the manifold smoothing theorem;
the estimate below combines its support control with local finiteness of hyperbolic volume. -/
theorem exists_smoothCompact_eLpNorm_sub_le_of_continuous
    {p : ℝ≥0∞} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {f : HyperbolicPlane → F} (hcompact : HasCompactSupport f) (hcontinuous : Continuous f) :
    ∃ g : HyperbolicPlane → F,
      HasCompactSupport g ∧
        ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) ∞ g ∧
        eLpNorm (f - g) p hyperbolicVolume ≤ ENNReal.ofReal epsilon := by
  rcases eq_or_ne p ∞ with rfl | hp
  · obtain ⟨g, hgApprox, hgSupport⟩ := hcontinuous.exists_contMDiff_approx
      (modelWithCornersSelf ℝ ℂ) (⊤ : ℕ∞) (ε := fun _ ↦ epsilon)
      (by fun_prop) (by intro; positivity)
    refine ⟨fun x ↦ g x, hcompact.mono hgSupport, g.contMDiff,
      eLpNormEssSup_le_of_ae_bound (.of_forall fun x ↦ ?_)⟩
    simpa [← dist_eq_norm_sub'] using (hgApprox x).le
  by_cases hf : f =ᵐ[hyperbolicVolume] 0
  · use 0
    simpa [HasCompactSupport.zero, eLpNorm_congr_ae hf] using!
      (contMDiff_const : ContMDiff (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ F) ∞ (0 : HyperbolicPlane → F))
  have hmeasure : hyperbolicVolume (tsupport f) ≠ ⊤ := hcompact.measure_lt_top.ne
  have hmeasurePos : 0 < (hyperbolicVolume <| tsupport f).toReal := by
    rw [← Measure.measure_support_eq_zero_iff _] at hf
    exact toReal_pos (pos_mono (subset_tsupport f) (pos_of_ne_zero hf)).ne' hmeasure
  set epsilon' :=
    epsilon * (hyperbolicVolume <| tsupport f).toReal ^ (-(1 / p.toReal))
      with epsilon'_def
  have hepsilon' : 0 < epsilon' := by positivity
  have hLpBound :
      ENNReal.ofReal epsilon' * hyperbolicVolume (tsupport f) ^ (1 / p.toReal) ≤
        ENNReal.ofReal epsilon := by
    rw [← ofReal_toReal hmeasure, ofReal_rpow_of_pos hmeasurePos,
      ← ofReal_mul hepsilon'.le, ofReal_le_ofReal_iff hepsilon.le, epsilon'_def, mul_assoc,
      ← Real.rpow_add hmeasurePos, neg_add_cancel, Real.rpow_zero, mul_one]
  obtain ⟨g, hgApprox, hgSupport⟩ := hcontinuous.exists_contMDiff_approx
    (modelWithCornersSelf ℝ ℂ) (⊤ : ℕ∞) (ε := fun _ ↦ epsilon')
    (by fun_prop) (by intro; positivity)
  refine ⟨fun x ↦ g x, hcompact.mono hgSupport, g.contMDiff,
    (eLpNorm_sub_le_of_dist_bdd hyperbolicVolume hp hcompact.measurableSet hepsilon'.le ?_
      (subset_tsupport f) (hgSupport.trans (subset_tsupport f))).trans hLpBound⟩
  intro x
  rw [dist_comm]
  exact (hgApprox x).le

/-- Every `Lᵖ` representative on the measured hyperbolic plane admits compactly supported smooth
approximants when `1 ≤ p < ∞`. -/
theorem memLp_exists_hyperbolic_smoothCompact_eLpNorm_sub_le
    {p : ℝ≥0∞} (hp : p ≠ ⊤) (hpOne : 1 ≤ p)
    {f : HyperbolicPlane → F} (hf : MemLp f p hyperbolicVolume)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ g : HyperbolicPlane → F,
      HasCompactSupport g ∧
        ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) ∞ g ∧
        eLpNorm (f - g) p hyperbolicVolume ≤ ENNReal.ofReal epsilon := by
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  have hepsilonHalfENN : 0 < ENNReal.ofReal (epsilon / 2) := by positivity
  obtain ⟨g, hgCompact, hgError, hgContinuous, hgMemLp⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le hp hepsilonHalfENN.ne'
  obtain ⟨g', hg'Compact, hg'Smooth, hg'Error⟩ :=
    exists_smoothCompact_eLpNorm_sub_le_of_continuous (p := p)
      hepsilonHalf hgCompact hgContinuous
  refine ⟨g', hg'Compact, hg'Smooth, ?_⟩
  have hsplit : f - g' = (f - g) - (g' - g) := by simp
  grw [hsplit,
    eLpNorm_sub_le (hf.aestronglyMeasurable.sub hgMemLp.aestronglyMeasurable)
      (hg'Smooth.continuous.aestronglyMeasurable.sub hgMemLp.aestronglyMeasurable) hpOne,
    hgError, eLpNorm_sub_comm, hg'Error,
    ← ENNReal.ofReal_add hepsilonHalf.le hepsilonHalf.le, add_halves]

/-- A smooth compactly supported field with values in one fixed normed vector space.  Scalars use
`F = ℝ`; one-forms use their norm-preserving orthonormal component fiber. -/
structure HyperbolicSmoothCompactSection (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  toFun : HyperbolicPlane → F
  contMDiff_toFun :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) ∞ toFun
  hasCompactSupport_toFun : HasCompactSupport toFun

instance : FunLike (HyperbolicSmoothCompactSection F) HyperbolicPlane F where
  coe := HyperbolicSmoothCompactSection.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

@[simp] theorem HyperbolicSmoothCompactSection.coe_apply
    (f : HyperbolicSmoothCompactSection F) (p : HyperbolicPlane) :
    f p = f.toFun p :=
  rfl

/-- Smooth compact support implies membership in every finite `Lᵖ`; in particular it gives the
`L²` proof used by `toL2`. -/
theorem HyperbolicSmoothCompactSection.memLp
    (f : HyperbolicSmoothCompactSection F) :
    MemLp f.toFun 2 hyperbolicVolume :=
  f.contMDiff_toFun.continuous.memLp_of_hasCompactSupport f.hasCompactSupport_toFun

instance : Zero (HyperbolicSmoothCompactSection F) where
  zero :=
    ⟨0, contMDiff_const, HasCompactSupport.zero⟩

instance : IsZeroApply (HyperbolicSmoothCompactSection F) HyperbolicPlane F where
  zero_apply _ := rfl

instance : Add (HyperbolicSmoothCompactSection F) where
  add f g :=
    ⟨f + g, f.contMDiff_toFun.add g.contMDiff_toFun,
      f.hasCompactSupport_toFun.add g.hasCompactSupport_toFun⟩

instance : IsAddApply (HyperbolicSmoothCompactSection F) HyperbolicPlane F where
  add_apply _ _ _ := rfl

@[simp] theorem HyperbolicSmoothCompactSection.toFun_add
    (f g : HyperbolicSmoothCompactSection F) :
    (f + g).toFun = f.toFun + g.toFun :=
  rfl

instance : Neg (HyperbolicSmoothCompactSection F) where
  neg f :=
    ⟨-f, f.contMDiff_toFun.neg, f.hasCompactSupport_toFun.neg⟩

instance : IsNegApply (HyperbolicSmoothCompactSection F) HyperbolicPlane F where
  neg_apply _ _ := rfl

instance : Sub (HyperbolicSmoothCompactSection F) where
  sub f g :=
    ⟨f - g, f.contMDiff_toFun.sub g.contMDiff_toFun,
      f.hasCompactSupport_toFun.sub g.hasCompactSupport_toFun⟩

instance : IsSubApply (HyperbolicSmoothCompactSection F) HyperbolicPlane F where
  sub_apply _ _ _ := rfl

instance : SMul ℕ (HyperbolicSmoothCompactSection F) where
  smul n f :=
    ⟨fun p ↦ n • f p, f.contMDiff_toFun.nsmul n,
      (f.hasCompactSupport_toFun.smul_left :
        HasCompactSupport ((fun _ : HyperbolicPlane ↦ n) • f.toFun))⟩

instance : IsSMulApply ℕ (HyperbolicSmoothCompactSection F) HyperbolicPlane F where
  smul_apply _ _ _ := rfl

@[simp] theorem HyperbolicSmoothCompactSection.toFun_nsmul
    (n : ℕ) (f : HyperbolicSmoothCompactSection F) :
    (n • f).toFun = n • f.toFun :=
  rfl

instance : SMul ℤ (HyperbolicSmoothCompactSection F) where
  smul n f :=
    ⟨fun p ↦ n • f p, by
        cases n with
        | ofNat n => simpa using f.contMDiff_toFun.nsmul n
        | negSucc n => simpa using (f.contMDiff_toFun.nsmul n.succ).neg,
      (f.hasCompactSupport_toFun.smul_left :
        HasCompactSupport ((fun _ : HyperbolicPlane ↦ n) • f.toFun))⟩

instance : IsSMulApply ℤ (HyperbolicSmoothCompactSection F) HyperbolicPlane F where
  smul_apply _ _ _ := rfl

@[simp] theorem HyperbolicSmoothCompactSection.toFun_zsmul
    (n : ℤ) (f : HyperbolicSmoothCompactSection F) :
    (n • f).toFun = n • f.toFun :=
  rfl

instance : AddCommGroup (HyperbolicSmoothCompactSection F) :=
  fast_instance% FunLike.addCommGroup

instance : SMul ℝ (HyperbolicSmoothCompactSection F) where
  smul scalar f :=
    ⟨scalar • f,
      contMDiff_const.smul (I := modelWithCornersSelf ℝ ℝ) f.contMDiff_toFun,
      f.hasCompactSupport_toFun.smul_left⟩

instance : IsSMulApply ℝ (HyperbolicSmoothCompactSection F) HyperbolicPlane F where
  smul_apply _ _ _ := rfl

@[simp] theorem HyperbolicSmoothCompactSection.toFun_smul
    (scalar : ℝ) (f : HyperbolicSmoothCompactSection F) :
    (scalar • f).toFun = scalar • f.toFun :=
  rfl

instance : Module ℝ (HyperbolicSmoothCompactSection F) :=
  fast_instance% FunLike.module

/-- The concrete inclusion of the smooth compact core into the actual `L²` quotient. -/
noncomputable def HyperbolicSmoothCompactSection.toL2
    (f : HyperbolicSmoothCompactSection F) : Lp F 2 hyperbolicVolume :=
  f.memLp.toLp f.toFun

theorem HyperbolicSmoothCompactSection.toL2_coe
    (f : HyperbolicSmoothCompactSection F) :
    f.toL2 =ᵐ[hyperbolicVolume] f.toFun :=
  f.memLp.coeFn_toLp

/-- The smooth-core inclusion is linear.  This is the map whose graph will carry the first
closed covariant derivative in the next analytic slice. -/
noncomputable def hyperbolicSmoothCompactToL2 :
    HyperbolicSmoothCompactSection F →ₗ[ℝ] Lp F 2 hyperbolicVolume where
  toFun := HyperbolicSmoothCompactSection.toL2
  map_add' f g := by
    simpa [HyperbolicSmoothCompactSection.toL2] using
      MemLp.toLp_add f.memLp g.memLp
  map_smul' scalar f := by
    simpa [HyperbolicSmoothCompactSection.toL2] using
      f.memLp.toLp_const_smul scalar

@[simp] theorem hyperbolicSmoothCompactToL2_apply
    (f : HyperbolicSmoothCompactSection F) :
    hyperbolicSmoothCompactToL2 f = f.toL2 :=
  rfl

/-- Full support of hyperbolic volume upgrades almost-everywhere equality of smooth fields to
pointwise equality.  Hence the smooth compact core is a genuine linear subspace of `L²`, not
merely a collection of representatives with an unidentified kernel. -/
theorem hyperbolicSmoothCompactToL2_injective : Function.Injective
    (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactSection F → Lp F 2 hyperbolicVolume) := by
  intro f g hfgL2
  simp only [hyperbolicSmoothCompactToL2_apply] at hfgL2
  apply DFunLike.ext f g
  intro p
  have htoL2 : (fun q ↦ f.toL2 q) =ᵐ[hyperbolicVolume] (fun q ↦ g.toL2 q) := by
    filter_upwards with q
    exact congrArg (fun h : Lp F 2 hyperbolicVolume ↦ h q) hfgL2
  have hfg : f.toFun =ᵐ[hyperbolicVolume] g.toFun :=
    f.toL2_coe.symm.trans <| htoL2.trans g.toL2_coe
  have hpointwise : f.toFun = g.toFun :=
    Measure.eq_of_ae_eq hfg f.contMDiff_toFun.continuous g.contMDiff_toFun.continuous
  exact congrFun hpointwise p

/-- Smooth compactly supported scalar fields in the global hyperbolic chart. -/
abbrev HyperbolicSmoothCompactScalar := HyperbolicSmoothCompactSection ℝ

/-- Smooth compactly supported orthonormal-component fields representing one-forms. -/
abbrev HyperbolicSmoothCompactOneForm :=
  HyperbolicSmoothCompactSection HyperbolicOneFormComponents

/-- Reconstruct the intrinsic raw one-form represented by a smooth compact component field. -/
noncomputable def smoothCompactOneFormToRaw
    (alpha : HyperbolicSmoothCompactOneForm) : HyperbolicRawOneForm :=
  oneFormOfComponents alpha.toFun

/-- A smooth compact component field reconstructs to an intrinsically square-integrable raw
one-form, because the reconstruction is pointwise isometric. -/
theorem smoothCompactOneFormToRaw_isL2
    (alpha : HyperbolicSmoothCompactOneForm) :
    IsHyperbolicOneFormL2 (smoothCompactOneFormToRaw alpha) := by
  simpa [IsHyperbolicOneFormL2, smoothCompactOneFormToRaw] using alpha.memLp

/-- Smooth compactly supported fields are dense in the concrete hyperbolic `L²` carrier. -/
theorem hyperbolicSmoothCompactSection_dense :
    Dense (Set.range
      (hyperbolicSmoothCompactToL2 :
        HyperbolicSmoothCompactSection F → Lp F 2 hyperbolicVolume)) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun epsilon hepsilon ↦ ?_
  obtain ⟨g, hgCompact, hgSmooth, hgError⟩ :=
    memLp_exists_hyperbolic_smoothCompact_eLpNorm_sub_le
      ENNReal.ofNat_ne_top fact_one_le_two_ennreal.elim (Lp.memLp f) hepsilon
  have hgMemLp : MemLp g 2 hyperbolicVolume :=
    hgSmooth.continuous.memLp_of_hasCompactSupport hgCompact
  let core : HyperbolicSmoothCompactSection F :=
    ⟨g, hgSmooth, hgCompact⟩
  refine ⟨core.toL2, ⟨core, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← le_ofReal_iff_toReal_le
      ((Lp.memLp f).sub (Lp.memLp core.toL2)).eLpNorm_ne_top hepsilon.le]
  convert hgError using 1
  apply eLpNorm_congr_ae
  gcongr
  exact core.toL2_coe

/-- The scalar smooth compact core is dense in scalar `L²`. -/
theorem hyperbolicSmoothCompactScalar_dense :
    Dense (Set.range
      (hyperbolicSmoothCompactToL2 :
        HyperbolicSmoothCompactScalar → HyperbolicScalarL2)) :=
  hyperbolicSmoothCompactSection_dense

/-- The smooth compact orthonormal-component core is dense in intrinsic one-form `L²`. -/
theorem hyperbolicSmoothCompactOneForm_dense :
    Dense (Set.range
      (hyperbolicSmoothCompactToL2 :
        HyperbolicSmoothCompactOneForm → HyperbolicOneFormL2)) :=
  hyperbolicSmoothCompactSection_dense

end HyperbolicPlane
end RiemannianFluids
