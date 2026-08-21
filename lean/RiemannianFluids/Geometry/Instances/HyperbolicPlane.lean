import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import RiemannianFluids.Geometry.Curvature
import RiemannianFluids.Tensors.VectorCalculus

/-!
# The hyperbolic upper half-plane as a concrete Riemannian manifold

Every geometric contract in this repository so far constrains user-supplied data; nothing yet
exhibits a manifold satisfying them. This module builds the first concrete carrier: the upper
half-plane

    ℍ² = {z : ℂ | 0 < Im z}

with the Poincaré metric `g_z(v,w) = ⟨v,w⟩ / (Im z)²`, where `⟨·,·⟩` is the Euclidean inner
product of `ℂ` viewed as a real plane.

## Why the carrier is Mathlib's upper half-plane

The project uses Mathlib's canonical `UpperHalfPlane` carrier rather than maintaining a second
copy of the same open subset. Mathlib equips this type with the genuine Poincaré distance, proves
that it is proper (hence complete), and supplies the invariant measure `dx dy / y²`. Its global
chart is still the inclusion into `ℂ`; `isManifold_singleton` makes the space a `C^n` manifold over the
model `𝓘(ℝ, ℂ)` for every `n` at once. Choosing `ℂ` rather than `ℝ²` as the ambient plane is
not cosmetic: the half-plane Christoffel symbols

    Γ^x_{xy} = Γ^x_{yx} = -1/y,   Γ^y_{xx} = 1/y,   Γ^y_{yy} = -1/y

assemble into the single complex-bilinear expression

    Γ(u, X) = (Im z)⁻¹ • (i · u · X),

so every connection computation below is one complex multiplication instead of four coordinate
cases.

## The single-chart dictionary

With one global chart, all bundle infrastructure trivializes, and this module proves the
dictionary once so later constructions never touch charts again:

* the inclusion `↑ : ℍ² → ℂ` is `C^n` with manifold derivative the identity;
* every tangent-bundle trivialization is the identity on fibers, so a section of `Tℍ²` is `C^n`
  exactly when it is `C^n` as a plain map `ℍ² → ℂ`;
* mathlib's canonical extension of a tangent vector is the constant field, and the Lie bracket
  of constant fields vanishes.

The proofs identify the written-in-chart representative of each map with the identity germ on
the open set `{z | 0 < Im z}` and never invert a nontrivial coordinate change.
-/

set_option linter.unusedSimpArgs false

namespace RiemannianFluids

open Bundle Complex Set Topology
open scoped Bundle ContDiff Manifold Topology

/-- The canonical upper half-plane carrier. Reusing Mathlib's type makes its hyperbolic metric,
properness/completeness theorem, topology, and invariant measure available to the geometric
structure already developed in this module. -/
abbrev HyperbolicPlane : Type := UpperHalfPlane

namespace HyperbolicPlane

/-- The inclusion of the half-plane into the complex plane. -/
@[coe] def coe (p : HyperbolicPlane) : ℂ := UpperHalfPlane.coe p

/-- The height coordinate: the imaginary part of the underlying complex number. -/
def im (p : HyperbolicPlane) : ℝ := (p : ℂ).im

/-- Membership in the half-plane is exactly positivity of the height coordinate. -/
theorem im_pos (p : HyperbolicPlane) : 0 < p.im := p.coe_im_pos

theorem im_ne_zero (p : HyperbolicPlane) : p.im ≠ 0 := (im_pos p).ne'

/-- Points of the half-plane are recovered from their complex coordinate. -/
@[ext] theorem ext {p q : HyperbolicPlane} (h : (p : ℂ) = (q : ℂ)) : p = q :=
  UpperHalfPlane.ext h

/-- The underlying set `{z | 0 < Im z}` is open, so the inclusion is an open embedding. -/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : HyperbolicPlane → ℂ) :=
  UpperHalfPlane.isOpenEmbedding_coe

theorem range_coe : Set.range ((↑) : HyperbolicPlane → ℂ) = {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.range_coe

/-- A one-chart atlas is compatible with every smoothness groupoid, so the half-plane is a
`C^n` manifold over `𝓘(ℝ, ℂ)` for every regularity simultaneously. -/
instance (n : ℕ∞ω) : IsManifold 𝓘(ℝ, ℂ) n HyperbolicPlane :=
  isOpenEmbedding_coe.isManifold_singleton

/-! ## The chart dictionary -/

@[simp] theorem coe_chartAt (p q : HyperbolicPlane) : chartAt ℂ p q = (q : ℂ) := rfl

@[simp] theorem chartAt_source (p : HyperbolicPlane) :
    (chartAt ℂ p).source = Set.univ :=
  rfl

/-- The extended chart of the model `𝓘(ℝ, ℂ)` is the inclusion itself. -/
theorem extChartAt_coe (p : HyperbolicPlane) :
    ⇑(extChartAt 𝓘(ℝ, ℂ) p) = ((↑) : HyperbolicPlane → ℂ) :=
  rfl

@[simp] theorem extChartAt_apply (p q : HyperbolicPlane) :
    extChartAt 𝓘(ℝ, ℂ) p q = (q : ℂ) :=
  rfl

/-- On the open target `{z | 0 < Im z}` the inverse chart is a genuine right inverse. -/
theorem coe_chartAt_symm {p : HyperbolicPlane} {z : ℂ} (hz : 0 < z.im) :
    (((chartAt ℂ p).symm z : HyperbolicPlane) : ℂ) = z := by
  refine isOpenEmbedding_coe.toOpenPartialHomeomorph_right_inv (f := ((↑) : HyperbolicPlane → ℂ)) ?_
  rw [range_coe]
  exact hz

/-- The inclusion is `C^n` for every `n`: it is literally the extended chart. -/
theorem contMDiff_coe {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n ((↑) : HyperbolicPlane → ℂ) :=
  fun _ => contMDiffAt_extChartAt

theorem mdifferentiable_coe :
    MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : HyperbolicPlane → ℂ) :=
  contMDiff_coe.mdifferentiable (n := 1) one_ne_zero

/-- The manifold derivative of the inclusion is the identity in the global chart. -/
theorem hasMFDerivAt_coe (p : HyperbolicPlane) :
    HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : HyperbolicPlane → ℂ) p
      (ContinuousLinearMap.id ℝ ℂ) := by
  refine ⟨(mdifferentiable_coe p).continuousAt, ?_⟩
  -- The written-in-chart representative agrees with the identity near the base point.
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hmem : ((p : ℂ)) ∈ {z : ℂ | 0 < z.im} := p.im_pos
  have hid : HasFDerivWithinAt (id : ℂ → ℂ) (ContinuousLinearMap.id ℝ ℂ)
      (Set.range (𝓘(ℝ, ℂ))) ((extChartAt 𝓘(ℝ, ℂ) p) p) :=
    (hasFDerivAt_id _).hasFDerivWithinAt
  -- The written representative sends `z` to the inclusion of the inverse chart at `z`.
  have hwritten : ∀ z : ℂ, 0 < z.im →
      writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) p ((↑) : HyperbolicPlane → ℂ) z = z := by
    intro z hz
    simpa [writtenInExtChartAt] using coe_chartAt_symm (p := p) hz
  refine hid.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem)] with z hz
    exact hwritten z hz
  · exact hwritten _ p.im_pos

@[simp] theorem mfderiv_coe (p : HyperbolicPlane) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : HyperbolicPlane → ℂ) p =
      ContinuousLinearMap.id ℝ ℂ :=
  (hasMFDerivAt_coe p).mfderiv

/-! ## Tangent-bundle trivializations are the identity

The atlas has one member, so the preferred chart is the same partial homeomorphism at every
base point and each tangent coordinate change is a self-change, which mathlib's bundle-core
axioms force to be the identity. -/

theorem achart_eq (p q : HyperbolicPlane) : achart ℂ p = achart ℂ q := rfl

theorem tangent_continuousLinearMapAt (p₀ p : HyperbolicPlane) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀).continuousLinearMapAt ℝ p =
      ContinuousLinearMap.id ℝ ℂ := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (Set.mem_univ p)]
  ext v
  exact (tangentBundleCore 𝓘(ℝ, ℂ) HyperbolicPlane).coordChange_self (achart ℂ p) p
    (Set.mem_univ p) v

theorem tangent_symmL (p₀ p : HyperbolicPlane) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀).symmL ℝ p =
      ContinuousLinearMap.id ℝ ℂ := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (Set.mem_univ p)]
  ext v
  exact (tangentBundleCore 𝓘(ℝ, ℂ) HyperbolicPlane).coordChange_self (achart ℂ p₀) p
    (Set.mem_univ p) v

/-- Fiber components of the tangent trivializations do nothing. -/
@[simp] theorem tangentTrivializationAt_snd (p₀ p : HyperbolicPlane)
    (v : TangentSpace 𝓘(ℝ, ℂ) p) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀ ⟨p, v⟩).2 = v := by
  rw [← (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀).continuousLinearMapAt_apply_of_mem
    (R := ℝ) (Set.mem_univ p) v, tangent_continuousLinearMapAt]
  rfl

@[simp] theorem tangentTrivializationAt_symm (p₀ p : HyperbolicPlane) (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀).symm p v = v := by
  rw [← (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀).symmL_apply (R := ℝ)
    (Set.mem_univ p) v, tangent_symmL]
  rfl

/-! ## Sections as complex functions -/

/-- Reinterpret a tangent-bundle section as a complex-valued function. The fibers of the
tangent bundle over the half-plane are the model plane itself, so the reinterpretation is the
identity of the underlying data. -/
def sectionToFun (σ : Π p : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) p) :
    HyperbolicPlane → ℂ :=
  σ

/-- The tangent field with the same complex value in every fiber. -/
def constantField (c : ℂ) : Π p : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) p :=
  fun _ => c

@[simp] theorem sectionToFun_constantField (c : ℂ) :
    sectionToFun (constantField c) = fun _ => c :=
  rfl

/-- Mathlib's canonical extension of a tangent vector is the constant field. -/
theorem extend_eq_constantField (p : HyperbolicPlane) (v : TangentSpace 𝓘(ℝ, ℂ) p) :
    FiberBundle.extend ℂ v = constantField v := by
  funext q
  show (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p).symm q
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p ⟨p, v⟩).2 = _
  rw [tangentTrivializationAt_snd, tangentTrivializationAt_symm]
  rfl

/-- A tangent-bundle section over the half-plane is `C^n` exactly when its underlying complex
function is. -/
theorem contMDiffAt_section_iff_fun {n : ℕ∞ω}
    {σ : Π p : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) p} {p₀ : HyperbolicPlane} :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
        (fun p => TotalSpace.mk' ℂ p (σ p)) p₀ ↔
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (sectionToFun σ) p₀ := by
  rw [contMDiffAt_section]
  have hfun : (fun p => (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀ ⟨p, σ p⟩).2) =
      sectionToFun σ :=
    funext fun p => tangentTrivializationAt_snd p₀ p (σ p)
  rw [hfun]

/-- Differentiability version of `contMDiffAt_section_iff_fun`. -/
theorem mdifferentiableAt_section_iff_fun
    {σ : Π p : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) p} {p₀ : HyperbolicPlane} :
    MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
        (fun p => TotalSpace.mk' ℂ p (σ p)) p₀ ↔
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun σ) p₀ := by
  rw [mdifferentiableAt_section]
  have hfun : (fun p => (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀ ⟨p, σ p⟩).2) =
      sectionToFun σ :=
    funext fun p => tangentTrivializationAt_snd p₀ p (σ p)
  rw [hfun]

/-- Constant tangent fields are `C^n` sections for every `n`. -/
theorem contMDiff_constantField {n : ℕ∞ω} (c : ℂ) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      (fun p => TotalSpace.mk' ℂ p (constantField c p)) :=
  fun _ => contMDiffAt_section_iff_fun.mpr (by exact contMDiffAt_const)

/-! ## Hom-bundle trivializations are the identity

The endomorphism, cotangent, and covariant two-tensor bundles used by the repository are hom
bundles built from the tangent bundle and the trivial real line bundle. Their trivializations
conjugate by the constituent trivializations, and both constituents are the identity over the
half-plane, so each hom trivialization fixes fibers as well. -/

theorem trivial_continuousLinearMapAt_apply (p₀ p : HyperbolicPlane) (v : ℝ) :
    (trivializationAt ℝ (Bundle.Trivial HyperbolicPlane ℝ) p₀).continuousLinearMapAt ℝ p v =
      v := by
  rw [(trivializationAt ℝ (Bundle.Trivial HyperbolicPlane ℝ)
    p₀).continuousLinearMapAt_apply_of_mem (R := ℝ) (Set.mem_univ p) v]
  rfl

theorem trivial_symmL_apply (p₀ p : HyperbolicPlane) (v : ℝ) :
    (trivializationAt ℝ (Bundle.Trivial HyperbolicPlane ℝ) p₀).symmL ℝ p v = v := by
  rw [(trivializationAt ℝ (Bundle.Trivial HyperbolicPlane ℝ) p₀).symmL_apply (R := ℝ)
    (Set.mem_univ p) v]
  exact Bundle.Trivial.trivialization_symm_apply HyperbolicPlane ℝ p v

/-- Fiber components of the cotangent trivializations do nothing. -/
@[simp] theorem cotangentTrivializationAt_snd (p₀ p : HyperbolicPlane)
    (φ : TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ] ℝ) :
    (trivializationAt (ℂ →L[ℝ] ℝ)
      (fun q : HyperbolicPlane => TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ) p₀ ⟨p, φ⟩).2 = φ := by
  refine ContinuousLinearMap.ext fun v => ?_
  show (trivializationAt ℝ (Bundle.Trivial HyperbolicPlane ℝ) p₀).continuousLinearMapAt ℝ p
    (φ ((trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀).symmL ℝ p v)) = φ v
  rw [tangent_symmL, trivial_continuousLinearMapAt_apply]
  rfl

theorem cotangent_continuousLinearMapAt_apply (p₀ p : HyperbolicPlane)
    (φ : TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ] ℝ) :
    (trivializationAt (ℂ →L[ℝ] ℝ)
        (fun q : HyperbolicPlane => TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ)
        p₀).continuousLinearMapAt ℝ p φ = φ := by
  rw [(trivializationAt (ℂ →L[ℝ] ℝ)
      (fun q : HyperbolicPlane => TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ)
      p₀).continuousLinearMapAt_apply_of_mem (R := ℝ) (by exact ⟨trivial, trivial⟩) φ]
  exact cotangentTrivializationAt_snd p₀ p φ

theorem cotangent_symm_apply (p₀ p : HyperbolicPlane) (φ : ℂ →L[ℝ] ℝ) :
    (trivializationAt (ℂ →L[ℝ] ℝ)
        (fun q : HyperbolicPlane => TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ) p₀).symm p φ = φ := by
  conv_lhs =>
    rw [show φ = (trivializationAt (ℂ →L[ℝ] ℝ)
      (fun q : HyperbolicPlane => TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ) p₀ ⟨p, φ⟩).2 from
      (cotangentTrivializationAt_snd p₀ p φ).symm]
  exact Trivialization.symm_apply_apply_mk _ (by exact ⟨trivial, trivial⟩) _

theorem cotangent_symmL_apply (p₀ p : HyperbolicPlane) (φ : ℂ →L[ℝ] ℝ) :
    (trivializationAt (ℂ →L[ℝ] ℝ)
        (fun q : HyperbolicPlane => TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ) p₀).symmL ℝ p φ = φ := by
  rw [Trivialization.symmL_apply (R := ℝ) _ (by exact ⟨trivial, trivial⟩)]
  exact cotangent_symm_apply p₀ p φ

/-- Fiber components of the endomorphism-bundle trivializations do nothing. -/
@[simp] theorem endomorphismTrivializationAt_snd (p₀ p : HyperbolicPlane)
    (A : TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) p) :
    (trivializationAt (ℂ →L[ℝ] ℂ)
      (fun q : HyperbolicPlane => TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) q)
      p₀ ⟨p, A⟩).2 = A := by
  refine ContinuousLinearMap.ext fun v => ?_
  show (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀).continuousLinearMapAt ℝ p
    (A ((trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀).symmL ℝ p v)) = A v
  rw [tangent_symmL, tangent_continuousLinearMapAt]
  rfl

/-- Fiber components of the covariant two-tensor trivializations do nothing. -/
@[simp] theorem twoTensorTrivializationAt_snd (p₀ p : HyperbolicPlane)
    (B : TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ] ℝ) :
    (trivializationAt (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      (fun q : HyperbolicPlane =>
        TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ)
      p₀ ⟨p, B⟩).2 = B := by
  refine ContinuousLinearMap.ext fun v => ?_
  show (trivializationAt (ℂ →L[ℝ] ℝ)
      (fun q : HyperbolicPlane => TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ) p₀).continuousLinearMapAt ℝ p
    (B ((trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀).symmL ℝ p v)) = B v
  rw [tangent_symmL]
  show (trivializationAt (ℂ →L[ℝ] ℝ)
      (fun q : HyperbolicPlane => TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ) p₀).continuousLinearMapAt ℝ p
    (B v) = B v
  exact cotangent_continuousLinearMapAt_apply p₀ p (B v)

/-! ## Smooth scalar coefficients -/

/-- The height coordinate is `C^n`: it is a continuous linear functional after the inclusion. -/
theorem contMDiff_im {n : ℕ∞ω} : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n im :=
  Complex.imCLM.contMDiff.comp contMDiff_coe

/-- The inverse squared height, the conformal factor of the Poincaré metric, is `C^n`. -/
theorem contMDiffAt_im_sq_inv {n : ℕ∞ω} (p₀ : HyperbolicPlane) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n (fun p : HyperbolicPlane => ((p.im) ^ 2)⁻¹) p₀ :=
  ((contMDiff_im.contMDiffAt.pow 2).inv₀ (pow_ne_zero 2 (im_ne_zero p₀)))

/-- The inverse height itself, the coefficient of the Christoffel form, is `C^n`. -/
theorem contMDiffAt_im_inv {n : ℕ∞ω} (p₀ : HyperbolicPlane) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n (fun p : HyperbolicPlane => (p.im)⁻¹) p₀ :=
  contMDiff_im.contMDiffAt.inv₀ (im_ne_zero p₀)

/-! ## The Poincaré metric

The fiber inner product over `p` is the Euclidean pairing of the plane divided by `(Im p)²`.
Mathlib's `ContMDiffRiemannianMetric` packages the pointwise bilinear forms together with
symmetry, positivity, von Neumann boundedness of the unit ball, and smoothness of the induced
hom-bundle section; registering `RiemannianBundle` from it installs the fiber inner products
and the smooth-metric class without instance diamonds. -/

/-- The Euclidean pairing of the plane, `⟨v,w⟩ = Re v · Re w + Im v · Im w`, as a continuous
real-bilinear form. -/
noncomputable def euclideanForm : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  Complex.reCLM.smulRight Complex.reCLM + Complex.imCLM.smulRight Complex.imCLM

theorem euclideanForm_apply (v w : ℂ) :
    euclideanForm v w = v.re * w.re + v.im * w.im := by
  simp [euclideanForm]

theorem euclideanForm_self (v : ℂ) : euclideanForm v v = Complex.normSq v := by
  rw [euclideanForm_apply, Complex.normSq_apply]

/-- The Poincaré inner product on the tangent fiber over `p`. -/
noncomputable def poincareInner (p : HyperbolicPlane) :
    TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ] ℝ :=
  ((p.im) ^ 2)⁻¹ • euclideanForm

theorem poincareInner_apply (p : HyperbolicPlane) (v w : TangentSpace 𝓘(ℝ, ℂ) p) :
    poincareInner p v w = ((p.im) ^ 2)⁻¹ * euclideanForm v w :=
  rfl

/-- The Poincaré metric as a bundled smooth Riemannian metric on the tangent bundle. -/
noncomputable def poincareMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℂ) ∞ ℂ
      (TangentSpace 𝓘(ℝ, ℂ) : HyperbolicPlane → Type _) where
  inner := poincareInner
  symm p v w := by
    rw [poincareInner_apply, poincareInner_apply, euclideanForm_apply, euclideanForm_apply]
    ring
  pos p v hv := by
    rw [poincareInner_apply, euclideanForm_self]
    have hv' : (v : ℂ) ≠ 0 := hv
    have hsq : (0 : ℝ) < ((p.im) ^ 2)⁻¹ :=
      inv_pos.mpr (pow_pos (im_pos p) 2)
    exact mul_pos hsq (Complex.normSq_pos.mpr hv')
  isVonNBounded p := by
    -- The Poincaré unit ball is the Euclidean ball of radius `Im p`, hence bounded.
    have hball : Bornology.IsVonNBounded ℝ (Metric.ball (0 : ℂ) (p.im + 1)) :=
      NormedSpace.isVonNBounded_ball ℝ ℂ (p.im + 1)
    refine hball.subset ?_
    intro v hv
    have hv' : poincareInner p v v < 1 := hv
    rw [poincareInner_apply, euclideanForm_self] at hv'
    have hnormSq : Complex.normSq v < (p.im) ^ 2 := by
      have hsq : (0 : ℝ) < (p.im) ^ 2 := pow_pos (im_pos p) 2
      have hmul := mul_lt_mul_of_pos_left hv' hsq
      rw [← mul_assoc, mul_inv_cancel₀ hsq.ne', one_mul, mul_one] at hmul
      exact hmul
    show (v : ℂ) ∈ Metric.ball (0 : ℂ) (p.im + 1)
    rw [Metric.mem_ball, dist_zero_right]
    have hnorm : ‖(v : ℂ)‖ ^ 2 < (p.im) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hnormSq
    nlinarith [norm_nonneg (v : ℂ), im_pos p]
  contMDiff := by
    -- Reduce section smoothness to smoothness of the plain map into the model tensor fiber.
    intro p₀
    rw [contMDiffAt_section]
    have hfun : (fun p => (trivializationAt (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
        (fun q : HyperbolicPlane =>
          TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ)
        p₀ ⟨p, poincareInner p⟩).2) =
        fun p : HyperbolicPlane => ((p.im) ^ 2)⁻¹ • euclideanForm :=
      funext fun p => twoTensorTrivializationAt_snd p₀ p (poincareInner p)
    rw [hfun]
    -- Smooth scalar coefficient times a constant bilinear form.
    exact (contMDiffAt_im_sq_inv p₀).smul contMDiffAt_const

/-- The tangent fibers of the half-plane carry the Poincaré inner product. This is the first
concrete `RiemannianBundle` instance in the repository. -/
noncomputable instance : RiemannianBundle (TangentSpace 𝓘(ℝ, ℂ) : HyperbolicPlane → Type _) :=
  ⟨poincareMetric.toRiemannianMetric⟩

example : IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ
    (TangentSpace 𝓘(ℝ, ℂ) : HyperbolicPlane → Type _) :=
  inferInstance

example : IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) 1 ℂ
    (TangentSpace 𝓘(ℝ, ℂ) : HyperbolicPlane → Type _) :=
  inferInstance

/-- The installed fiber inner product is the Poincaré pairing. -/
theorem inner_tangent_eq (p : HyperbolicPlane) (v w : TangentSpace 𝓘(ℝ, ℂ) p) :
    inner ℝ v w = ((p.im) ^ 2)⁻¹ * euclideanForm v w :=
  rfl

/-! ## The hyperbolic covariant derivative

In the global chart the Levi-Civita connection of the Poincaré metric is the flat derivative
plus one bilinear correction: writing tangent vectors as complex numbers,

    ∇_X σ = D_X σ + (Im p)⁻¹ • (i · σ · X).

Expanding the complex product recovers the four classical half-plane Christoffel symbols. -/

/-- The Christoffel correction at `p`: the bilinear map `(u, X) ↦ (Im p)⁻¹ • (i·u·X)`. The
first argument is the differentiated section's value, the second is the direction, matching the
argument order of mathlib's covariant derivatives. -/
noncomputable def christoffelSymbol (p : HyperbolicPlane) : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (p.im)⁻¹ • ((ContinuousLinearMap.mul ℝ ℂ).comp (ContinuousLinearMap.mul ℝ ℂ Complex.I))

theorem christoffelSymbol_apply (p : HyperbolicPlane) (u X : ℂ) :
    christoffelSymbol p u X = (p.im)⁻¹ • (Complex.I * u * X) :=
  rfl

/-- The flat derivative of a section in the global chart, as a fiber endomorphism. The value
and direction fibers are the plane itself, so the underlying map is `mvfderiv` of the section's
complex function. -/
noncomputable def flatDerivative (σ : Π p : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) p)
    (p : HyperbolicPlane) : TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) p :=
  mvfderiv 𝓘(ℝ, ℂ) (sectionToFun σ) p

/-- The Christoffel correction as an endomorphism of the tangent fiber. -/
noncomputable def christoffelTangent (p : HyperbolicPlane) (u : TangentSpace 𝓘(ℝ, ℂ) p) :
    TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) p :=
  christoffelSymbol p u

/-- The hyperbolic covariant derivative on the tangent bundle of the half-plane: the flat
derivative of the global chart corrected by the Christoffel form. -/
noncomputable def hyperbolicCovariantDerivative :
    CovariantDerivative 𝓘(ℝ, ℂ) ℂ (TangentSpace 𝓘(ℝ, ℂ) : HyperbolicPlane → Type _) where
  toFun σ p := flatDerivative σ p + christoffelTangent p (σ p)
  isCovariantDerivativeOnUniv := by
    constructor
    · -- Additivity: the flat derivative is additive and the correction is fiberwise linear.
      intro σ σ' x hσ hσ' _
      have hfun : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun σ) x :=
        mdifferentiableAt_section_iff_fun.mp hσ
      have hfun' : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun σ') x :=
        mdifferentiableAt_section_iff_fun.mp hσ'
      have hflat : flatDerivative (σ + σ') x = flatDerivative σ x + flatDerivative σ' x :=
        mvfderiv_add hfun hfun'
      have hchristoffel : christoffelTangent x ((σ + σ') x) =
          christoffelTangent x (σ x) + christoffelTangent x (σ' x) :=
        map_add (christoffelSymbol x) (σ x) (σ' x)
      show flatDerivative (σ + σ') x + christoffelTangent x ((σ + σ') x) = _
      rw [hflat, hchristoffel]
      abel
    · -- The Leibniz rule: the scalar derivative appears only through the flat part.
      intro σ g x hσ hg _
      have hfun : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun σ) x :=
        mdifferentiableAt_section_iff_fun.mp hσ
      have hflat : flatDerivative (g • σ) x =
          g x • flatDerivative σ x + (mvfderiv 𝓘(ℝ, ℂ) g x).smulRight (σ x) :=
        mvfderiv_smul hg hfun
      have hchristoffel : christoffelTangent x ((g • σ) x) =
          g x • christoffelTangent x (σ x) :=
        map_smul (christoffelSymbol x) (g x) (σ x)
      show flatDerivative (g • σ) x + christoffelTangent x ((g • σ) x) = _
      rw [hflat, hchristoffel, smul_add]
      abel

/-! ## Lie brackets of constant fields vanish

The Lie bracket is natural under pullback, and the inclusion into the plane has identity
derivative, so brackets over the half-plane are computed by the flat bracket of the plane,
which kills constant fields. -/

/-- Constant tangent fields on the model plane are differentiable sections. -/
theorem mdifferentiableAt_constant_model (c : ℂ) (z : ℂ) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ).tangent
      (fun w : ℂ =>
        TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℝ, ℂ)) w ((fun _ : ℂ => c) w)) z := by
  have h := (contMDiffAt_vectorSpace_iff_contDiffAt (𝕜 := ℝ) (V := fun _ : ℂ => c)
    (n := 1) (x := z)).mpr contDiffAt_const
  exact h.mdifferentiableAt one_ne_zero

/-- Pulling back a plane field along the inclusion evaluates it at the underlying point. -/
theorem mpullback_coe_apply (V : Π z : ℂ, TangentSpace 𝓘(ℝ, ℂ) z) (p : HyperbolicPlane) :
    VectorField.mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : HyperbolicPlane → ℂ) V p = V (p : ℂ) := by
  show (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : HyperbolicPlane → ℂ) p).inverse (V (p : ℂ)) = V (p : ℂ)
  have hstep : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : HyperbolicPlane → ℂ) p).inverse (V (p : ℂ)) =
      (ContinuousLinearMap.id ℝ ℂ).inverse (V (p : ℂ)) := by
    rw [mfderiv_coe]
    exact rfl
  rw [hstep, ContinuousLinearMap.inverse_id]
  rfl

theorem mpullback_coe_constant (c : ℂ) :
    VectorField.mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : HyperbolicPlane → ℂ) (fun _ : ℂ => c) =
      constantField c :=
  funext fun p => mpullback_coe_apply (fun _ : ℂ => c) p

/-- The Lie bracket of constant fields on the model plane vanishes. -/
theorem mlieBracket_constant_model (c c' : ℂ) :
    VectorField.mlieBracket 𝓘(ℝ, ℂ) (fun _ : ℂ => c) (fun _ : ℂ => c') = 0 := by
  funext z
  rw [← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_eq_lieBracketWithin]
  simp only [VectorField.lieBracketWithin, fderivWithin_univ, fderiv_fun_const,
    Pi.zero_apply, zero_apply, sub_self]
  exact Eq.refl (0 : ℂ)

/-- The Lie bracket of constant tangent fields on the half-plane vanishes. -/
theorem mlieBracket_constantField (c c' : ℂ) :
    VectorField.mlieBracket 𝓘(ℝ, ℂ) (constantField c) (constantField c') = 0 := by
  funext p
  have hpull := VectorField.mpullback_mlieBracket (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
    (f := ((↑) : HyperbolicPlane → ℂ)) (V := fun _ : ℂ => c) (W := fun _ : ℂ => c')
    (x₀ := p) (n := 2)
    (mdifferentiableAt_constant_model c (p : ℂ))
    (mdifferentiableAt_constant_model c' (p : ℂ))
    contMDiff_coe.contMDiffAt
    (by simp)
  rw [mpullback_coe_constant, mpullback_coe_constant] at hpull
  rw [← hpull, mlieBracket_constant_model]
  show (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : HyperbolicPlane → ℂ) p).inverse 0 = 0
  simp

/-! ## The connection is torsion-free -/

theorem flatDerivative_constantField (c : ℂ) (p : HyperbolicPlane) :
    flatDerivative (constantField c) p = 0 :=
  mvfderiv_const c

/-- The hyperbolic covariant derivative of a constant field is the Christoffel correction. -/
theorem hyperbolicCovariantDerivative_constantField (c : ℂ) (p : HyperbolicPlane) :
    hyperbolicCovariantDerivative (constantField c) p = christoffelTangent p c := by
  show flatDerivative (constantField c) p + christoffelTangent p (constantField c p) =
    christoffelTangent p c
  rw [flatDerivative_constantField]
  exact zero_add _

/-- The hyperbolic connection is torsion-free: the Christoffel form is symmetric because
complex multiplication commutes. -/
theorem hyperbolicCovariantDerivative_torsion :
    hyperbolicCovariantDerivative.torsion = 0 := by
  funext x
  refine ContinuousLinearMap.ext fun X₀ => ?_
  refine ContinuousLinearMap.ext fun Y₀ => ?_
  rw [CovariantDerivative.torsion_apply_eq_extend,
    extend_eq_constantField x X₀, extend_eq_constantField x Y₀,
    mlieBracket_constantField,
    hyperbolicCovariantDerivative_constantField,
    hyperbolicCovariantDerivative_constantField]
  have hcomm : christoffelTangent x Y₀ (constantField X₀ x) =
      christoffelTangent x X₀ (constantField Y₀ x) := by
    show christoffelSymbol x Y₀ X₀ = christoffelSymbol x X₀ Y₀
    rw [christoffelSymbol_apply, christoffelSymbol_apply]
    exact congrArg (fun z : ℂ => (x.im)⁻¹ • z) (by ring)
  simp only [hcomm, sub_self, Pi.zero_apply, zero_apply]

/-! ## Metric compatibility

Differentiating `g(σ,τ) = ⟨σ,τ⟩/y²` produces the Euclidean product rule plus a `-2/y³`-term
from the conformal factor; the latter is exactly absorbed by the two Christoffel corrections
because of the complex-arithmetic identity

    ⟨i·a·v, b⟩ + ⟨a, i·b·v⟩ = -2 (Im v) ⟨a, b⟩.
-/

/-- The height coordinate differentiates to the imaginary-part functional. -/
theorem hasMFDerivAt_im (p : HyperbolicPlane) :
    HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) im p (Complex.imCLM : ℂ →L[ℝ] ℝ) := by
  have him : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) Complex.im ((p : ℂ))
      (Complex.imCLM : ℂ →L[ℝ] ℝ) :=
    Complex.imCLM.hasFDerivAt.hasMFDerivAt
  have h := him.comp p (hasMFDerivAt_coe p)
  convert h using 1
  · exact rfl
  · exact (ContinuousLinearMap.comp_id (Complex.imCLM : ℂ →L[ℝ] ℝ)).symm

/-- Reinterpret a tangent vector as a complex number. -/
def toComplex {p : HyperbolicPlane} (v : TangentSpace 𝓘(ℝ, ℂ) p) : ℂ := v

@[simp] theorem toComplex_constantField (c : ℂ) (p : HyperbolicPlane) :
    toComplex (constantField c p) = c :=
  rfl

/-- Pointwise formula for the hyperbolic covariant derivative. -/
theorem hyperbolicCovariantDerivative_apply
    (σ : Π q : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) q) (p : HyperbolicPlane)
    (v : TangentSpace 𝓘(ℝ, ℂ) p) :
    hyperbolicCovariantDerivative σ p v =
      mvfderiv 𝓘(ℝ, ℂ) (sectionToFun σ) p v +
        (p.im)⁻¹ • (Complex.I * sectionToFun σ p * toComplex v) :=
  rfl

/-- Pointwise formula for the hyperbolic covariant derivative along a second section. -/
theorem hyperbolicCovariantDerivative_apply_section
    (σ X : Π q : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) q) (p : HyperbolicPlane) :
    hyperbolicCovariantDerivative σ p (X p) =
      mvfderiv 𝓘(ℝ, ℂ) (sectionToFun σ) p (X p) +
        (p.im)⁻¹ • (Complex.I * sectionToFun σ p * sectionToFun X p) :=
  rfl

set_option maxHeartbeats 1600000 in
/-- The hyperbolic covariant derivative preserves the Poincaré metric. -/
theorem hyperbolic_metricCompatible :
    IsMetricCompatibleTangentConnection 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative := by
  intro x X σ τ hX hσ hτ
  have hσf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun σ) x :=
    mdifferentiableAt_section_iff_fun.mp hσ
  have hτf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun τ) x :=
    mdifferentiableAt_section_iff_fun.mp hτ
  have hDσ := hσf.hasMFDerivAt
  have hDτ := hτf.hasMFDerivAt
  set Dσ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun σ) x
  set Dτ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun τ) x
  -- Real and imaginary components of the two sections.
  have hre : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) Complex.re (sectionToFun σ x)
      (Complex.reCLM : ℂ →L[ℝ] ℝ) := Complex.reCLM.hasFDerivAt.hasMFDerivAt
  have him : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) Complex.im (sectionToFun σ x)
      (Complex.imCLM : ℂ →L[ℝ] ℝ) := Complex.imCLM.hasFDerivAt.hasMFDerivAt
  have hre' : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) Complex.re (sectionToFun τ x)
      (Complex.reCLM : ℂ →L[ℝ] ℝ) := Complex.reCLM.hasFDerivAt.hasMFDerivAt
  have him' : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) Complex.im (sectionToFun τ x)
      (Complex.imCLM : ℂ →L[ℝ] ℝ) := Complex.imCLM.hasFDerivAt.hasMFDerivAt
  have hu₁ : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun y => (sectionToFun σ y).re) x
      (Complex.reCLM.comp Dσ) := hre.comp x hDσ
  have hu₂ : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun y => (sectionToFun σ y).im) x
      (Complex.imCLM.comp Dσ) := him.comp x hDσ
  have hv₁ : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun y => (sectionToFun τ y).re) x
      (Complex.reCLM.comp Dτ) := hre'.comp x hDτ
  have hv₂ : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun y => (sectionToFun τ y).im) x
      (Complex.imCLM.comp Dτ) := him'.comp x hDτ
  -- The conformal factor.
  have hw := (hasMFDerivAt_im x).mul (hasMFDerivAt_im x)
  have hwne : im x * im x ≠ 0 := mul_ne_zero (im_ne_zero x) (im_ne_zero x)
  have hwinv := hw.inv hwne
  -- The Euclidean pairing of the two sections.
  have hb := (hu₁.mul hv₁).add (hu₂.mul hv₂)
  have hf := hwinv.mul hb
  -- The metric coefficient function is the product of the two scalar factors above.
  have heq : (fun y : HyperbolicPlane => inner ℝ (σ y) (τ y)) =
      (im * im)⁻¹ *
        ((fun y => (sectionToFun σ y).re) * (fun y => (sectionToFun τ y).re) +
          (fun y => (sectionToFun σ y).im) * (fun y => (sectionToFun τ y).im)) := by
    funext y
    show ((im y) ^ 2)⁻¹ *
        ((sectionToFun σ y).re * (sectionToFun τ y).re +
          (sectionToFun σ y).im * (sectionToFun τ y).im) = _
    rw [pow_two]
    rfl
  rw [← heq] at hf
  -- Evaluate the derivative of the metric coefficient at the direction `X x`.
  show mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun y : HyperbolicPlane => inner ℝ (σ y) (τ y)) x (X x) = _
  rw [hf.mfderiv]
  rw [hyperbolicCovariantDerivative_apply_section σ X x,
    hyperbolicCovariantDerivative_apply_section τ X x]
  have hσatom : ∀ v : TangentSpace 𝓘(ℝ, ℂ) x,
      mvfderiv 𝓘(ℝ, ℂ) (sectionToFun σ) x v = Dσ v := fun _ => rfl
  have hτatom : ∀ v : TangentSpace 𝓘(ℝ, ℂ) x,
      mvfderiv 𝓘(ℝ, ℂ) (sectionToFun τ) x v = Dτ v := fun _ => rfl
  have hσval : sectionToFun σ x = σ x := rfl
  have hτval : sectionToFun τ x = τ x := rfl
  have hXval : sectionToFun X x = X x := rfl
  -- Reduce to a polynomial identity over the reals in the components.
  simp only [hσatom, hτatom, inner_tangent_eq, euclideanForm_apply, hσval, hτval, hXval,
    add_apply, smul_apply, ContinuousLinearMap.comp_apply, neg_apply,
    Pi.mul_apply, Pi.inv_apply, Pi.add_apply, smul_eq_mul,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.real_smul,
    Complex.ofReal_re, Complex.ofReal_im, pow_two]
  -- The bundled operator application unfolds definitionally to real arithmetic.
  show (x.im * x.im)⁻¹ * (Complex.re (σ x) * Complex.re (Dτ (X x)) +
        Complex.re (τ x) * Complex.re (Dσ (X x)) +
        (Complex.im (σ x) * Complex.im (Dτ (X x)) +
          Complex.im (τ x) * Complex.im (Dσ (X x)))) +
      (Complex.re (σ x) * Complex.re (τ x) + Complex.im (σ x) * Complex.im (τ x)) *
        (-(x.im * x.im * (x.im * x.im))⁻¹ *
          (x.im * Complex.im (X x) + x.im * Complex.im (X x))) = _
  have hy := im_ne_zero x
  field_simp
  ring

/-- The Levi-Civita connection of the Poincaré metric, packaged with both defining
properties for the repository's downstream operators. -/
noncomputable def hyperbolicLeviCivitaConnection :
    LeviCivitaConnection (M := HyperbolicPlane) 𝓘(ℝ, ℂ) where
  connection := hyperbolicCovariantDerivative
  metricCompatible := hyperbolic_metricCompatible
  torsionFree := hyperbolicCovariantDerivative_torsion

/-! ## The connection is smooth

The covariant derivative of a `C^(k+1)` section is a `C^k` endomorphism field: the flat part is
the smooth derivative family of the section's complex function, and the Christoffel part is a
smooth scalar times a fixed bilinear map applied to the section. -/

/-- The derivative family of a section, as a map into the model operator space. -/
noncomputable def flatDerivativeFun (σ : Π p : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) p) :
    HyperbolicPlane → (ℂ →L[ℝ] ℂ) :=
  fun p => flatDerivative σ p

/-- The Christoffel correction of a section, as a map into the model operator space. -/
noncomputable def christoffelFun (σ : Π p : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) p) :
    HyperbolicPlane → (ℂ →L[ℝ] ℂ) :=
  fun p => christoffelTangent p (σ p)

/-- The derivative family of a `C^(k+1)` section is a `C^k` map into the operator space. -/
theorem contMDiffAt_flatDerivativeFun {k : ℕ∞ω}
    (σ : Π p : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) p) (p₀ : HyperbolicPlane)
    (hσ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (k + 1) (sectionToFun σ) p₀) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) k (flatDerivativeFun σ) p₀ := by
  have h := hσ.mfderiv_const (m := k) le_rfl
  refine h.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun p => ?_
  -- Both coordinate conjugations in `inTangentCoordinates` are the identity.
  have hcoord : inTangentCoordinates 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) id (sectionToFun σ)
      (fun q => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun σ) q) p₀ p =
      flatDerivativeFun σ p := by
    ext v
    show (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) (sectionToFun σ p₀)).continuousLinearMapAt
        ℝ (sectionToFun σ p)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun σ) p
          ((trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p₀).symmL ℝ p v)) =
      flatDerivativeFun σ p v
    rw [tangent_symmL, TangentBundle.continuousLinearMapAt_model_space]
    rfl
  exact hcoord.symm

set_option maxHeartbeats 800000 in
/-- The hyperbolic covariant derivative maps `C^(k+1)` sections to `C^k` endomorphism fields,
for every regularity `k` at once. -/
instance hyperbolicCovariantDerivative_contMDiff (k : ℕ∞ω) :
    CovariantDerivative.ContMDiffCovariantDerivative hyperbolicCovariantDerivative k := by
  constructor
  constructor
  intro σ hσ
  rw [contMDiffOn_univ] at hσ ⊢
  intro p₀
  rw [contMDiffAt_section]
  have hσf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (k + 1) (sectionToFun σ) := by
    intro p
    exact contMDiffAt_section_iff_fun.mp (hσ p)
  have hfun : (fun p => (trivializationAt (ℂ →L[ℝ] ℂ)
      (fun q : HyperbolicPlane => TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) q)
      p₀ ⟨p, hyperbolicCovariantDerivative σ p⟩).2) =
      flatDerivativeFun σ + christoffelFun σ := by
    funext p
    rw [endomorphismTrivializationAt_snd]
    rfl
  rw [hfun]
  have hflat := contMDiffAt_flatDerivativeFun σ p₀ (hσf p₀)
  have hchristoffelEq : christoffelFun σ = fun p : HyperbolicPlane =>
      (p.im)⁻¹ • ((ContinuousLinearMap.mul ℝ ℂ).comp
        (ContinuousLinearMap.mul ℝ ℂ Complex.I)) (sectionToFun σ p) := rfl
  have hchristoffel : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) k (christoffelFun σ) p₀ := by
    rw [hchristoffelEq]
    have hmul : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) k
        (fun p : HyperbolicPlane =>
          ((ContinuousLinearMap.mul ℝ ℂ).comp
            (ContinuousLinearMap.mul ℝ ℂ Complex.I)) (sectionToFun σ p)) p₀ :=
      ((ContinuousLinearMap.mul ℝ ℂ).comp
        (ContinuousLinearMap.mul ℝ ℂ Complex.I)).contMDiff.contMDiffAt.comp p₀
        ((hσf p₀).of_le (by exact_mod_cast le_self_add))
    exact (contMDiffAt_im_inv p₀).smul hmul
  exact hflat.add hchristoffel

/-! ## The hyperbolic orthonormal frame

The vectors `y·∂x` and `y·∂y` form an orthonormal frame of the Poincaré fiber over a point of
height `y`. The frame computes traces and Ricci contractions in closed form below. -/

/-- The identity linear equivalence between the plane and a tangent fiber. -/
def tangentLinearEquiv (p : HyperbolicPlane) : ℂ ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, ℂ) p where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The basis `(y·1, y·i)` of the tangent fiber over a point of height `y`. -/
noncomputable def tangentBasis (p : HyperbolicPlane) :
    Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) p) :=
  (Complex.basisOneI.isUnitSMul
    (fun _ => (isUnit_iff_ne_zero).mpr (im_ne_zero p))).map (tangentLinearEquiv p)

theorem tangentBasis_apply_zero (p : HyperbolicPlane) :
    tangentBasis p 0 = ((p.im : ℂ)) := by
  show tangentLinearEquiv p (Complex.basisOneI.isUnitSMul
    (fun _ => (isUnit_iff_ne_zero).mpr (im_ne_zero p)) 0) = ((p.im : ℂ))
  rw [Module.Basis.isUnitSMul_apply]
  show p.im • Complex.basisOneI 0 = ((p.im : ℂ))
  rw [Complex.coe_basisOneI]
  simp [Complex.real_smul]

theorem tangentBasis_apply_one (p : HyperbolicPlane) :
    tangentBasis p 1 = ((p.im : ℂ) * Complex.I) := by
  show tangentLinearEquiv p (Complex.basisOneI.isUnitSMul
    (fun _ => (isUnit_iff_ne_zero).mpr (im_ne_zero p)) 1) = ((p.im : ℂ) * Complex.I)
  rw [Module.Basis.isUnitSMul_apply]
  show p.im • Complex.basisOneI 1 = ((p.im : ℂ) * Complex.I)
  rw [Complex.coe_basisOneI]
  simp [Complex.real_smul]

theorem tangentBasis_zero_re (p : HyperbolicPlane) :
    Complex.re (tangentBasis p 0) = p.im :=
  (congrArg Complex.re (tangentBasis_apply_zero p)).trans (by simp)

theorem tangentBasis_zero_im (p : HyperbolicPlane) :
    Complex.im (tangentBasis p 0) = 0 :=
  (congrArg Complex.im (tangentBasis_apply_zero p)).trans (by simp)

theorem tangentBasis_one_re (p : HyperbolicPlane) :
    Complex.re (tangentBasis p 1) = 0 :=
  (congrArg Complex.re (tangentBasis_apply_one p)).trans (by simp)

theorem tangentBasis_one_im (p : HyperbolicPlane) :
    Complex.im (tangentBasis p 1) = p.im :=
  (congrArg Complex.im (tangentBasis_apply_one p)).trans (by simp)

theorem tangentBasis_orthonormal (p : HyperbolicPlane) :
    Orthonormal ℝ (tangentBasis p) := by
  rw [orthonormal_iff_ite]
  have hy := im_ne_zero p
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [inner_tangent_eq, euclideanForm_apply, tangentBasis_zero_re,
      tangentBasis_zero_im, tangentBasis_one_re, tangentBasis_one_im, pow_two] <;>
    norm_num <;>
    field_simp

/-- The hyperbolic orthonormal frame `(y·∂x, y·∂y)` of the Poincaré fiber. -/
noncomputable def orthonormalFrame (p : HyperbolicPlane) :
    OrthonormalBasis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) p) :=
  (tangentBasis p).toOrthonormalBasis (tangentBasis_orthonormal p)

theorem orthonormalFrame_apply_zero (p : HyperbolicPlane) :
    orthonormalFrame p 0 = ((p.im : ℂ)) := by
  rw [orthonormalFrame, Module.Basis.coe_toOrthonormalBasis]
  exact tangentBasis_apply_zero p

theorem orthonormalFrame_apply_one (p : HyperbolicPlane) :
    orthonormalFrame p 1 = ((p.im : ℂ) * Complex.I) := by
  rw [orthonormalFrame, Module.Basis.coe_toOrthonormalBasis]
  exact tangentBasis_apply_one p

/-- Every orthonormal frame of a Poincaré fiber computes the intrinsic endomorphism trace. -/
theorem tangentTrace_eq_sum_inner_frame (p : HyperbolicPlane)
    (basis : OrthonormalBasis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) p))
    (A : TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) p) :
    tangentTrace 𝓘(ℝ, ℂ) p A = ∑ i, inner ℝ (basis i) (A (basis i)) := by
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, ℂ) p) :=
    tangentFiniteDimensional 𝓘(ℝ, ℂ) p
  exact LinearMap.trace_eq_sum_inner _ basis

/-! ## The divergence-free witness field -/

/-- The horizontal coordinate field `∂x`, bundled as a `C^n` vector field for every `n`. -/
noncomputable def horizontalField (n : ℕ∞ω) :
    SmoothVectorField (M := HyperbolicPlane) 𝓘(ℝ, ℂ) n :=
  ⟨constantField 1, contMDiff_constantField 1⟩

/-- The covariant derivative of `∂x` has vanishing trace at every point: its diagonal frame
entries are `g(y∂x, Γ(∂x)(y∂x)) = 0` and `g(y∂y, Γ(∂x)(y∂y)) = 0`. -/
theorem horizontalField_divergence_pointwise (p : HyperbolicPlane) :
    tangentTrace 𝓘(ℝ, ℂ) p (hyperbolicCovariantDerivative (constantField 1) p) = 0 := by
  rw [hyperbolicCovariantDerivative_constantField 1 p,
    tangentTrace_eq_sum_inner_frame p (orthonormalFrame p), Fin.sum_univ_two,
    orthonormalFrame_apply_zero, orthonormalFrame_apply_one]
  have hy := im_ne_zero p
  show ((p.im) ^ 2)⁻¹ * euclideanForm ((p.im : ℂ))
      (christoffelSymbol p 1 ((p.im : ℂ))) +
    ((p.im) ^ 2)⁻¹ * euclideanForm ((p.im : ℂ) * Complex.I)
      (christoffelSymbol p 1 ((p.im : ℂ) * Complex.I)) = 0
  rw [christoffelSymbol_apply, christoffelSymbol_apply, euclideanForm_apply,
    euclideanForm_apply]
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.real_smul,
    Complex.ofReal_re, Complex.ofReal_im]

/-- `∂x` is divergence-free for the hyperbolic Levi-Civita connection, at every regularity. -/
theorem horizontalField_isDivergenceFree (k : ℕ∞ω) :
    IsDivergenceFree 𝓘(ℝ, ℂ) hyperbolicLeviCivitaConnection k
      (hyperbolicCovariantDerivative_contMDiff k) (horizontalField (k + 1)) := by
  rw [isDivergenceFree_iff_pointwise]
  intro p
  exact horizontalField_divergence_pointwise p

/-! ## Curvature of the hyperbolic plane

On the constant coordinate frame the curvature commutator reduces to two covariant derivatives
of fields of the shape `y⁻¹ • K` with `K` a complex constant, and the bracket term vanishes.
The result is `R(∂x, ∂y)∂x = y⁻² ∂y`, the sign and size of curvature `-1`. -/

/-- Covariant derivative of a constant field along a constant field. -/
theorem covariantDerivativeAlong_constant (c d : ℂ) :
    covariantDerivativeAlong 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative
      (constantField d) (constantField c) =
      fun q => (im q)⁻¹ • (Complex.I * c * d) := by
  funext q
  show hyperbolicCovariantDerivative (constantField c) q (constantField d q) = _
  rw [hyperbolicCovariantDerivative_constantField]
  rfl

/-- Pointwise covariant derivative of the conformally-scaled constant field `y⁻¹ • K`. -/
theorem hyperbolicCovariantDerivative_invIm_smul (K : ℂ) (p : HyperbolicPlane)
    (v : TangentSpace 𝓘(ℝ, ℂ) p) :
    hyperbolicCovariantDerivative (fun q => (im q)⁻¹ • K) p v =
      (-((p.im ^ 2)⁻¹ * Complex.im (toComplex v))) • K +
        (p.im)⁻¹ • (Complex.I * ((p.im)⁻¹ • K) * toComplex v) := by
  rw [hyperbolicCovariantDerivative_apply]
  have hane := im_ne_zero p
  -- The scalar coefficient composed with scaling by `K` differentiates by the chain rule.
  have hKL : HasFDerivAt (fun t : ℝ => t • K)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight K) ((im⁻¹ : HyperbolicPlane → ℝ) p) :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight K).hasFDerivAt
  have hinv : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (im⁻¹ : HyperbolicPlane → ℝ) p
      (-(im p ^ 2)⁻¹ • (Complex.imCLM : ℂ →L[ℝ] ℝ)) :=
    (hasMFDerivAt_im p).inv hane
  have hcomp := hKL.hasMFDerivAt.comp p hinv
  have hfun : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun (fun q => (im q)⁻¹ • K)) p
      (((ContinuousLinearMap.id ℝ ℝ).smulRight K).comp
        (-(im p ^ 2)⁻¹ • (Complex.imCLM : ℂ →L[ℝ] ℝ))) := hcomp
  have hflat : mvfderiv 𝓘(ℝ, ℂ) (sectionToFun (fun q => (im q)⁻¹ • K)) p v =
      (-((p.im ^ 2)⁻¹ * Complex.im (toComplex v))) • K := by
    show mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (sectionToFun (fun q => (im q)⁻¹ • K)) p v = _
    rw [hfun.mfderiv]
    show (-(im p ^ 2)⁻¹ * Complex.imCLM v) • K = _
    rw [neg_mul]
    exact rfl
  rw [hflat]
  rfl

set_option maxHeartbeats 800000 in
/-- The curvature commutator on the coordinate frame: `R(∂x, ∂y)Z = y⁻² (i·Z)` for every
constant field `Z`. On `Z = ∂x` this is `y⁻² ∂y`; on `Z = ∂y` it is `-y⁻² ∂x`. -/
theorem curvatureAction_coordinate (c : ℂ) (p : HyperbolicPlane) :
    connectionCurvatureAction 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative
      (constantField 1) (constantField Complex.I) (constantField c) p =
      ((p.im) ^ 2)⁻¹ • (Complex.I * c) := by
  have h₁ := covariantDerivativeAlong_constant c Complex.I
  have h₂ := covariantDerivativeAlong_constant c 1
  show covariantDerivativeAlong 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative (constantField 1)
      (covariantDerivativeAlong 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative
        (constantField Complex.I) (constantField c)) p -
    covariantDerivativeAlong 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative (constantField Complex.I)
      (covariantDerivativeAlong 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative
        (constantField 1) (constantField c)) p -
    covariantDerivativeAlong 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative
      (VectorField.mlieBracket 𝓘(ℝ, ℂ) (constantField 1) (constantField Complex.I))
      (constantField c) p = ((p.im) ^ 2)⁻¹ • (Complex.I * c)
  rw [h₁, h₂, mlieBracket_constantField]
  show hyperbolicCovariantDerivative (fun q => (im q)⁻¹ • (Complex.I * c * Complex.I)) p
      (constantField 1 p) -
    hyperbolicCovariantDerivative (fun q => (im q)⁻¹ • (Complex.I * c * 1)) p
      (constantField Complex.I p) -
    hyperbolicCovariantDerivative (constantField c) p
      ((0 : Π q : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) q) p) =
    ((p.im) ^ 2)⁻¹ • (Complex.I * c)
  have hy := im_ne_zero p
  have hterm₁ : hyperbolicCovariantDerivative
      (fun q => (im q)⁻¹ • (Complex.I * c * Complex.I)) p (constantField 1 p) =
      (((p.im)⁻¹ • ((p.im)⁻¹ • (Complex.I * (Complex.I * c * Complex.I)))) : ℂ) :=
    (hyperbolicCovariantDerivative_invIm_smul _ p _).trans (by
      refine Complex.ext ?_ ?_ <;>
        simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.real_smul,
          Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
          Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, toComplex_constantField,
          mul_one, mul_zero, zero_mul, neg_zero, zero_add, add_zero, sub_zero, zero_sub] <;>
        ring)
  have hterm₂ : hyperbolicCovariantDerivative
      (fun q => (im q)⁻¹ • (Complex.I * c * 1)) p (constantField Complex.I p) =
      (((-(p.im ^ 2)⁻¹) • (Complex.I * c * 1) +
        (p.im)⁻¹ • ((p.im)⁻¹ • (Complex.I * (Complex.I * c * 1) * Complex.I))) : ℂ) :=
    (hyperbolicCovariantDerivative_invIm_smul _ p _).trans (by
      refine Complex.ext ?_ ?_ <;>
        simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.real_smul,
          Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
          Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, toComplex_constantField,
          mul_one, mul_zero, zero_mul, neg_zero, zero_add, add_zero, sub_zero, zero_sub] <;>
        ring)
  have hzero : hyperbolicCovariantDerivative (constantField c) p
      ((0 : Π q : HyperbolicPlane, TangentSpace 𝓘(ℝ, ℂ) q) p) = 0 :=
    map_zero (hyperbolicCovariantDerivative (constantField c) p)
  refine ((congrArg₂ (fun a b : TangentSpace 𝓘(ℝ, ℂ) p => a - b)
    (congrArg₂ (fun a b : TangentSpace 𝓘(ℝ, ℂ) p => a - b) hterm₁ hterm₂) hzero).trans ?_)
  show ((p.im)⁻¹ • ((p.im)⁻¹ • (Complex.I * (Complex.I * c * Complex.I))) -
      ((-(p.im ^ 2)⁻¹) • (Complex.I * c * 1) +
        (p.im)⁻¹ • ((p.im)⁻¹ • (Complex.I * (Complex.I * c * 1) * Complex.I))) - 0 : ℂ) =
    ((((p.im) ^ 2)⁻¹ • (Complex.I * c)) : ℂ)
  have hyC : ((p.im : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.real_smul,
          Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
          Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
          toComplex_constantField, mul_one, mul_zero, zero_mul, neg_zero, zero_add, add_zero,
          sub_zero, zero_sub] <;>
    field_simp <;>
    ring

/-! ## Ricci and scalar curvature

The pointwise curvature tensor is assembled by mathlib-grade tensoriality from the commutator
above; the regularity input is discharged by the smooth-connection bridge. Contracting in the
hyperbolic orthonormal frame yields `Ric = -g` and scalar curvature `-2`. -/

/-- The local curvature-regularity bridge holds at every point: the connection is `C¹`. -/
theorem hyperbolic_hasCurvatureRegularity (p : HyperbolicPlane) :
    HasConnectionCurvatureRegularityAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p :=
  hasConnectionCurvatureRegularityAt_of_contMDiff 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative
    (hyperbolicCovariantDerivative_contMDiff 1) p

/-- Constant fields are `C²` sections, in the form consumed by the curvature tensor. -/
theorem contMDiffAt_two_constantField (c : ℂ) (p : HyperbolicPlane) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 2
      (fun q => TotalSpace.mk' ℂ q (constantField c q)) p :=
  (contMDiff_constantField c) p

theorem mdifferentiableAt_constantField (c : ℂ) (p : HyperbolicPlane) :
    MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun q => TotalSpace.mk' ℂ q (constantField c q)) p :=
  ((contMDiff_constantField c) p).mdifferentiableAt one_ne_zero

/-- The pointwise curvature tensor on coordinate values: `R(∂x, ∂y)Z = y⁻² (i·Z)`. -/
theorem curvatureTensor_coordinate (c : ℂ) (p : HyperbolicPlane) :
    connectionCurvatureTensorAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p)
      (constantField 1 p) (constantField Complex.I p) (constantField c p) =
      ((p.im) ^ 2)⁻¹ • (Complex.I * c) := by
  rw [connectionCurvatureTensorAt_apply 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p)
    (mdifferentiableAt_constantField 1 p) (mdifferentiableAt_constantField Complex.I p)
    (contMDiffAt_two_constantField c p)]
  exact curvatureAction_coordinate c p

/-- `R(∂x, ∂y)∂x` as a scaled vertical field. -/
theorem curvatureTensor_coordinate_horizontal (p : HyperbolicPlane) :
    connectionCurvatureTensorAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p)
      (constantField 1 p) (constantField Complex.I p) (constantField 1 p) =
      ((p.im) ^ 2)⁻¹ • constantField Complex.I p :=
  (curvatureTensor_coordinate 1 p).trans (by
    show (((p.im) ^ 2)⁻¹ • (Complex.I * 1) : ℂ) = ((p.im) ^ 2)⁻¹ • Complex.I
    rw [mul_one])

/-- `R(∂x, ∂y)∂y` as a scaled horizontal field. -/
theorem curvatureTensor_coordinate_vertical (p : HyperbolicPlane) :
    connectionCurvatureTensorAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p)
      (constantField 1 p) (constantField Complex.I p) (constantField Complex.I p) =
      (-((p.im) ^ 2)⁻¹) • constantField 1 p :=
  (curvatureTensor_coordinate Complex.I p).trans (by
    show (((p.im) ^ 2)⁻¹ • (Complex.I * Complex.I) : ℂ) = (-((p.im) ^ 2)⁻¹) • (1 : ℂ)
    rw [Complex.I_mul_I]
    refine Complex.ext ?_ ?_ <;> simp)

/-- The frame vectors are height multiples of the constant coordinate fields. -/
theorem orthonormalFrame_zero_eq (p : HyperbolicPlane) :
    orthonormalFrame p 0 = p.im • constantField 1 p := by
  refine (orthonormalFrame_apply_zero p).trans ?_
  show ((p.im : ℂ)) = p.im • (1 : ℂ)
  refine Complex.ext ?_ ?_ <;> simp

theorem orthonormalFrame_one_eq (p : HyperbolicPlane) :
    orthonormalFrame p 1 = p.im • constantField Complex.I p := by
  refine (orthonormalFrame_apply_one p).trans ?_
  show ((p.im : ℂ) * Complex.I) = p.im • Complex.I
  refine Complex.ext ?_ ?_ <;> simp

/-- The fiber inner product of constant fields. -/
theorem inner_constantField (c d : ℂ) (p : HyperbolicPlane) :
    inner ℝ (constantField c p) (constantField d p) =
      ((p.im) ^ 2)⁻¹ * (c.re * d.re + c.im * d.im) :=
  rfl

set_option maxHeartbeats 800000 in
/-- The Ricci form on the horizontal field: `Ric(∂x, ∂x) = -y⁻²`, the value of `-g(∂x, ∂x)`. -/
theorem ricciForm_horizontal (p : HyperbolicPlane) :
    connectionRicciFormAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p) (constantField 1 p) (constantField 1 p) =
      -((p.im) ^ 2)⁻¹ := by
  rw [connectionRicciFormAt_eq_sum_inner 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p) (orthonormalFrame p), Fin.sum_univ_two,
    orthonormalFrame_zero_eq, orthonormalFrame_one_eq]
  have hswap := connectionCurvatureTensorAt_swap 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p)
    (constantField Complex.I p) (constantField 1 p) (constantField 1 p)
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply,
    connectionCurvatureTensorAt_self, real_inner_smul_left, real_inner_smul_right,
    hswap, curvatureTensor_coordinate_horizontal, inner_constantField,
    inner_zero_right, smul_zero, mul_zero, inner_neg_right, smul_neg]
  have hy := im_ne_zero p
  simp [Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  field_simp

set_option maxHeartbeats 800000 in
/-- The Ricci form on the vertical field: `Ric(∂y, ∂y) = -y⁻²`. -/
theorem ricciForm_vertical (p : HyperbolicPlane) :
    connectionRicciFormAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p)
      (constantField Complex.I p) (constantField Complex.I p) =
      -((p.im) ^ 2)⁻¹ := by
  rw [connectionRicciFormAt_eq_sum_inner 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p) (orthonormalFrame p), Fin.sum_univ_two,
    orthonormalFrame_zero_eq, orthonormalFrame_one_eq]
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply,
    connectionCurvatureTensorAt_self, real_inner_smul_left, real_inner_smul_right,
    curvatureTensor_coordinate_vertical, inner_constantField,
    inner_zero_right, smul_zero, mul_zero, inner_neg_right, smul_neg]
  have hy := im_ne_zero p
  simp [Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  field_simp

/-- The Ricci endomorphism does not annihilate the divergence-free witness `∂x`. This is the
curved input consumed by the CZ24 operator-census witness theorem. -/
theorem ricciAction_horizontal_ne_zero (p : HyperbolicPlane) :
    connectionRicciActionAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p) (constantField 1 p) ≠ 0 := by
  intro hzero
  have hpair := connectionRicciActionAt_inner 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p) (constantField 1 p) (constantField 1 p)
  rw [hzero, inner_zero_left, ricciForm_horizontal] at hpair
  have hy := im_ne_zero p
  have : ((p.im) ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hy)
  exact this (neg_eq_zero.mp hpair.symm)

set_option maxHeartbeats 800000 in
/-- The scalar curvature of the hyperbolic plane is the constant `-2`. -/
theorem scalarCurvature_neg_two (p : HyperbolicPlane) :
    connectionScalarCurvatureAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p) = -2 := by
  show tangentTrace 𝓘(ℝ, ℂ) p (connectionRicciActionAt 𝓘(ℝ, ℂ)
    hyperbolicCovariantDerivative p (hyperbolic_hasCurvatureRegularity p)) = -2
  rw [tangentTrace_eq_sum_inner_frame p (orthonormalFrame p), Fin.sum_univ_two]
  have h₀ := connectionRicciActionAt_inner 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p) (orthonormalFrame p 0) (orthonormalFrame p 0)
  have h₁ := connectionRicciActionAt_inner 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p) (orthonormalFrame p 1) (orthonormalFrame p 1)
  rw [real_inner_comm] at h₀ h₁
  rw [h₀, h₁, orthonormalFrame_zero_eq, orthonormalFrame_one_eq]
  have hform : ∀ c : ℂ, connectionRicciFormAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p)
      (p.im • constantField c p) (p.im • constantField c p) =
      p.im * (p.im * connectionRicciFormAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
        (hyperbolic_hasCurvatureRegularity p) (constantField c p) (constantField c p)) := by
    intro c
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hform 1, hform Complex.I, ricciForm_horizontal, ricciForm_vertical]
  have hy := im_ne_zero p
  field_simp
  ring

/-! ## The surface Ricci identity `Ric = -g`

The Ricci endomorphism acts as `-1` on both frame directions and hence on every tangent
vector; this inhabits the repository's surface-Ricci space-form contract with Gaussian
curvature `-1`. -/

theorem tangent_add_re (p : HyperbolicPlane) (v w : TangentSpace 𝓘(ℝ, ℂ) p) :
    Complex.re (v + w) = Complex.re v + Complex.re w :=
  rfl

theorem tangent_add_im (p : HyperbolicPlane) (v w : TangentSpace 𝓘(ℝ, ℂ) p) :
    Complex.im (v + w) = Complex.im v + Complex.im w :=
  rfl

theorem tangent_smul_re (p : HyperbolicPlane) (r : ℝ) (v : TangentSpace 𝓘(ℝ, ℂ) p) :
    Complex.re (r • v) = r * Complex.re v :=
  Complex.smul_re r v

theorem tangent_smul_im (p : HyperbolicPlane) (r : ℝ) (v : TangentSpace 𝓘(ℝ, ℂ) p) :
    Complex.im (r • v) = r * Complex.im v :=
  Complex.smul_im r v

theorem re_constantField (c : ℂ) (p : HyperbolicPlane) :
    Complex.re (constantField c p) = c.re :=
  rfl

theorem im_constantField (c : ℂ) (p : HyperbolicPlane) :
    Complex.im (constantField c p) = c.im :=
  rfl

/-- Every tangent vector decomposes over the constant coordinate fields. -/
theorem tangent_decomp (p : HyperbolicPlane) (v : TangentSpace 𝓘(ℝ, ℂ) p) :
    v = Complex.re v • constantField 1 p + Complex.im v • constantField Complex.I p := by
  refine Complex.ext ?_ ?_
  · rw [tangent_add_re, tangent_smul_re, tangent_smul_re, re_constantField, re_constantField]
    simp
  · rw [tangent_add_im, tangent_smul_im, tangent_smul_im, im_constantField, im_constantField]
    simp

set_option maxHeartbeats 800000 in
/-- The Ricci form vanishes on the mixed coordinate pair `(∂x, ∂y)`. -/
theorem ricciForm_mixed_horizontal_vertical (p : HyperbolicPlane) :
    connectionRicciFormAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p)
      (constantField 1 p) (constantField Complex.I p) = 0 := by
  rw [connectionRicciFormAt_eq_sum_inner 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p) (orthonormalFrame p), Fin.sum_univ_two,
    orthonormalFrame_zero_eq, orthonormalFrame_one_eq]
  have hswap := connectionCurvatureTensorAt_swap 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p)
    (constantField Complex.I p) (constantField 1 p) (constantField Complex.I p)
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply,
    connectionCurvatureTensorAt_self, real_inner_smul_left, real_inner_smul_right,
    hswap, curvatureTensor_coordinate_vertical, inner_constantField,
    inner_zero_right, smul_zero, inner_neg_right, smul_neg]
  simp [Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]

set_option maxHeartbeats 800000 in
/-- The Ricci form vanishes on the mixed coordinate pair `(∂y, ∂x)`. -/
theorem ricciForm_mixed_vertical_horizontal (p : HyperbolicPlane) :
    connectionRicciFormAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p)
      (constantField Complex.I p) (constantField 1 p) = 0 := by
  rw [connectionRicciFormAt_eq_sum_inner 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p) (orthonormalFrame p), Fin.sum_univ_two,
    orthonormalFrame_zero_eq, orthonormalFrame_one_eq]
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply,
    connectionCurvatureTensorAt_self, real_inner_smul_left, real_inner_smul_right,
    curvatureTensor_coordinate_horizontal, inner_constantField,
    inner_zero_right, smul_zero, inner_neg_right, smul_neg]
  simp [Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]

set_option maxHeartbeats 1600000 in
/-- The Ricci form is the negative of the Poincaré metric: `Ric = -g`. -/
theorem ricciForm_eq_neg_inner (p : HyperbolicPlane)
    (v w : TangentSpace 𝓘(ℝ, ℂ) p) :
    connectionRicciFormAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p) v w = -(inner ℝ v w) := by
  rw [tangent_decomp p v, tangent_decomp p w]
  simp only [map_add, map_smul, add_apply, FunLike.coe_smul,
    Pi.smul_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, ricciForm_horizontal, ricciForm_vertical,
    ricciForm_mixed_horizontal_vertical, ricciForm_mixed_vertical_horizontal,
    inner_constantField, smul_eq_mul, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im]
  ring

/-- The Ricci endomorphism is `-1` on every tangent vector. -/
theorem ricciAction_eq_neg (p : HyperbolicPlane) (v : TangentSpace 𝓘(ℝ, ℂ) p) :
    connectionRicciActionAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p) v = -v := by
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, ℂ) p) :=
    tangentFiniteDimensional 𝓘(ℝ, ℂ) p
  letI : CompleteSpace (TangentSpace 𝓘(ℝ, ℂ) p) := FiniteDimensional.complete ℝ _
  apply ext_inner_right ℝ
  intro w
  rw [connectionRicciActionAt_inner, ricciForm_eq_neg_inner, inner_neg_left]

/-- The connection-derived curvature package of the hyperbolic plane.

The Riemann and Ricci fields are derived from the hyperbolic connection; the scalar and
sectional entries are the supplied constants `-2` and `-1`. The scalar value agrees with the
independently proved `scalarCurvature_neg_two`; the sectional entry is supplied data whose
derivation from the trilinear tensor is not part of this construction. -/
noncomputable def hyperbolicCurvatureData :
    RiemannianCurvatureData (I := 𝓘(ℝ, ℂ)) (M := HyperbolicPlane) :=
  connectionRiemannianCurvatureData 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative
    hyperbolic_hasCurvatureRegularity (fun _ => -2) (fun _ _ _ => -1)

/-- The hyperbolic plane satisfies the surface Ricci identity with Gaussian curvature `-1`:
the first concrete inhabitant of the repository's space-form contracts. -/
theorem hyperbolic_hasSurfaceRicciIdentity :
    HasRiemannianSurfaceRicciIdentity 𝓘(ℝ, ℂ) hyperbolicCurvatureData
      (fun _ => (-1 : ℝ)) := by
  intro p v
  show connectionRicciActionAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
    (hyperbolic_hasCurvatureRegularity p) v = (-1 : ℝ) • v
  rw [ricciAction_eq_neg, neg_one_smul]

end HyperbolicPlane

end RiemannianFluids
