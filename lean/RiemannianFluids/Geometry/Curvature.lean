import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import RiemannianFluids.Geometry.Musical
import RiemannianFluids.Tensors.Contraction

/-!
# Curvature tensors and contractions

The curvature convention used by the fluid operators is

`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.

Mathlib's pinned manifold API supplies bundled covariant derivatives and Lie brackets, but not a
fiberwise Riemann tensor or its Ricci contraction. This module therefore separates two layers:

* `connectionCurvatureAction` constructs the field-level commutator from an actual bundled
  connection. Its defining commutator identity and alternating law are proved below.
* `RiemannianCurvatureData` records the fiberwise Riemann, Ricci, scalar, and sectional observables
  needed downstream. A compatibility constructor retains separately supplied scalar and sectional
  data, while `connectionRiemannianCurvatureDataOfRegularCurvature` derives every field from the
  constructed connection curvature.

This boundary matters for the CCD17 program. The construction below fixes the curvature sign and
eliminates independent data for the three differentiated terms and their commutator. Under an
explicit local connection-regularity condition and a `C³` atlas, tensoriality is proved in all
three slots and packaged as a continuous trilinear map on `T_xM`. Its first/output contraction is
then defined by algebraic trace and raised with the Riemannian metric. A centered-coordinate
contraction regularity contract promotes the Ricci form, raised action, and scalar trace to global
`C^k` fields; sectional curvature is the normalized pointwise contraction on nondegenerate pairs.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Riemann, Ricci, scalar, and sectional curvature on actual Mathlib tangent fibers.

`connectionRiemannianCurvatureData` fills `riemann` and `ricciAction` from a bundled connection and
accepts the last two fields explicitly. `connectionRiemannianCurvatureDataOfRegularCurvature`
derives all four fields when the connection curvature satisfies the global contraction contract. -/
structure RiemannianCurvatureData where
  riemann : ∀ x : M,
    TangentSpace I x → TangentSpace I x → TangentSpace I x → TangentSpace I x
  ricciAction : ∀ x : M, TangentSpace I x → TangentSpace I x
  scalarCurvature : M → ℝ
  sectionalCurvature : ∀ x : M, TangentSpace I x → TangentSpace I x → ℝ

/-- The curvature commutator convention on actual tangent fields. -/
structure RiemannianCurvatureCommutatorData where
  firstThenSecond :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x)
  secondThenFirst :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x)
  bracketDerivative :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x)
  curvatureAction :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x)

/-- `∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y]Z = R(X,Y)Z`. -/
def HasRiemannianCurvatureCommutator
    (data : RiemannianCurvatureCommutatorData (I := I) (M := M)) : Prop :=
  ∀ first second field x,
    data.firstThenSecond first second field x -
        data.secondThenFirst first second field x -
        data.bracketDerivative first second field x =
      data.curvatureAction first second field x

/-! ## Curvature commutator constructed from a connection -/

noncomputable section

/-- Covariant differentiation of `field` along `direction`, as a raw tangent field.

No regularity conclusion is asserted here. The bundled connection can act on raw sections; later
operator constructions attach the appropriate `C^k` hypotheses and derivative loss. -/
def covariantDerivativeAlong
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (direction field : (x : M) → TangentSpace I x) :
    (x : M) → TangentSpace I x :=
  fun x ↦ connection field x (direction x)

/-- The curvature action constructed from a bundled tangent connection.

The argument order follows the displayed convention: `first` is the outer direction in the first
term and `second` is the outer direction in the second term. -/
def connectionCurvatureAction
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (first second field : (x : M) → TangentSpace I x) :
    (x : M) → TangentSpace I x :=
  covariantDerivativeAlong I connection first
      (covariantDerivativeAlong I connection second field) -
    covariantDerivativeAlong I connection second
      (covariantDerivativeAlong I connection first field) -
    covariantDerivativeAlong I connection (VectorField.mlieBracket I first second) field

/-- Populate every term of the curvature-commutator interface from one bundled connection. -/
def connectionCurvatureCommutatorData
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    RiemannianCurvatureCommutatorData (I := I) (M := M) where
  firstThenSecond first second field :=
    covariantDerivativeAlong I connection first
      (covariantDerivativeAlong I connection second field)
  secondThenFirst first second field :=
    covariantDerivativeAlong I connection second
      (covariantDerivativeAlong I connection first field)
  bracketDerivative first second field :=
    covariantDerivativeAlong I connection (VectorField.mlieBracket I first second) field
  curvatureAction := connectionCurvatureAction I connection

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The connection-derived data satisfies the curvature commutator with no additional hypothesis. -/
theorem connectionCurvatureCommutatorData_hasCommutator
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    HasRiemannianCurvatureCommutator I
      (connectionCurvatureCommutatorData I connection) := by
  intro first second field x
  rfl

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- Curvature is alternating in its two direction fields for every bundled connection. -/
theorem connectionCurvatureAction_swap
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (first second field : (x : M) → TangentSpace I x) :
    connectionCurvatureAction I connection first second field =
      -connectionCurvatureAction I connection second first field := by
  rw [connectionCurvatureAction, connectionCurvatureAction,
    VectorField.mlieBracket_swap]
  funext x
  simp only [covariantDerivativeAlong, Pi.sub_apply, Pi.neg_apply,
    ContinuousLinearMap.map_neg]
  module

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- Applying curvature twice in the same direction gives zero. -/
@[simp]
theorem connectionCurvatureAction_self
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (direction field : (x : M) → TangentSpace I x) :
    connectionCurvatureAction I connection direction direction field = 0 := by
  rw [connectionCurvatureAction, VectorField.mlieBracket_self]
  funext x
  simp [covariantDerivativeAlong]

/-! ## Pointwise curvature tensor

The curvature commutator is second order in the differentiated field. To make its two direction
arguments pointwise, we need the local regularity statement that differentiating a `C²` field
along a differentiable direction produces a differentiable field. The pinned Mathlib API exposes
global connection regularity but not the local consequence needed by its tensoriality criterion,
so `HasConnectionCurvatureRegularityAt` records exactly that bridge. On a smooth Hausdorff
manifold, `hasConnectionCurvatureRegularityAt_of_contMDiff` discharges the bridge from mathlib's
`C¹` connection-regularity class by cutting fields off with a smooth bump function.

Under this condition, the derivative terms created by multiplying either direction by a scalar
function cancel against the corresponding Lie-bracket product rule. The resulting
`connectionCurvatureDirectionsAt` is an actual continuous bilinear map on `T_xM`, not freely
supplied curvature data. The differentiated-field calculation uses a separate `C²` tensoriality
contract, because the commutator is second order in that argument. Its scalar commutator terms
cancel by the manifold Jacobi identity, yielding `connectionCurvatureTensorAt`, an actual
continuous trilinear map in conventional `R(X,Y)Z` order.
-/

section PointwiseDirections

variable [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]

/-- The local regularity needed to form curvature from two successive covariant derivatives.

For a differentiable direction `X` and a twice differentiable field `Z`, the once differentiated
field `∇_X Z` must itself be differentiable at `x`. -/
def HasConnectionCurvatureRegularityAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M) : Prop :=
  ∀ (direction field : (y : M) → TangentSpace I y),
    MDiffAt (T% direction) x → CMDiffAt 2 (T% field) x →
      MDiffAt (T% (covariantDerivativeAlong I connection direction field)) x

omit [CompleteSpace E] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- Mathlib's global connection-regularity class discharges the local curvature-regularity
bridge on a smooth Hausdorff manifold.

The class consumes globally `C²` sections, while the curvature construction differentiates
fields that are only `C²` near the base point.  A smooth bump function supported inside the
regularity neighborhood cuts the field off to a globally `C²` section agreeing with it near
the point; the class then makes the covariant-derivative section of the cutoff differentiable,
application to the direction field is differentiable by the bundle-hom calculus, and locality
of the covariant derivative transports the conclusion back to the original field.  The smooth
atlas and Hausdorff hypotheses are what mathlib's bump functions require. -/
theorem hasConnectionCurvatureRegularityAt_of_contMDiff
    [T2Space M] [IsManifold I ∞ M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (smooth : CovariantDerivative.ContMDiffCovariantDerivative connection 1)
    (x : M) :
    HasConnectionCurvatureRegularityAt I connection x := by
  intro direction field hdirection hfield
  -- The field is `C²` on an open neighborhood `v` of `x`.
  rcases (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by simp)).mp hfield with ⟨u, hu, hfieldOn⟩
  rcases mem_nhds_iff.mp hu with ⟨v, hvu, hvopen, hxv⟩
  have hfieldV : CMDiff[v] 2 (T% field) := hfieldOn.mono hvu
  -- Choose a smooth bump function at `x` supported inside `v`.
  obtain ⟨f, hf⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (hvopen.mem_nhds hxv)).ex_mem
  -- Cutting the field off with the bump gives a globally `C²` section.
  have htwo_le : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hcutoff : CMDiff 2 (T% ((f : M → ℝ) • field)) :=
    ContMDiffOn.smul_section_of_tsupport
      ((f.contMDiff.of_le htwo_le).contMDiffOn) hvopen hf hfieldV
  -- The regularity class makes the covariant-derivative section of the cutoff `C¹`.
  have hhom : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) y
        (connection ((f : M → ℝ) • field) y)) x := by
    have hone_one : ((1 : ℕ∞ω) + 1) = 2 := by norm_num
    have hglobal := smooth.contMDiff.contMDiff
      (σ := (f : M → ℝ) • field) (hone_one ▸ hcutoff.contMDiffOn)
    exact ((contMDiffOn_univ.mp hglobal) x).mdifferentiableAt (by norm_num)
  -- Applying the covariant-derivative section to the direction field is differentiable.
  have happlied :
      MDiffAt (T% (covariantDerivativeAlong I connection direction ((f : M → ℝ) • field))) x :=
    hhom.clm_bundle_apply hdirection
  -- The bump equals one near `x`, so the cutoff agrees with the field near `x`.
  have hone_nhds : {y | f y = 1} ∈ nhds x := by
    filter_upwards [f.eventuallyEq_one] with y hy
    simpa using hy
  have hinterior : interior {y | f y = 1} ∩ v ∈ nhds x :=
    inter_mem (interior_mem_nhds.mpr hone_nhds) (hvopen.mem_nhds hxv)
  -- Locality of the covariant derivative transfers the differentiated section.
  have heventually :
      T% (covariantDerivativeAlong I connection direction field) =ᶠ[nhds x]
        T% (covariantDerivativeAlong I connection direction ((f : M → ℝ) • field)) := by
    filter_upwards [eventually_mem_nhds_iff.mpr hinterior] with y hy
    obtain ⟨hy_one, hy_v⟩ := mem_of_mem_nhds hy
    have hcutoff_eventually : ∀ᶠ z in nhds y, ((f : M → ℝ) • field) z = field z := by
      filter_upwards [(isOpen_interior.inter hvopen).mem_nhds (mem_of_mem_nhds hy)]
        with z hz
      have hz_one : f z = 1 := by
        have := interior_subset (s := {y | f y = 1}) hz.1
        simpa using this
      show f z • field z = field z
      rw [hz_one, one_smul]
    have hfield_at : MDiffAt (T% field) y :=
      ((hfieldV y hy_v).contMDiffAt (hvopen.mem_nhds hy_v)).mdifferentiableAt (by norm_num)
    have hcutoff_at : MDiffAt (T% ((f : M → ℝ) • field)) y :=
      (hcutoff y).mdifferentiableAt (by norm_num)
    have hvalue :
        connection field y = connection ((f : M → ℝ) • field) y :=
      connection.isCovariantDerivativeOn.congr_of_eventuallyEq hfield_at hcutoff_at
        Filter.univ_mem (hcutoff_eventually.mono fun z hz => hz.symm)
    simp only [covariantDerivativeAlong, hvalue]
  exact happlied.congr_of_eventuallyEq heventually

/-- Tensoriality at `x` tested on `C²` scalar functions and tangent fields.

Mathlib's `TensorialAt` uses differentiable fields, which is exactly right for first-order
operators. Curvature is second order in its differentiated field, so using that predicate for the
third slot would assert behavior of a raw bundled connection outside the regularity controlled by
its axioms. This version records the honest `C²` contract. -/
structure C2TensorialAt {A : Type*} [AddCommGroup A] [Module ℝ A]
    (Φ : ((y : M) → TangentSpace I y) → A) (x : M) : Prop where
  smul : ∀ {f : M → ℝ} {field : (y : M) → TangentSpace I y},
    CMDiffAt 2 f x → CMDiffAt 2 (T% field) x → Φ (f • field) = f x • Φ field
  add : ∀ {field field' : (y : M) → TangentSpace I y},
    CMDiffAt 2 (T% field) x → CMDiffAt 2 (T% field') x →
      Φ (field + field') = Φ field + Φ field'

namespace C2TensorialAt

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (TangentSpace I : M → Type _)] [IsManifold I 2 M] in
/-- A `C²`-tensorial operation depends only on the germ of its field argument at `x`. -/
protected theorem «local» {A : Type*} [AddCommGroup A] [Module ℝ A]
    {Φ : ((y : M) → TangentSpace I y) → A} {x : M}
    (hΦ : C2TensorialAt I Φ x)
    {field field' : (y : M) → TangentSpace I y}
    (hfield : CMDiffAt 2 (T% field) x)
    (hfield' : CMDiffAt 2 (T% field') x)
    (heq : field =ᶠ[nhds x] field') : Φ field = Φ field' := by
  classical
  let ψ (y : M) : ℝ := if field y = field' y then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, heq.self_of_nhds]
  have hψ : CMDiffAt 2 ψ x := by
    have hone : CMDiffAt 2 (fun _ : M ↦ (1 : ℝ)) x := contMDiffAt_const
    exact hone.congr_of_eventuallyEq (heq.mono fun y hy ↦ by simp [ψ, hy])
  have hscaled (y : M) : (ψ • field) y = (ψ • field') y := by
    dsimp [ψ]
    split_ifs with hy <;> simp [hy]
  calc
    Φ field = Φ (ψ • field) := by simp [hΦ.smul hψ hfield, hψx]
    _ = Φ (ψ • field') := by rw [funext hscaled]
    _ = Φ field' := by simp [hΦ.smul hψ hfield', hψx]

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (TangentSpace I : M → Type _)] [IsManifold I 2 M] in
/-- A `C²`-tensorial operation respects finite sums of `C²` tangent fields. -/
theorem sum {A : Type*} [AddCommGroup A] [Module ℝ A]
    {Φ : ((y : M) → TangentSpace I y) → A} {x : M}
    (hΦ : C2TensorialAt I Φ x)
    {ι : Type*} {s : Finset ι}
    (field : ι → (y : M) → TangentSpace I y)
    (hfield : ∀ i ∈ s, CMDiffAt 2 (T% (field i)) x) :
    Φ (fun y ↦ ∑ i ∈ s, field i y) = ∑ i ∈ s, Φ (field i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change Φ (0 : (y : M) → TangentSpace I y) = 0
      have hzero : CMDiffAt 2 (T% (0 : (y : M) → TangentSpace I y)) x := by
        exact (contMDiff_zeroSection ℝ (TangentSpace I)).contMDiffAt.of_le le_top
      have hz := hΦ.smul (f := fun _ : M ↦ (0 : ℝ))
        (field := (0 : (y : M) → TangentSpace I y)) contMDiffAt_const hzero
      simpa using hz
  | @insert a s ha ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hfield
      simp only [Finset.sum_insert ha, ← ih hfield.2]
      exact hΦ.add hfield.1 (.sum_section hfield.2)

omit [RiemannianBundle (TangentSpace I : M → Type _)] [CompleteSpace E] in
/-- A `C²`-tensorial operation depends only on the field value at `x`. -/
theorem pointwise {A : Type*} [AddCommGroup A] [Module ℝ A]
    [IsManifold I 3 M]
    {Φ : ((y : M) → TangentSpace I y) → A} {x : M}
    (hΦ : C2TensorialAt I Φ x)
    {field field' : (y : M) → TangentSpace I y}
    (hfield : CMDiffAt 2 (T% field) x)
    (hfield' : CMDiffAt 2 (T% field') x)
    (heq : field x = field' x) : Φ field = Φ field' := by
  letI : IsManifold I ((2 : ℕ∞ω) + 1) M := by
    norm_num
    infer_instance
  letI : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  letI : IsManifold I.tangent 2 (TangentBundle I M) := inferInstance
  let t := trivializationAt E (TangentSpace I) x
  have x_mem : x ∈ t.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  let b := Module.Basis.ofVectorSpace ℝ E
  let frame := t.localFrame b
  let coeff := t.localFrame_coeff I b
  have hframe (i) : CMDiffAt 2 (T% (frame i)) x :=
    contMDiffAt_localFrame_of_mem 2 t b i x_mem
  have hcoeff {field₀ : (y : M) → TangentSpace I y}
      (hfield₀ : CMDiffAt 2 (T% field₀) x) (i) :
      CMDiffAt 2 (LinearMap.piApply (coeff i) field₀) x :=
    contMDiffAt_localFrame_coeff b x_mem hfield₀ i
  have hΦ_eq {field₀ : (y : M) → TangentSpace I y}
      (hfield₀ : CMDiffAt 2 (T% field₀) x) :
      Φ field₀ = Φ (fun y ↦ ∑ i, coeff i y (field₀ y) • frame i y) :=
    C2TensorialAt.«local» I hΦ hfield₀
      (.sum_section fun i _ ↦ (hcoeff hfield₀ i).smul_section (hframe i))
      (t.eventually_eq_localFrame_sum_coeff_smul b x_mem)
  rw [hΦ_eq hfield, hΦ_eq hfield', hΦ.sum, hΦ.sum]
  · congr! 1 with i
    calc
      Φ ((LinearMap.piApply (coeff i) field) • frame i) =
          coeff i x (field x) • Φ (frame i) :=
        hΦ.smul (hcoeff hfield i) (hframe i)
      _ = coeff i x (field' x) • Φ (frame i) := by rw [heq]
      _ = Φ ((LinearMap.piApply (coeff i) field') • frame i) :=
        (hΦ.smul (hcoeff hfield' i) (hframe i)).symm
  · exact fun i _ ↦ (hcoeff hfield' i).smul_section (hframe i)
  · exact fun i _ ↦ (hcoeff hfield i).smul_section (hframe i)

end C2TensorialAt

/-! ### Scalar commutator cancellation

The third-slot calculation differentiates the scalar coefficients produced by two applications of
the connection Leibniz rule. The following two lemmas isolate the intrinsic calculus needed to
cancel those coefficients. `scalarLieCommutator_smul` is deliberately stated after multiplying by
the field value: that is the exact identity used by curvature, and it remains valid even when the
field vanishes at the base point.
-/

/-- Differentiation of a scalar function along a tangent field. -/
def scalarDirectionalDerivative
    (f : M → ℝ) (direction : (y : M) → TangentSpace I y) : M → ℝ :=
  fun y ↦ d% f y (direction y)

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (TangentSpace I : M → Type _)] in
set_option maxHeartbeats 800000 in
/-- A `C²` scalar differentiated along a `C¹` tangent field is `C¹` at the base point. -/
theorem contMDiffAt_one_scalarDirectionalDerivative
    {x : M} {f : M → ℝ} {direction : (y : M) → TangentSpace I y}
    (hf : CMDiffAt 2 f x) (hdirection : CMDiffAt 1 (T% direction) x) :
    CMDiffAt 1 (scalarDirectionalDerivative I f direction) x := by
  rcases (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by simp)).mp hf with
    ⟨u, hu, hfu⟩
  rcases mem_nhds_iff.mp hu with ⟨v, hvu, hvopen, hxv⟩
  have hfv : CMDiff[v] 2 f := hfu.mono hvu
  have htmWithin : CMDiff[(π E (TangentSpace I) ⁻¹' v)] 1
      (tangentMap[v] f) :=
    hfv.contMDiffOn_tangentMapWithin (by norm_num) hvopen.uniqueMDiffOn
  have hcompWithin : CMDiffAt[v] 1
      ((tangentMap[v] f) ∘ fun y ↦ (T% direction y)) x := by
    exact (htmWithin (T% direction x) hxv).comp x hdirection.contMDiffWithinAt
      (by intro y hy; exact hy)
  have hcompAt : CMDiffAt 1
      ((tangentMap[v] f) ∘ fun y ↦ (T% direction y)) x :=
    hcompWithin.contMDiffAt (hvopen.mem_nhds hxv)
  have heq :
      ((tangentMap% f) ∘ fun y ↦ (T% direction y)) =ᶠ[nhds x]
        ((tangentMap[v] f) ∘ fun y ↦ (T% direction y)) := by
    filter_upwards [hvopen.mem_nhds hxv] with y hy
    simp only [Function.comp_apply, tangentMapWithin, tangentMap,
      mfderivWithin_of_isOpen hvopen hy]
  have hcomp : CMDiffAt 1
      ((tangentMap% f) ∘ fun y ↦ (T% direction y)) x :=
    hcompAt.congr_of_eventuallyEq heq
  have hsnd := contMDiff_snd_tangentBundle_modelSpace (n := 1) ℝ 𝓘(ℝ, ℝ)
  have heval :
      ((fun p : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ p.snd) ∘
        (tangentMap% f) ∘ fun y ↦ (T% direction y)) =
        scalarDirectionalDerivative I f direction := by
    rfl
  rw [← heval]
  exact hsnd.contMDiffAt.comp x hcomp

omit [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
set_option maxHeartbeats 800000 in
/-- The scalar Lie-derivative commutator vanishes after acting on the field value.

This is the cancellation
`(X(Yf) - Y(Xf) - [X,Y]f) • Z = 0`. It follows from Mathlib's manifold Jacobi identity and Lie
bracket product rules. The `C³` atlas assumption is the regularity currently required by that
Jacobi theorem; the scalar and vector fields themselves only need two derivatives at `x`. -/
theorem scalarLieCommutator_smul
    [IsManifold I 3 M]
    {x : M} {f : M → ℝ}
    {first second field : (y : M) → TangentSpace I y}
    (hf : CMDiffAt 2 f x)
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x)
    (hfield : CMDiffAt 2 (T% field) x) :
    (d% (scalarDirectionalDerivative I f second) x (first x) -
          d% (scalarDirectionalDerivative I f first) x (second x) -
          d% f x (VectorField.mlieBracket I first second x)) • field x = 0 := by
  letI : IsManifold I (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold I 2 M)
  letI : IsManifold I (minSmoothness ℝ 3) M := by
    simpa using (inferInstance : IsManifold I 3 M)
  letI : IsManifold I ((2 : ℕ∞ω) + 1) M := by
    norm_num
    infer_instance
  letI : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  letI : IsManifold I.tangent 2 (TangentBundle I M) := inferInstance
  let firstF := scalarDirectionalDerivative I f first
  let secondF := scalarDirectionalDerivative I f second
  let firstSecond := VectorField.mlieBracket I first second
  let firstField := VectorField.mlieBracket I first field
  let secondField := VectorField.mlieBracket I second field
  have hfirstF : CMDiffAt 1 firstF x :=
    contMDiffAt_one_scalarDirectionalDerivative I hf (hfirst.of_le (by norm_num))
  have hsecondF : CMDiffAt 1 secondF x :=
    contMDiffAt_one_scalarDirectionalDerivative I hf (hsecond.of_le (by norm_num))
  have hfirstSecond : CMDiffAt 1 (T% firstSecond) x :=
    hfirst.mlieBracket_vectorField hsecond (m := 1) (n := (2 : ℕ∞)) (by norm_num)
  have hfirstField : CMDiffAt 1 (T% firstField) x :=
    hfirst.mlieBracket_vectorField hfield (m := 1) (n := (2 : ℕ∞)) (by norm_num)
  have hsecondField : CMDiffAt 1 (T% secondField) x :=
    hsecond.mlieBracket_vectorField hfield (m := 1) (n := (2 : ℕ∞)) (by norm_num)
  have hf_one : CMDiffAt 1 f x := hf.of_le (by norm_num)
  have hfield_one : CMDiffAt 1 (T% field) x := hfield.of_le (by norm_num)
  have hf_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 f y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hf
  have hfirst_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 (T% first) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hfirst
  have hsecond_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 (T% second) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hsecond
  have hfield_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 (T% field) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hfield
  have hsecond_smul :
      VectorField.mlieBracket I second (f • field) =ᶠ[nhds x]
        secondF • field + f • secondField := by
    filter_upwards [hf_eventually, hsecond_eventually, hfield_eventually] with y hfy hsy hzy
    change VectorField.mlieBracket I second (f • field) y =
      d% f y (second y) • field y +
        f y • VectorField.mlieBracket I second field y
    exact VectorField.mlieBracket_smul_right (I := I)
      (hfy.mdifferentiableAt (by norm_num))
      (hzy.mdifferentiableAt (by norm_num)) (V := second)
  have hfirst_smul :
      VectorField.mlieBracket I first (f • field) =ᶠ[nhds x]
        firstF • field + f • firstField := by
    filter_upwards [hf_eventually, hfirst_eventually, hfield_eventually] with y hfy hxy hzy
    change VectorField.mlieBracket I first (f • field) y =
      d% f y (first y) • field y +
        f y • VectorField.mlieBracket I first field y
    exact VectorField.mlieBracket_smul_right (I := I)
      (hfy.mdifferentiableAt (by norm_num))
      (hzy.mdifferentiableAt (by norm_num)) (V := first)
  have hfirst_min : CMDiffAt (minSmoothness ℝ 2) (T% first) x := by
    simpa using hfirst
  have hsecond_min : CMDiffAt (minSmoothness ℝ 2) (T% second) x := by
    simpa using hsecond
  have hfield_min : CMDiffAt (minSmoothness ℝ 2) (T% field) x := by
    simpa using hfield
  have hf_field_min : CMDiffAt (minSmoothness ℝ 2) (T% (f • field)) x := by
    simpa using hf.smul_section hfield
  have hjacobiScaled := VectorField.leibniz_identity_mlieBracket_apply
    (I := I) hfirst_min hsecond_min hf_field_min
  have hfirst_refl : first =ᶠ[nhds x] first := Filter.EventuallyEq.rfl
  have hsecond_refl : second =ᶠ[nhds x] second := Filter.EventuallyEq.rfl
  have houterSecond :
      VectorField.mlieBracket I first
          (VectorField.mlieBracket I second (f • field)) x =
        VectorField.mlieBracket I first (secondF • field + f • secondField) x :=
    hfirst_refl.mlieBracket_vectorField_eq hsecond_smul
  have houterFirst :
      VectorField.mlieBracket I second
          (VectorField.mlieBracket I first (f • field)) x =
        VectorField.mlieBracket I second (firstF • field + f • firstField) x :=
    hsecond_refl.mlieBracket_vectorField_eq hfirst_smul
  rw [houterSecond, houterFirst] at hjacobiScaled
  have hsecondF_field : CMDiffAt 1 (T% (secondF • field)) x :=
    hsecondF.smul_section hfield_one
  have hf_secondField : CMDiffAt 1 (T% (f • secondField)) x :=
    hf_one.smul_section hsecondField
  have hfirstF_field : CMDiffAt 1 (T% (firstF • field)) x :=
    hfirstF.smul_section hfield_one
  have hf_firstField : CMDiffAt 1 (T% (f • firstField)) x :=
    hf_one.smul_section hfirstField
  rw [VectorField.mlieBracket_add_right
      (hsecondF_field.mdifferentiableAt (by norm_num))
      (hf_secondField.mdifferentiableAt (by norm_num)),
    VectorField.mlieBracket_add_right
      (hfirstF_field.mdifferentiableAt (by norm_num))
      (hf_firstField.mdifferentiableAt (by norm_num))]
      at hjacobiScaled
  rw [VectorField.mlieBracket_smul_right (hsecondF.mdifferentiableAt (by norm_num))
      (hfield_one.mdifferentiableAt (by norm_num)),
    VectorField.mlieBracket_smul_right (hf.mdifferentiableAt (by norm_num))
      (hsecondField.mdifferentiableAt (by norm_num)),
    VectorField.mlieBracket_smul_right (hf.mdifferentiableAt (by norm_num))
      (hfield.mdifferentiableAt (by norm_num)),
    VectorField.mlieBracket_smul_right (hfirstF.mdifferentiableAt (by norm_num))
      (hfield_one.mdifferentiableAt (by norm_num)),
    VectorField.mlieBracket_smul_right (hf.mdifferentiableAt (by norm_num))
      (hfirstField.mdifferentiableAt (by norm_num))] at hjacobiScaled
  have hjacobi := VectorField.leibniz_identity_mlieBracket_apply
    (I := I) hfirst_min hsecond_min hfield_min
  change VectorField.mlieBracket I first secondField x =
      VectorField.mlieBracket I firstSecond field x +
        VectorField.mlieBracket I second firstField x at hjacobi
  dsimp only [firstF, secondF, firstSecond, firstField, secondField] at hjacobiScaled hjacobi ⊢
  rw [hjacobi] at hjacobiScaled
  simp only [scalarDirectionalDerivative] at hjacobiScaled ⊢
  rw [← sub_eq_zero] at hjacobiScaled
  simp only [smul_add] at hjacobiScaled
  simp only [sub_smul]
  abel_nf at hjacobiScaled ⊢
  exact hjacobiScaled

omit [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
set_option maxHeartbeats 800000 in
/-- The connection curvature action is tensorial in the differentiated-field slot.

The `C²` hypotheses expose the real order of the calculation: multiplying `Z` by `f` creates
first-derivative terms in both iterated covariant derivatives, and those terms cancel against
`∇_[X,Y](fZ)` by `scalarLieCommutator_smul`. The proof uses equality of the connection Leibniz
expansion on a neighborhood of `x`, rather than substituting a merely pointwise identity beneath
the outer covariant derivative. -/
theorem connectionCurvatureAction_tensorial_field_smul
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    {f : M → ℝ} {first second field : (y : M) → TangentSpace I y}
    (hf : CMDiffAt 2 f x)
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x)
    (hfield : CMDiffAt 2 (T% field) x) :
    connectionCurvatureAction I connection first second (f • field) x =
      f x • connectionCurvatureAction I connection first second field x := by
  letI : IsManifold I ((2 : ℕ∞ω) + 1) M := by
    norm_num
    infer_instance
  letI : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  letI : IsManifold I.tangent 2 (TangentBundle I M) := inferInstance
  let firstF := scalarDirectionalDerivative I f first
  let secondF := scalarDirectionalDerivative I f second
  let firstDerived := covariantDerivativeAlong I connection first field
  let secondDerived := covariantDerivativeAlong I connection second field
  let firstScaledDerived := covariantDerivativeAlong I connection first (f • field)
  let secondScaledDerived := covariantDerivativeAlong I connection second (f • field)
  let expandedFirst := f • firstDerived + firstF • field
  let expandedSecond := f • secondDerived + secondF • field
  have hf_one : CMDiffAt 1 f x := hf.of_le (by norm_num)
  have hfirst_one : CMDiffAt 1 (T% first) x := hfirst.of_le (by norm_num)
  have hsecond_one : CMDiffAt 1 (T% second) x := hsecond.of_le (by norm_num)
  have hfield_one : CMDiffAt 1 (T% field) x := hfield.of_le (by norm_num)
  have hscaledField : CMDiffAt 2 (T% (f • field)) x := hf.smul_section hfield
  have hfirstDerived : MDiffAt (T% firstDerived) x :=
    regular first field (hfirst_one.mdifferentiableAt (by norm_num)) hfield
  have hsecondDerived : MDiffAt (T% secondDerived) x :=
    regular second field (hsecond_one.mdifferentiableAt (by norm_num)) hfield
  have hfirstScaledDerived : MDiffAt (T% firstScaledDerived) x :=
    regular first (f • field) (hfirst_one.mdifferentiableAt (by norm_num)) hscaledField
  have hsecondScaledDerived : MDiffAt (T% secondScaledDerived) x :=
    regular second (f • field) (hsecond_one.mdifferentiableAt (by norm_num)) hscaledField
  have hfirstF : CMDiffAt 1 firstF x :=
    contMDiffAt_one_scalarDirectionalDerivative I hf hfirst_one
  have hsecondF : CMDiffAt 1 secondF x :=
    contMDiffAt_one_scalarDirectionalDerivative I hf hsecond_one
  have hf_firstDerived : MDiffAt (T% (f • firstDerived)) x :=
    (hf_one.mdifferentiableAt (by norm_num)).smul_section hfirstDerived
  have hf_secondDerived : MDiffAt (T% (f • secondDerived)) x :=
    (hf_one.mdifferentiableAt (by norm_num)).smul_section hsecondDerived
  have hfirstF_field : MDiffAt (T% (firstF • field)) x :=
    (hfirstF.mdifferentiableAt (by norm_num)).smul_section
      (hfield_one.mdifferentiableAt (by norm_num))
  have hsecondF_field : MDiffAt (T% (secondF • field)) x :=
    (hsecondF.mdifferentiableAt (by norm_num)).smul_section
      (hfield_one.mdifferentiableAt (by norm_num))
  have hexpandedFirst : MDiffAt (T% expandedFirst) x :=
    mdifferentiableAt_add_section hf_firstDerived hfirstF_field
  have hexpandedSecond : MDiffAt (T% expandedSecond) x :=
    mdifferentiableAt_add_section hf_secondDerived hsecondF_field
  have hf_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 f y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hf
  have hfield_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 (T% field) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hfield
  have hfirstExpansion : firstScaledDerived =ᶠ[nhds x] expandedFirst := by
    filter_upwards [hf_eventually, hfield_eventually] with y hfy hzy
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.leibniz
        (hzy.mdifferentiableAt (by norm_num))
        (hfy.mdifferentiableAt (by norm_num))) (first y)
  have hsecondExpansion : secondScaledDerived =ᶠ[nhds x] expandedSecond := by
    filter_upwards [hf_eventually, hfield_eventually] with y hfy hzy
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.leibniz
        (hzy.mdifferentiableAt (by norm_num))
        (hfy.mdifferentiableAt (by norm_num))) (second y)
  have houterFirst :
      covariantDerivativeAlong I connection second firstScaledDerived x =
        covariantDerivativeAlong I connection second expandedFirst x := by
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.congr_of_eventuallyEq
        hfirstScaledDerived hexpandedFirst Filter.univ_mem hfirstExpansion) (second x)
  have houterSecond :
      covariantDerivativeAlong I connection first secondScaledDerived x =
        covariantDerivativeAlong I connection first expandedSecond x := by
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.congr_of_eventuallyEq
        hsecondScaledDerived hexpandedSecond Filter.univ_mem hsecondExpansion) (first x)
  have hfirstExpanded :
      covariantDerivativeAlong I connection second expandedFirst x =
        f x • covariantDerivativeAlong I connection second firstDerived x +
          firstF x • covariantDerivativeAlong I connection second field x +
          (d% f x (second x) • firstDerived x +
            d% firstF x (second x) • field x) := by
    rw [covariantDerivativeAlong]
    rw [connection.isCovariantDerivativeOn.add hf_firstDerived hfirstF_field]
    rw [connection.isCovariantDerivativeOn.leibniz hfirstDerived
      (hf_one.mdifferentiableAt (by norm_num))]
    rw [connection.isCovariantDerivativeOn.leibniz
      (hfield_one.mdifferentiableAt (by norm_num))
      (hfirstF.mdifferentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    simp only [covariantDerivativeAlong]
    module
  have hsecondExpanded :
      covariantDerivativeAlong I connection first expandedSecond x =
        f x • covariantDerivativeAlong I connection first secondDerived x +
          secondF x • covariantDerivativeAlong I connection first field x +
          (d% f x (first x) • secondDerived x +
            d% secondF x (first x) • field x) := by
    rw [covariantDerivativeAlong]
    rw [connection.isCovariantDerivativeOn.add hf_secondDerived hsecondF_field]
    rw [connection.isCovariantDerivativeOn.leibniz hsecondDerived
      (hf_one.mdifferentiableAt (by norm_num))]
    rw [connection.isCovariantDerivativeOn.leibniz
      (hfield_one.mdifferentiableAt (by norm_num))
      (hsecondF.mdifferentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    simp only [covariantDerivativeAlong]
    module
  have hbracket :
      covariantDerivativeAlong I connection (VectorField.mlieBracket I first second)
          (f • field) x =
        f x • covariantDerivativeAlong I connection
            (VectorField.mlieBracket I first second) field x +
          d% f x (VectorField.mlieBracket I first second x) • field x := by
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.leibniz
        (hfield_one.mdifferentiableAt (by norm_num))
        (hf_one.mdifferentiableAt (by norm_num)))
      (VectorField.mlieBracket I first second x)
  have hscalar := scalarLieCommutator_smul I hf hfirst hsecond hfield
  rw [connectionCurvatureAction, connectionCurvatureAction]
  simp only [Pi.sub_apply]
  change
    covariantDerivativeAlong I connection first secondScaledDerived x -
          covariantDerivativeAlong I connection second firstScaledDerived x -
          covariantDerivativeAlong I connection (VectorField.mlieBracket I first second)
            (f • field) x = _
  rw [houterSecond, houterFirst, hsecondExpanded, hfirstExpanded, hbracket]
  dsimp only [firstF, secondF, firstDerived, secondDerived] at hscalar ⊢
  simp only [scalarDirectionalDerivative] at hscalar ⊢
  rw [← sub_eq_zero]
  simp only [smul_sub, sub_smul] at hscalar ⊢
  abel_nf at hscalar ⊢
  exact hscalar

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (TangentSpace I : M → Type _)] in
set_option maxHeartbeats 800000 in
/-- The connection curvature action is additive in the differentiated-field slot. -/
theorem connectionCurvatureAction_tensorial_field_add
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    {first second field field' : (y : M) → TangentSpace I y}
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x)
    (hfield : CMDiffAt 2 (T% field) x)
    (hfield' : CMDiffAt 2 (T% field') x) :
    connectionCurvatureAction I connection first second (field + field') x =
      connectionCurvatureAction I connection first second field x +
        connectionCurvatureAction I connection first second field' x := by
  letI : IsManifold I ((2 : ℕ∞ω) + 1) M := by
    norm_num
    infer_instance
  letI : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  letI : IsManifold I.tangent 2 (TangentBundle I M) := inferInstance
  let firstDerived := covariantDerivativeAlong I connection first field
  let firstDerived' := covariantDerivativeAlong I connection first field'
  let secondDerived := covariantDerivativeAlong I connection second field
  let secondDerived' := covariantDerivativeAlong I connection second field'
  let firstSumDerived := covariantDerivativeAlong I connection first (field + field')
  let secondSumDerived := covariantDerivativeAlong I connection second (field + field')
  let expandedFirst := firstDerived + firstDerived'
  let expandedSecond := secondDerived + secondDerived'
  have hfirst_one : MDiffAt (T% first) x :=
    hfirst.mdifferentiableAt (by norm_num)
  have hsecond_one : MDiffAt (T% second) x :=
    hsecond.mdifferentiableAt (by norm_num)
  have hfield_one : MDiffAt (T% field) x :=
    hfield.mdifferentiableAt (by norm_num)
  have hfield'_one : MDiffAt (T% field') x :=
    hfield'.mdifferentiableAt (by norm_num)
  have hsumField : CMDiffAt 2 (T% (field + field')) x := hfield.add_section hfield'
  have hfirstDerived : MDiffAt (T% firstDerived) x :=
    regular first field hfirst_one hfield
  have hfirstDerived' : MDiffAt (T% firstDerived') x :=
    regular first field' hfirst_one hfield'
  have hsecondDerived : MDiffAt (T% secondDerived) x :=
    regular second field hsecond_one hfield
  have hsecondDerived' : MDiffAt (T% secondDerived') x :=
    regular second field' hsecond_one hfield'
  have hfirstSumDerived : MDiffAt (T% firstSumDerived) x :=
    regular first (field + field') hfirst_one hsumField
  have hsecondSumDerived : MDiffAt (T% secondSumDerived) x :=
    regular second (field + field') hsecond_one hsumField
  have hexpandedFirst : MDiffAt (T% expandedFirst) x :=
    mdifferentiableAt_add_section hfirstDerived hfirstDerived'
  have hexpandedSecond : MDiffAt (T% expandedSecond) x :=
    mdifferentiableAt_add_section hsecondDerived hsecondDerived'
  have hfield_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 (T% field) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hfield
  have hfield'_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 (T% field') y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hfield'
  have hfirstExpansion : firstSumDerived =ᶠ[nhds x] expandedFirst := by
    filter_upwards [hfield_eventually, hfield'_eventually] with y hzy hz'y
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.add
        (hzy.mdifferentiableAt (by norm_num))
        (hz'y.mdifferentiableAt (by norm_num))) (first y)
  have hsecondExpansion : secondSumDerived =ᶠ[nhds x] expandedSecond := by
    filter_upwards [hfield_eventually, hfield'_eventually] with y hzy hz'y
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.add
        (hzy.mdifferentiableAt (by norm_num))
        (hz'y.mdifferentiableAt (by norm_num))) (second y)
  have houterFirst :
      covariantDerivativeAlong I connection second firstSumDerived x =
        covariantDerivativeAlong I connection second expandedFirst x := by
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.congr_of_eventuallyEq
        hfirstSumDerived hexpandedFirst Filter.univ_mem hfirstExpansion) (second x)
  have houterSecond :
      covariantDerivativeAlong I connection first secondSumDerived x =
        covariantDerivativeAlong I connection first expandedSecond x := by
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.congr_of_eventuallyEq
        hsecondSumDerived hexpandedSecond Filter.univ_mem hsecondExpansion) (first x)
  have hfirstExpanded :
      covariantDerivativeAlong I connection second expandedFirst x =
        covariantDerivativeAlong I connection second firstDerived x +
          covariantDerivativeAlong I connection second firstDerived' x := by
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.add hfirstDerived hfirstDerived') (second x)
  have hsecondExpanded :
      covariantDerivativeAlong I connection first expandedSecond x =
        covariantDerivativeAlong I connection first secondDerived x +
          covariantDerivativeAlong I connection first secondDerived' x := by
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.add hsecondDerived hsecondDerived') (first x)
  have hbracket :
      covariantDerivativeAlong I connection (VectorField.mlieBracket I first second)
          (field + field') x =
        covariantDerivativeAlong I connection (VectorField.mlieBracket I first second) field x +
          covariantDerivativeAlong I connection (VectorField.mlieBracket I first second) field' x := by
    exact DFunLike.congr_fun
      (connection.isCovariantDerivativeOn.add hfield_one hfield'_one)
      (VectorField.mlieBracket I first second x)
  rw [connectionCurvatureAction, connectionCurvatureAction, connectionCurvatureAction]
  simp only [Pi.sub_apply]
  change
    covariantDerivativeAlong I connection first secondSumDerived x -
          covariantDerivativeAlong I connection second firstSumDerived x -
          covariantDerivativeAlong I connection (VectorField.mlieBracket I first second)
            (field + field') x = _
  rw [houterSecond, houterFirst, hsecondExpanded, hfirstExpanded, hbracket]
  dsimp only [firstDerived, firstDerived', secondDerived, secondDerived']
  abel

omit [RiemannianBundle (TangentSpace I : M → Type _)] [FiniteDimensional ℝ E] in
/-- Curvature is a `C²`-tensorial operation in the differentiated-field slot. -/
theorem connectionCurvatureAction_tensorial_field
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (first second : (y : M) → TangentSpace I y)
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x) :
    C2TensorialAt I
      (fun field ↦ connectionCurvatureAction I connection first second field x) x where
  smul hf hfield :=
    connectionCurvatureAction_tensorial_field_smul I connection x regular
      hf hfirst hsecond hfield
  add hfield hfield' :=
    connectionCurvatureAction_tensorial_field_add I connection x regular
      hfirst hsecond hfield hfield'

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- For `C²` fields, the curvature action at `x` depends only on the value of `Z(x)`. -/
theorem connectionCurvatureAction_field_pointwise
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    {first second field field' : (y : M) → TangentSpace I y}
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x)
    (hfield : CMDiffAt 2 (T% field) x)
    (hfield' : CMDiffAt 2 (T% field') x)
    (heq : field x = field' x) :
    connectionCurvatureAction I connection first second field x =
      connectionCurvatureAction I connection first second field' x :=
  C2TensorialAt.pointwise I
    (connectionCurvatureAction_tensorial_field I connection x regular first second
      hfirst hsecond) hfield hfield' heq

omit [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The connection curvature action is tensorial in its first direction argument. -/
theorem connectionCurvatureAction_tensorial_first
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (second field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x) :
    TensorialAt I E
      (fun first ↦ connectionCurvatureAction I connection first second field x) x where
  smul {f first} hf hfirst := by
    let derived := covariantDerivativeAlong I connection first field
    have hderived : MDiffAt (T% derived) x := regular first field hfirst hfield
    have hscaled :
        covariantDerivativeAlong I connection (f • first) field = f • derived := by
      funext y
      simp [covariantDerivativeAlong, derived]
    have houter :
        covariantDerivativeAlong I connection second (f • derived) x =
          f x • covariantDerivativeAlong I connection second derived x +
            d% f x (second x) • derived x := by
      exact DFunLike.congr_fun
        (connection.isCovariantDerivativeOn.leibniz hderived hf) (second x)
    have hfirstTerm :
        covariantDerivativeAlong I connection (f • first)
            (covariantDerivativeAlong I connection second field) x =
          f x • covariantDerivativeAlong I connection first
            (covariantDerivativeAlong I connection second field) x := by
      simp [covariantDerivativeAlong]
    have hbracket :
        covariantDerivativeAlong I connection
            (VectorField.mlieBracket I (f • first) second) field x =
          -(d% f x (second x)) • derived x +
            f x • covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first second) field x := by
      rw [covariantDerivativeAlong, VectorField.mlieBracket_smul_left hf hfirst]
      simp [derived, covariantDerivativeAlong]
    rw [connectionCurvatureAction, connectionCurvatureAction, hscaled]
    simp only [Pi.sub_apply]
    rw [hfirstTerm, houter, hbracket]
    simp only [derived]
    module
  add {first first'} hfirst hfirst' := by
    let derived := covariantDerivativeAlong I connection first field
    let derived' := covariantDerivativeAlong I connection first' field
    have hderived : MDiffAt (T% derived) x := regular first field hfirst hfield
    have hderived' : MDiffAt (T% derived') x := regular first' field hfirst' hfield
    have hadd :
        covariantDerivativeAlong I connection (first + first') field = derived + derived' := by
      funext y
      simp [covariantDerivativeAlong, derived, derived']
    have houter :
        covariantDerivativeAlong I connection second (derived + derived') x =
          covariantDerivativeAlong I connection second derived x +
            covariantDerivativeAlong I connection second derived' x := by
      exact DFunLike.congr_fun
        (connection.isCovariantDerivativeOn.add hderived hderived') (second x)
    have hfirstTerm :
        covariantDerivativeAlong I connection (first + first')
            (covariantDerivativeAlong I connection second field) x =
          covariantDerivativeAlong I connection first
              (covariantDerivativeAlong I connection second field) x +
            covariantDerivativeAlong I connection first'
              (covariantDerivativeAlong I connection second field) x := by
      simp [covariantDerivativeAlong]
    have hbracket :
        covariantDerivativeAlong I connection
            (VectorField.mlieBracket I (first + first') second) field x =
          covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first second) field x +
            covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first' second) field x := by
      rw [covariantDerivativeAlong, VectorField.mlieBracket_add_left hfirst hfirst']
      simp [covariantDerivativeAlong]
    rw [connectionCurvatureAction, connectionCurvatureAction,
      connectionCurvatureAction, hadd]
    simp only [Pi.sub_apply]
    rw [hfirstTerm, houter, hbracket]
    simp only [derived, derived']
    module

omit [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The connection curvature action is tensorial in its second direction argument. -/
theorem connectionCurvatureAction_tensorial_second
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (first field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x) :
    TensorialAt I E
      (fun second ↦ connectionCurvatureAction I connection first second field x) x where
  smul {f second} hf hsecond := by
    let derived := covariantDerivativeAlong I connection second field
    have hderived : MDiffAt (T% derived) x := regular second field hsecond hfield
    have hscaled :
        covariantDerivativeAlong I connection (f • second) field = f • derived := by
      funext y
      simp [covariantDerivativeAlong, derived]
    have houter :
        covariantDerivativeAlong I connection first (f • derived) x =
          f x • covariantDerivativeAlong I connection first derived x +
            d% f x (first x) • derived x := by
      exact DFunLike.congr_fun
        (connection.isCovariantDerivativeOn.leibniz hderived hf) (first x)
    have hsecondTerm :
        covariantDerivativeAlong I connection (f • second)
            (covariantDerivativeAlong I connection first field) x =
          f x • covariantDerivativeAlong I connection second
            (covariantDerivativeAlong I connection first field) x := by
      simp [covariantDerivativeAlong]
    have hbracket :
        covariantDerivativeAlong I connection
            (VectorField.mlieBracket I first (f • second)) field x =
          d% f x (first x) • derived x +
            f x • covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first second) field x := by
      rw [covariantDerivativeAlong, VectorField.mlieBracket_smul_right hf hsecond]
      simp [derived, covariantDerivativeAlong]
    rw [connectionCurvatureAction, connectionCurvatureAction, hscaled]
    simp only [Pi.sub_apply]
    rw [houter, hsecondTerm, hbracket]
    simp only [derived]
    module
  add {second second'} hsecond hsecond' := by
    let derived := covariantDerivativeAlong I connection second field
    let derived' := covariantDerivativeAlong I connection second' field
    have hderived : MDiffAt (T% derived) x := regular second field hsecond hfield
    have hderived' : MDiffAt (T% derived') x := regular second' field hsecond' hfield
    have hadd :
        covariantDerivativeAlong I connection (second + second') field = derived + derived' := by
      funext y
      simp [covariantDerivativeAlong, derived, derived']
    have houter :
        covariantDerivativeAlong I connection first (derived + derived') x =
          covariantDerivativeAlong I connection first derived x +
            covariantDerivativeAlong I connection first derived' x := by
      exact DFunLike.congr_fun
        (connection.isCovariantDerivativeOn.add hderived hderived') (first x)
    have hsecondTerm :
        covariantDerivativeAlong I connection (second + second')
            (covariantDerivativeAlong I connection first field) x =
          covariantDerivativeAlong I connection second
              (covariantDerivativeAlong I connection first field) x +
            covariantDerivativeAlong I connection second'
              (covariantDerivativeAlong I connection first field) x := by
      simp [covariantDerivativeAlong]
    have hbracket :
        covariantDerivativeAlong I connection
            (VectorField.mlieBracket I first (second + second')) field x =
          covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first second) field x +
            covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first second') field x := by
      rw [covariantDerivativeAlong, VectorField.mlieBracket_add_right hsecond hsecond']
      simp [covariantDerivativeAlong]
    rw [connectionCurvatureAction, connectionCurvatureAction,
      connectionCurvatureAction, hadd]
    simp only [Pi.sub_apply]
    rw [houter, hsecondTerm, hbracket]
    simp only [derived, derived']
    module

/-- The curvature action as a continuous bilinear map in the two tangent directions at `x`.

Evaluating this map on `X(x)` and `Y(x)` recovers the connection commutator for any differentiable
extensions `X` and `Y`; see `connectionCurvatureDirectionsAt_apply`. -/
def connectionCurvatureDirectionsAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  TensorialAt.mkHom₂
    (fun first second ↦ connectionCurvatureAction I connection first second field x) x
    (fun second _ ↦
      connectionCurvatureAction_tensorial_first I connection x regular second field hfield)
    (fun first _ ↦
      connectionCurvatureAction_tensorial_second I connection x regular first field hfield)

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- Applying the pointwise direction map recovers the field-level connection commutator. -/
theorem connectionCurvatureDirectionsAt_apply
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x)
    {first second : (y : M) → TangentSpace I y}
    (hfirst : MDiffAt (T% first) x) (hsecond : MDiffAt (T% second) x) :
    connectionCurvatureDirectionsAt I connection x regular field hfield
        (first x) (second x) =
      connectionCurvatureAction I connection first second field x := by
  apply TensorialAt.mkHom₂_apply
  exacts [hfirst, hsecond]

/-- Auxiliary field-first currying of the pointwise curvature tensor.

The outer argument is `Z(x)` and the two inner arguments are `X(x)` and `Y(x)`. The conventional
`R(X,Y)Z` order is exposed by `connectionCurvatureTensorAt` below. -/
def connectionCurvatureTensorFieldFirstAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x) :
    TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  LinearMap.toContinuousLinearMap {
    toFun fieldValue := connectionCurvatureDirectionsAt I connection x regular
      (FiberBundle.extend E fieldValue)
      (FiberBundle.contMDiffAt_extend (k := 2) I E fieldValue)
    map_add' fieldValue fieldValue' := by
      ext firstValue secondValue
      simp only [add_apply]
      rw [connectionCurvatureDirectionsAt, TensorialAt.mkHom₂_apply_eq_extend]
      rw [connectionCurvatureDirectionsAt, TensorialAt.mkHom₂_apply_eq_extend]
      rw [connectionCurvatureDirectionsAt, TensorialAt.mkHom₂_apply_eq_extend]
      let first := FiberBundle.extend E firstValue
      let second := FiberBundle.extend E secondValue
      let field := FiberBundle.extend E fieldValue
      let field' := FiberBundle.extend E fieldValue'
      have hfirst : CMDiffAt 2 (T% first) x :=
        FiberBundle.contMDiffAt_extend (k := 2) I E firstValue
      have hsecond : CMDiffAt 2 (T% second) x :=
        FiberBundle.contMDiffAt_extend (k := 2) I E secondValue
      have hfield : CMDiffAt 2 (T% field) x :=
        FiberBundle.contMDiffAt_extend (k := 2) I E fieldValue
      have hfield' : CMDiffAt 2 (T% field') x :=
        FiberBundle.contMDiffAt_extend (k := 2) I E fieldValue'
      have hsum : CMDiffAt 2 (T% (field + field')) x := hfield.add_section hfield'
      have hpoint := connectionCurvatureAction_field_pointwise I connection x regular
        hfirst hsecond
        (FiberBundle.contMDiffAt_extend (k := 2) I E (fieldValue + fieldValue')) hsum
        (show FiberBundle.extend E (fieldValue + fieldValue') x = (field + field') x by
          simp [field, field'])
      rw [hpoint]
      rw [connectionCurvatureAction_tensorial_field_add I connection x regular
        hfirst hsecond hfield hfield']
    map_smul' scalar fieldValue := by
      ext firstValue secondValue
      simp only [smul_apply]
      rw [connectionCurvatureDirectionsAt, TensorialAt.mkHom₂_apply_eq_extend]
      rw [connectionCurvatureDirectionsAt, TensorialAt.mkHom₂_apply_eq_extend]
      let first := FiberBundle.extend E firstValue
      let second := FiberBundle.extend E secondValue
      let field := FiberBundle.extend E fieldValue
      have hfirst : CMDiffAt 2 (T% first) x :=
        FiberBundle.contMDiffAt_extend (k := 2) I E firstValue
      have hsecond : CMDiffAt 2 (T% second) x :=
        FiberBundle.contMDiffAt_extend (k := 2) I E secondValue
      have hfield : CMDiffAt 2 (T% field) x :=
        FiberBundle.contMDiffAt_extend (k := 2) I E fieldValue
      have hscaled : CMDiffAt 2 (T% ((fun _ : M ↦ scalar) • field)) x :=
        contMDiffAt_const.smul_section hfield
      have hpoint := connectionCurvatureAction_field_pointwise I connection x regular
        hfirst hsecond
        (FiberBundle.contMDiffAt_extend (k := 2) I E (scalar • fieldValue)) hscaled
        (show FiberBundle.extend E (scalar • fieldValue) x =
            ((fun _ : M ↦ scalar) • field) x by simp [field])
      rw [hpoint]
      rw [connectionCurvatureAction_tensorial_field_smul I connection x regular
        contMDiffAt_const hfirst hsecond hfield]
      simp [first, second, field]
  }

/-- The connection curvature as a continuous trilinear map in conventional `R(X,Y)Z` order. -/
def connectionCurvatureTensorAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x) :
    TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  ((ContinuousLinearMap.flipₗᵢ ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x)).toContinuousLinearEquiv.toContinuousLinearMap).comp
    (connectionCurvatureTensorFieldFirstAt I connection x regular).flip

/-- Evaluating the trilinear tensor on tangent vectors uses their canonical `C²` extensions. -/
theorem connectionCurvatureTensorAt_apply_extend
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (first second field : TangentSpace I x) :
    connectionCurvatureTensorAt I connection x regular first second field =
      connectionCurvatureAction I connection
        (FiberBundle.extend E first) (FiberBundle.extend E second)
        (FiberBundle.extend E field) x := by
  simp only [connectionCurvatureTensorAt, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_flipₗᵢ,
    ContinuousLinearMap.flip_apply]
  change connectionCurvatureDirectionsAt I connection x regular
      (FiberBundle.extend E field)
      (FiberBundle.contMDiffAt_extend (k := 2) I E field) first second = _
  rw [connectionCurvatureDirectionsAt, TensorialAt.mkHom₂_apply_eq_extend]

/-- Evaluating the trilinear tensor recovers the field-level curvature commutator. -/
theorem connectionCurvatureTensorAt_apply
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    {first second field : (y : M) → TangentSpace I y}
    (hfirst : MDiffAt (T% first) x)
    (hsecond : MDiffAt (T% second) x)
    (hfield : CMDiffAt 2 (T% field) x) :
    connectionCurvatureTensorAt I connection x regular
        (first x) (second x) (field x) =
      connectionCurvatureAction I connection first second field x := by
  rw [connectionCurvatureTensorAt_apply_extend]
  let firstExtension := FiberBundle.extend E (first x)
  let secondExtension := FiberBundle.extend E (second x)
  let fieldExtension := FiberBundle.extend E (field x)
  have hfirstExtension : CMDiffAt 2 (T% firstExtension) x :=
    FiberBundle.contMDiffAt_extend (k := 2) I E (first x)
  have hsecondExtension : CMDiffAt 2 (T% secondExtension) x :=
    FiberBundle.contMDiffAt_extend (k := 2) I E (second x)
  have hfieldExtension : CMDiffAt 2 (T% fieldExtension) x :=
    FiberBundle.contMDiffAt_extend (k := 2) I E (field x)
  have hfieldPointwise := connectionCurvatureAction_field_pointwise I connection x regular
    hfirstExtension hsecondExtension hfieldExtension hfield
    (show fieldExtension x = field x by simp [fieldExtension])
  rw [hfieldPointwise]
  calc
    connectionCurvatureAction I connection firstExtension secondExtension field x =
        connectionCurvatureDirectionsAt I connection x regular field hfield
          (first x) (second x) := by
      symm
      simpa [firstExtension, secondExtension] using
        (connectionCurvatureDirectionsAt_apply I connection x regular field hfield
          (hfirst := hfirstExtension.mdifferentiableAt (by norm_num))
          (hsecond := hsecondExtension.mdifferentiableAt (by norm_num)))
    _ = connectionCurvatureAction I connection first second field x :=
      connectionCurvatureDirectionsAt_apply I connection x regular field hfield hfirst hsecond

/-- The pointwise curvature tensor is alternating in its first two arguments. -/
theorem connectionCurvatureTensorAt_swap
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (first second field : TangentSpace I x) :
    connectionCurvatureTensorAt I connection x regular first second field =
      -connectionCurvatureTensorAt I connection x regular second first field := by
  rw [connectionCurvatureTensorAt_apply_extend, connectionCurvatureTensorAt_apply_extend]
  exact congrFun
    (connectionCurvatureAction_swap I connection
      (FiberBundle.extend E first) (FiberBundle.extend E second)
      (FiberBundle.extend E field)) x

/-- The pointwise curvature tensor vanishes on a repeated direction. -/
@[simp]
theorem connectionCurvatureTensorAt_self
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (direction field : TangentSpace I x) :
    connectionCurvatureTensorAt I connection x regular direction direction field = 0 := by
  rw [connectionCurvatureTensorAt_apply_extend]
  exact congrFun
    (connectionCurvatureAction_self I connection
      (FiberBundle.extend E direction) (FiberBundle.extend E field)) x

/-! ## Ricci contraction -/

/-- Express a pointwise curvature tensor in the tangent trivialization centered at `x₀`.

The definition is total even outside the trivialization base set. The regularity predicate below
uses it only as a germ at `x₀`, where the forward and inverse coordinate maps are equivalences. -/
def curvatureTensorInTangentCoordinatesAt
    (x₀ x : M)
    (curvature : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :
    E →L[ℝ] E [×2]→L[ℝ] E :=
  let coordinates :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt ℝ x
  let fromCoordinates :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x
  let curried : E →L[ℝ] E →L[ℝ] E →L[ℝ] E := LinearMap.toContinuousLinearMap {
    toFun := fun first ↦ LinearMap.toContinuousLinearMap {
      toFun := fun second ↦ LinearMap.toContinuousLinearMap {
        toFun := fun field ↦ coordinates
          (curvature (fromCoordinates first) (fromCoordinates second)
            (fromCoordinates field))
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
  curriedTrilinearToLeftCurriedMultilinear curried

set_option synthInstance.maxHeartbeats 1000000 in
/-- A pointwise curvature tensor field is `C^k` when its components in every centered tangent
trivialization are `C^k` at the center.

This is the strictly upstream tensor-valued regularity statement: it mentions only the trilinear
curvature field, not any trace. The bounded model-space contraction is smooth, but the current
Mathlib manifold API carries two non-definitionally-equal topology instances for these bundled
operator spaces; `HasRicciContractionRegularity` records the remaining global bridge explicitly. -/
def HasCurvatureTensorFieldRegularity
    (regularity : ℕ∞ω)
    (curvature : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) : Prop :=
  ∀ x₀, ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E [×2]→L[ℝ] E) regularity
    (fun x ↦ curvatureTensorInTangentCoordinatesAt I x₀ x (curvature x)) x₀

/-- The contraction-level regularity contract needed to promote curvature-derived Ricci forms to
a global `C^k` tensor. The contracted coordinate field is fixed canonically by `curvature`; this
predicate supplies no independent Ricci data. It is separated from full tensor-field regularity
because Mathlib currently exposes non-definitionally-equal topology instances on spaces of
bundled continuous maps. -/
def HasRicciContractionRegularity
    (regularity : ℕ∞ω)
    (curvature : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) : Prop :=
  ∀ x₀, ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) regularity
    (fun x ↦ ricciFormOfLeftCurriedMultilinearCurvatureTensor
      (curvatureTensorInTangentCoordinatesAt I x₀ x (curvature x))) x₀

set_option synthInstance.maxHeartbeats 1000000 in
/-- The global regularity condition specialized to the connection-derived curvature tensor. -/
def HasConnectionCurvatureTensorRegularity
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x) : Prop :=
  HasCurvatureTensorFieldRegularity I regularity
    (fun x ↦ connectionCurvatureTensorAt I connection x (regular x))

/-- Contraction-level regularity specialized to the curvature tensor constructed from a bundled
connection. -/
def HasConnectionRicciContractionRegularity
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x) : Prop :=
  HasRicciContractionRegularity I regularity
    (fun x ↦ connectionCurvatureTensorAt I connection x (regular x))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- A `C^k` curvature tensor has a `C^k` Ricci bilinear-form field.

The proof contracts in tangent coordinates with a fixed continuous linear map, then uses trace
invariance under conjugation to identify that coordinate contraction with the intrinsic one. -/
def ricciFormOfRegularCurvatureTensor
    (regularity : ℕ∞ω)
    (curvature : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (hcontraction : HasRicciContractionRegularity I regularity curvature) :
    SmoothCovariantTwoTensor (M := M) I regularity where
  toFun x :=
    letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
    ricciFormOfCurvatureTensor (curvature x)
  contMDiff_toFun := by
    intro x₀
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hcontracted :
        ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) regularity
          (fun x ↦ ricciFormOfLeftCurriedMultilinearCurvatureTensor
            (curvatureTensorInTangentCoordinatesAt I x₀ x (curvature x))) x₀ :=
      hcontraction x₀
    apply hcontracted.congr_of_eventuallyEq
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
    letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
    let tangentCoordinates :=
      (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt
        ℝ x hx
    have hcurvatureCoordinates :
        curvatureTensorInTangentCoordinatesAt I x₀ x (curvature x) =
          curriedTrilinearToLeftCurriedMultilinear
            (curvatureTensorInCoordinates tangentCoordinates (curvature x)) := by
      ext first v
      simp [curvatureTensorInTangentCoordinatesAt, curvatureTensorInCoordinates,
        tangentCoordinates,
        Trivialization.coe_linearMapAt_of_mem _ hx,
        Trivialization.symmL_apply (e :=
          trivializationAt E (TangentSpace I : M → Type _) x₀) hx]
    rw [hcurvatureCoordinates]
    change ContinuousLinearMap.inCoordinates
        E (TangentSpace I : M → Type _)
        (E →L[ℝ] ℝ) (fun y : M => TangentSpace I y →L[ℝ] ℝ)
        x₀ x x₀ x (ricciFormOfCurvatureTensor (curvature x)) =
      ricciFormOfLeftCurriedMultilinearCurvatureTensor
        (curriedTrilinearToLeftCurriedMultilinear
          (curvatureTensorInCoordinates tangentCoordinates (curvature x)))
    rw [ricciFormOfLeftCurriedMultilinearCurvatureTensor_curried]
    rw [ricciForm_curvatureTensorInCoordinates]
    rw [ContinuousLinearMap.inCoordinates_eq hx hxstar]
    ext first second
    simp [covariantTwoTensorInCoordinates, tangentCoordinates,
      hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      Trivialization.symm_continuousLinearEquivAt_eq _ hx]

/-- Raise the second index of the curvature-derived Ricci form to obtain a global `C^k`
endomorphism field. -/
noncomputable def ricciActionOfRegularCurvatureTensor
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (curvature : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (hcontraction : HasRicciContractionRegularity I regularity curvature) :
    SmoothVectorOneForm (M := M) I regularity :=
  raiseCovariantTwoTensor I regularity
    (ricciFormOfRegularCurvatureTensor I regularity curvature hcontraction)

omit [IsManifold I 2 M] in
/-- The global raised Ricci field agrees pointwise with the established Riesz contraction. -/
@[simp]
theorem ricciActionOfRegularCurvatureTensor_apply
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (curvature : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (hcontraction : HasRicciContractionRegularity I regularity curvature)
    (x : M) (second : TangentSpace I x) :
    ricciActionOfRegularCurvatureTensor I regularity curvature hcontraction x second =
      (letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
       ricciActionOfCurvatureTensor (curvature x) second) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  apply ext_inner_right ℝ
  intro field
  change inner ℝ
      (raiseCovariantTwoTensor I regularity
        (ricciFormOfRegularCurvatureTensor I regularity curvature hcontraction) x second)
      field = _
  rw [raiseCovariantTwoTensor_inner, ricciActionOfCurvatureTensor_inner]
  rfl

/-- Scalar curvature is the second trace: the fiberwise trace of the raised Ricci endomorphism. -/
noncomputable def scalarCurvatureOfRegularCurvatureTensor
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (curvature : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (hcontraction : HasRicciContractionRegularity I regularity curvature) :
    SmoothScalarField (M := M) I regularity :=
  traceVectorOneForm I regularity
    (ricciActionOfRegularCurvatureTensor I regularity curvature hcontraction)

omit [IsManifold I 2 M] in
@[simp]
theorem scalarCurvatureOfRegularCurvatureTensor_apply
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (curvature : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (hcontraction : HasRicciContractionRegularity I regularity curvature)
    (x : M) :
    scalarCurvatureOfRegularCurvatureTensor I regularity curvature hcontraction x =
      (letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
       tangentTrace I x (ricciActionOfCurvatureTensor (curvature x))) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  change tangentTrace I x
      (ricciActionOfRegularCurvatureTensor I regularity curvature hcontraction x) = _
  congr 1
  ext second
  exact ricciActionOfRegularCurvatureTensor_apply I regularity curvature hcontraction x second

/-- Gram determinant of two tangent vectors, the normalization denominator for sectional
curvature. It is nonzero precisely on nondegenerate two-planes. -/
def sectionalCurvatureDenominatorAt (x : M)
    (first second : TangentSpace I x) : ℝ :=
  inner ℝ first first * inner ℝ second second - inner ℝ first second ^ 2

/-- Sectional curvature obtained by contracting `R(X,Y)Y` against `X` and normalizing by the
Gram determinant. Lean's division is total; the geometric interpretation is restricted to pairs
with nonzero denominator (in particular, linearly independent pairs). -/
def sectionalCurvatureOfCurvatureTensorAt (x : M)
    (curvature : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (first second : TangentSpace I x) : ℝ :=
  inner ℝ (curvature first second second) first /
    sectionalCurvatureDenominatorAt I x first second

/-- For fixed `Y,Z ∈ TₓM`, the endomorphism `X ↦ R(X,Y)Z` whose trace defines Ricci. -/
def connectionCurvatureFirstSlotEndomorphismAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (second field : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  curvatureFirstSlotEndomorphism
    (connectionCurvatureTensorAt I connection x regular) second field

/-- The pointwise Ricci bilinear form
`Ric(Y,Z) = tr (X ↦ R(X,Y)Z)` constructed from the connection curvature tensor. -/
def connectionRicciFormAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  ricciFormOfCurvatureTensor (connectionCurvatureTensorAt I connection x regular)

/-- The metric-raised pointwise Ricci endomorphism constructed from the connection curvature. -/
def connectionRicciActionAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  ricciActionOfCurvatureTensor (connectionCurvatureTensorAt I connection x regular)

/-- Pointwise scalar curvature obtained by tracing the connection-derived Ricci endomorphism. -/
def connectionScalarCurvatureAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x) : ℝ :=
  tangentTrace I x (connectionRicciActionAt I connection x regular)

/-- Pointwise sectional curvature of the two-plane represented by `first, second`, derived from
the connection curvature tensor with the selected sign convention. -/
def connectionSectionalCurvatureAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (first second : TangentSpace I x) : ℝ :=
  sectionalCurvatureOfCurvatureTensorAt I x
    (connectionCurvatureTensorAt I connection x regular) first second

/-- The connection Ricci form is literally the trace of its first curvature slot. -/
@[simp]
theorem connectionRicciFormAt_apply
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (second field : TangentSpace I x) :
    connectionRicciFormAt I connection x regular second field =
      tangentTrace I x
        (connectionCurvatureFirstSlotEndomorphismAt I connection x regular second field) := by
  rfl

/-- Raising the Ricci form is characterized by the Riemannian inner product. -/
@[simp]
theorem connectionRicciActionAt_inner
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (second field : TangentSpace I x) :
    inner ℝ (connectionRicciActionAt I connection x regular second) field =
      connectionRicciFormAt I connection x regular second field := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  exact ricciActionOfCurvatureTensor_inner
    (connectionCurvatureTensorAt I connection x regular) second field

/-- Every orthonormal frame computes the same intrinsic Ricci contraction. -/
theorem connectionRicciFormAt_eq_sum_inner
    [IsManifold I 3 M]
    {ι : Type*} [Fintype ι]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (basis : OrthonormalBasis ι ℝ (TangentSpace I x))
    (second field : TangentSpace I x) :
    connectionRicciFormAt I connection x regular second field =
      ∑ i, inner ℝ (basis i)
        (connectionCurvatureTensorAt I connection x regular (basis i) second field) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  exact ricciFormOfCurvatureTensor_eq_sum_inner
    (connectionCurvatureTensorAt I connection x regular) basis second field

/-- The extra global hypothesis needed to turn pointwise Ricci contractions into a `C^k` field. -/
def HasConnectionRicciRegularity
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) regularity
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) x
      (connectionRicciActionAt I connection x (regular x)))

/-- Package the connection-derived Ricci endomorphisms as a smooth tangent-valued one-form.

The explicit `smooth` argument is the current global regularity boundary: pointwise tensoriality
alone does not prove smooth dependence on the base point. -/
def connectionRicciVectorOneForm
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (smooth : HasConnectionRicciRegularity I regularity connection regular) :
    SmoothVectorOneForm (M := M) I regularity where
  toFun x := connectionRicciActionAt I connection x (regular x)
  contMDiff_toFun := by
    simpa [HasConnectionRicciRegularity] using smooth

/-- The connection-derived Ricci form as a global `C^k` covariant two-tensor, under the canonical
contraction regularity contract. -/
noncomputable def connectionRicciFormTensor
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular) :
    SmoothCovariantTwoTensor (M := M) I regularity :=
  ricciFormOfRegularCurvatureTensor I regularity
    (fun x ↦ connectionCurvatureTensorAt I connection x (regular x)) hcontraction

/-- Global smooth Ricci endomorphism derived from sufficiently regular connection curvature. -/
noncomputable def connectionRicciVectorOneFormOfCurvatureRegularity
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular) :
    SmoothVectorOneForm (M := M) I regularity :=
  ricciActionOfRegularCurvatureTensor I regularity
    (fun x ↦ connectionCurvatureTensorAt I connection x (regular x)) hcontraction

@[simp]
theorem connectionRicciVectorOneFormOfCurvatureRegularity_apply
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular)
    (x : M) (vector : TangentSpace I x) :
    connectionRicciVectorOneFormOfCurvatureRegularity I regularity connection regular
        hcontraction x vector =
      connectionRicciActionAt I connection x (regular x) vector := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  simp [connectionRicciVectorOneFormOfCurvatureRegularity, connectionRicciActionAt,
    ricciActionOfRegularCurvatureTensor_apply]

/-- The contraction regularity contract discharges the older downstream smooth-Ricci interface. -/
theorem hasConnectionRicciRegularity_of_contraction
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular) :
    HasConnectionRicciRegularity I regularity connection regular := by
  unfold HasConnectionRicciRegularity
  apply (connectionRicciVectorOneFormOfCurvatureRegularity I regularity connection regular
    hcontraction).contMDiff.congr
  intro x
  congr 1
  ext vector
  symm
  exact connectionRicciVectorOneFormOfCurvatureRegularity_apply I regularity connection
    regular hcontraction x vector

/-- Global `C^k` scalar curvature derived by tracing the smooth connection Ricci field. -/
noncomputable def connectionScalarCurvatureField
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular) :
    SmoothScalarField (M := M) I regularity :=
  scalarCurvatureOfRegularCurvatureTensor I regularity
    (fun x ↦ connectionCurvatureTensorAt I connection x (regular x)) hcontraction

@[simp]
theorem connectionScalarCurvatureField_apply
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular)
    (x : M) :
    connectionScalarCurvatureField I regularity connection regular hcontraction x =
      connectionScalarCurvatureAt I connection x (regular x) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  simp [connectionScalarCurvatureField, connectionScalarCurvatureAt,
    connectionRicciActionAt, scalarCurvatureOfRegularCurvatureTensor_apply]

/-- Populate the existing curvature interface with connection-derived Riemann and Ricci fields.

Scalar and sectional curvature are still supplied explicitly; this constructor does not claim
their derivation from the trilinear tensor. -/
def connectionRiemannianCurvatureData
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (scalarCurvature : M → ℝ)
    (sectionalCurvature : ∀ x : M,
      TangentSpace I x → TangentSpace I x → ℝ) :
    RiemannianCurvatureData (I := I) (M := M) where
  riemann x first second field :=
    connectionCurvatureTensorAt I connection x (regular x) first second field
  ricciAction x vector := connectionRicciActionAt I connection x (regular x) vector
  scalarCurvature := scalarCurvature
  sectionalCurvature := sectionalCurvature

/-- Populate the complete downstream curvature interface from sufficiently regular connection
curvature. Ricci and scalar curvature are global smooth contractions; sectional curvature is the
normalized pointwise contraction on pairs of tangent vectors. -/
noncomputable def connectionRiemannianCurvatureDataOfRegularCurvature
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular) :
    RiemannianCurvatureData (I := I) (M := M) where
  riemann x first second field :=
    connectionCurvatureTensorAt I connection x (regular x) first second field
  ricciAction x :=
    connectionRicciVectorOneFormOfCurvatureRegularity I regularity connection regular
      hcontraction x
  scalarCurvature :=
    connectionScalarCurvatureField I regularity connection regular hcontraction
  sectionalCurvature x :=
    connectionSectionalCurvatureAt I connection x (regular x)

@[simp]
theorem connectionRiemannianCurvatureDataOfRegularCurvature_ricciAction
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular)
    (x : M) (vector : TangentSpace I x) :
    (connectionRiemannianCurvatureDataOfRegularCurvature I regularity connection regular
      hcontraction).ricciAction x vector =
      connectionRicciActionAt I connection x (regular x) vector := by
  exact connectionRicciVectorOneFormOfCurvatureRegularity_apply I regularity connection regular
    hcontraction x vector

@[simp]
theorem connectionRiemannianCurvatureDataOfRegularCurvature_scalarCurvature
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular)
    (x : M) :
    (connectionRiemannianCurvatureDataOfRegularCurvature I regularity connection regular
      hcontraction).scalarCurvature x =
      connectionScalarCurvatureAt I connection x (regular x) := by
  exact connectionScalarCurvatureField_apply I regularity connection regular hcontraction x

@[simp]
theorem connectionRiemannianCurvatureDataOfRegularCurvature_sectionalCurvature
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular)
    (x : M) (first second : TangentSpace I x) :
    (connectionRiemannianCurvatureDataOfRegularCurvature I regularity connection regular
      hcontraction).sectionalCurvature x first second =
      connectionSectionalCurvatureAt I connection x (regular x) first second := by
  rfl

@[simp]
theorem connectionRiemannianCurvatureData_riemann
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (scalarCurvature : M → ℝ)
    (sectionalCurvature : ∀ x : M,
      TangentSpace I x → TangentSpace I x → ℝ)
    (x : M) (first second field : TangentSpace I x) :
    (connectionRiemannianCurvatureData I connection regular scalarCurvature
      sectionalCurvature).riemann x first second field =
      connectionCurvatureTensorAt I connection x (regular x) first second field :=
  rfl

@[simp]
theorem connectionRiemannianCurvatureData_ricciAction
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (scalarCurvature : M → ℝ)
    (sectionalCurvature : ∀ x : M,
      TangentSpace I x → TangentSpace I x → ℝ)
    (x : M) (vector : TangentSpace I x) :
    (connectionRiemannianCurvatureData I connection regular scalarCurvature
      sectionalCurvature).ricciAction x vector =
      connectionRicciActionAt I connection x (regular x) vector :=
  rfl

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The pointwise direction map is alternating. -/
theorem connectionCurvatureDirectionsAt_swap
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x)
    (first second : TangentSpace I x) :
    connectionCurvatureDirectionsAt I connection x regular field hfield first second =
      -connectionCurvatureDirectionsAt I connection x regular field hfield second first := by
  rw [connectionCurvatureDirectionsAt, TensorialAt.mkHom₂_apply_eq_extend,
    TensorialAt.mkHom₂_apply_eq_extend]
  exact congrFun
    (connectionCurvatureAction_swap I connection
      (FiberBundle.extend E first) (FiberBundle.extend E second) field) x

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The pointwise direction map vanishes on a repeated direction. -/
@[simp]
theorem connectionCurvatureDirectionsAt_self
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x)
    (direction : TangentSpace I x) :
    connectionCurvatureDirectionsAt I connection x regular field hfield direction direction = 0 := by
  rw [connectionCurvatureDirectionsAt, TensorialAt.mkHom₂_apply_eq_extend]
  exact congrFun
    (connectionCurvatureAction_self I connection (FiberBundle.extend E direction) field) x

end PointwiseDirections

end

/-- Constant sectional curvature on all nondegenerate tangent two-planes. -/
def HasRiemannianConstantSectionalCurvature
    (data : RiemannianCurvatureData (I := I) (M := M)) (curvature : ℝ) : Prop :=
  ∀ x first second,
    LinearIndependent ℝ ![first, second] →
      data.sectionalCurvature x first second = curvature

/-- Pointwise pinching `-b² ≤ K_M ≤ -a²` on every nondegenerate tangent two-plane.

Unlike `HasPinchedNegativeCurvature` in `Geometry.SpaceForms`, this declaration is tied
to Mathlib's actual dependent tangent fibers.  The weaker profile-level version remains
useful for source statements which have not yet selected a concrete manifold model. -/
def HasRiemannianPinchedSectionalCurvature
    (data : RiemannianCurvatureData (I := I) (M := M)) (a b : ℝ) : Prop :=
  0 < a ∧ a ≤ b ∧
    ∀ x first second,
      LinearIndependent ℝ ![first, second] →
        -(b ^ 2) ≤ data.sectionalCurvature x first second ∧
          data.sectionalCurvature x first second ≤ -(a ^ 2)

/-- A pointwise lower bound for the quadratic form of the Ricci endomorphism.

The metric pairing is supplied explicitly because the curvature package records the Ricci
endomorphism while Mathlib owns the tangent fibers and their inner products. -/
def HasRiemannianRicciLowerBound
    (data : RiemannianCurvatureData (I := I) (M := M)) (bound : ℝ) : Prop :=
  ∀ x vector,
    bound * ‖vector‖ ^ 2 ≤ inner ℝ (data.ricciAction x vector) vector

/-- A pointwise upper bound for the quadratic form of the Ricci endomorphism. -/
def HasRiemannianRicciUpperBound
    (data : RiemannianCurvatureData (I := I) (M := M)) (bound : ℝ) : Prop :=
  ∀ x vector,
    inner ℝ (data.ricciAction x vector) vector ≤ bound * ‖vector‖ ^ 2

/-- In intrinsic dimension two, Ricci is Gaussian curvature times the identity. -/
def HasRiemannianSurfaceRicciIdentity
    (data : RiemannianCurvatureData (I := I) (M := M))
    (gaussianCurvature : M → ℝ) : Prop :=
  ∀ x vector,
    data.ricciAction x vector = gaussianCurvature x • vector

/-- Carrier-polymorphic curvature observables retained for source statements made before a
concrete manifold realization is selected. -/
structure CurvatureData (Vector : Type*) where
  riemann : Vector → Vector → Vector → Vector
  ricciAction : Vector → Vector
  scalarCurvature : ℝ
  sectionalCurvature : Vector → Vector → ℝ

/-- The curvature commutator convention used in CCD17 and CCG25. -/
structure CurvatureCommutatorData (Derivative Vector : Type*) where
  firstThenSecond : Vector → Vector → Vector → Derivative
  secondThenFirst : Vector → Vector → Vector → Derivative
  bracketDerivative : Vector → Vector → Vector → Derivative
  curvatureAction : Vector → Vector → Vector → Derivative

def HasCurvatureCommutator
    {Derivative Vector : Type*} [AddCommGroup Derivative]
    (data : CurvatureCommutatorData Derivative Vector) : Prop :=
  ∀ X Y Z,
    data.firstThenSecond X Y Z - data.secondThenFirst X Y Z -
        data.bracketDerivative X Y Z = data.curvatureAction X Y Z

/-- Constant sectional curvature `K` in arbitrary dimension. -/
def HasConstantSectionalCurvature
    {Vector : Type*} (data : CurvatureData Vector) (K : ℝ) : Prop :=
  ∀ X Y, data.sectionalCurvature X Y = K

/-- In dimension two, the Ricci endomorphism is multiplication by Gaussian curvature. -/
structure SurfaceRicciData (Vector : Type*) where
  gaussianCurvature : ℝ
  ricciAction : Vector → Vector

def HasSurfaceRicciIdentity
    {Vector : Type*} [AddCommGroup Vector] [Module ℝ Vector]
    (data : SurfaceRicciData Vector) : Prop :=
  ∀ vector, data.ricciAction vector = data.gaussianCurvature • vector

end RiemannianFluids
