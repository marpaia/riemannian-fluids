import RiemannianFluids.Geometry.LocalSubmanifoldInducedConnection
import RiemannianFluids.Geometry.SubmanifoldGauss

/-!
# Differentiating the germ-local Gauss formula

This module starts the second-order migration of the CCG25 geometry engine.  A single
normal-form chart centered at `x` supplies canonical ambient tangent extensions.  Their normal
Gauss term is kept as a genuine field along the immersion and differentiated once with the local
normal connection.  The two intrinsic connection corrections then give the covariant derivative
of the second fundamental form at `x`.

The construction uses an intrinsic Levi--Civita connection on the source, already identified
with the locally induced connection in `LocalSubmanifoldInducedConnection`.  No global ambient
extension operator is an input.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)]
  {immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)}
  {x : M}

namespace LocalSubmanifoldExtensionDataAt

/-- The normal Gauss term obtained from the canonical fixed-chart extensions of two tangent
vectors at the center, retained as a field along the immersion near that center. -/
def canonicalSecondFundamentalFieldAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (first second : TangentSpace I x) : AmbientVectorFieldAlong immersion :=
  fun q ↦ splitting.normalProjection q
    (ambientConnection (extensions.canonicalTangentExtensionAt second)
      (immersion.toFun q)
      (mfderiv I I' immersion.toFun q
        (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first q)))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [I.Boundaryless] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- At the center, the fixed-chart normal Gauss field is the constructed second fundamental
value. -/
theorem canonicalSecondFundamentalFieldAt_apply
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : TangentSpace I x) :
    extensions.canonicalSecondFundamentalFieldAt splitting ambientConnection first second x =
      extensions.projectedSecondFundamentalValueAt splitting ambientConnection
        decomposition leftInverse first second := by
  simp [canonicalSecondFundamentalFieldAt, projectedSecondFundamentalValueAt]

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [I.Boundaryless] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- Every value of the fixed-chart Gauss field lies in the kernel-normal summand. -/
theorem tangentProjection_canonicalSecondFundamentalFieldAt_eq_zero
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : TangentSpace I x) (q : M) :
    splitting.tangentProjection q
        (extensions.canonicalSecondFundamentalFieldAt
          splitting ambientConnection first second q) = 0 :=
  tangentProjection_normalProjection_eq_zero immersion splitting
    decomposition leftInverse q _

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- The fixed-chart Gauss field is additive in its direction vector. -/
theorem canonicalSecondFundamentalFieldAt_add_first
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (first first' second : TangentSpace I x) :
    extensions.canonicalSecondFundamentalFieldAt splitting ambientConnection
        (first + first') second =
      extensions.canonicalSecondFundamentalFieldAt splitting ambientConnection first second +
        extensions.canonicalSecondFundamentalFieldAt
          splitting ambientConnection first' second := by
  funext q
  simp [canonicalSecondFundamentalFieldAt]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- Constant scalars pull through the direction vector of the fixed-chart Gauss field. -/
theorem canonicalSecondFundamentalFieldAt_smul_first
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (scalar : ℝ) (first second : TangentSpace I x) :
    extensions.canonicalSecondFundamentalFieldAt splitting ambientConnection
        (scalar • first) second =
      scalar • extensions.canonicalSecondFundamentalFieldAt
        splitting ambientConnection first second := by
  funext q
  simp [canonicalSecondFundamentalFieldAt]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- Additivity in the differentiated tangent vector holds as a germ at the chart center.
Unlike additivity in the direction vector, this identity uses the connection law and therefore
requires differentiability of the two canonical ambient extensions at the varying point.  Their
`C²` regularity supplies that hypothesis on a neighborhood. -/
theorem canonicalSecondFundamentalFieldAt_add_second_eventuallyEq
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (first second second' : TangentSpace I x) :
    extensions.canonicalSecondFundamentalFieldAt splitting ambientConnection
        first (second + second') =ᶠ[nhds x]
      extensions.canonicalSecondFundamentalFieldAt splitting ambientConnection first second +
        extensions.canonicalSecondFundamentalFieldAt
          splitting ambientConnection first second' := by
  have hsecondNear : ∀ᶠ y in nhds (immersion.toFun x),
      MDiffAt (T% (extensions.canonicalTangentExtensionAt second)) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp
      ((extensions.canonicalTangentExtensionAt_contMDiffAt_two second).of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have hsecondNear' : ∀ᶠ y in nhds (immersion.toFun x),
      MDiffAt (T% (extensions.canonicalTangentExtensionAt second')) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp
      ((extensions.canonicalTangentExtensionAt_contMDiffAt_two second').of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have hsecondAlong := (immersion.contMDiff x).continuousAt.eventually hsecondNear
  have hsecondAlong' := (immersion.contMDiff x).continuousAt.eventually hsecondNear'
  filter_upwards [hsecondAlong, hsecondAlong'] with q hsecond hsecond'
  have connectionAdd := DFunLike.congr_fun
    (ambientConnection.isCovariantDerivativeOn.add hsecond hsecond')
    (mfderiv I I' immersion.toFun q
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first q))
  change splitting.normalProjection q
      (ambientConnection (extensions.canonicalTangentExtensionAt (second + second'))
        (immersion.toFun q)
        (mfderiv I I' immersion.toFun q
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first q))) =
    splitting.normalProjection q
        (ambientConnection (extensions.canonicalTangentExtensionAt second)
          (immersion.toFun q)
          (mfderiv I I' immersion.toFun q
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first q))) +
      splitting.normalProjection q
        (ambientConnection (extensions.canonicalTangentExtensionAt second')
          (immersion.toFun q)
          (mfderiv I I' immersion.toFun q
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first q)))
  rw [show extensions.canonicalTangentExtensionAt (second + second') =
      extensions.canonicalTangentExtensionAt second +
        extensions.canonicalTangentExtensionAt second' by
    simp [canonicalTangentExtensionAt]]
  rw [connectionAdd]
  simp only [add_apply, map_add]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- Constant scalars pull through the differentiated tangent vector as a germ at the chart
center. -/
theorem canonicalSecondFundamentalFieldAt_smul_second_eventuallyEq
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (scalar : ℝ) (first second : TangentSpace I x) :
    extensions.canonicalSecondFundamentalFieldAt splitting ambientConnection
        first (scalar • second) =ᶠ[nhds x]
      scalar • extensions.canonicalSecondFundamentalFieldAt
        splitting ambientConnection first second := by
  have hsecondNear : ∀ᶠ y in nhds (immersion.toFun x),
      MDiffAt (T% (extensions.canonicalTangentExtensionAt second)) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp
      ((extensions.canonicalTangentExtensionAt_contMDiffAt_two second).of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have hsecondAlong := (immersion.contMDiff x).continuousAt.eventually hsecondNear
  filter_upwards [hsecondAlong] with q hsecond
  have connectionSmul := DFunLike.congr_fun
    (ambientConnection.isCovariantDerivativeOn.smul_const scalar hsecond)
    (mfderiv I I' immersion.toFun q
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first q))
  change splitting.normalProjection q
      (ambientConnection (extensions.canonicalTangentExtensionAt (scalar • second))
        (immersion.toFun q)
        (mfderiv I I' immersion.toFun q
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first q))) =
    scalar • splitting.normalProjection q
      (ambientConnection (extensions.canonicalTangentExtensionAt second)
        (immersion.toFun q)
        (mfderiv I I' immersion.toFun q
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first q)))
  rw [show extensions.canonicalTangentExtensionAt (scalar • second) =
      scalar • extensions.canonicalTangentExtensionAt second by
    simp [canonicalTangentExtensionAt]]
  rw [connectionSmul]
  simp only [smul_apply, map_smul]

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- Ambient torsion-freeness and germ-local bracket naturality make the two fixed-chart Gauss
fields symmetric on a source neighborhood.  This is the field-level identity that can safely be
differentiated by the local normal connection. -/
theorem canonicalSecondFundamentalFieldAt_comm_eventuallyEq
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : TangentSpace I x) :
    extensions.canonicalSecondFundamentalFieldAt splitting
        ambientLeviCivita.connection first second =ᶠ[nhds x]
      extensions.canonicalSecondFundamentalFieldAt splitting
        ambientLeviCivita.connection second first := by
  let firstSource :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondSource :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let firstAmbient := extensions.canonicalTangentExtensionAt first
  let secondAmbient := extensions.canonicalTangentExtensionAt second
  have hfirstSource : CMDiffAt 2 (T% firstSource) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x first
  have hsecondSource : CMDiffAt 2 (T% secondSource) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x second
  have hfirstSourceNear : ∀ᶠ q in nhds x, MDiffAt (T% firstSource) q := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (hfirstSource.of_le (by norm_num))
    exact hnear.mono fun _ hq ↦ hq.mdifferentiableAt one_ne_zero
  have hsecondSourceNear : ∀ᶠ q in nhds x, MDiffAt (T% secondSource) q := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (hsecondSource.of_le (by norm_num))
    exact hnear.mono fun _ hq ↦ hq.mdifferentiableAt one_ne_zero
  have hfirstAmbientNearTarget : ∀ᶠ y in nhds (immersion.toFun x),
      MDiffAt (T% firstAmbient) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp
      ((extensions.canonicalTangentExtensionAt_contMDiffAt_two first).of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have hsecondAmbientNearTarget : ∀ᶠ y in nhds (immersion.toFun x),
      MDiffAt (T% secondAmbient) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp
      ((extensions.canonicalTangentExtensionAt_contMDiffAt_two second).of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have hfirstAmbientNear :=
    (immersion.contMDiff x).continuousAt.eventually hfirstAmbientNearTarget
  have hsecondAmbientNear :=
    (immersion.contMDiff x).continuousAt.eventually hsecondAmbientNearTarget
  have firstRelated : firstAmbient ∘ immersion.toFun =ᶠ[nhds x]
      fun q ↦ mfderiv I I' immersion.toFun q (firstSource q) := by
    simpa only [firstAmbient, firstSource, canonicalTangentExtensionAt] using
      extensions.tangentExtension_agrees firstSource
  have secondRelated : secondAmbient ∘ immersion.toFun =ᶠ[nhds x]
      fun q ↦ mfderiv I I' immersion.toFun q (secondSource q) := by
    simpa only [secondAmbient, secondSource, canonicalTangentExtensionAt] using
      extensions.tangentExtension_agrees secondSource
  have firstRelatedNear : ∀ᶠ q in nhds x,
      firstAmbient ∘ immersion.toFun =ᶠ[nhds q]
        fun y ↦ mfderiv I I' immersion.toFun y (firstSource y) :=
    eventually_eventuallyEq_nhds.mpr firstRelated
  have secondRelatedNear : ∀ᶠ q in nhds x,
      secondAmbient ∘ immersion.toFun =ᶠ[nhds q]
        fun y ↦ mfderiv I I' immersion.toFun y (secondSource y) :=
    eventually_eventuallyEq_nhds.mpr secondRelated
  filter_upwards [hfirstSourceNear, hsecondSourceNear, hfirstAmbientNear,
    hsecondAmbientNear, firstRelatedNear, secondRelatedNear] with q hfirst hsecond
      hfirstAmbient hsecondAmbient hfirstRelated hsecondRelated
  have bracketNaturality := VectorField.mlieBracket_eq_mfderiv_mlieBracket_of_related
    (immersion.contMDiff.of_le (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top))
    hfirst hsecond hfirstAmbient hsecondAmbient hfirstRelated hsecondRelated
  have bracketZero : splitting.normalProjection q
      (VectorField.mlieBracket I' firstAmbient secondAmbient
        (immersion.toFun q)) = 0 := by
    rw [bracketNaturality]
    exact normalProjection_mfderiv_eq_zero immersion splitting
      decomposition leftInverse q _
  have torsionIdentity := ambientLeviCivita.connection.torsion_eq_zero_iff.mp
    ambientLeviCivita.torsionFree hfirstAmbient hsecondAmbient
  have projectedIdentity := congrArg (splitting.normalProjection q) torsionIdentity
  have firstValue := hfirstRelated.self_of_nhds
  have secondValue := hsecondRelated.self_of_nhds
  change firstAmbient (immersion.toFun q) =
    mfderiv I I' immersion.toFun q (firstSource q) at firstValue
  change secondAmbient (immersion.toFun q) =
    mfderiv I I' immersion.toFun q (secondSource q) at secondValue
  change splitting.normalProjection q
      (ambientLeviCivita.connection secondAmbient (immersion.toFun q)
        (mfderiv I I' immersion.toFun q (firstSource q))) =
    splitting.normalProjection q
      (ambientLeviCivita.connection firstAmbient (immersion.toFun q)
        (mfderiv I I' immersion.toFun q (secondSource q)))
  rw [← firstValue, ← secondValue]
  rw [map_sub, bracketZero] at projectedIdentity
  exact sub_eq_zero.mp projectedIdentity

/-- The genuine regularity obligation for differentiating the fixed-chart normal Gauss field.
It contains no curvature, Codazzi, tensoriality, or trace identity. -/
structure HasCanonicalSecondFundamentalRegularityAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _)) : Prop where
  contMDiffAt_one : ∀ first second : TangentSpace I x,
    CMDiffAt 1
      (fun q ↦
        (⟨immersion.toFun q,
          extensions.canonicalSecondFundamentalFieldAt
            splitting ambientConnection first second q⟩ : TangentBundle I' N)) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- The stored `C¹` regularity gives the differentiability consumed by the normal connection. -/
theorem HasCanonicalSecondFundamentalRegularityAt.mdifferentiableAt
    {extensions : LocalSubmanifoldExtensionDataAt immersion x}
    {splitting : SubmanifoldSplittingData immersion}
    {ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _)}
    (regular : extensions.HasCanonicalSecondFundamentalRegularityAt
      splitting ambientConnection)
    (first second : TangentSpace I x) :
    MDiffAt
      (fun q ↦
        (⟨immersion.toFun q,
          extensions.canonicalSecondFundamentalFieldAt
            splitting ambientConnection first second q⟩ : TangentBundle I' N)) x :=
  (regular.contMDiffAt_one first second).mdifferentiableAt one_ne_zero

/-- Raw ambient-fiber value of the locally constructed covariant derivative `∇ᴮ II`.
The first term is the normal derivative of the actual varying Gauss field; the last two are the
intrinsic connection corrections. -/
def covariantDerivativeSecondFundamentalRawAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (direction first second : TangentSpace I x) :
    TangentSpace I' (immersion.toFun x) :=
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let derivativeFirst := intrinsicConnection firstField x direction
  let derivativeSecond := intrinsicConnection secondField x direction
  extensions.normalDerivativeAt splitting ambientConnection directionField
      (extensions.canonicalSecondFundamentalFieldAt
        splitting ambientConnection first second) -
    (extensions.projectedSecondFundamentalFormAt splitting ambientConnection
      decomposition leftInverse derivativeFirst second : TangentSpace I' (immersion.toFun x)) -
    (extensions.projectedSecondFundamentalFormAt splitting ambientConnection
      decomposition leftInverse first derivativeSecond : TangentSpace I' (immersion.toFun x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- The locally constructed covariant derivative of `II`, valued in the actual kernel-normal
fiber. -/
def projectedCovariantDerivativeSecondFundamentalValueAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (direction first second : TangentSpace I x) :
    LinearMap.ker (splitting.tangentProjection x).toLinearMap :=
  ⟨extensions.covariantDerivativeSecondFundamentalRawAt splitting ambientConnection
      intrinsicConnection decomposition leftInverse direction first second, by
    change splitting.tangentProjection x
      (extensions.covariantDerivativeSecondFundamentalRawAt splitting ambientConnection
        intrinsicConnection decomposition leftInverse direction first second) = 0
    rw [covariantDerivativeSecondFundamentalRawAt, map_sub, map_sub]
    rw [extensions.tangentProjection_normalDerivativeAt_eq_zero splitting ambientConnection
      decomposition leftInverse]
    have hfirst := (extensions.projectedSecondFundamentalFormAt splitting ambientConnection
      decomposition leftInverse
        (intrinsicConnection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first)
          x direction) second).property
    change splitting.tangentProjection x
      (extensions.projectedSecondFundamentalFormAt splitting ambientConnection
        decomposition leftInverse
          (intrinsicConnection
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first)
            x direction) second) = 0 at hfirst
    have hsecond := (extensions.projectedSecondFundamentalFormAt splitting ambientConnection
      decomposition leftInverse first
        (intrinsicConnection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second)
          x direction)).property
    change splitting.tangentProjection x
      (extensions.projectedSecondFundamentalFormAt splitting ambientConnection
        decomposition leftInverse first
          (intrinsicConnection
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second)
            x direction)) = 0 at hsecond
    rw [hfirst, hsecond]
    simp⟩

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem projectedCovariantDerivativeSecondFundamentalValueAt_coe
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (direction first second : TangentSpace I x) :
    (extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
      ambientConnection intrinsicConnection decomposition leftInverse direction first second :
        TangentSpace I' (immersion.toFun x)) =
      extensions.covariantDerivativeSecondFundamentalRawAt splitting ambientConnection
        intrinsicConnection decomposition leftInverse direction first second :=
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- Additivity in the covariant-derivative direction follows directly from the two connection
laws and the bilinearity of the locally constructed second fundamental form. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_add_direction
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (direction direction' first second : TangentSpace I x) :
    extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientConnection intrinsicConnection decomposition leftInverse
        (direction + direction') first second =
      extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
          ambientConnection intrinsicConnection decomposition leftInverse
          direction first second +
        extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
          ambientConnection intrinsicConnection decomposition leftInverse
          direction' first second := by
  apply Subtype.ext
  simp [projectedCovariantDerivativeSecondFundamentalValueAt,
    covariantDerivativeSecondFundamentalRawAt,
    normalDerivativeAt, ambientDerivativeAlongAt]
  rw [extensions.projectedSecondFundamentalValueAt_add_second splitting ambientConnection
    decomposition leftInverse]
  simp only [Submodule.coe_add]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- Constant scalars pull through the covariant-derivative direction. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_smul_direction
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (scalar : ℝ) (direction first second : TangentSpace I x) :
    extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientConnection intrinsicConnection decomposition leftInverse
        (scalar • direction) first second =
      scalar • extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientConnection intrinsicConnection decomposition leftInverse
        direction first second := by
  apply Subtype.ext
  simp [projectedCovariantDerivativeSecondFundamentalValueAt,
    covariantDerivativeSecondFundamentalRawAt,
    normalDerivativeAt, ambientDerivativeAlongAt]
  module

/-- Additivity in the first `II` slot uses only regularity of the two genuine fixed-chart Gauss
fields; all geometric identities remain derived. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_add_first
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (regular : extensions.HasCanonicalSecondFundamentalRegularityAt
      splitting ambientConnection)
    (direction first first' second : TangentSpace I x) :
    extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientConnection intrinsicConnection decomposition leftInverse
        direction (first + first') second =
      extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
          ambientConnection intrinsicConnection decomposition leftInverse
          direction first second +
        extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
          ambientConnection intrinsicConnection decomposition leftInverse
          direction first' second := by
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let firstField' :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first'
  have hnormal := regular.mdifferentiableAt first second
  have hnormal' := regular.mdifferentiableAt first' second
  have normalDerivativeAdd := extensions.normalDerivativeAt_add splitting ambientConnection
    (direction := directionField) hnormal hnormal'
  have hfirst : MDiffAt (T% firstField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt (I := I) x first
  have hfirst' : MDiffAt (T% firstField') x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt (I := I) x first'
  have connectionAdd := DFunLike.congr_fun
    (intrinsicConnection.isCovariantDerivativeOn.add hfirst hfirst') direction
  have derivativeFirstAdd :
      intrinsicConnection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (first + first'))
          x direction =
        intrinsicConnection firstField x direction +
          intrinsicConnection firstField' x direction := by
    rw [map_add]
    simpa only [add_apply] using connectionAdd
  apply Subtype.ext
  change extensions.covariantDerivativeSecondFundamentalRawAt splitting ambientConnection
      intrinsicConnection decomposition leftInverse direction (first + first') second =
    extensions.covariantDerivativeSecondFundamentalRawAt splitting ambientConnection
        intrinsicConnection decomposition leftInverse direction first second +
      extensions.covariantDerivativeSecondFundamentalRawAt splitting ambientConnection
        intrinsicConnection decomposition leftInverse direction first' second
  simp only [covariantDerivativeSecondFundamentalRawAt]
  rw [canonicalSecondFundamentalFieldAt_add_first, normalDerivativeAdd,
    derivativeFirstAdd]
  simp only [map_add, add_apply, Submodule.coe_add]
  dsimp only [directionField, firstField, firstField']
  abel

/-- Constant scalars pull through the first `II` slot. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_smul_first
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (regular : extensions.HasCanonicalSecondFundamentalRegularityAt
      splitting ambientConnection)
    (scalar : ℝ) (direction first second : TangentSpace I x) :
    extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientConnection intrinsicConnection decomposition leftInverse
        direction (scalar • first) second =
      scalar • extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientConnection intrinsicConnection decomposition leftInverse
        direction first second := by
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  have hnormal := regular.mdifferentiableAt first second
  have normalDerivativeSmul := extensions.normalDerivativeAt_smul_const
    splitting ambientConnection (direction := directionField) scalar hnormal
  have hfirst : MDiffAt (T% firstField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt (I := I) x first
  have connectionSmul := DFunLike.congr_fun
    (intrinsicConnection.isCovariantDerivativeOn.smul_const scalar hfirst) direction
  have derivativeFirstSmul :
      intrinsicConnection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (scalar • first))
          x direction =
        scalar • intrinsicConnection firstField x direction := by
    rw [map_smul]
    simpa only [smul_apply] using connectionSmul
  apply Subtype.ext
  change extensions.covariantDerivativeSecondFundamentalRawAt splitting ambientConnection
      intrinsicConnection decomposition leftInverse direction (scalar • first) second =
    scalar • extensions.covariantDerivativeSecondFundamentalRawAt splitting ambientConnection
      intrinsicConnection decomposition leftInverse direction first second
  simp only [covariantDerivativeSecondFundamentalRawAt]
  rw [canonicalSecondFundamentalFieldAt_smul_first, normalDerivativeSmul,
    derivativeFirstSmul]
  simp only [map_smul, smul_apply, Submodule.coe_smul]
  dsimp only [directionField, firstField]
  module

/-- Additivity in the differentiated `II` slot is a germ-level consequence of the
Levi--Civita restriction-locality theorem.  The local extension operator need not preserve the
connection law away from the immersed germ. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_add_second
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (regular : extensions.HasCanonicalSecondFundamentalRegularityAt
      splitting ambientLeviCivita.connection)
    (direction first second second' : TangentSpace I x) :
    extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
        direction first (second + second') =
      extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
          ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
          direction first second +
        extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
          ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
          direction first second' := by
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let secondField' :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second'
  let normalSum := extensions.canonicalSecondFundamentalFieldAt
    splitting ambientLeviCivita.connection first (second + second')
  let normal := extensions.canonicalSecondFundamentalFieldAt
    splitting ambientLeviCivita.connection first second
  let normal' := extensions.canonicalSecondFundamentalFieldAt
    splitting ambientLeviCivita.connection first second'
  have hnormalSum := regular.mdifferentiableAt first (second + second')
  have hnormal := regular.mdifferentiableAt first second
  have hnormal' := regular.mdifferentiableAt first second'
  have normalAgreement : normalSum =ᶠ[nhds x] normal + normal' :=
    extensions.canonicalSecondFundamentalFieldAt_add_second_eventuallyEq
      splitting ambientLeviCivita.connection first second second'
  have hnormalAdded : MDiffAt
      (fun q ↦ (⟨immersion.toFun q, (normal + normal') q⟩ : TangentBundle I' N)) x :=
    hnormalSum.congr_of_eventuallyEq <| normalAgreement.symm.mono fun q hq ↦
      congrArg (fun value ↦
        (⟨immersion.toFun q, value⟩ : TangentBundle I' N)) hq
  have normalDerivativeEq := extensions.normalDerivativeAt_eq_of_eventuallyEq
    splitting ambientLeviCivita (direction := directionField)
    hnormalSum hnormalAdded normalAgreement
  have normalDerivativeAdd := extensions.normalDerivativeAt_add
    splitting ambientLeviCivita.connection (direction := directionField) hnormal hnormal'
  have hsecond : MDiffAt (T% secondField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x second
  have hsecond' : MDiffAt (T% secondField') x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x second'
  have connectionAdd := DFunLike.congr_fun
    (intrinsicConnection.isCovariantDerivativeOn.add hsecond hsecond') direction
  have derivativeSecondAdd :
      intrinsicConnection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt
            (I := I) x (second + second')) x direction =
        intrinsicConnection secondField x direction +
          intrinsicConnection secondField' x direction := by
    rw [map_add]
    simpa only [add_apply] using connectionAdd
  apply Subtype.ext
  change extensions.covariantDerivativeSecondFundamentalRawAt splitting
      ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
      direction first (second + second') =
    extensions.covariantDerivativeSecondFundamentalRawAt splitting
        ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
        direction first second +
      extensions.covariantDerivativeSecondFundamentalRawAt splitting
        ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
        direction first second'
  simp only [covariantDerivativeSecondFundamentalRawAt]
  rw [show extensions.normalDerivativeAt splitting ambientLeviCivita.connection
        directionField normalSum =
      extensions.normalDerivativeAt splitting ambientLeviCivita.connection
          directionField normal +
        extensions.normalDerivativeAt splitting ambientLeviCivita.connection
          directionField normal' from normalDerivativeEq.trans normalDerivativeAdd,
    derivativeSecondAdd]
  simp only [map_add, Submodule.coe_add]
  dsimp only [directionField, secondField, secondField', normalSum, normal, normal']
  abel

/-- Constant scalars pull through the differentiated `II` slot by the same germ-local
restriction argument. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_smul_second
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (regular : extensions.HasCanonicalSecondFundamentalRegularityAt
      splitting ambientLeviCivita.connection)
    (scalar : ℝ) (direction first second : TangentSpace I x) :
    extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
        direction first (scalar • second) =
      scalar • extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
        direction first second := by
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let normalScaled := extensions.canonicalSecondFundamentalFieldAt
    splitting ambientLeviCivita.connection first (scalar • second)
  let normal := extensions.canonicalSecondFundamentalFieldAt
    splitting ambientLeviCivita.connection first second
  have hnormalScaled := regular.mdifferentiableAt first (scalar • second)
  have hnormal := regular.mdifferentiableAt first second
  have normalAgreement : normalScaled =ᶠ[nhds x] scalar • normal :=
    extensions.canonicalSecondFundamentalFieldAt_smul_second_eventuallyEq
      splitting ambientLeviCivita.connection scalar first second
  have hnormalTarget : MDiffAt
      (fun q ↦ (⟨immersion.toFun q, (scalar • normal) q⟩ : TangentBundle I' N)) x :=
    hnormalScaled.congr_of_eventuallyEq <| normalAgreement.symm.mono fun q hq ↦
      congrArg (fun value ↦
        (⟨immersion.toFun q, value⟩ : TangentBundle I' N)) hq
  have normalDerivativeEq := extensions.normalDerivativeAt_eq_of_eventuallyEq
    splitting ambientLeviCivita (direction := directionField)
    hnormalScaled hnormalTarget normalAgreement
  have normalDerivativeSmul := extensions.normalDerivativeAt_smul_const
    splitting ambientLeviCivita.connection (direction := directionField) scalar hnormal
  have hsecond : MDiffAt (T% secondField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x second
  have connectionSmul := DFunLike.congr_fun
    (intrinsicConnection.isCovariantDerivativeOn.smul_const scalar hsecond) direction
  have derivativeSecondSmul :
      intrinsicConnection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt
            (I := I) x (scalar • second)) x direction =
        scalar • intrinsicConnection secondField x direction := by
    rw [map_smul]
    simpa only [smul_apply] using connectionSmul
  apply Subtype.ext
  change extensions.covariantDerivativeSecondFundamentalRawAt splitting
      ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
      direction first (scalar • second) =
    scalar • extensions.covariantDerivativeSecondFundamentalRawAt splitting
      ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
      direction first second
  simp only [covariantDerivativeSecondFundamentalRawAt]
  rw [show extensions.normalDerivativeAt splitting ambientLeviCivita.connection
        directionField normalScaled =
      scalar • extensions.normalDerivativeAt splitting ambientLeviCivita.connection
        directionField normal from normalDerivativeEq.trans normalDerivativeSmul,
    derivativeSecondSmul]
  simp only [map_smul, Submodule.coe_smul]
  dsimp only [directionField, secondField, normalScaled, normal]
  module

set_option synthInstance.maxHeartbeats 100000 in
/-- The germ-local covariant derivative of the second fundamental form as a genuine continuous
trilinear tensor.  All six linearity laws are derived from connection laws and restriction
locality; the regularity input contains no tensoriality equation. -/
def projectedCovariantDerivativeSecondFundamentalAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (regular : extensions.HasCanonicalSecondFundamentalRegularityAt
      splitting ambientLeviCivita.connection) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ]
        LinearMap.ker (splitting.tangentProjection x).toLinearMap :=
  LinearMap.toContinuousLinearMap {
    toFun := fun direction ↦ LinearMap.toContinuousLinearMap {
      toFun := fun first ↦ LinearMap.toContinuousLinearMap {
        toFun := fun second ↦
          extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
            ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
            direction first second
        map_add' := fun second second' ↦
          extensions.projectedCovariantDerivativeSecondFundamentalValueAt_add_second splitting
            ambientLeviCivita intrinsicConnection decomposition leftInverse regular
            direction first second second'
        map_smul' := fun scalar second ↦
          extensions.projectedCovariantDerivativeSecondFundamentalValueAt_smul_second splitting
            ambientLeviCivita intrinsicConnection decomposition leftInverse regular
            scalar direction first second }
      map_add' := by
        intro first first'
        apply ContinuousLinearMap.ext
        intro second
        exact extensions.projectedCovariantDerivativeSecondFundamentalValueAt_add_first splitting
          ambientLeviCivita.connection intrinsicConnection decomposition leftInverse regular
          direction first first' second
      map_smul' := by
        intro scalar first
        apply ContinuousLinearMap.ext
        intro second
        exact extensions.projectedCovariantDerivativeSecondFundamentalValueAt_smul_first splitting
          ambientLeviCivita.connection intrinsicConnection decomposition leftInverse regular
          scalar direction first second }
    map_add' := by
      intro direction direction'
      apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      exact extensions.projectedCovariantDerivativeSecondFundamentalValueAt_add_direction
        splitting ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
        direction direction' first second
    map_smul' := by
      intro scalar direction
      apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      exact extensions.projectedCovariantDerivativeSecondFundamentalValueAt_smul_direction
        splitting ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
        scalar direction first second }

@[simp]
theorem projectedCovariantDerivativeSecondFundamentalAt_apply
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (regular : extensions.HasCanonicalSecondFundamentalRegularityAt
      splitting ambientLeviCivita.connection)
    (direction first second : TangentSpace I x) :
    extensions.projectedCovariantDerivativeSecondFundamentalAt splitting ambientLeviCivita
        intrinsicConnection decomposition leftInverse regular direction first second =
      extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
        direction first second :=
  rfl

/-- The locally constructed `∇ᴮ II` value is symmetric in its two second-fundamental-form
slots.  Field-level symmetry is transported through the normal derivative by germ locality;
the two connection-correction terms then exchange using symmetry of the local `II`. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_comm
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (regular : extensions.HasCanonicalSecondFundamentalRegularityAt
      splitting ambientLeviCivita.connection)
    (direction first second : TangentSpace I x) :
    extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
        direction first second =
      extensions.projectedCovariantDerivativeSecondFundamentalValueAt splitting
        ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
        direction second first := by
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let normal := extensions.canonicalSecondFundamentalFieldAt
    splitting ambientLeviCivita.connection first second
  let normalSwapped := extensions.canonicalSecondFundamentalFieldAt
    splitting ambientLeviCivita.connection second first
  let derivativeFirst := intrinsicConnection firstField x direction
  let derivativeSecond := intrinsicConnection secondField x direction
  have normalAgreement : normal =ᶠ[nhds x] normalSwapped :=
    extensions.canonicalSecondFundamentalFieldAt_comm_eventuallyEq splitting
      ambientLeviCivita decomposition leftInverse first second
  have hnormal := regular.mdifferentiableAt first second
  have hnormalSwapped := regular.mdifferentiableAt second first
  have normalDerivativeComm := extensions.normalDerivativeAt_eq_of_eventuallyEq
    splitting ambientLeviCivita (direction := directionField)
      hnormal hnormalSwapped normalAgreement
  have correctionFirstComm := extensions.projectedSecondFundamentalFormAt_comm
    splitting ambientLeviCivita decomposition leftInverse derivativeFirst second
  have correctionSecondComm := extensions.projectedSecondFundamentalFormAt_comm
    splitting ambientLeviCivita decomposition leftInverse first derivativeSecond
  apply Subtype.ext
  change extensions.covariantDerivativeSecondFundamentalRawAt splitting
      ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
      direction first second =
    extensions.covariantDerivativeSecondFundamentalRawAt splitting
      ambientLeviCivita.connection intrinsicConnection decomposition leftInverse
      direction second first
  simp only [covariantDerivativeSecondFundamentalRawAt]
  rw [show extensions.normalDerivativeAt splitting ambientLeviCivita.connection
        directionField normal =
      extensions.normalDerivativeAt splitting ambientLeviCivita.connection
        directionField normalSwapped from normalDerivativeComm,
    correctionFirstComm, correctionSecondComm]
  dsimp only [directionField, firstField, secondField, normal, normalSwapped,
    derivativeFirst, derivativeSecond]
  abel

/-- Symmetry of the continuous germ-local `∇ᴮ II` tensor in its final two slots. -/
theorem projectedCovariantDerivativeSecondFundamentalAt_comm
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (regular : extensions.HasCanonicalSecondFundamentalRegularityAt
      splitting ambientLeviCivita.connection)
    (direction first second : TangentSpace I x) :
    extensions.projectedCovariantDerivativeSecondFundamentalAt splitting ambientLeviCivita
        intrinsicConnection decomposition leftInverse regular direction first second =
      extensions.projectedCovariantDerivativeSecondFundamentalAt splitting ambientLeviCivita
        intrinsicConnection decomposition leftInverse regular direction second first :=
  extensions.projectedCovariantDerivativeSecondFundamentalValueAt_comm splitting
    ambientLeviCivita intrinsicConnection decomposition leftInverse regular
    direction first second

end LocalSubmanifoldExtensionDataAt

namespace SmoothIsometricEmbeddingData

/-- Embedding-level local `∇ᴮ II` value.  Its extensions, splitting, and projection laws are
all constructed internally; the source and ambient Levi--Civita connections are the geometric
inputs. -/
def localProjectedCovariantDerivativeSecondFundamentalValueAt
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicLeviCivita : LeviCivitaConnection (M := M) I)
    (x : M) (direction first second : TangentSpace I x) :
    LinearMap.ker
      (embedding.toSmoothIsometricImmersionData.orthogonalSplitting.tangentProjection x
        ).toLinearMap :=
  (embedding.localSubmanifoldExtensionDataAt x
    ).projectedCovariantDerivativeSecondFundamentalValueAt
      embedding.toSmoothIsometricImmersionData.orthogonalSplitting
      ambientLeviCivita.connection intrinsicLeviCivita.connection
      embedding.toSmoothIsometricImmersionData.hasTangentNormalDecomposition
      embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse
      direction first second

/-- Embedding-level continuous trilinear `∇ᴮ II`, constructed from the embedding's local
normal-form chart and the two Levi--Civita connections. -/
def localProjectedCovariantDerivativeSecondFundamentalAt
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicLeviCivita : LeviCivitaConnection (M := M) I)
    (x : M)
    (regular : (embedding.localSubmanifoldExtensionDataAt x
      ).HasCanonicalSecondFundamentalRegularityAt
        embedding.toSmoothIsometricImmersionData.orthogonalSplitting
        ambientLeviCivita.connection) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ]
        LinearMap.ker
          (embedding.toSmoothIsometricImmersionData.orthogonalSplitting.tangentProjection x
            ).toLinearMap :=
  (embedding.localSubmanifoldExtensionDataAt x
    ).projectedCovariantDerivativeSecondFundamentalAt
      embedding.toSmoothIsometricImmersionData.orthogonalSplitting
      ambientLeviCivita intrinsicLeviCivita.connection
      embedding.toSmoothIsometricImmersionData.hasTangentNormalDecomposition
      embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse regular

@[simp]
theorem localProjectedCovariantDerivativeSecondFundamentalAt_apply
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicLeviCivita : LeviCivitaConnection (M := M) I)
    (x : M)
    (regular : (embedding.localSubmanifoldExtensionDataAt x
      ).HasCanonicalSecondFundamentalRegularityAt
        embedding.toSmoothIsometricImmersionData.orthogonalSplitting
        ambientLeviCivita.connection)
    (direction first second : TangentSpace I x) :
    embedding.localProjectedCovariantDerivativeSecondFundamentalAt ambientLeviCivita
        intrinsicLeviCivita x regular direction first second =
      embedding.localProjectedCovariantDerivativeSecondFundamentalValueAt
        ambientLeviCivita intrinsicLeviCivita x direction first second :=
  rfl

/-- The embedding-level local `∇ᴮ II` tensor is symmetric in its final two slots. -/
theorem localProjectedCovariantDerivativeSecondFundamentalAt_comm
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicLeviCivita : LeviCivitaConnection (M := M) I)
    (x : M)
    (regular : (embedding.localSubmanifoldExtensionDataAt x
      ).HasCanonicalSecondFundamentalRegularityAt
        embedding.toSmoothIsometricImmersionData.orthogonalSplitting
        ambientLeviCivita.connection)
    (direction first second : TangentSpace I x) :
    embedding.localProjectedCovariantDerivativeSecondFundamentalAt ambientLeviCivita
        intrinsicLeviCivita x regular direction first second =
      embedding.localProjectedCovariantDerivativeSecondFundamentalAt ambientLeviCivita
        intrinsicLeviCivita x regular direction second first :=
  (embedding.localSubmanifoldExtensionDataAt x
    ).projectedCovariantDerivativeSecondFundamentalAt_comm
      embedding.toSmoothIsometricImmersionData.orthogonalSplitting
      ambientLeviCivita intrinsicLeviCivita.connection
      embedding.toSmoothIsometricImmersionData.hasTangentNormalDecomposition
      embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse regular
      direction first second

end SmoothIsometricEmbeddingData

end

end RiemannianFluids
