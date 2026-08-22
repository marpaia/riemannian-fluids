import RiemannianFluids.Geometry.SubmanifoldTangentHessian

/-!
# Mean-curvature fields from geodesic tangent frames

The CCG25 Bochner/Hodge calculation differentiates the mean-curvature vector field.  A
paper-level proof chooses a smooth tangent frame which is geodesic at the base point and traces
the second fundamental form in that frame.  This module supplies the missing construction.

The first layer records only smoothness preservation by the chosen ambient extension operators.
It then proves that the field-level covariant derivative of `II` is pointwise in all three
tangent fields.  The proof is geometric: symmetry in the two `II` slots, Codazzi, and
tensoriality of ambient curvature move every varying field to its value at the base point.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped BigOperators Bundle ContDiff Manifold Topology

noncomputable section

section ManifoldFibers

variable
  {ι κ : Type*} [Fintype ι] [Fintype κ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)]

/-- Local smoothness preservation needed for source-style differentiated Gauss calculations.

This is deliberately a regularity contract, not a geometric identity.  It says that a chosen
ambient tangent extension preserves `C²` regularity at the base point and that the chosen
ambient extension of `II(X,Y)` is differentiable whenever `X` and `Y` are `C²` there.  A smooth
tubular-neighborhood extension operator is intended to discharge this contract. -/
structure CovariantSubmanifoldFieldExtensionData.HasSmoothGaussExtensionRegularityAt
    [IsManifold I 3 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (x : M) : Prop where
  tangentExtension_contMDiffAt_two :
    ∀ field : (y : M) → TangentSpace I y,
      CMDiffAt 2 (T% field) x →
        CMDiffAt 2
          (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension field))
          (immersion.toFun x)
  normalGaussExtension_mdifferentiableAt :
    ∀ first second : (y : M) → TangentSpace I y,
      CMDiffAt 2 (T% first) x → CMDiffAt 2 (T% second) x →
        MDiffAt
          (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
            (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
              immersion splitting ambientConnection first second)))
          (immersion.toFun x)

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- Universal smooth-extension regularity implies the canonical regularity package used to
construct the pointwise `∇ᴮ II` tensor. -/
theorem CovariantSubmanifoldFieldExtensionData.HasSmoothGaussExtensionRegularityAt.toDifferentiated
    [IsManifold I 3 M] [IsManifold I' 2 N]
    {immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)}
    {splitting : SubmanifoldSplittingData immersion}
    {ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _)}
    {extensions : CovariantSubmanifoldFieldExtensionData immersion}
    {x : M}
    (regular : extensions.HasSmoothGaussExtensionRegularityAt
      immersion splitting ambientConnection x) :
    extensions.HasDifferentiatedGaussRegularityAt
      immersion splitting ambientConnection x where
  tangentExtension_contMDiffAt_two field :=
    regular.tangentExtension_contMDiffAt_two
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field)
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
        (I := I) x field)
  normalGaussExtension_mdifferentiableAt first second :=
    regular.normalGaussExtension_mdifferentiableAt
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first)
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second)
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
        (I := I) x first)
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
        (I := I) x second)

/-- Under smooth-extension regularity, the covariant derivative of `II` is symmetric in its two
`II` slots for arbitrary `C²` tangent fields. -/
theorem CovariantSubmanifoldFieldExtensionData.covariantDerivativeSecondFundamentalAlong_comm_of_smooth
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x)
    (smoothExtensions : extensions.HasSmoothGaussExtensionRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    {direction first second : (y : M) → TangentSpace I y}
    (hdirection : MDiffAt (T% direction) x)
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x) :
    extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        direction first second x =
      extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        direction second first x := by
  let induced :=
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normal := secondFundamental first second
  let normalSwapped := secondFundamental second first
  let derivativeFirst := covariantDerivativeAlong I induced direction first
  let derivativeSecond := covariantDerivativeAlong I induced direction second
  have hfirstNear : ∀ᶠ y in nhds x, MDiffAt (T% first) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (hfirst.of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have hsecondNear : ∀ᶠ y in nhds x, MDiffAt (T% second) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (hsecond.of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have normalAgreement : normal =ᶠ[nhds x] normalSwapped := by
    filter_upwards [hfirstNear, hsecondNear] with y hyFirst hySecond
    exact extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      hyFirst hySecond
  have normalDerivativeComm :
      normalDerivative direction normal x = normalDerivative direction normalSwapped x :=
    extensions.normalDerivative_eq_of_eventuallyEq immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita
      (smoothExtensions.normalGaussExtension_mdifferentiableAt first second hfirst hsecond)
      (smoothExtensions.normalGaussExtension_mdifferentiableAt second first hsecond hfirst)
      normalAgreement
  have hderivativeFirst : MDiffAt (T% derivativeFirst) x :=
    intrinsicRegular direction first hdirection hfirst
  have hderivativeSecond : MDiffAt (T% derivativeSecond) x :=
    intrinsicRegular direction second hdirection hsecond
  have correctionFirstComm :
      secondFundamental derivativeFirst second x =
        secondFundamental second derivativeFirst x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      hderivativeFirst (hsecond.mdifferentiableAt (by norm_num))
  have correctionSecondComm :
      secondFundamental first derivativeSecond x =
        secondFundamental derivativeSecond first x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      (hfirst.mdifferentiableAt (by norm_num)) hderivativeSecond
  change
    normalDerivative direction normal x -
          secondFundamental derivativeFirst second x -
        secondFundamental first derivativeSecond x =
      normalDerivative direction normalSwapped x -
          secondFundamental derivativeSecond first x -
        secondFundamental second derivativeFirst x
  rw [normalDerivativeComm, correctionFirstComm, correctionSecondComm]
  abel

/-- The covariant-derivative direction of the field-level `∇ᴮ II` is pointwise.  The only
subtle correction term is moved into the direction slot of `II` using torsion-free symmetry. -/
theorem CovariantSubmanifoldFieldExtensionData.covariantDerivativeSecondFundamentalAlong_direction_congr
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x)
    {direction direction' first second : (y : M) → TangentSpace I y}
    (hdirectionRegular : MDiffAt (T% direction) x)
    (hdirectionRegular' : MDiffAt (T% direction') x)
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x)
    (hdirection : direction x = direction' x) :
    extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        direction first second x =
      extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        direction' first second x := by
  let induced :=
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normal := secondFundamental first second
  let derivativeFirst := covariantDerivativeAlong I induced direction first
  let derivativeFirst' := covariantDerivativeAlong I induced direction' first
  let derivativeSecond := covariantDerivativeAlong I induced direction second
  let derivativeSecond' := covariantDerivativeAlong I induced direction' second
  have hderivativeFirst : MDiffAt (T% derivativeFirst) x :=
    intrinsicRegular direction first hdirectionRegular hfirst
  have hderivativeFirst' : MDiffAt (T% derivativeFirst') x :=
    intrinsicRegular direction' first hdirectionRegular' hfirst
  have hderivativeSecond : MDiffAt (T% derivativeSecond) x :=
    intrinsicRegular direction second hdirectionRegular hsecond
  have hderivativeSecond' : MDiffAt (T% derivativeSecond') x :=
    intrinsicRegular direction' second hdirectionRegular' hsecond
  have derivativeFirstValue : derivativeFirst x = derivativeFirst' x := by
    simp [derivativeFirst, derivativeFirst', covariantDerivativeAlong, hdirection]
  have derivativeSecondValue : derivativeSecond x = derivativeSecond' x := by
    simp [derivativeSecond, derivativeSecond', covariantDerivativeAlong, hdirection]
  have normalDirection :
      normalDerivative direction normal x = normalDerivative direction' normal x := by
    simp [normalDerivative, SubmanifoldFieldExtensionData.normalDerivative,
      SubmanifoldFieldExtensionData.ambientDerivativeAlong, hdirection]
  have firstCorrection :
      secondFundamental derivativeFirst second x =
        secondFundamental derivativeFirst' second x := by
    simp [secondFundamental, SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent, derivativeFirstValue]
  have secondComm :
      secondFundamental first derivativeSecond x =
        secondFundamental derivativeSecond first x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      (hfirst.mdifferentiableAt (by norm_num)) hderivativeSecond
  have secondComm' :
      secondFundamental first derivativeSecond' x =
        secondFundamental derivativeSecond' first x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      (hfirst.mdifferentiableAt (by norm_num)) hderivativeSecond'
  have secondCorrection :
      secondFundamental derivativeSecond first x =
        secondFundamental derivativeSecond' first x := by
    simp [secondFundamental, SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent, derivativeSecondValue]
  change
    normalDerivative direction normal x - secondFundamental derivativeFirst second x -
        secondFundamental first derivativeSecond x =
      normalDerivative direction' normal x - secondFundamental derivativeFirst' second x -
        secondFundamental first derivativeSecond' x
  rw [normalDirection, firstCorrection, secondComm, secondComm', secondCorrection]

/-- The first `II` slot of the field-level `∇ᴮ II` is pointwise.  Codazzi moves that slot
into the covariant-derivative direction, symmetry moves the remaining fields into the required
order, and tensoriality of ambient curvature cancels the two curvature terms. -/
theorem CovariantSubmanifoldFieldExtensionData.covariantDerivativeSecondFundamentalAlong_first_congr_of_smooth
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (smoothExtensions : extensions.HasSmoothGaussExtensionRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    {direction first first' second : (y : M) → TangentSpace I y}
    (hdirection : CMDiffAt 2 (T% direction) x)
    (hfirst : CMDiffAt 2 (T% first) x)
    (hfirst' : CMDiffAt 2 (T% first') x)
    (hsecond : CMDiffAt 2 (T% second) x)
    (hfirstValue : first x = first' x) :
    extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        direction first second x =
      extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        direction first' second x := by
  let derivative :=
    extensions.covariantDerivativeSecondFundamentalAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
  let ambientDirection :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension direction
  let ambientFirst :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension first
  let ambientFirst' :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension first'
  let ambientSecond :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension second
  have hambientDirection : CMDiffAt 2 (T% ambientDirection) (immersion.toFun x) :=
    smoothExtensions.tangentExtension_contMDiffAt_two direction hdirection
  have hambientFirst : CMDiffAt 2 (T% ambientFirst) (immersion.toFun x) :=
    smoothExtensions.tangentExtension_contMDiffAt_two first hfirst
  have hambientFirst' : CMDiffAt 2 (T% ambientFirst') (immersion.toFun x) :=
    smoothExtensions.tangentExtension_contMDiffAt_two first' hfirst'
  have hambientSecond : CMDiffAt 2 (T% ambientSecond) (immersion.toFun x) :=
    smoothExtensions.tangentExtension_contMDiffAt_two second hsecond
  have ambientFirstValue :
      ambientFirst (immersion.toFun x) = ambientFirst' (immersion.toFun x) := by
    dsimp only [ambientFirst, ambientFirst']
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first x,
      extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first' x,
      hfirstValue]
  have curvatureAgreementRaw :
      connectionCurvatureAction I' ambientLeviCivita.connection
          ambientDirection ambientFirst ambientSecond (immersion.toFun x) =
        connectionCurvatureAction I' ambientLeviCivita.connection
          ambientDirection ambientFirst' ambientSecond (immersion.toFun x) :=
    (connectionCurvatureAction_tensorial_second I' ambientLeviCivita.connection
      (immersion.toFun x) ambientRegular ambientDirection ambientSecond hambientSecond
      ).pointwise
        (hambientFirst.mdifferentiableAt (by norm_num))
        (hambientFirst'.mdifferentiableAt (by norm_num)) ambientFirstValue
  have curvatureAgreement :
      immersion.orthogonalSplitting.normalProjection x
          (connectionCurvatureAction I' ambientLeviCivita.connection
            ambientDirection ambientFirst ambientSecond (immersion.toFun x)) =
        immersion.orthogonalSplitting.normalProjection x
          (connectionCurvatureAction I' ambientLeviCivita.connection
            ambientDirection ambientFirst' ambientSecond (immersion.toFun x)) :=
    congrArg (immersion.orthogonalSplitting.normalProjection x) curvatureAgreementRaw
  have codazzi :=
    ambientCurvatureAction_normalProjection_eq_covariantDerivativeSecondFundamental_sub
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
      (hdirection.mdifferentiableAt (by norm_num))
      (hfirst.mdifferentiableAt (by norm_num)) hsecond hambientSecond
      (smoothExtensions.normalGaussExtension_mdifferentiableAt first second hfirst hsecond)
      (smoothExtensions.normalGaussExtension_mdifferentiableAt direction second
        hdirection hsecond)
  have codazzi' :=
    ambientCurvatureAction_normalProjection_eq_covariantDerivativeSecondFundamental_sub
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
      (hdirection.mdifferentiableAt (by norm_num))
      (hfirst'.mdifferentiableAt (by norm_num)) hsecond hambientSecond
      (smoothExtensions.normalGaussExtension_mdifferentiableAt first' second hfirst' hsecond)
      (smoothExtensions.normalGaussExtension_mdifferentiableAt direction second
        hdirection hsecond)
  change
    immersion.orthogonalSplitting.normalProjection x
        (connectionCurvatureAction I' ambientLeviCivita.connection
          ambientDirection ambientFirst ambientSecond (immersion.toFun x)) =
      derivative direction first second x - derivative first direction second x at codazzi
  change
    immersion.orthogonalSplitting.normalProjection x
        (connectionCurvatureAction I' ambientLeviCivita.connection
          ambientDirection ambientFirst' ambientSecond (immersion.toFun x)) =
      derivative direction first' second x - derivative first' direction second x at codazzi'
  have symmetry :=
    extensions.covariantDerivativeSecondFundamentalAlong_comm_of_smooth
      immersion ambientLeviCivita x intrinsicRegular smoothExtensions
      (hfirst.mdifferentiableAt (by norm_num)) hdirection hsecond
  change derivative first direction second x = derivative first second direction x at symmetry
  have symmetry' :=
    extensions.covariantDerivativeSecondFundamentalAlong_comm_of_smooth
      immersion ambientLeviCivita x intrinsicRegular smoothExtensions
      (hfirst'.mdifferentiableAt (by norm_num)) hdirection hsecond
  change derivative first' direction second x = derivative first' second direction x at symmetry'
  have directionAgreement :=
    extensions.covariantDerivativeSecondFundamentalAlong_direction_congr
      immersion ambientLeviCivita x intrinsicRegular
      (hfirst.mdifferentiableAt (by norm_num))
      (hfirst'.mdifferentiableAt (by norm_num)) hsecond hdirection hfirstValue
  change derivative first second direction x = derivative first' second direction x at directionAgreement
  rw [curvatureAgreement, symmetry, directionAgreement, ← symmetry'] at codazzi
  exact sub_left_inj.mp (codazzi.symm.trans codazzi')

/-- Evaluate the field-level covariant derivative of `II` on arbitrary `C²` tangent fields.
Only their three values at the base point remain, and the result is exactly the already
constructed continuous trilinear point tensor. -/
theorem CovariantSubmanifoldFieldExtensionData.covariantDerivativeSecondFundamentalAlong_eq_point_of_smooth
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (smoothExtensions : extensions.HasSmoothGaussExtensionRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    {direction first second : (y : M) → TangentSpace I y}
    (hdirection : CMDiffAt 2 (T% direction) x)
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x) :
    extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        direction first second x =
      (projectedCovariantDerivativeSecondFundamentalValueAt
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse x (direction x) (first x) (second x) :
          TangentSpace I' (immersion.toFun x)) := by
  let derivative :=
    extensions.covariantDerivativeSecondFundamentalAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
  let canonicalDirection :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (direction x)
  let canonicalFirst :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (first x)
  let canonicalSecond :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (second x)
  have hcanonicalDirection : CMDiffAt 2 (T% canonicalDirection) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x (direction x)
  have hcanonicalFirst : CMDiffAt 2 (T% canonicalFirst) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x (first x)
  have hcanonicalSecond : CMDiffAt 2 (T% canonicalSecond) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x (second x)
  have directionToCanonical :=
    extensions.covariantDerivativeSecondFundamentalAlong_direction_congr
      immersion ambientLeviCivita x intrinsicRegular
      (hdirection.mdifferentiableAt (by norm_num))
      (hcanonicalDirection.mdifferentiableAt (by norm_num)) hfirst hsecond
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self
        (I := I) x (direction x)).symm
  change derivative direction first second x =
    derivative canonicalDirection first second x at directionToCanonical
  have firstToCanonical :=
    extensions.covariantDerivativeSecondFundamentalAlong_first_congr_of_smooth
      immersion ambientLeviCivita x intrinsicRegular ambientRegular smoothExtensions
      hcanonicalDirection hfirst hcanonicalFirst hsecond
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self
        (I := I) x (first x)).symm
  change derivative canonicalDirection first second x =
    derivative canonicalDirection canonicalFirst second x at firstToCanonical
  have swapSecond :=
    extensions.covariantDerivativeSecondFundamentalAlong_comm_of_smooth
      immersion ambientLeviCivita x intrinsicRegular smoothExtensions
      (hcanonicalDirection.mdifferentiableAt (by norm_num)) hcanonicalFirst hsecond
  change derivative canonicalDirection canonicalFirst second x =
    derivative canonicalDirection second canonicalFirst x at swapSecond
  have secondToCanonical :=
    extensions.covariantDerivativeSecondFundamentalAlong_first_congr_of_smooth
      immersion ambientLeviCivita x intrinsicRegular ambientRegular smoothExtensions
      hcanonicalDirection hsecond hcanonicalSecond hcanonicalFirst
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self
        (I := I) x (second x)).symm
  change derivative canonicalDirection second canonicalFirst x =
    derivative canonicalDirection canonicalSecond canonicalFirst x at secondToCanonical
  have swapCanonical :=
    extensions.covariantDerivativeSecondFundamentalAlong_comm_of_smooth
      immersion ambientLeviCivita x intrinsicRegular smoothExtensions
      (hcanonicalDirection.mdifferentiableAt (by norm_num)) hcanonicalSecond hcanonicalFirst
  change derivative canonicalDirection canonicalSecond canonicalFirst x =
    derivative canonicalDirection canonicalFirst canonicalSecond x at swapCanonical
  change derivative direction first second x =
    derivative canonicalDirection canonicalFirst canonicalSecond x
  exact directionToCanonical.trans <|
    firstToCanonical.trans <| swapSecond.trans <|
      secondToCanonical.trans swapCanonical

/-- The field-level second fundamental form depends only on the two tangent-field values at the
base point and agrees with the canonical kernel-normal construction. -/
theorem CovariantSubmanifoldFieldExtensionData.secondFundamentalFormAlong_eq_point
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M)
    {first second : (y : M) → TangentSpace I y}
    (hsecond : MDiffAt (T% second) x) :
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection first second x =
      (extensions.projectedSecondFundamentalFormAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection
        immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse x
        (first x) (second x) : TangentSpace I' (immersion.toFun x)) := by
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let canonicalFirst :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (first x)
  let canonicalSecond :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (second x)
  have hcanonicalFirst : MDiffAt (T% canonicalFirst) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x (first x)
  have hcanonicalSecond : MDiffAt (T% canonicalSecond) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x (second x)
  have firstToCanonical : secondFundamental first second x =
      secondFundamental canonicalFirst second x := by
    simp [secondFundamental, SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent, canonicalFirst,
      SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self]
  have swapSecond : secondFundamental canonicalFirst second x =
      secondFundamental second canonicalFirst x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      hcanonicalFirst hsecond
  have secondToCanonical : secondFundamental second canonicalFirst x =
      secondFundamental canonicalSecond canonicalFirst x := by
    simp [secondFundamental, SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent, canonicalSecond,
      SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self]
  have swapCanonical : secondFundamental canonicalSecond canonicalFirst x =
      secondFundamental canonicalFirst canonicalSecond x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      hcanonicalSecond hcanonicalFirst
  have canonicalPoint : secondFundamental canonicalFirst canonicalSecond x =
      (extensions.projectedSecondFundamentalFormAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection
        immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse x
        (first x) (second x) : TangentSpace I' (immersion.toFun x)) := by
    rw [CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt_apply]
    simp [secondFundamental, canonicalFirst, canonicalSecond,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent,
      SubmanifoldFieldExtensionData.projectedSecondFundamentalValueAt,
      SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self]
  change secondFundamental first second x = _
  exact firstToCanonical.trans <| swapSecond.trans <|
    secondToCanonical.trans <| swapCanonical.trans canonicalPoint

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- A finite sum passes through the constructed normal connection at a point whenever the chosen
ambient extensions of all summands are differentiable there. -/
theorem CovariantSubmanifoldFieldExtensionData.normalDerivative_sum_normal_at
    [IsManifold I 2 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    {direction : (y : M) → TangentSpace I y}
    (normal : ι → AmbientVectorFieldAlong immersion) {x : M}
    (hnormal : ∀ i, MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension (normal i)))
      (immersion.toFun x)) :
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion splitting ambientConnection direction (∑ i, normal i) x =
      ∑ i, extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion splitting ambientConnection direction (normal i) x := by
  classical
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion splitting ambientConnection
  have hsmoothSum (s : Finset ι) : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (∑ i ∈ s, normal i))) (immersion.toFun x) := by
    rw [map_sum]
    simpa only [Finset.sum_apply] using
      (MDifferentiableAt.sum_section (s := s) fun i _ ↦ hnormal i)
  have hsumDerivative (s : Finset ι) :
      normalDerivative direction (∑ i ∈ s, normal i) x =
        ∑ i ∈ s, normalDerivative direction (normal i) x := by
    induction s using Finset.induction_on with
    | empty =>
        simp [normalDerivative, SubmanifoldFieldExtensionData.normalDerivative,
          SubmanifoldFieldExtensionData.ambientDerivativeAlong]
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        have hadd := extensions.normalDerivative_add_normal_at immersion splitting
          ambientConnection (direction := direction) (hnormal a) (hsmoothSum s)
        change normalDerivative direction (normal a + ∑ i ∈ s, normal i) x =
          normalDerivative direction (normal a) x +
            normalDerivative direction (∑ i ∈ s, normal i) x at hadd
        rw [hadd, ih]
  exact hsumDerivative Finset.univ

/-- Source-level data for the smooth-field CCG25 calculation.  The tangent frame is represented
by genuine `C²` fields whose values give the chosen orthonormal basis and whose induced covariant
derivatives vanish at the base point.  No mean-curvature field or derivative identity is stored. -/
structure SmoothSubmanifoldLaplacianSourceDataAt
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M) where
  tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x)
  normalFrame : OrthonormalBasis κ ℝ
    (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x)
  field : (y : M) → TangentSpace I y
  fieldRegular : CMDiffAt 2 (T% field) x
  geodesicFrame : ι → (y : M) → TangentSpace I y
  geodesicFrameRegular : ∀ i, CMDiffAt 2 (T% (geodesicFrame i)) x
  geodesicFrame_value : ∀ i, geodesicFrame i x = tangentFrame i
  geodesicFrame_covariantDerivative_eq_zero : ∀ i,
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
      (geodesicFrame i) x = 0

/-- The local mean-curvature field obtained by tracing `II` in the geodesic frame. -/
def SmoothSubmanifoldLaplacianSourceDataAt.meanNormalField
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    {immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N)}
    {ambientLeviCivita : LeviCivitaConnection (M := N) I'}
    {extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData}
    {x : M}
    (data : SmoothSubmanifoldLaplacianSourceDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x) :
    AmbientVectorFieldAlong immersion.toSmoothImmersionData :=
  (Fintype.card ι : ℝ)⁻¹ •
    ∑ i, extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection (data.geodesicFrame i) (data.geodesicFrame i)

/-- The chosen ambient extension of the constructed mean-curvature trace is differentiable. -/
theorem SmoothSubmanifoldLaplacianSourceDataAt.meanNormalField_extension_mdifferentiableAt
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    {immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N)}
    {ambientLeviCivita : LeviCivitaConnection (M := N) I'}
    {extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData}
    {x : M}
    (data : SmoothSubmanifoldLaplacianSourceDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x)
    (smoothExtensions : extensions.HasSmoothGaussExtensionRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x) :
    MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension data.meanNormalField))
      (immersion.toFun x) := by
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normal : ι → AmbientVectorFieldAlong immersion.toSmoothImmersionData :=
    fun i ↦ secondFundamental (data.geodesicFrame i) (data.geodesicFrame i)
  have hnormal (i : ι) : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension (normal i)))
      (immersion.toFun x) :=
    smoothExtensions.normalGaussExtension_mdifferentiableAt
      (data.geodesicFrame i) (data.geodesicFrame i)
      (data.geodesicFrameRegular i) (data.geodesicFrameRegular i)
  have hsum : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension (∑ i, normal i)))
      (immersion.toFun x) := by
    rw [map_sum]
    simpa only [Finset.sum_apply] using
      (MDifferentiableAt.sum_section (s := (Finset.univ : Finset ι)) fun i _ ↦ hnormal i)
  change MDiffAt
    (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
      ((Fintype.card ι : ℝ)⁻¹ • ∑ i, normal i))) (immersion.toFun x)
  rw [map_smul]
  exact mdifferentiableAt_const.smul_section hsum

/-- The traced field remains in the actual kernel-normal summand at every source point. -/
theorem SmoothSubmanifoldLaplacianSourceDataAt.meanNormalField_mem
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    {immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N)}
    {ambientLeviCivita : LeviCivitaConnection (M := N) I'}
    {extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData}
    {x : M}
    (data : SmoothSubmanifoldLaplacianSourceDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x)
    (y : M) :
    immersion.orthogonalSplitting.tangentProjection y (data.meanNormalField y) = 0 := by
  have hterm (i : ι) :
      immersion.orthogonalSplitting.tangentProjection y
          (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection (data.geodesicFrame i) (data.geodesicFrame i) y) = 0 :=
    extensions.toSubmanifoldFieldExtensionData.tangentProjection_secondFundamentalFormAlong_eq_zero
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse
        (data.geodesicFrame i) (data.geodesicFrame i) y
  simp only [SmoothSubmanifoldLaplacianSourceDataAt.meanNormalField,
    Pi.smul_apply, Finset.sum_apply, map_smul, map_sum]
  simp only [hterm, Finset.sum_const_zero, smul_zero]

/-- At the base point, the traced geodesic-frame field is the canonical normalized mean
curvature vector. -/
theorem SmoothSubmanifoldLaplacianSourceDataAt.meanNormalField_value
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    {immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N)}
    {ambientLeviCivita : LeviCivitaConnection (M := N) I'}
    {extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData}
    {x : M}
    (data : SmoothSubmanifoldLaplacianSourceDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x) :
    data.meanNormalField x =
      (inducedLeviCivitaSubmanifoldMeanCurvatureAt immersion ambientLeviCivita
        extensions x data.tangentFrame : TangentSpace I' (immersion.toFun x)) := by
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  have hterm (i : ι) :
      secondFundamental (data.geodesicFrame i) (data.geodesicFrame i) x =
        (extensions.projectedSecondFundamentalFormAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection
          immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse x
          (data.tangentFrame i) (data.tangentFrame i) :
            TangentSpace I' (immersion.toFun x)) := by
    simpa only [data.geodesicFrame_value i] using
      (extensions.secondFundamentalFormAlong_eq_point immersion ambientLeviCivita x
        (first := data.geodesicFrame i) (second := data.geodesicFrame i)
        ((data.geodesicFrameRegular i).mdifferentiableAt (by norm_num)))
  simp only [SmoothSubmanifoldLaplacianSourceDataAt.meanNormalField,
    inducedLeviCivitaSubmanifoldMeanCurvatureAt,
    meanCurvatureOfSecondFundamental, Pi.smul_apply, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i]
  simp only [Submodule.coe_smul, Submodule.coe_sum]

/-- Differentiating the constructed trace in the stored source-field direction gives the
tensorial normal derivative of mean curvature.  The two frame-derivative correction terms
vanish because the frame is geodesic at the base point. -/
theorem SmoothSubmanifoldLaplacianSourceDataAt.meanNormalField_derivative
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    {immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N)}
    {ambientLeviCivita : LeviCivitaConnection (M := N) I'}
    {extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData}
    {x : M}
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (smoothExtensions : extensions.HasSmoothGaussExtensionRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (data : SmoothSubmanifoldLaplacianSourceDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x) :
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection data.field data.meanNormalField x =
      (inducedLeviCivitaSubmanifoldMeanNormalDerivativeAt immersion ambientLeviCivita
        extensions x intrinsicRegular extensionRegular data.tangentFrame (data.field x) :
          TangentSpace I' (immersion.toFun x)) := by
  let induced :=
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normal : ι → AmbientVectorFieldAlong immersion.toSmoothImmersionData :=
    fun i ↦ secondFundamental (data.geodesicFrame i) (data.geodesicFrame i)
  let derivativeFrame (i : ι) :=
    covariantDerivativeAlong I induced data.field (data.geodesicFrame i)
  let pointDerivative :=
    projectedCovariantDerivativeSecondFundamentalAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting ambientLeviCivita
      extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x intrinsicRegular extensionRegular
  have hnormal (i : ι) : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension (normal i)))
      (immersion.toFun x) :=
    smoothExtensions.normalGaussExtension_mdifferentiableAt
      (data.geodesicFrame i) (data.geodesicFrame i)
      (data.geodesicFrameRegular i) (data.geodesicFrameRegular i)
  have hsum : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension (∑ i, normal i)))
      (immersion.toFun x) := by
    rw [map_sum]
    simpa only [Finset.sum_apply] using
      (MDifferentiableAt.sum_section (s := (Finset.univ : Finset ι)) fun i _ ↦ hnormal i)
  have hderivativeFrame (i : ι) : MDiffAt (T% (derivativeFrame i)) x :=
    intrinsicRegular data.field (data.geodesicFrame i)
      (data.fieldRegular.mdifferentiableAt (by norm_num)) (data.geodesicFrameRegular i)
  have derivativeFrame_value (i : ι) : derivativeFrame i x = 0 := by
    change induced (data.geodesicFrame i) x (data.field x) = 0
    rw [data.geodesicFrame_covariantDerivative_eq_zero i]
    rfl
  have firstCorrection_zero (i : ι) :
      secondFundamental (derivativeFrame i) (data.geodesicFrame i) x = 0 := by
    simp [secondFundamental, SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent, derivativeFrame_value i]
  have secondCorrection_zero (i : ι) :
      secondFundamental (data.geodesicFrame i) (derivativeFrame i) x = 0 := by
    have comm := extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      ((data.geodesicFrameRegular i).mdifferentiableAt (by norm_num))
      (hderivativeFrame i)
    change secondFundamental (data.geodesicFrame i) (derivativeFrame i) x =
      secondFundamental (derivativeFrame i) (data.geodesicFrame i) x at comm
    exact comm.trans (firstCorrection_zero i)
  have derivativeTerm (i : ι) :
      normalDerivative data.field (normal i) x =
        (pointDerivative (data.field x) (data.tangentFrame i) (data.tangentFrame i) :
          TangentSpace I' (immersion.toFun x)) := by
    have tensorValue :=
      extensions.covariantDerivativeSecondFundamentalAlong_eq_point_of_smooth
        immersion ambientLeviCivita x intrinsicRegular ambientRegular smoothExtensions
        data.fieldRegular (data.geodesicFrameRegular i) (data.geodesicFrameRegular i)
    change
      normalDerivative data.field (normal i) x -
            secondFundamental (derivativeFrame i) (data.geodesicFrame i) x -
          secondFundamental (data.geodesicFrame i) (derivativeFrame i) x =
        (projectedCovariantDerivativeSecondFundamentalValueAt
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
          immersion.hasTangentProjectionLeftInverse x (data.field x)
          (data.geodesicFrame i x) (data.geodesicFrame i x) :
            TangentSpace I' (immersion.toFun x)) at tensorValue
    rw [firstCorrection_zero i, secondCorrection_zero i, sub_zero] at tensorValue
    simp only [sub_zero] at tensorValue
    rw [projectedCovariantDerivativeSecondFundamentalAt_apply]
    simpa only [data.geodesicFrame_value i] using tensorValue
  calc
    normalDerivative data.field data.meanNormalField x =
        (Fintype.card ι : ℝ)⁻¹ •
          normalDerivative data.field (∑ i, normal i) x := by
      change normalDerivative data.field
          ((Fintype.card ι : ℝ)⁻¹ • ∑ i, normal i) x = _
      exact extensions.normalDerivative_smul_normal_at
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection (Fintype.card ι : ℝ)⁻¹ hsum
    _ = (Fintype.card ι : ℝ)⁻¹ •
          ∑ i, normalDerivative data.field (normal i) x := by
      have htrace := extensions.normalDerivative_sum_normal_at
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection (direction := data.field) normal hnormal
      change normalDerivative data.field (∑ i, normal i) x =
        ∑ i, normalDerivative data.field (normal i) x at htrace
      rw [htrace]
    _ = (Fintype.card ι : ℝ)⁻¹ •
          ∑ i, (pointDerivative (data.field x) (data.tangentFrame i)
            (data.tangentFrame i) : TangentSpace I' (immersion.toFun x)) := by
      rw [Finset.sum_congr rfl fun i _ ↦ derivativeTerm i]
    _ = (inducedLeviCivitaSubmanifoldMeanNormalDerivativeAt immersion ambientLeviCivita
          extensions x intrinsicRegular extensionRegular data.tangentFrame (data.field x) :
            TangentSpace I' (immersion.toFun x)) := by
      simp only [inducedLeviCivitaSubmanifoldMeanNormalDerivativeAt, pointDerivative,
        Submodule.coe_smul, Submodule.coe_sum]

/-- Universal smooth-extension regularity discharges the two varying Gauss-field regularity
conditions used in the constructed tangent-Hessian trace. -/
theorem CovariantSubmanifoldFieldExtensionData.HasSmoothGaussExtensionRegularityAt.toVarying
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    {immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N)}
    {ambientLeviCivita : LeviCivitaConnection (M := N) I'}
    {extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData}
    {x : M}
    {intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x}
    {extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x}
    (smoothExtensions : extensions.HasSmoothGaussExtensionRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (data : SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular) :
    data.HasVaryingFieldGaussRegularityAt where
  forward direction :=
    smoothExtensions.normalGaussExtension_mdifferentiableAt
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction)
      data.field
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
        (I := I) x direction)
      data.fieldRegular
  swapped direction :=
    smoothExtensions.normalGaussExtension_mdifferentiableAt
      data.field
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction)
      data.fieldRegular
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
        (I := I) x direction)

/-- Assemble the existing smooth-field Gauss--Weingarten jet from source-level field data and a
geodesic frame.  In particular, the mean-curvature first-jet identity is now filled by the
preceding theorem rather than provided by the caller. -/
def SmoothSubmanifoldLaplacianSourceDataAt.toFieldJetData
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    {immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N)}
    {ambientLeviCivita : LeviCivitaConnection (M := N) I'}
    {extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData}
    {x : M}
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (smoothExtensions : extensions.HasSmoothGaussExtensionRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (data : SmoothSubmanifoldLaplacianSourceDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x) :
    SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular where
  tangentFrame := data.tangentFrame
  normalFrame := data.normalFrame
  field := data.field
  fieldRegular := data.fieldRegular
  ambientFieldRegular :=
    smoothExtensions.tangentExtension_contMDiffAt_two data.field data.fieldRegular
  meanNormalField := data.meanNormalField
  meanNormalField_extension_mdifferentiableAt :=
    data.meanNormalField_extension_mdifferentiableAt smoothExtensions
  meanNormalField_mem := data.meanNormalField_mem
  meanNormalField_value := data.meanNormalField_value
  meanNormalField_derivative :=
    data.meanNormalField_derivative intrinsicRegular ambientRegular extensionRegular
      smoothExtensions

end ManifoldFibers

end

end RiemannianFluids
