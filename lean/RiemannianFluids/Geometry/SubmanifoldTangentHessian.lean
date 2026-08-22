import RiemannianFluids.Geometry.SubmanifoldOperatorBridge

/-!
# Tangent Hessian of an ambient extension along a submanifold

This module closes the last differential step between the CCG25 Gauss--Weingarten jet and the
ambient rough Laplacian.  The source assumes that the tangent field and the local ambient fields
used in the calculation are smooth.  The regularity structure below records exactly the two
varying normal Gauss fields whose chosen ambient extensions must therefore be differentiable.
It contains no Hessian identity or Laplacian formula.
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

/-- Smoothness of the two varying normal Gauss fields used when the Gauss formula is
differentiated for the actual source field.  These are regularity facts about chosen ambient
extensions, not the tangent-Hessian or Laplacian identity that they will prove. -/
structure SmoothSubmanifoldLaplacianFieldJetDataAt.HasVaryingFieldGaussRegularityAt
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
    (data : SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular) : Prop where
  forward : ∀ direction : TangentSpace I x,
    MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction)
          data.field)))
      (immersion.toFun x)
  swapped : ∀ direction : TangentSpace I x,
    MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection data.field
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction))))
      (immersion.toFun x)

/-- Symmetry of the covariant derivative of `II` in its two `II` slots, specialized to the
actual source field and one canonical tangent direction.  The proof differentiates the
field-level symmetry of `II`; the two fields in `HasVaryingFieldGaussRegularityAt` are exactly
the normal extensions consumed by restriction locality. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.covariantDerivativeSecondFundamentalAlong_comm_actual
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
    (data : SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular)
    (varyingRegular : data.HasVaryingFieldGaussRegularityAt)
    (direction : TangentSpace I x) :
    let directionField :=
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
    extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        directionField directionField data.field x =
      extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        directionField data.field directionField x := by
  dsimp only
  let induced :=
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normal := secondFundamental directionField data.field
  let normalSwapped := secondFundamental data.field directionField
  let derivativeDirection :=
    covariantDerivativeAlong I induced directionField directionField
  let derivativeField := covariantDerivativeAlong I induced directionField data.field
  have hdirection : CMDiffAt 2 (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x direction
  have hdirectionNear : ∀ᶠ y in nhds x, MDiffAt (T% directionField) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (hdirection.of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have hfieldNear : ∀ᶠ y in nhds x, MDiffAt (T% data.field) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (data.fieldRegular.of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have normalAgreement : normal =ᶠ[nhds x] normalSwapped := by
    filter_upwards [hdirectionNear, hfieldNear] with y hyDirection hyField
    exact extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      hyDirection hyField
  have normalDerivativeComm :
      normalDerivative directionField normal x =
        normalDerivative directionField normalSwapped x :=
    extensions.normalDerivative_eq_of_eventuallyEq immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita
      (varyingRegular.forward direction) (varyingRegular.swapped direction) normalAgreement
  have hderivativeDirection : MDiffAt (T% derivativeDirection) x :=
    intrinsicRegular directionField directionField
      (hdirection.mdifferentiableAt (by norm_num)) hdirection
  have hderivativeField : MDiffAt (T% derivativeField) x :=
    intrinsicRegular directionField data.field
      (hdirection.mdifferentiableAt (by norm_num)) data.fieldRegular
  have correctionDirectionComm :
      secondFundamental derivativeDirection data.field x =
        secondFundamental data.field derivativeDirection x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      hderivativeDirection (data.fieldRegular.mdifferentiableAt (by norm_num))
  have correctionFieldComm :
      secondFundamental directionField derivativeField x =
        secondFundamental derivativeField directionField x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      (hdirection.mdifferentiableAt (by norm_num)) hderivativeField
  change
    normalDerivative directionField normal x -
          secondFundamental derivativeDirection data.field x -
        secondFundamental directionField derivativeField x =
      normalDerivative directionField normalSwapped x -
          secondFundamental derivativeField directionField x -
        secondFundamental data.field derivativeDirection x
  rw [normalDerivativeComm, correctionDirectionComm, correctionFieldComm]
  abel

/-- The direction slot of the field-level covariant derivative of `II` is pointwise.  Hence an
actual source field used only as that direction agrees with the canonical pointwise tensor at
its value. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.covariantDerivativeSecondFundamentalAlong_actualDirection_eq_point
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
    (data : SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular)
    (direction : TangentSpace I x) :
    let directionField :=
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
    extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        data.field directionField directionField x =
      (projectedCovariantDerivativeSecondFundamentalAt
        immersion.toSmoothImmersionData immersion.orthogonalSplitting ambientLeviCivita
        extensions immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse x intrinsicRegular extensionRegular
        (data.field x) direction direction : TangentSpace I' (immersion.toFun x)) := by
  dsimp only
  rw [projectedCovariantDerivativeSecondFundamentalAt_apply]
  let induced :=
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let canonicalField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (data.field x)
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normal := secondFundamental directionField directionField
  let derivativeActual := covariantDerivativeAlong I induced data.field directionField
  let derivativeCanonical :=
    covariantDerivativeAlong I induced canonicalField directionField
  have hdirectionTwo : CMDiffAt 2 (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x direction
  have hdirection : MDiffAt (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x direction
  have hcanonical : MDiffAt (T% canonicalField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x (data.field x)
  have hderivativeActual : MDiffAt (T% derivativeActual) x :=
    intrinsicRegular data.field directionField
      (data.fieldRegular.mdifferentiableAt (by norm_num)) hdirectionTwo
  have hderivativeCanonical : MDiffAt (T% derivativeCanonical) x :=
    intrinsicRegular canonicalField directionField hcanonical hdirectionTwo
  have derivativeAgreement : derivativeActual x = derivativeCanonical x := by
    simp only [derivativeActual, derivativeCanonical, covariantDerivativeAlong,
      canonicalField, SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self]
  have normalDirectionAgreement :
      normalDerivative data.field normal x = normalDerivative canonicalField normal x := by
    simp only [normalDerivative, SubmanifoldFieldExtensionData.normalDerivative,
      SubmanifoldFieldExtensionData.ambientDerivativeAlong, canonicalField,
      SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self]
  have firstCorrectionAgreement :
      secondFundamental derivativeActual directionField x =
        secondFundamental derivativeCanonical directionField x := by
    simp only [secondFundamental, SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent]
    rw [derivativeAgreement]
  have actualCorrectionComm :
      secondFundamental directionField derivativeActual x =
        secondFundamental derivativeActual directionField x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      hdirection hderivativeActual
  have canonicalCorrectionComm :
      secondFundamental directionField derivativeCanonical x =
        secondFundamental derivativeCanonical directionField x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      hdirection hderivativeCanonical
  change
    normalDerivative data.field normal x -
          secondFundamental derivativeActual directionField x -
        secondFundamental directionField derivativeActual x =
      normalDerivative canonicalField normal x -
          secondFundamental derivativeCanonical directionField x -
        secondFundamental directionField derivativeCanonical x
  rw [normalDirectionAgreement, firstCorrectionAgreement,
    actualCorrectionComm, canonicalCorrectionComm, firstCorrectionAgreement]

/-- Evaluating `II` on a canonical first direction and any differentiable actual tangent field
agrees with the constructed pointwise second fundamental form.  Torsion-free symmetry moves the
actual field into the tensorial direction slot, after which only its value at `x` remains. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.secondFundamentalFormAlong_direction_eq_point
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
    (_data : SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular)
    (direction : TangentSpace I x)
    {field : (y : M) → TangentSpace I y} (hfield : MDiffAt (T% field) x) :
    let directionField :=
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection directionField field x =
      (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse x direction (field x) :
          TangentSpace I' (immersion.toFun x)) := by
  dsimp only
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let pointII :=
    CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x
  have hdirection : MDiffAt (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x direction
  have actualComm : secondFundamental directionField field x =
      secondFundamental field directionField x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      hdirection hfield
  have pointComm : pointII direction (field x) = pointII (field x) direction :=
    extensions.projectedSecondFundamentalFormAt_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      x direction (field x)
  change secondFundamental directionField field x =
    (pointII direction (field x) : TangentSpace I' (immersion.toFun x))
  rw [actualComm, pointComm]
  rw [CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt_apply]
  simp only [secondFundamental,
    SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
    SubmanifoldFieldExtensionData.ambientDerivativeTangent,
    SubmanifoldFieldExtensionData.projectedSecondFundamentalValueAt,
    Subtype.coe_mk, directionField]

/-- The field-level `(∇ᴮ_E II)(E,v)` computed with the actual varying source field equals the
canonical pointwise tensor applied to `v(x)`.  The proof uses differentiated Gauss (Codazzi) to
move the varying field out of the derivative-sensitive slot; curvature and the remaining
direction slot are pointwise, while symmetry returns the two `II` slots to the desired order. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.covariantDerivativeSecondFundamentalAlong_diagonal_actual_eq_point
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
    (data : SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (varyingRegular : data.HasVaryingFieldGaussRegularityAt)
    (direction : TangentSpace I x) :
    let directionField :=
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
    extensions.covariantDerivativeSecondFundamentalAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        directionField directionField data.field x =
      (projectedCovariantDerivativeSecondFundamentalAt
        immersion.toSmoothImmersionData immersion.orthogonalSplitting ambientLeviCivita
        extensions immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse x intrinsicRegular extensionRegular
        direction direction (data.field x) : TangentSpace I' (immersion.toFun x)) := by
  dsimp only
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let ambientDirection :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension directionField
  let ambientField :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field
  let derivative :=
    extensions.covariantDerivativeSecondFundamentalAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
  let pointDerivative :=
    projectedCovariantDerivativeSecondFundamentalAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting ambientLeviCivita
      extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x intrinsicRegular extensionRegular
  let pointCurvature :=
    normalAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      x ambientRegular
  have hdirection : MDiffAt (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x direction
  have hdirectionTwo : CMDiffAt 2 (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x direction
  have hambientDirection : CMDiffAt 2 (T% ambientDirection) (immersion.toFun x) := by
    exact extensionRegular.tangentExtension_contMDiffAt_two direction
  have fieldCodazzi :=
    ambientCurvatureAction_normalProjection_eq_covariantDerivativeSecondFundamental_sub
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
      hdirection (data.fieldRegular.mdifferentiableAt (by norm_num)) hdirectionTwo
      hambientDirection (varyingRegular.swapped direction)
      (extensionRegular.normalGaussExtension_mdifferentiableAt direction direction)
  change
    immersion.orthogonalSplitting.normalProjection x
        (connectionCurvatureAction I' ambientLeviCivita.connection
          ambientDirection ambientField ambientDirection (immersion.toFun x)) =
      derivative directionField data.field directionField x -
        derivative data.field directionField directionField x at fieldCodazzi
  have ambientTensor :=
    connectionCurvatureTensorAt_apply I' ambientLeviCivita.connection
      (immersion.toFun x) ambientRegular
      (hambientDirection.mdifferentiableAt (by norm_num))
      (data.ambientFieldRegular.mdifferentiableAt (by norm_num))
      hambientDirection
  have ambientDirectionValue : ambientDirection (immersion.toFun x) =
      mfderiv I I' immersion.toFun x direction := by
    simpa only [ambientDirection, directionField,
      SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self] using
      (extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees directionField x)
  have ambientFieldValue : ambientField (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (data.field x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees data.field x
  have ambientTensor' :
      connectionCurvatureTensorAt I' ambientLeviCivita.connection (immersion.toFun x)
          ambientRegular
          (mfderiv I I' immersion.toFun x direction)
          (mfderiv I I' immersion.toFun x (data.field x))
          (mfderiv I I' immersion.toFun x direction) =
        connectionCurvatureAction I' ambientLeviCivita.connection
          ambientDirection ambientField ambientDirection (immersion.toFun x) := by
    simpa only [ambientDirectionValue, ambientField,
      extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees] using ambientTensor
  have curvatureAgreement :
      immersion.orthogonalSplitting.normalProjection x
          (connectionCurvatureAction I' ambientLeviCivita.connection
            ambientDirection ambientField ambientDirection (immersion.toFun x)) =
        (pointCurvature direction (data.field x) direction :
          TangentSpace I' (immersion.toFun x)) := by
    rw [normalAmbientConnectionCurvatureAt_coe]
    rw [ambientTensor']
  have actualSymmetry :=
    data.covariantDerivativeSecondFundamentalAlong_comm_actual varyingRegular direction
  change derivative directionField directionField data.field x =
      derivative directionField data.field directionField x at actualSymmetry
  have actualDirection :=
    data.covariantDerivativeSecondFundamentalAlong_actualDirection_eq_point direction
  change derivative data.field directionField directionField x =
      (pointDerivative (data.field x) direction direction :
        TangentSpace I' (immersion.toFun x)) at actualDirection
  have pointCodazzi := data.hasCodazziEquation ambientRegular
    direction (data.field x) direction
  change pointCurvature direction (data.field x) direction =
      pointDerivative direction (data.field x) direction -
        pointDerivative (data.field x) direction direction at pointCodazzi
  have pointSymmetry := data.isSymmetricDerivative ambientRegular
    direction direction (data.field x)
  change pointDerivative direction direction (data.field x) =
      pointDerivative direction (data.field x) direction at pointSymmetry
  have pointCodazziCoe := congrArg
    (fun normal : SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x ↦
        (normal : TangentSpace I' (immersion.toFun x))) pointCodazzi
  have pointSymmetryCoe := congrArg
    (fun normal : SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x ↦
        (normal : TangentSpace I' (immersion.toFun x))) pointSymmetry
  change derivative directionField directionField data.field x =
    (pointDerivative direction direction (data.field x) :
      TangentSpace I' (immersion.toFun x))
  rw [curvatureAgreement] at fieldCodazzi
  rw [actualDirection] at fieldCodazzi
  have fieldSolved := (eq_sub_iff_add_eq.mp fieldCodazzi).symm
  have pointSolved := eq_sub_iff_add_eq.mp pointCodazziCoe
  rw [actualSymmetry, pointSymmetryCoe]
  exact fieldSolved.trans pointSolved

/-- The shape term in the twice-differentiated Gauss formula is the Riesz shape operator of the
constructed pointwise second fundamental form, even though its normal field is `II(E,v)` for the
actual varying field.  Weingarten duality makes the shape value depend only on that normal
field's value at the base point. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.shapeOperatorAlong_actualGauss_eq_point
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
    (data : SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular)
    (varyingRegular : data.HasVaryingFieldGaussRegularityAt)
    (direction : TangentSpace I x) :
    let directionField :=
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
    let normal :=
      extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection directionField data.field
    extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection directionField normal x =
      shapeOperatorOfSecondFundamental
        (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
          immersion.hasTangentProjectionLeftInverse x)
        (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
          immersion.hasTangentProjectionLeftInverse x direction (data.field x)) direction := by
  dsimp only
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normal := secondFundamental directionField data.field
  let pointII :=
    CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x
  have hdirection : MDiffAt (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x direction
  have actualSecondFundamentalComm :
      secondFundamental directionField data.field x =
        secondFundamental data.field directionField x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      hdirection (data.fieldRegular.mdifferentiableAt (by norm_num))
  have pointSecondFundamentalComm :
      pointII direction (data.field x) = pointII (data.field x) direction :=
    extensions.projectedSecondFundamentalFormAt_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree
      (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
      x direction (data.field x)
  have normalValue : normal x =
      (pointII direction (data.field x) : TangentSpace I' (immersion.toFun x)) := by
    change secondFundamental directionField data.field x = _
    rw [actualSecondFundamentalComm, pointSecondFundamentalComm]
    rw [CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt_apply]
    simp only [secondFundamental,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent,
      SubmanifoldFieldExtensionData.projectedSecondFundamentalValueAt,
      Subtype.coe_mk, directionField]
  have normalOrthogonal : ∀ y tangent,
      inner ℝ (normal y) (mfderiv I I' immersion.toFun y tangent) = 0 := by
    intro y tangent
    exact immersion.hasOrthogonalNormalProjection y
      (extensions.toSubmanifoldFieldExtensionData.ambientDerivativeTangent
        immersion.toSmoothImmersionData ambientLeviCivita.connection
        directionField data.field y) tangent
  apply ext_inner_right ℝ
  intro test
  let testField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x test
  have shapePairing := shapeOperatorAlong_inner_secondFundamentalFormAlong
    immersion ambientLeviCivita extensions normal
    (x := x) (hfirst := hdirection)
    (htest := SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x test)
    (hnormalExtension := varyingRegular.forward direction) normalOrthogonal
  change inner ℝ
      (extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection directionField normal x) test = _
  have shapePairing' :
      inner ℝ
          (extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection directionField normal x) test =
        inner ℝ (secondFundamental directionField testField x) (normal x) := by
    simpa only [testField,
      SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self] using shapePairing
  have testValue : secondFundamental directionField testField x =
      (pointII direction test : TangentSpace I' (immersion.toFun x)) := by
    rw [CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt_apply]
    simp only [secondFundamental,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent,
      SubmanifoldFieldExtensionData.projectedSecondFundamentalValueAt,
      Subtype.coe_mk, directionField, testField,
      SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self]
  rw [shapePairing']
  rw [shapeOperatorOfSecondFundamental_inner]
  rw [normalValue, testValue]
  rfl

/-- One diagonal tangent restriction of the ambient covariant Hessian, before contracting the
tangent frame.  This is the twice-differentiated Gauss formula with its correction direction
split once more by Gauss. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.ambientTangentHessianDiagonal_eq_rawGauss
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
    (data : SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (varyingRegular : data.HasVaryingFieldGaussRegularityAt)
    (direction : TangentSpace I x) :
    let induced :=
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
    let directionField :=
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
    let intrinsicDerivative := covariantDerivativeAlong I induced directionField data.field
    let intrinsicDirection := covariantDerivativeAlong I induced directionField directionField
    let normal :=
      extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection directionField data.field
    secondCovariantDerivativeAt I' ambientLeviCivita.connection (immersion.toFun x)
        ambientRegular
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
        data.ambientFieldRegular
        (mfderiv I I' immersion.toFun x direction)
        (mfderiv I I' immersion.toFun x direction) =
      mfderiv I I' immersion.toFun x
          (secondCovariantDerivativeAt I induced x intrinsicRegular data.field
              data.fieldRegular direction direction -
            extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
              immersion.toSmoothImmersionData immersion.orthogonalSplitting
              ambientLeviCivita.connection directionField normal x) +
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection directionField intrinsicDerivative x +
          extensions.toSubmanifoldFieldExtensionData.normalDerivative
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection directionField normal x -
          extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection intrinsicDirection data.field x) -
        ambientNormalDerivativeOfTangentFieldAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection extensions x data.field
          (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
            immersion.hasTangentProjectionLeftInverse x direction direction) := by
  dsimp only
  let induced :=
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let ambientDirection :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension directionField
  let ambientField :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field
  let intrinsicDerivative := covariantDerivativeAlong I induced directionField data.field
  let intrinsicDirection := covariantDerivativeAlong I induced directionField directionField
  let normal :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection directionField data.field
  let diagonalNormal :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection directionField directionField
  let tangentDerivativeExtension :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension intrinsicDerivative
  let normalExtension := extensions.toSubmanifoldFieldExtensionData.alongExtension normal
  let comparison := tangentDerivativeExtension + normalExtension
  let ambientDerived :=
    covariantDerivativeAlong I' ambientLeviCivita.connection ambientDirection ambientField
  have hdirection : CMDiffAt 2 (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x direction
  have hambientDirection : CMDiffAt 2 (T% ambientDirection) (immersion.toFun x) := by
    exact extensionRegular.tangentExtension_contMDiffAt_two direction
  have hintrinsicDerivative : MDiffAt (T% intrinsicDerivative) x :=
    intrinsicRegular directionField data.field
      (hdirection.mdifferentiableAt (by norm_num)) data.fieldRegular
  have htangentDerivativeExtension : MDiffAt
      (T% tangentDerivativeExtension) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hintrinsicDerivative
  have hnormalExtension : MDiffAt (T% normalExtension) (immersion.toFun x) := by
    exact varyingRegular.forward direction
  have hcomparison : MDiffAt (T% comparison) (immersion.toFun x) :=
    mdifferentiableAt_add_section htangentDerivativeExtension hnormalExtension
  have hambientDerived : MDiffAt (T% ambientDerived) (immersion.toFun x) :=
    ambientRegular ambientDirection ambientField
      (hambientDirection.mdifferentiableAt (by norm_num)) data.ambientFieldRegular
  have ambientDerived_agrees (y : M) :
      ambientDerived (immersion.toFun y) = comparison (immersion.toFun y) := by
    dsimp only [ambientDerived, comparison, tangentDerivativeExtension, normalExtension,
      intrinsicDerivative, normal, ambientDirection, ambientField, covariantDerivativeAlong]
    simp only [Pi.add_apply]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees directionField y]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees
      (covariantDerivativeAlong I induced directionField data.field) y]
    rw [extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees]
    exact extensions.ambientDerivativeTangent_eq_gauss_inducedCovariantDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse directionField data.field y
  have hImmersion : MDiffAt immersion.toFun x :=
    immersion.contMDiff.mdifferentiableAt (by simp)
  have outerComparison := ambientLeviCivita.eq_on_mfderiv_of_comp_eq I'
    hImmersion hambientDerived hcomparison ambientDerived_agrees direction
  have ambientDirectionValue : ambientDirection (immersion.toFun x) =
      mfderiv I I' immersion.toFun x direction := by
    simpa [ambientDirection, directionField] using
      (extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees directionField x)
  have firstTerm :
      ambientLeviCivita.connection ambientDerived (immersion.toFun x)
          (mfderiv I I' immersion.toFun x direction) =
        mfderiv I I' immersion.toFun x (induced intrinsicDerivative x direction) +
          extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection directionField intrinsicDerivative x -
          mfderiv I I' immersion.toFun x
            (extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
              immersion.toSmoothImmersionData immersion.orthogonalSplitting
              ambientLeviCivita.connection directionField normal x) +
          extensions.toSubmanifoldFieldExtensionData.normalDerivative
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection directionField normal x := by
    rw [outerComparison]
    change ambientLeviCivita.connection
        (tangentDerivativeExtension + normalExtension) (immersion.toFun x)
          (mfderiv I I' immersion.toFun x direction) = _
    rw [DFunLike.congr_fun
      (ambientLeviCivita.connection.isCovariantDerivativeOn.add
        htangentDerivativeExtension hnormalExtension)]
    simp only [add_apply]
    have tangentGauss :=
      extensions.ambientDerivativeTangent_eq_gauss_inducedCovariantDerivative
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse directionField intrinsicDerivative x
    have normalWeingarten :=
      extensions.toSubmanifoldFieldExtensionData.ambientDerivativeAlong_eq_weingarten
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
        directionField normal x
    change
      ambientLeviCivita.connection tangentDerivativeExtension (immersion.toFun x)
          (mfderiv I I' immersion.toFun x direction) +
        ambientLeviCivita.connection normalExtension (immersion.toFun x)
          (mfderiv I I' immersion.toFun x direction) = _
    change _ =
      mfderiv I I' immersion.toFun x
          (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
            immersion.orthogonalSplitting ambientLeviCivita.connection
            immersion.hasTangentProjectionLeftInverse intrinsicDerivative x direction) +
        extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection directionField intrinsicDerivative x -
          mfderiv I I' immersion.toFun x
            (extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
              immersion.toSmoothImmersionData immersion.orthogonalSplitting
              ambientLeviCivita.connection directionField normal x) +
        extensions.toSubmanifoldFieldExtensionData.normalDerivative
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection directionField normal x
    have tangentGauss' :
        ambientLeviCivita.connection tangentDerivativeExtension (immersion.toFun x)
            (mfderiv I I' immersion.toFun x direction) =
          mfderiv I I' immersion.toFun x
              (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
                immersion.orthogonalSplitting ambientLeviCivita.connection
                immersion.hasTangentProjectionLeftInverse intrinsicDerivative x direction) +
            extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
              immersion.toSmoothImmersionData immersion.orthogonalSplitting
              ambientLeviCivita.connection directionField intrinsicDerivative x := by
      simpa only [tangentDerivativeExtension, directionField,
        SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self,
        SubmanifoldFieldExtensionData.ambientDerivativeTangent] using tangentGauss
    have normalWeingarten' :
        ambientLeviCivita.connection normalExtension (immersion.toFun x)
            (mfderiv I I' immersion.toFun x direction) =
          -(mfderiv I I' immersion.toFun x
              (extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
                immersion.toSmoothImmersionData immersion.orthogonalSplitting
                ambientLeviCivita.connection directionField normal x)) +
            extensions.toSubmanifoldFieldExtensionData.normalDerivative
              immersion.toSmoothImmersionData immersion.orthogonalSplitting
              ambientLeviCivita.connection directionField normal x := by
      simpa only [normalExtension, directionField,
        SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self,
        SubmanifoldFieldExtensionData.ambientDerivativeAlong] using normalWeingarten
    rw [tangentGauss', normalWeingarten']
    module
  have directionGauss :=
    extensions.ambientDerivativeTangent_eq_gauss_inducedCovariantDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse directionField directionField x
  have correctionTerm :
      ambientLeviCivita.connection ambientField (immersion.toFun x)
          (ambientLeviCivita.connection ambientDirection (immersion.toFun x)
            (ambientDirection (immersion.toFun x))) =
        mfderiv I I' immersion.toFun x (induced data.field x (intrinsicDirection x)) +
          extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection intrinsicDirection data.field x +
          ambientNormalDerivativeOfTangentFieldAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting ambientLeviCivita.connection extensions x data.field
            (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
              immersion.toSmoothImmersionData immersion.orthogonalSplitting
              ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
              immersion.hasTangentProjectionLeftInverse x direction direction) := by
    have directionGauss' :
        ambientLeviCivita.connection ambientDirection (immersion.toFun x)
            (ambientDirection (immersion.toFun x)) =
          mfderiv I I' immersion.toFun x (intrinsicDirection x) + diagonalNormal x := by
      simpa [induced,
        CovariantSubmanifoldFieldExtensionData.inducedLeviCivitaConnection,
        CovariantSubmanifoldFieldExtensionData.inducedLeviCivitaConnectionOfBracketCompatibility,
        ambientDirectionValue, ambientDirection, intrinsicDirection, diagonalNormal,
        directionField, covariantDerivativeAlong,
        SubmanifoldFieldExtensionData.ambientDerivativeTangent] using
        directionGauss
    rw [directionGauss', map_add]
    have tangentGauss :=
      extensions.ambientDerivativeTangent_eq_gauss_inducedCovariantDerivative
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse intrinsicDirection data.field x
    have diagonalNormalValue : diagonalNormal x =
        (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
          immersion.hasTangentProjectionLeftInverse x direction direction :
            TangentSpace I' (immersion.toFun x)) := by
      change immersion.orthogonalSplitting.normalProjection x
          (extensions.toSubmanifoldFieldExtensionData.ambientDerivativeTangent
            immersion.toSmoothImmersionData ambientLeviCivita.connection
            directionField directionField x) = _
      rw [CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt_apply]
      simp only [SubmanifoldFieldExtensionData.projectedSecondFundamentalValueAt,
        Subtype.coe_mk, directionField,
        SubmanifoldFieldExtensionData.ambientDerivativeTangent,
        SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self]
    rw [diagonalNormalValue]
    simpa [induced,
      CovariantSubmanifoldFieldExtensionData.inducedLeviCivitaConnection,
      CovariantSubmanifoldFieldExtensionData.inducedLeviCivitaConnectionOfBracketCompatibility,
      ambientField, intrinsicDirection,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent] using
      congrArg₂ (· + ·) tangentGauss
        (ambientNormalDerivativeOfTangentFieldAt_apply
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection extensions x data.field
          (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
            immersion.hasTangentProjectionLeftInverse x direction direction)).symm
  have ambientHessianApply :
      secondCovariantDerivativeAt I' ambientLeviCivita.connection (immersion.toFun x)
          ambientRegular ambientField data.ambientFieldRegular
          (mfderiv I I' immersion.toFun x direction)
          (mfderiv I I' immersion.toFun x direction) =
        secondCovariantDerivativeAlong I' ambientLeviCivita.connection
          ambientDirection ambientDirection ambientField (immersion.toFun x) := by
    rw [← ambientDirectionValue]
    exact secondCovariantDerivativeAt_apply I' ambientLeviCivita.connection
      (immersion.toFun x) ambientRegular ambientField data.ambientFieldRegular
      (hambientDirection.mdifferentiableAt (by norm_num))
      (hambientDirection.mdifferentiableAt (by norm_num))
  rw [ambientHessianApply]
  simp only [secondCovariantDerivativeAlong_apply]
  rw [ambientDirectionValue, firstTerm]
  have correctionTerm' :
      ambientLeviCivita.connection ambientField (immersion.toFun x)
          (ambientLeviCivita.connection ambientDirection (immersion.toFun x)
            (mfderiv I I' immersion.toFun x direction)) =
        mfderiv I I' immersion.toFun x (induced data.field x (intrinsicDirection x)) +
          extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection intrinsicDirection data.field x +
          ambientNormalDerivativeOfTangentFieldAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting ambientLeviCivita.connection extensions x data.field
            (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
              immersion.toSmoothImmersionData immersion.orthogonalSplitting
              ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
              immersion.hasTangentProjectionLeftInverse x direction direction) := by
    rw [← ambientDirectionValue]
    exact correctionTerm
  rw [correctionTerm']
  have intrinsicHessianApply :
      secondCovariantDerivativeAt I induced x intrinsicRegular data.field data.fieldRegular
          direction direction =
        secondCovariantDerivativeAlong I induced directionField directionField data.field x := by
    simpa [directionField] using
      (secondCovariantDerivativeAt_apply I induced x intrinsicRegular data.field
        data.fieldRegular (hdirection.mdifferentiableAt (by norm_num))
        (hdirection.mdifferentiableAt (by norm_num)))
  rw [intrinsicHessianApply]
  simp only [secondCovariantDerivativeAlong_apply, intrinsicDerivative, intrinsicDirection]
  simp only [map_sub]
  simp only [directionField,
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self, normal,
    covariantDerivativeAlong]
  module

/-- The diagonal ambient tangent Hessian in the pointwise tensors stored by the differentiated
Gauss--Weingarten jet.  The normal summand is
`(∇ᴮ_E II)(E,v) + 2 II(E,∇_E v)`; it is written additively so its finite trace matches
`normalDerivativeTrace + secondFundamentalDerivativeTrace` definitionally. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.ambientTangentHessianDiagonal_eq_pointGauss
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
    (data : SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (varyingRegular : data.HasVaryingFieldGaussRegularityAt)
    (direction : TangentSpace I x) :
    let induced :=
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
    let pointII :=
      CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse x
    let pointDerivative :=
      projectedCovariantDerivativeSecondFundamentalAt
        immersion.toSmoothImmersionData immersion.orthogonalSplitting ambientLeviCivita
        extensions immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse x intrinsicRegular extensionRegular
    secondCovariantDerivativeAt I' ambientLeviCivita.connection (immersion.toFun x)
        ambientRegular
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
        data.ambientFieldRegular
        (mfderiv I I' immersion.toFun x direction)
        (mfderiv I I' immersion.toFun x direction) =
      mfderiv I I' immersion.toFun x
          (secondCovariantDerivativeAt I induced x intrinsicRegular data.field
              data.fieldRegular direction direction -
            shapeOperatorOfSecondFundamental pointII
              (pointII direction (data.field x)) direction) +
        ((pointDerivative direction direction (data.field x) +
            pointII direction (induced data.field x direction) +
            pointII direction (induced data.field x direction) :
          SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x) : TangentSpace I' (immersion.toFun x)) -
        ambientNormalDerivativeOfTangentFieldAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection extensions x data.field
          (pointII direction direction) := by
  dsimp only
  let induced :=
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let intrinsicDerivative := covariantDerivativeAlong I induced directionField data.field
  let intrinsicDirection := covariantDerivativeAlong I induced directionField directionField
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normal := secondFundamental directionField data.field
  let pointII :=
    CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x
  let pointDerivative :=
    projectedCovariantDerivativeSecondFundamentalAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting ambientLeviCivita
      extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x intrinsicRegular extensionRegular
  rw [data.ambientTangentHessianDiagonal_eq_rawGauss ambientRegular varyingRegular direction]
  have shapeEquality := data.shapeOperatorAlong_actualGauss_eq_point
    varyingRegular direction
  change
    extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection directionField normal x =
      shapeOperatorOfSecondFundamental pointII (pointII direction (data.field x)) direction
      at shapeEquality
  have derivativePoint :=
    data.covariantDerivativeSecondFundamentalAlong_diagonal_actual_eq_point
      ambientRegular varyingRegular direction
  change
    normalDerivative directionField normal x -
          secondFundamental intrinsicDirection data.field x -
        secondFundamental directionField intrinsicDerivative x =
      (pointDerivative direction direction (data.field x) :
        TangentSpace I' (immersion.toFun x)) at derivativePoint
  have hintrinsicDerivative : MDiffAt (T% intrinsicDerivative) x :=
    intrinsicRegular directionField data.field
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
        (I := I) x direction) data.fieldRegular
  have secondFundamentalDerivativePoint :=
    data.secondFundamentalFormAlong_direction_eq_point direction hintrinsicDerivative
  change secondFundamental directionField intrinsicDerivative x =
      (pointII direction (intrinsicDerivative x) :
        TangentSpace I' (immersion.toFun x)) at secondFundamentalDerivativePoint
  have intrinsicDerivativeValue : intrinsicDerivative x =
      induced data.field x direction := by
    simp only [intrinsicDerivative, covariantDerivativeAlong, directionField,
      SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self]
  change
    mfderiv I I' immersion.toFun x
          (secondCovariantDerivativeAt I induced x intrinsicRegular data.field
              data.fieldRegular direction direction -
            extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
              immersion.toSmoothImmersionData immersion.orthogonalSplitting
              ambientLeviCivita.connection directionField normal x) +
        (secondFundamental directionField intrinsicDerivative x +
            normalDerivative directionField normal x -
          secondFundamental intrinsicDirection data.field x) -
      ambientNormalDerivativeOfTangentFieldAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection extensions x data.field
        (pointII direction direction) =
      mfderiv I I' immersion.toFun x
          (secondCovariantDerivativeAt I induced x intrinsicRegular data.field
              data.fieldRegular direction direction -
            shapeOperatorOfSecondFundamental pointII
              (pointII direction (data.field x)) direction) +
        ((pointDerivative direction direction (data.field x) +
            pointII direction (induced data.field x direction) +
            pointII direction (induced data.field x direction) :
          SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x) : TangentSpace I' (immersion.toFun x)) -
      ambientNormalDerivativeOfTangentFieldAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection extensions x data.field
        (pointII direction direction)
  rw [shapeEquality, secondFundamentalDerivativePoint, intrinsicDerivativeValue]
  simp only [Submodule.coe_add]
  rw [← derivativePoint]
  rw [secondFundamentalDerivativePoint, intrinsicDerivativeValue]
  module

/-- The tangent trace bridge required by the constructed ambient rough Laplacian follows from
the twice-differentiated Gauss formula and smoothness of the two varying normal Gauss fields.
This discharges `HasAmbientTangentHessianTraceGaussAt` without assuming any Hessian or Laplacian
identity. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.hasAmbientTangentHessianTraceGaussAt
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
    (data : SmoothSubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (varyingRegular : data.HasVaryingFieldGaussRegularityAt) :
    data.HasAmbientTangentHessianTraceGaussAt ambientRegular := by
  rw [SmoothSubmanifoldLaplacianFieldJetDataAt.HasAmbientTangentHessianTraceGaussAt]
  let induced :=
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
  let pointII :=
    CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x
  let pointDerivative :=
    projectedCovariantDerivativeSecondFundamentalAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting ambientLeviCivita
      extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x intrinsicRegular extensionRegular
  let ambientNormalDerivative :=
    ambientNormalDerivativeOfTangentFieldAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection extensions x data.field
  have diagonal (i : ι) :
      secondCovariantDerivativeAt I' ambientLeviCivita.connection (immersion.toFun x)
          ambientRegular
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
          data.ambientFieldRegular
          (mfderiv I I' immersion.toFun x (data.tangentFrame i))
          (mfderiv I I' immersion.toFun x (data.tangentFrame i)) =
        mfderiv I I' immersion.toFun x
            (secondCovariantDerivativeAt I induced x intrinsicRegular data.field
                data.fieldRegular (data.tangentFrame i) (data.tangentFrame i) -
              shapeOperatorOfSecondFundamental pointII
                (pointII (data.tangentFrame i) (data.field x)) (data.tangentFrame i)) +
          ((pointDerivative (data.tangentFrame i) (data.tangentFrame i) (data.field x) +
              pointII (data.tangentFrame i)
                (induced data.field x (data.tangentFrame i)) +
              pointII (data.tangentFrame i)
                (induced data.field x (data.tangentFrame i)) :
            SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
              immersion.orthogonalSplitting x) : TangentSpace I' (immersion.toFun x)) -
          ambientNormalDerivative (pointII (data.tangentFrame i) (data.tangentFrame i)) := by
    exact data.ambientTangentHessianDiagonal_eq_pointGauss
      ambientRegular varyingRegular (data.tangentFrame i)
  have diagonalSum :
      (∑ i, secondCovariantDerivativeAt I' ambientLeviCivita.connection
          (immersion.toFun x) ambientRegular
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
          data.ambientFieldRegular
          (mfderiv I I' immersion.toFun x (data.tangentFrame i))
          (mfderiv I I' immersion.toFun x (data.tangentFrame i))) =
        ∑ i,
          (mfderiv I I' immersion.toFun x
              (secondCovariantDerivativeAt I induced x intrinsicRegular data.field
                  data.fieldRegular (data.tangentFrame i) (data.tangentFrame i) -
                shapeOperatorOfSecondFundamental pointII
                  (pointII (data.tangentFrame i) (data.field x)) (data.tangentFrame i)) +
            ((pointDerivative (data.tangentFrame i) (data.tangentFrame i) (data.field x) +
                pointII (data.tangentFrame i)
                  (induced data.field x (data.tangentFrame i)) +
                pointII (data.tangentFrame i)
                  (induced data.field x (data.tangentFrame i)) :
              SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
                immersion.orthogonalSplitting x) : TangentSpace I' (immersion.toFun x)) -
            ambientNormalDerivative
              (pointII (data.tangentFrame i) (data.tangentFrame i))) := by
    apply Finset.sum_congr rfl
    intro i _
    exact diagonal i
  rw [diagonalSum]
  change
    -∑ i,
        (mfderiv I I' immersion.toFun x
            (secondCovariantDerivativeAt I induced x intrinsicRegular data.field
                data.fieldRegular (data.tangentFrame i) (data.tangentFrame i) -
              shapeOperatorOfSecondFundamental pointII
                (pointII (data.tangentFrame i) (data.field x)) (data.tangentFrame i)) +
          ((pointDerivative (data.tangentFrame i) (data.tangentFrame i) (data.field x) +
              pointII (data.tangentFrame i)
                (induced data.field x (data.tangentFrame i)) +
              pointII (data.tangentFrame i)
                (induced data.field x (data.tangentFrame i)) :
            SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
              immersion.orthogonalSplitting x) : TangentSpace I' (immersion.toFun x)) -
          ambientNormalDerivative
            (pointII (data.tangentFrame i) (data.tangentFrame i))) =
      mfderiv I I' immersion.toFun x
          (-∑ i, secondCovariantDerivativeAt I induced x intrinsicRegular data.field
              data.fieldRegular (data.tangentFrame i) (data.tangentFrame i) +
            ∑ i, shapeOperatorOfSecondFundamental pointII
              (pointII (data.tangentFrame i) (data.field x)) (data.tangentFrame i)) +
        ((-(
            (∑ i, pointII (data.tangentFrame i)
              (induced data.field x (data.tangentFrame i))) +
            ∑ i,
              (pointDerivative (data.tangentFrame i) (data.tangentFrame i) (data.field x) +
                pointII (data.tangentFrame i)
                  (induced data.field x (data.tangentFrame i)))) :
          SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x) : TangentSpace I' (immersion.toFun x)) +
        ambientNormalDerivative
          (∑ i, pointII (data.tangentFrame i) (data.tangentFrame i))
  simp only [Submodule.coe_neg, Submodule.coe_add, Submodule.coe_sum, map_sub, map_add,
    map_neg, map_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  module

end ManifoldFibers

end

end RiemannianFluids
