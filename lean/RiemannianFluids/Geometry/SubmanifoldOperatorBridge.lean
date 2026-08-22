import RiemannianFluids.Geometry.SubmanifoldHodge
import RiemannianFluids.Geometry.LeviCivitaCurvature
import RiemannianFluids.Operators.ConstructedHodge

/-!
# Constructed-operator bridge for submanifold Gauss traces

`Geometry.SubmanifoldLaplacian` and `Geometry.SubmanifoldHodge` derive the CCG25 formulas from
one differentiated Gauss--Weingarten jet.  This module identifies those jet values with the
repository's independently constructed rough and Hodge operators wherever the currently
available regularity is sufficient.

The intrinsic rough value is identified without an extra hypothesis: the jet stores the actual
covariant Hessian of its source field and its frame trace is the basis expansion of
`roughLaplacianAt`.  The normal part of the ambient trace is also identified with the actual
ambient covariant Hessian.  This module exposes the exact remaining tangent-trace proposition so
that no pointwise jet identity is silently advertised as an equality of constructed differential
operators.  `Geometry.SubmanifoldTangentHessian` proves that proposition by differentiating Gauss
for the actual varying source field.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

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

/-- The contribution of the tangent-frame ambient Hessian after twice differentiating the Gauss
splitting.  The full jet value subtracts the normal Hessian trace from this expression. -/
def PointwiseBochnerGaussJet.tangentAmbientBochner
    {Tangent Normal Ambient : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [FiniteDimensional ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [FiniteDimensional ℝ Normal]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.tangentLift
      (-jet.intrinsicSecondTrace +
        ∑ i,
          shapeOperatorOfSecondFundamental jet.secondFundamental
            (jet.secondFundamental (jet.tangentFrame i) jet.field)
            (jet.tangentFrame i)) +
    jet.normalLift
      (-(jet.secondFundamentalDerivativeTrace + jet.normalDerivativeTrace)) +
    jet.ambientNormalDerivative jet.secondFundamentalTrace

/-- The full ambient Bochner jet is its differentiated tangent trace minus the covariant normal
Hessian trace, written in the paper's raw-iteration-plus-acceleration notation. -/
theorem PointwiseBochnerGaussJet.ambientBochner_eq_tangentAmbientBochner_sub_normal
    {Tangent Normal Ambient : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [FiniteDimensional ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [FiniteDimensional ℝ Normal]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    jet.ambientBochner =
      jet.tangentAmbientBochner - jet.normalSecondDerivativeTrace +
        jet.normalAccelerationDerivativeTrace :=
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [CompleteSpace E'] in
/-- Expanding the ambient rough Laplacian in the immersion's adapted frame splits its trace into
the tangent and kernel-normal diagonal Hessian sums. -/
theorem SmoothIsometricImmersionData.roughLaplacianAt_eq_neg_tangent_sum_sub_normal_sum
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x))
    (field : (y : N) → TangentSpace I' y)
    (fieldRegular : CMDiffAt 2 (T% field) (immersion.toFun x)) :
    roughLaplacianAt I' ambientConnection (immersion.toFun x) ambientRegular
        field fieldRegular =
      -∑ i, secondCovariantDerivativeAt I' ambientConnection (immersion.toFun x)
          ambientRegular field fieldRegular
          (mfderiv I I' immersion.toFun x (tangentFrame i))
          (mfderiv I I' immersion.toFun x (tangentFrame i)) -
        ∑ l, secondCovariantDerivativeAt I' ambientConnection (immersion.toFun x)
          ambientRegular field fieldRegular
          (normalFrame l : TangentSpace I' (immersion.toFun x))
          (normalFrame l : TangentSpace I' (immersion.toFun x)) := by
  rw [roughLaplacianAt_eq_neg_sum I' ambientConnection (immersion.toFun x) ambientRegular
    field fieldRegular
    (immersion.adaptedAmbientOrthonormalBasisAt x tangentFrame normalFrame),
    Fintype.sum_sum_type]
  simp only [SmoothIsometricImmersionData.adaptedAmbientOrthonormalBasisAt_apply_inl,
    SmoothIsometricImmersionData.adaptedAmbientOrthonormalBasisAt_apply_inr]
  module

/-- The intrinsic Bochner value of the smooth submanifold jet is exactly the differential of
the immersion applied to the independently constructed intrinsic rough Laplacian. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.intrinsicBochner_eq_mfderiv_roughLaplacianAt
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
      ambientLeviCivita.connection (immersion.toFun x)) :
    (data.toDifferentiatedGaussWeingartenJet ambientRegular
      ).toPointwiseBochnerGaussJet.intrinsicBochner =
      mfderiv I I' immersion.toFun x
        (roughLaplacianAt I
          (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
          x intrinsicRegular data.field data.fieldRegular) := by
  rw [roughLaplacianAt_eq_neg_sum I
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
    x intrinsicRegular data.field data.fieldRegular data.tangentFrame]
  rfl

/-- In the smooth-field jet, subtracting the normal-frame acceleration trace from the stored raw
normal iteration leaves exactly the normal restriction of the ambient covariant Hessian. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.normalSecondDerivativeTrace_sub_acceleration_eq
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
      ambientLeviCivita.connection (immersion.toFun x)) :
    let jet := (data.toDifferentiatedGaussWeingartenJet ambientRegular
      ).toPointwiseBochnerGaussJet
    jet.normalSecondDerivativeTrace - jet.normalAccelerationDerivativeTrace =
      ∑ l, secondCovariantDerivativeAt I' ambientLeviCivita.connection
        (immersion.toFun x) ambientRegular
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
        data.ambientFieldRegular
        (data.normalFrame l : TangentSpace I' (immersion.toFun x))
        (data.normalFrame l : TangentSpace I' (immersion.toFun x)) := by
  dsimp only
  rw [PointwiseBochnerGaussJet.normalSecondDerivativeTrace,
    PointwiseBochnerGaussJet.normalAccelerationDerivativeTrace,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  simp [SmoothSubmanifoldLaplacianFieldJetDataAt.toDifferentiatedGaussWeingartenJet,
    inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfTangentFieldAt,
    inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt,
    connectionSubmanifoldDifferentiatedGaussWeingartenJetAt,
    submanifoldDifferentiatedGaussWeingartenJetAt,
    PointwiseDifferentiatedGaussWeingartenJet.toPointwiseBochnerGaussJet,
    ambientNormalRawSecondDerivativeOfTangentFieldAt]
  exact ambientNormalCovariantHessianOfTangentFieldAt_apply
    immersion.toSmoothImmersionData immersion.orthogonalSplitting
    ambientLeviCivita.connection extensions x ambientRegular data.field
    data.ambientFieldRegular (data.normalFrame l) (data.normalFrame l)

/-- The one remaining trace-level regularity statement needed to identify the jet's ambient
Bochner value with `roughLaplacianAt`: the negative tangent restriction of the actual ambient
Hessian equals the differentiated Gauss expression.  This is deliberately narrower than assuming
the final CCG25 formula or the equality of the complete operators. -/
def SmoothSubmanifoldLaplacianFieldJetDataAt.HasAmbientTangentHessianTraceGaussAt
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
      ambientLeviCivita.connection (immersion.toFun x)) : Prop :=
  -∑ i, secondCovariantDerivativeAt I' ambientLeviCivita.connection
        (immersion.toFun x) ambientRegular
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
        data.ambientFieldRegular
        (mfderiv I I' immersion.toFun x (data.tangentFrame i))
        (mfderiv I I' immersion.toFun x (data.tangentFrame i)) =
    (data.toDifferentiatedGaussWeingartenJet ambientRegular
      ).toPointwiseBochnerGaussJet.tangentAmbientBochner

/-- Once the single tangent-Hessian trace bridge is available, the smooth jet's ambient Bochner
value is exactly the independently constructed ambient rough Laplacian. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.ambientBochner_eq_roughLaplacianAt
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
    (tangentTraceGauss : data.HasAmbientTangentHessianTraceGaussAt ambientRegular) :
    (data.toDifferentiatedGaussWeingartenJet ambientRegular
      ).toPointwiseBochnerGaussJet.ambientBochner =
      roughLaplacianAt I' ambientLeviCivita.connection (immersion.toFun x) ambientRegular
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
        data.ambientFieldRegular := by
  let jet := (data.toDifferentiatedGaussWeingartenJet ambientRegular
    ).toPointwiseBochnerGaussJet
  rw [jet.ambientBochner_eq_tangentAmbientBochner_sub_normal]
  rw [immersion.roughLaplacianAt_eq_neg_tangent_sum_sub_normal_sum
    ambientLeviCivita.connection x ambientRegular data.tangentFrame data.normalFrame
    (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
    data.ambientFieldRegular]
  rw [← tangentTraceGauss]
  rw [← data.normalSecondDerivativeTrace_sub_acceleration_eq ambientRegular]
  module

/-- Under Ricci symmetry, the intrinsic Hodge value in the CCG25 jet is the immersion
differential applied to the repository's independently constructed Hodge Laplacian. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.intrinsicHodge_eq_mfderiv_hodgeLaplacianConstructedAt
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
    (ricciSymmetric : ConnectionRicciSymmetricAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
      x intrinsicRegular) :
    (data.toRicciGaussJet ambientRegular).intrinsicHodge =
      mfderiv I I' immersion.toFun x
        (hodgeLaplacianConstructedAt I
          (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
          x intrinsicRegular data.field data.fieldRegular) := by
  let intrinsicConnection :=
    extensions.inducedLeviCivitaConnection immersion ambientLeviCivita
  rw [PointwiseRicciGaussJet.intrinsicHodge]
  change (data.toDifferentiatedGaussWeingartenJet ambientRegular
      ).toPointwiseBochnerGaussJet.intrinsicBochner + _ = _
  rw [data.intrinsicBochner_eq_mfderiv_roughLaplacianAt ambientRegular]
  change mfderiv I I' immersion.toFun x
        (roughLaplacianAt I intrinsicConnection.connection x intrinsicRegular
          data.field data.fieldRegular) +
      mfderiv I I' immersion.toFun x
        (connectionRicciActionAt I intrinsicConnection.connection x intrinsicRegular
          (data.field x)) = _
  rw [← map_add]
  rw [weitzenbock_constructedVectorAt I intrinsicConnection x intrinsicRegular
    data.fieldRegular,
    connectionRicciTransposeActionAt_eq_connectionRicciActionAt I
      intrinsicConnection.connection x intrinsicRegular ricciSymmetric (data.field x)]

/-- Under the tangent-Hessian trace bridge and ambient Ricci symmetry, the ambient Hodge value
in the CCG25 jet is exactly the constructed Hodge Laplacian of the chosen ambient field. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.ambientHodge_eq_hodgeLaplacianConstructedAt
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
    (tangentTraceGauss : data.HasAmbientTangentHessianTraceGaussAt ambientRegular)
    (ricciSymmetric : ConnectionRicciSymmetricAt I' ambientLeviCivita.connection
      (immersion.toFun x) ambientRegular) :
    (data.toRicciGaussJet ambientRegular).ambientHodge =
      hodgeLaplacianConstructedAt I' ambientLeviCivita.connection
        (immersion.toFun x) ambientRegular
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
        data.ambientFieldRegular := by
  rw [PointwiseRicciGaussJet.ambientHodge]
  change (data.toDifferentiatedGaussWeingartenJet ambientRegular
      ).toPointwiseBochnerGaussJet.ambientBochner + _ = _
  rw [data.ambientBochner_eq_roughLaplacianAt ambientRegular tangentTraceGauss]
  change roughLaplacianAt I' ambientLeviCivita.connection (immersion.toFun x)
        ambientRegular
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
        data.ambientFieldRegular +
      connectionRicciActionAt I' ambientLeviCivita.connection (immersion.toFun x)
        ambientRegular (mfderiv I I' immersion.toFun x (data.field x)) = _
  rw [weitzenbock_constructedVectorAt I' ambientLeviCivita (immersion.toFun x)
    ambientRegular data.ambientFieldRegular,
    connectionRicciTransposeActionAt_eq_connectionRicciActionAt I'
      ambientLeviCivita.connection (immersion.toFun x) ambientRegular ricciSymmetric]
  rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees]

/-- For a `C²` source metric, Levi--Civita curvature symmetry discharges the Ricci-symmetry
premise in the intrinsic Hodge operator bridge. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.intrinsicHodge_eq_mfderiv_hodgeLaplacianConstructedAt_of_leviCivita
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E (fun y : M ↦ TangentSpace I y)]
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
      ambientLeviCivita.connection (immersion.toFun x)) :
    (data.toRicciGaussJet ambientRegular).intrinsicHodge =
      mfderiv I I' immersion.toFun x
        (hodgeLaplacianConstructedAt I
          (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
          x intrinsicRegular data.field data.fieldRegular) :=
  data.intrinsicHodge_eq_mfderiv_hodgeLaplacianConstructedAt ambientRegular
    (LeviCivitaConnection.connectionRicciSymmetricAt (I := I)
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita)
      x intrinsicRegular)

/-- For a `C²` ambient metric, Levi--Civita curvature symmetry discharges the Ricci-symmetry
premise in the ambient Hodge operator bridge. -/
theorem SmoothSubmanifoldLaplacianFieldJetDataAt.ambientHodge_eq_hodgeLaplacianConstructedAt_of_leviCivita
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 2 E' (fun y : N ↦ TangentSpace I' y)]
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
    (tangentTraceGauss : data.HasAmbientTangentHessianTraceGaussAt ambientRegular) :
    (data.toRicciGaussJet ambientRegular).ambientHodge =
      hodgeLaplacianConstructedAt I' ambientLeviCivita.connection
        (immersion.toFun x) ambientRegular
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension data.field)
        data.ambientFieldRegular :=
  data.ambientHodge_eq_hodgeLaplacianConstructedAt ambientRegular tangentTraceGauss
    (LeviCivitaConnection.connectionRicciSymmetricAt
      (I := I') ambientLeviCivita (immersion.toFun x) ambientRegular)

end ManifoldFibers

end

end RiemannianFluids
