import RiemannianFluids.Geometry.LocalSubmanifoldSecondFundamental

/-!
# The induced Levi--Civita connection from germ-local extensions

An embedded submanifold only needs ambient extensions near the point where a derivative is
evaluated.  A family of `LocalSubmanifoldExtensionDataAt` packages therefore defines a global
covariant derivative by using the package centered at the current point.  The connection laws
are pointwise, so no global ambient extension field is needed.

For an isometric embedding, ambient metric compatibility and torsion-freeness descend to this
connection.  Levi--Civita uniqueness then identifies every differentiable value with any chosen
intrinsic Levi--Civita connection on the source.  This supplies the intrinsic term in the local
Gauss formula without assuming a compatible global extension operator.
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
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)]

namespace LocalSubmanifoldExtensionDataAt

variable
  {immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)}

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- Differentiating the germ agreement for a locally extended scalar gives the scalar chain
rule used in the induced connection's Leibniz identity. -/
theorem scalarExtension_mfderiv_mfderiv
    {x : M} (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    {scalar : M → ℝ} (smooth : MDiffAt scalar x)
    (direction : TangentSpace I x) :
    d% (extensions.scalarExtension scalar) (immersion.toFun x)
        (mfderiv I I' immersion.toFun x direction) =
      d% scalar x direction := by
  have hscalarExtension : MDiffAt (extensions.scalarExtension scalar)
      (immersion.toFun x) :=
    extensions.scalarExtension_mdifferentiableAt smooth
  have chain := mfderiv_comp_apply x hscalarExtension
    (immersion.contMDiff.mdifferentiableAt (by simp)) direction
  rw [(extensions.scalarExtension_agrees scalar).mfderiv_eq] at chain
  exact chain.symm

/-- A covariant derivative assembled pointwise from germ-local extension packages.  The package
used at `x` only needs to agree with the immersed fields on a neighborhood of `x`. -/
def localInducedCovariantDerivative
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensionAt : ∀ x, LocalSubmanifoldExtensionDataAt immersion x)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting) :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun field x :=
    (splitting.tangentProjection x).comp
      ((ambientConnection ((extensionAt x).tangentExtension field)
        (immersion.toFun x)).comp (mfderiv I I' immersion.toFun x))
  isCovariantDerivativeOnUniv := by
    constructor
    · intro field field' x smooth smooth' _
      apply ContinuousLinearMap.ext
      intro direction
      have hfield : MDiffAt (T% ((extensionAt x).tangentExtension field))
          (immersion.toFun x) :=
        (extensionAt x).tangentExtension_mdifferentiableAt smooth
      have hfield' : MDiffAt (T% ((extensionAt x).tangentExtension field'))
          (immersion.toFun x) :=
        (extensionAt x).tangentExtension_mdifferentiableAt smooth'
      have connectionAdd := DFunLike.congr_fun
        (ambientConnection.isCovariantDerivativeOn.add hfield hfield')
        (mfderiv I I' immersion.toFun x direction)
      simpa only [ContinuousLinearMap.comp_apply, map_add, add_apply] using
        congrArg (splitting.tangentProjection x) connectionAdd
    · intro field scalar x smoothField smoothScalar _
      apply ContinuousLinearMap.ext
      intro direction
      have hfield : MDiffAt (T% ((extensionAt x).tangentExtension field))
          (immersion.toFun x) :=
        (extensionAt x).tangentExtension_mdifferentiableAt smoothField
      have hscalar : MDiffAt ((extensionAt x).scalarExtension scalar)
          (immersion.toFun x) :=
        (extensionAt x).scalarExtension_mdifferentiableAt smoothScalar
      have connectionLeibniz := DFunLike.congr_fun
        (ambientConnection.isCovariantDerivativeOn.leibniz hfield hscalar)
        (mfderiv I I' immersion.toFun x direction)
      have fieldValue : (extensionAt x).tangentExtension field (immersion.toFun x) =
          mfderiv I I' immersion.toFun x (field x) :=
        (extensionAt x).tangentExtension_agrees_at field
      have scalarValue : (extensionAt x).scalarExtension scalar (immersion.toFun x) =
          scalar x :=
        (extensionAt x).scalarExtension_agrees_at scalar
      have scalarDerivative :
          d% ((extensionAt x).scalarExtension scalar) (immersion.toFun x)
              (mfderiv I I' immersion.toFun x direction) =
            d% scalar x direction :=
        (extensionAt x).scalarExtension_mfderiv_mfderiv smoothScalar direction
      change splitting.tangentProjection x
          (ambientConnection ((extensionAt x).tangentExtension (scalar • field))
            (immersion.toFun x) (mfderiv I I' immersion.toFun x direction)) = _
      rw [(extensionAt x).tangentExtension_smul]
      rw [connectionLeibniz]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul]
      rw [scalarValue, scalarDerivative, fieldValue, leftInverse]
      rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
@[simp]
theorem localInducedCovariantDerivative_apply
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensionAt : ∀ x, LocalSubmanifoldExtensionDataAt immersion x)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (field : (x : M) → TangentSpace I x) (x : M) (direction : TangentSpace I x) :
    localInducedCovariantDerivative splitting ambientConnection extensionAt leftInverse
        field x direction =
      splitting.tangentProjection x
        (ambientConnection ((extensionAt x).tangentExtension field)
          (immersion.toFun x) (mfderiv I I' immersion.toFun x direction)) :=
  rfl

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)] in
/-- Ambient torsion-freeness descends to the pointwise locally induced connection. -/
theorem localInducedCovariantDerivative_torsionFree
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensionAt : ∀ x, LocalSubmanifoldExtensionDataAt immersion x)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting) :
    (localInducedCovariantDerivative splitting ambientLeviCivita.connection
      extensionAt leftInverse).torsion = 0 := by
  apply (CovariantDerivative.torsion_eq_zero_iff _).mpr
  intro first second x smoothFirst smoothSecond
  let extensions := extensionAt x
  have hfirst : MDiffAt (T% (extensions.tangentExtension first))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt smoothFirst
  have hsecond : MDiffAt (T% (extensions.tangentExtension second))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt smoothSecond
  have firstValue : extensions.tangentExtension first (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (first x) :=
    extensions.tangentExtension_agrees_at first
  have secondValue : extensions.tangentExtension second (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (second x) :=
    extensions.tangentExtension_agrees_at second
  have ambientTorsionIdentity := ambientLeviCivita.connection.torsion_eq_zero_iff.mp
    ambientLeviCivita.torsionFree hfirst hsecond
  have projectedIdentity := congrArg (splitting.tangentProjection x) ambientTorsionIdentity
  change splitting.tangentProjection x
        (ambientLeviCivita.connection (extensions.tangentExtension second)
          (immersion.toFun x) (mfderiv I I' immersion.toFun x (first x))) -
      splitting.tangentProjection x
        (ambientLeviCivita.connection (extensions.tangentExtension first)
          (immersion.toFun x) (mfderiv I I' immersion.toFun x (second x))) = _
  rw [← firstValue, ← secondValue, ← map_sub, projectedIdentity]
  rw [VectorField.mlieBracket_eq_mfderiv_mlieBracket_of_related
    (immersion.contMDiff.of_le (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top))
    smoothFirst smoothSecond hfirst hsecond
    (extensions.tangentExtension_agrees first)
    (extensions.tangentExtension_agrees second)]
  exact leftInverse x _

end LocalSubmanifoldExtensionDataAt

namespace SmoothIsometricEmbeddingData

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- Pairing the locally induced derivative with a source tangent vector equals the ambient
pairing with its immersed image. -/
theorem localInducedCovariantDerivative_inner
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (field : (x : M) → TangentSpace I x) (x : M)
    (direction test : TangentSpace I x) :
    inner ℝ
        (LocalSubmanifoldExtensionDataAt.localInducedCovariantDerivative
          embedding.toSmoothIsometricImmersionData.orthogonalSplitting ambientConnection
          embedding.localSubmanifoldExtensionDataAt
          embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse
          field x direction)
        test =
      inner ℝ
        (ambientConnection
          ((embedding.localSubmanifoldExtensionDataAt x).tangentExtension field)
          (embedding.toFun x) (mfderiv I I' embedding.toFun x direction))
        (mfderiv I I' embedding.toFun x test) := by
  change inner ℝ
      ((mfderiv I I' embedding.toFun x).adjoint
        (ambientConnection
          ((embedding.localSubmanifoldExtensionDataAt x).tangentExtension field)
          (embedding.toFun x) (mfderiv I I' embedding.toFun x direction))) test = _
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The locally induced connection is metric-compatible for an isometric embedding. -/
theorem localInducedCovariantDerivative_metricCompatible
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I') :
    IsMetricCompatibleTangentConnection I
      (LocalSubmanifoldExtensionDataAt.localInducedCovariantDerivative
        embedding.toSmoothIsometricImmersionData.orthogonalSplitting
        ambientLeviCivita.connection embedding.localSubmanifoldExtensionDataAt
        embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse) := by
  intro x direction first second smoothDirection smoothFirst smoothSecond
  let extensions := embedding.localSubmanifoldExtensionDataAt x
  let directionExtension := extensions.tangentExtension direction
  let firstExtension := extensions.tangentExtension first
  let secondExtension := extensions.tangentExtension second
  let ambientInner : N → ℝ := fun y ↦ inner ℝ (firstExtension y) (secondExtension y)
  have smoothDirectionExtension : MDiffAt (T% directionExtension) (embedding.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt smoothDirection
  have smoothFirstExtension : MDiffAt (T% firstExtension) (embedding.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt smoothFirst
  have smoothSecondExtension : MDiffAt (T% secondExtension) (embedding.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt smoothSecond
  have smoothAmbientInner : MDiffAt ambientInner (embedding.toFun x) :=
    MDifferentiableAt.inner_bundle (F := E')
      (E := (TangentSpace I' : N → Type _))
      smoothFirstExtension smoothSecondExtension
  have directionValue : directionExtension (embedding.toFun x) =
      mfderiv I I' embedding.toFun x (direction x) :=
    extensions.tangentExtension_agrees_at direction
  have firstValue : firstExtension (embedding.toFun x) =
      mfderiv I I' embedding.toFun x (first x) :=
    extensions.tangentExtension_agrees_at first
  have secondValue : secondExtension (embedding.toFun x) =
      mfderiv I I' embedding.toFun x (second x) :=
    extensions.tangentExtension_agrees_at second
  have innerAgreement : ambientInner ∘ embedding.toFun =ᶠ[nhds x]
      fun y ↦ inner ℝ (first y) (second y) := by
    filter_upwards [extensions.tangentExtension_agrees first,
      extensions.tangentExtension_agrees second] with y hfirst hsecond
    change extensions.tangentExtension first (embedding.toFun y) =
      mfderiv I I' embedding.toFun y (first y) at hfirst
    change extensions.tangentExtension second (embedding.toFun y) =
      mfderiv I I' embedding.toFun y (second y) at hsecond
    change inner ℝ (extensions.tangentExtension first (embedding.toFun y))
      (extensions.tangentExtension second (embedding.toFun y)) = _
    rw [hfirst, hsecond, embedding.toSmoothIsometricImmersionData.mfderiv_inner]
  have chain := mfderiv_comp_apply x smoothAmbientInner
    (embedding.contMDiff.mdifferentiableAt (by simp)) (direction x)
  rw [innerAgreement.mfderiv_eq] at chain
  have ambientMetric := ambientLeviCivita.metricCompatible
    smoothDirectionExtension smoothFirstExtension smoothSecondExtension
  calc
    d% (fun y ↦ inner ℝ (first y) (second y)) x (direction x) =
        d% ambientInner (embedding.toFun x)
          (mfderiv I I' embedding.toFun x (direction x)) := chain
    _ = d% ambientInner (embedding.toFun x)
          (directionExtension (embedding.toFun x)) := by rw [directionValue]
    _ = inner ℝ
          (ambientLeviCivita.connection firstExtension (embedding.toFun x)
            (directionExtension (embedding.toFun x)))
          (secondExtension (embedding.toFun x)) +
        inner ℝ (firstExtension (embedding.toFun x))
          (ambientLeviCivita.connection secondExtension (embedding.toFun x)
            (directionExtension (embedding.toFun x))) := ambientMetric
    _ = inner ℝ
          (LocalSubmanifoldExtensionDataAt.localInducedCovariantDerivative
            embedding.toSmoothIsometricImmersionData.orthogonalSplitting
            ambientLeviCivita.connection embedding.localSubmanifoldExtensionDataAt
            embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse
            first x (direction x))
          (second x) +
        inner ℝ (first x)
          (LocalSubmanifoldExtensionDataAt.localInducedCovariantDerivative
            embedding.toSmoothIsometricImmersionData.orthogonalSplitting
            ambientLeviCivita.connection embedding.localSubmanifoldExtensionDataAt
            embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse
            second x (direction x)) := by
      rw [directionValue, firstValue, secondValue]
      dsimp only [firstExtension, secondExtension]
      rw [embedding.localInducedCovariantDerivative_inner ambientLeviCivita.connection
        first x (direction x) (second x)]
      rw [real_inner_comm
        (ambientLeviCivita.connection
          ((embedding.localSubmanifoldExtensionDataAt x).tangentExtension second)
          (embedding.toFun x) (mfderiv I I' embedding.toFun x (direction x)))
        (mfderiv I I' embedding.toFun x (first x))]
      rw [← embedding.localInducedCovariantDerivative_inner
        ambientLeviCivita.connection second x (direction x) (first x)]
      dsimp only [extensions]
      congr 1
      exact real_inner_comm _ _

/-- The Levi--Civita connection constructed entirely from the ambient connection and the
normal-form-chart extension available at each point of an isometric embedding. -/
def localInducedLeviCivitaConnection
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I') :
    LeviCivitaConnection (M := M) I where
  connection :=
    LocalSubmanifoldExtensionDataAt.localInducedCovariantDerivative
      embedding.toSmoothIsometricImmersionData.orthogonalSplitting
      ambientLeviCivita.connection embedding.localSubmanifoldExtensionDataAt
      embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse
  metricCompatible := embedding.localInducedCovariantDerivative_metricCompatible
    ambientLeviCivita
  torsionFree :=
    LocalSubmanifoldExtensionDataAt.localInducedCovariantDerivative_torsionFree
      embedding.toSmoothIsometricImmersionData.orthogonalSplitting ambientLeviCivita
      embedding.localSubmanifoldExtensionDataAt
      embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse

/-- The chart-constructed induced connection agrees, on differentiable germs, with any chosen
intrinsic Levi--Civita connection on the source. -/
theorem localInducedLeviCivitaConnection_eq_intrinsic
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicLeviCivita : LeviCivitaConnection (M := M) I)
    {direction field : (q : M) → TangentSpace I q} {x : M}
    (hdirection : MDiffAt (T% direction) x)
    (hfield : MDiffAt (T% field) x) :
    (embedding.localInducedLeviCivitaConnection ambientLeviCivita).connection
        field x (direction x) =
      intrinsicLeviCivita.connection field x (direction x) :=
  LeviCivitaConnection.eq_on_mdifferentiable I
    (embedding.localInducedLeviCivitaConnection ambientLeviCivita)
    intrinsicLeviCivita hdirection hfield

/-- Germ-local Gauss formula with the tangential term identified as the intrinsic
Levi--Civita derivative. -/
theorem localAmbientDerivativeTangentAt_eq_intrinsic_gauss
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (intrinsicLeviCivita : LeviCivitaConnection (M := M) I)
    {direction field : (q : M) → TangentSpace I q} {x : M}
    (hdirection : MDiffAt (T% direction) x)
    (hfield : MDiffAt (T% field) x) :
    (embedding.localSubmanifoldExtensionDataAt x).ambientDerivativeTangentAt
        ambientLeviCivita.connection direction field =
      mfderiv I I' embedding.toFun x
          (intrinsicLeviCivita.connection field x (direction x)) +
        (embedding.localSubmanifoldExtensionDataAt x).secondFundamentalFormAlongAt
          embedding.toSmoothIsometricImmersionData.orthogonalSplitting
          ambientLeviCivita.connection direction field := by
  rw [(embedding.localSubmanifoldExtensionDataAt x).ambientDerivativeTangentAt_eq_gauss
    embedding.toSmoothIsometricImmersionData.orthogonalSplitting
    ambientLeviCivita.connection
    embedding.toSmoothIsometricImmersionData.hasTangentNormalDecomposition]
  congr 2
  exact embedding.localInducedLeviCivitaConnection_eq_intrinsic ambientLeviCivita
    intrinsicLeviCivita hdirection hfield

end SmoothIsometricEmbeddingData

end

end RiemannianFluids
