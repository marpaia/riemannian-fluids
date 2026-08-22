import RiemannianFluids.Geometry.SubmanifoldConnection

/-!
# The induced covariant derivative of a submanifold

The first-order Gauss--Weingarten construction differentiates chosen ambient extensions and
projects the result.  To iterate that operation in Gauss and Codazzi, its tangential part must be
an actual `CovariantDerivative`, not merely a binary operation on raw fields.

This module states the extension algebra supplied by a tubular retraction: scalar functions and
tangent fields extend compatibly with products, agree on the immersed submanifold, and preserve
pointwise differentiability.  Those laws are exactly enough to prove additivity and the Leibniz
rule for the projected ambient connection.  No connection axiom is stored in the extension data.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 2 N]

/-- Extension data compatible with the module structure of tangent fields.  A tubular
neighborhood retraction supplies these fields by pullback along the retraction and tangential
transport. -/
structure CovariantSubmanifoldFieldExtensionData
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    extends SubmanifoldFieldExtensionData immersion where
  scalarExtension : (M → ℝ) → (N → ℝ)
  scalarExtension_agrees : ∀ scalar x,
    scalarExtension scalar (immersion.toFun x) = scalar x
  tangentExtension_smul : ∀ scalar field,
    toSubmanifoldFieldExtensionData.tangentExtension (scalar • field) =
      scalarExtension scalar •
        toSubmanifoldFieldExtensionData.tangentExtension field
  tangentExtension_mdifferentiableAt : ∀ {field : (x : M) → TangentSpace I x} {x : M},
    MDiffAt (T% field) x →
      MDiffAt
        (T% (toSubmanifoldFieldExtensionData.tangentExtension field))
        (immersion.toFun x)
  scalarExtension_mdifferentiableAt : ∀ {scalar : M → ℝ} {x : M},
    MDiffAt scalar x → MDiffAt (scalarExtension scalar) (immersion.toFun x)

namespace CovariantSubmanifoldFieldExtensionData

variable
  (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
  (splitting : SubmanifoldSplittingData immersion)
  (ambientConnection :
    CovariantDerivative I' E' (TangentSpace I' : N → Type _))
  (extensions : CovariantSubmanifoldFieldExtensionData immersion)

/-- Differentiating the agreement `ḡ ∘ f = g` gives the scalar chain rule needed by the
induced connection's Leibniz law. -/
theorem scalarExtension_mfderiv_mfderiv
    {scalar : M → ℝ} {x : M} (smooth : MDiffAt scalar x)
    (direction : TangentSpace I x) :
    d% (extensions.scalarExtension scalar) (immersion.toFun x)
        (mfderiv I I' immersion.toFun x direction) =
      d% scalar x direction := by
  have chain := mfderiv_comp_apply x
    (extensions.scalarExtension_mdifferentiableAt smooth)
    (immersion.contMDiff.mdifferentiableAt (by simp)) direction
  have agreement : extensions.scalarExtension scalar ∘ immersion.toFun = scalar := by
    funext y
    exact extensions.scalarExtension_agrees scalar y
  rw [agreement] at chain
  exact chain.symm

/-- The tangential projection of the ambient covariant derivative, transported through `df`,
is a genuine covariant derivative on the source tangent bundle. -/
def inducedCovariantDerivative
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting) :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun field x :=
    (splitting.tangentProjection x).comp
      ((ambientConnection
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension field)
        (immersion.toFun x)).comp
          (mfderiv I I' immersion.toFun x))
  isCovariantDerivativeOnUniv := by
    constructor
    · intro field field' x smooth smooth' _
      apply ContinuousLinearMap.ext
      intro direction
      have connectionAdd := DFunLike.congr_fun
        (ambientConnection.isCovariantDerivativeOn.add
          (extensions.tangentExtension_mdifferentiableAt smooth)
          (extensions.tangentExtension_mdifferentiableAt smooth'))
        (mfderiv I I' immersion.toFun x direction)
      simpa only [ContinuousLinearMap.comp_apply, LinearMap.map_add, add_apply,
        map_add] using congrArg (splitting.tangentProjection x) connectionAdd
    · intro field scalar x smoothField smoothScalar _
      apply ContinuousLinearMap.ext
      intro direction
      have connectionLeibniz := DFunLike.congr_fun
        (ambientConnection.isCovariantDerivativeOn.leibniz
          (extensions.tangentExtension_mdifferentiableAt smoothField)
          (extensions.scalarExtension_mdifferentiableAt smoothScalar))
        (mfderiv I I' immersion.toFun x direction)
      have fieldValue :
          extensions.toSubmanifoldFieldExtensionData.tangentExtension field
              (immersion.toFun x) =
          mfderiv I I' immersion.toFun x (field x) := by
        exact extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees field x
      have scalarValue :
          extensions.scalarExtension scalar (immersion.toFun x) = scalar x :=
        extensions.scalarExtension_agrees scalar x
      have scalarDerivative :
          d% (extensions.scalarExtension scalar) (immersion.toFun x)
              (mfderiv I I' immersion.toFun x direction) =
            d% scalar x direction :=
        extensions.scalarExtension_mfderiv_mfderiv immersion smoothScalar direction
      change splitting.tangentProjection x
          (ambientConnection
            (extensions.toSubmanifoldFieldExtensionData.tangentExtension (scalar • field))
            (immersion.toFun x) (mfderiv I I' immersion.toFun x direction)) = _
      rw [extensions.tangentExtension_smul]
      rw [connectionLeibniz]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul]
      rw [scalarValue, scalarDerivative, fieldValue, leftInverse]
      rfl

@[simp]
theorem inducedCovariantDerivative_apply
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (field : (x : M) → TangentSpace I x) (x : M) (direction : TangentSpace I x) :
    extensions.inducedCovariantDerivative immersion splitting ambientConnection leftInverse
        field x direction =
      splitting.tangentProjection x
        (ambientConnection
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension field)
          (immersion.toFun x) (mfderiv I I' immersion.toFun x direction)) :=
  rfl

@[simp]
theorem inducedCovariantDerivative_eq_intrinsicDerivative
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : (x : M) → TangentSpace I x) (x : M) :
    extensions.inducedCovariantDerivative immersion splitting ambientConnection leftInverse
        second x (first x) =
      extensions.toSubmanifoldFieldExtensionData.intrinsicDerivative
        immersion splitting ambientConnection first second x :=
  rfl

/-- Gauss' formula with the tangential term exposed through the constructed bundled covariant
derivative.  This is the first-derivative identity that can now be iterated by the curvature
layer. -/
theorem ambientDerivativeTangent_eq_gauss_inducedCovariantDerivative
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : (x : M) → TangentSpace I x) (x : M) :
    extensions.toSubmanifoldFieldExtensionData.ambientDerivativeTangent
        immersion ambientConnection first second x =
      mfderiv I I' immersion.toFun x
          (extensions.inducedCovariantDerivative immersion splitting ambientConnection
            leftInverse second x (first x)) +
        extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion splitting ambientConnection first second x := by
  exact extensions.toSubmanifoldFieldExtensionData.ambientDerivativeTangent_eq_gauss
    immersion splitting ambientConnection decomposition first second x

/-- Full naturality of Lie brackets for the chosen tangent extensions: the ambient bracket along
the immersion is the differential of the source bracket.  A tubular retraction or an embedded
submanifold chart supplies exactly this `f`-related-fields identity. -/
def HasBracketCompatibility : Prop :=
  ∀ {first second : (x : M) → TangentSpace I x} {x : M},
    MDiffAt (T% first) x → MDiffAt (T% second) x →
      VectorField.mlieBracket I'
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension first)
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension second)
          (immersion.toFun x) =
        mfderiv I I' immersion.toFun x
          (VectorField.mlieBracket I first second x)

/-- The tangential projection consequence of full bracket compatibility. -/
def HasTangentBracketCompatibility : Prop :=
  ∀ {first second : (x : M) → TangentSpace I x} {x : M},
    MDiffAt (T% first) x → MDiffAt (T% second) x →
      splitting.tangentProjection x
          (VectorField.mlieBracket I'
            (extensions.toSubmanifoldFieldExtensionData.tangentExtension first)
            (extensions.toSubmanifoldFieldExtensionData.tangentExtension second)
            (immersion.toFun x)) =
        VectorField.mlieBracket I first second x

/-- Full bracket compatibility implies its tangential projection form. -/
theorem HasBracketCompatibility.hasTangentBracketCompatibility
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (compatibility : extensions.HasBracketCompatibility immersion) :
    extensions.HasTangentBracketCompatibility immersion splitting := by
  intro first second x smoothFirst smoothSecond
  rw [compatibility smoothFirst smoothSecond, leftInverse]

/-- The differentiability premise used by the pointwise bilinear second fundamental form follows
from the canonical source extension and preservation of differentiability by the ambient extension
operator. -/
theorem hasDifferentiableCanonicalTangentExtensionsAt (x : M) :
    extensions.toSubmanifoldFieldExtensionData.HasDifferentiableCanonicalTangentExtensionsAt
      immersion x := by
  intro tangent
  exact extensions.tangentExtension_mdifferentiableAt
    (SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x tangent)

/-- Full `f`-related bracket naturality implies that brackets of canonical ambient extensions
have zero normal projection.  Thus the pointwise symmetry theorem needs no separate involutivity
hypothesis once the stronger geometric extension law is available. -/
theorem HasBracketCompatibility.hasTangentCanonicalBracketAt
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (compatibility : extensions.HasBracketCompatibility immersion)
    (x : M) :
    extensions.toSubmanifoldFieldExtensionData.HasTangentCanonicalBracketAt
      immersion splitting x := by
  intro first second
  rw [compatibility
    (SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x first)
    (SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x second)]
  exact normalProjection_mfderiv_eq_zero immersion splitting decomposition leftInverse x _

/-- The actual kernel-normal-valued second fundamental form built from the covariant extension
data.  Its canonical extension regularity is discharged internally. -/
def projectedSecondFundamentalFormAt
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [CompleteSpace E'] [FiniteDimensional ℝ E']
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [RiemannianBundle (fun x : N => TangentSpace I' x)]
    [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      LinearMap.ker (splitting.tangentProjection x).toLinearMap :=
  extensions.toSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
    immersion splitting ambientConnection decomposition leftInverse x
    (extensions.hasDifferentiableCanonicalTangentExtensionsAt immersion x)

@[simp]
theorem projectedSecondFundamentalFormAt_apply
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [CompleteSpace E'] [FiniteDimensional ℝ E']
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [RiemannianBundle (fun x : N => TangentSpace I' x)]
    [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (first second : TangentSpace I x) :
    projectedSecondFundamentalFormAt
        (ambientConnection := ambientConnection) (extensions := extensions)
        immersion splitting
        decomposition leftInverse x first second =
      extensions.toSubmanifoldFieldExtensionData.projectedSecondFundamentalValueAt
        immersion splitting ambientConnection decomposition leftInverse x first second :=
  rfl

/-- Ambient torsion-freeness and full bracket naturality prove symmetry of the canonically
constructed, actual-normal-fiber second fundamental form. -/
theorem projectedSecondFundamentalFormAt_comm
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [CompleteSpace E'] [FiniteDimensional ℝ E']
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [RiemannianBundle (fun x : N => TangentSpace I' x)]
    [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (ambientTorsionFree : ambientConnection.torsion = 0)
    (bracketCompatibility : extensions.HasBracketCompatibility immersion)
    (x : M) (first second : TangentSpace I x) :
    projectedSecondFundamentalFormAt
        (ambientConnection := ambientConnection) (extensions := extensions)
        immersion splitting
        decomposition leftInverse x first second =
      projectedSecondFundamentalFormAt
        (ambientConnection := ambientConnection) (extensions := extensions)
        immersion splitting
        decomposition leftInverse x second first := by
  exact extensions.toSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt_comm
    immersion splitting ambientConnection decomposition leftInverse x
    (extensions.hasDifferentiableCanonicalTangentExtensionsAt immersion x)
    (bracketCompatibility.hasTangentCanonicalBracketAt immersion splitting extensions
      decomposition leftInverse x)
    ambientTorsionFree first second

/-- Ambient torsion-freeness descends to the induced connection once the extension operator
commutes with Lie brackets along the immersion. -/
theorem inducedCovariantDerivative_torsionFree
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [CompleteSpace E'] [FiniteDimensional ℝ E']
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (ambientTorsionFree : ambientConnection.torsion = 0)
    (bracketCompatibility : extensions.HasBracketCompatibility immersion) :
    (extensions.inducedCovariantDerivative immersion splitting ambientConnection
      leftInverse).torsion = 0 := by
  apply (CovariantDerivative.torsion_eq_zero_iff
    (extensions.inducedCovariantDerivative immersion splitting ambientConnection
      leftInverse)).mpr
  intro first second x smoothFirst smoothSecond
  have smoothFirstExtension :=
    extensions.tangentExtension_mdifferentiableAt smoothFirst
  have smoothSecondExtension :=
    extensions.tangentExtension_mdifferentiableAt smoothSecond
  have firstValue :
      extensions.toSubmanifoldFieldExtensionData.tangentExtension first
          (immersion.toFun x) =
        mfderiv I I' immersion.toFun x (first x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first x
  have secondValue :
      extensions.toSubmanifoldFieldExtensionData.tangentExtension second
          (immersion.toFun x) =
        mfderiv I I' immersion.toFun x (second x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees second x
  have ambientTorsionIdentity := ambientConnection.torsion_eq_zero_iff.mp
    ambientTorsionFree smoothFirstExtension smoothSecondExtension
  have projectedIdentity := congrArg (splitting.tangentProjection x) ambientTorsionIdentity
  change splitting.tangentProjection x
        (ambientConnection
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension second)
          (immersion.toFun x) (mfderiv I I' immersion.toFun x (first x))) -
      splitting.tangentProjection x
        (ambientConnection
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension first)
          (immersion.toFun x) (mfderiv I I' immersion.toFun x (second x))) = _
  rw [← firstValue, ← secondValue]
  rw [← map_sub, projectedIdentity]
  exact bracketCompatibility.hasTangentBracketCompatibility
    immersion splitting extensions leftInverse smoothFirst smoothSecond

/-- With `f`-related brackets, ambient torsion-freeness also proves symmetry of the field-level
normal derivative term in Gauss' formula. -/
theorem secondFundamentalFormAlong_comm
    [CompleteSpace E'] [FiniteDimensional ℝ E']
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (ambientTorsionFree : ambientConnection.torsion = 0)
    (bracketCompatibility : extensions.HasBracketCompatibility immersion)
    {first second : (x : M) → TangentSpace I x} {x : M}
    (smoothFirst : MDiffAt (T% first) x) (smoothSecond : MDiffAt (T% second) x) :
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion splitting ambientConnection first second x =
      extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion splitting ambientConnection second first x := by
  have smoothFirstExtension :=
    extensions.tangentExtension_mdifferentiableAt smoothFirst
  have smoothSecondExtension :=
    extensions.tangentExtension_mdifferentiableAt smoothSecond
  have firstValue :
      extensions.toSubmanifoldFieldExtensionData.tangentExtension first
          (immersion.toFun x) =
        mfderiv I I' immersion.toFun x (first x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first x
  have secondValue :
      extensions.toSubmanifoldFieldExtensionData.tangentExtension second
          (immersion.toFun x) =
        mfderiv I I' immersion.toFun x (second x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees second x
  have ambientTorsionIdentity := ambientConnection.torsion_eq_zero_iff.mp
    ambientTorsionFree smoothFirstExtension smoothSecondExtension
  have projectedIdentity := congrArg (splitting.normalProjection x) ambientTorsionIdentity
  change splitting.normalProjection x
      (ambientConnection
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension second)
        (immersion.toFun x) (mfderiv I I' immersion.toFun x (first x))) =
    splitting.normalProjection x
      (ambientConnection
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension first)
        (immersion.toFun x) (mfderiv I I' immersion.toFun x (second x)))
  rw [← firstValue, ← secondValue]
  rw [map_sub, bracketCompatibility smoothFirst smoothSecond,
    normalProjection_mfderiv_eq_zero immersion splitting decomposition leftInverse] at projectedIdentity
  exact sub_eq_zero.mp projectedIdentity

end CovariantSubmanifoldFieldExtensionData

/-! ## Isometric immersions -/

section IsometricImmersion

variable
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I' 1 E' (fun x : N ↦ TangentSpace I' x)]
  [∀ x : M, CompleteSpace (TangentSpace I x)]
  [∀ x : N, CompleteSpace (TangentSpace I' x)]

namespace CovariantSubmanifoldFieldExtensionData

variable
  (immersion : SmoothIsometricImmersionData
    (I := I) (I' := I') (M := M) (N := N))
  (ambientConnection :
    CovariantDerivative I' E' (TangentSpace I' : N → Type _))
  (extensions : CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I' 1 E' (fun x : N ↦ TangentSpace I' x)] in
/-- Pairing the induced derivative against a tangent vector is exactly the ambient pairing
against its immersed image.  This is the adjoint characterization of the canonical tangential
projection. -/
theorem inducedCovariantDerivative_inner
    (field : (x : M) → TangentSpace I x) (x : M)
    (direction test : TangentSpace I x) :
    inner ℝ
        (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientConnection
          immersion.hasTangentProjectionLeftInverse field x direction)
        test =
      inner ℝ
        (ambientConnection
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension field)
          (immersion.toFun x) (mfderiv I I' immersion.toFun x direction))
        (mfderiv I I' immersion.toFun x test) := by
  change inner ℝ
      ((mfderiv I I' immersion.toFun x).adjoint
        (ambientConnection
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension field)
          (immersion.toFun x) (mfderiv I I' immersion.toFun x direction))) test = _
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- Metric compatibility descends from the ambient connection through an isometric immersion.
The proof differentiates the equality of the source inner product with the ambient inner product
of the chosen extensions and then uses the adjoint projection identity above. -/
theorem inducedCovariantDerivative_metricCompatible
    (ambientLeviCivita : LeviCivitaConnection (M := N) I') :
    IsMetricCompatibleTangentConnection I
      (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection
        immersion.hasTangentProjectionLeftInverse) := by
  intro x direction first second smoothDirection smoothFirst smoothSecond
  let directionExtension :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension direction
  let firstExtension :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension first
  let secondExtension :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension second
  let ambientInner : N → ℝ := fun y ↦
    inner ℝ (firstExtension y) (secondExtension y)
  have smoothDirectionExtension : MDiffAt (T% directionExtension) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt smoothDirection
  have smoothFirstExtension : MDiffAt (T% firstExtension) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt smoothFirst
  have smoothSecondExtension : MDiffAt (T% secondExtension) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt smoothSecond
  have smoothAmbientInner : MDiffAt ambientInner (immersion.toFun x) :=
    MDifferentiableAt.inner_bundle (F := E')
      (E := (TangentSpace I' : N → Type _))
      smoothFirstExtension smoothSecondExtension
  have directionValue : directionExtension (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (direction x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees direction x
  have firstValue : firstExtension (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (first x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first x
  have secondValue : secondExtension (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (second x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees second x
  have innerAgreement : ambientInner ∘ immersion.toFun =
      fun y ↦ inner ℝ (first y) (second y) := by
    funext y
    change inner ℝ
        (firstExtension (immersion.toFun y)) (secondExtension (immersion.toFun y)) = _
    have firstValueAt : firstExtension (immersion.toFun y) =
        mfderiv I I' immersion.toFun y (first y) :=
      extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first y
    have secondValueAt : secondExtension (immersion.toFun y) =
        mfderiv I I' immersion.toFun y (second y) :=
      extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees second y
    rw [firstValueAt, secondValueAt, immersion.mfderiv_inner]
  have chain := mfderiv_comp_apply x smoothAmbientInner
    (immersion.contMDiff.mdifferentiableAt (by simp)) (direction x)
  rw [innerAgreement] at chain
  have ambientMetric := ambientLeviCivita.metricCompatible
    smoothDirectionExtension smoothFirstExtension smoothSecondExtension
  calc
    d% (fun y ↦ inner ℝ (first y) (second y)) x (direction x) =
        d% ambientInner (immersion.toFun x)
          (mfderiv I I' immersion.toFun x (direction x)) := chain
    _ = d% ambientInner (immersion.toFun x)
          (directionExtension (immersion.toFun x)) := by rw [directionValue]
    _ = inner ℝ
          (ambientLeviCivita.connection firstExtension (immersion.toFun x)
            (directionExtension (immersion.toFun x)))
          (secondExtension (immersion.toFun x)) +
        inner ℝ (firstExtension (immersion.toFun x))
          (ambientLeviCivita.connection secondExtension (immersion.toFun x)
            (directionExtension (immersion.toFun x))) := ambientMetric
    _ = inner ℝ
          (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
            immersion.orthogonalSplitting ambientLeviCivita.connection
            immersion.hasTangentProjectionLeftInverse first x (direction x))
          (second x) +
        inner ℝ (first x)
          (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
            immersion.orthogonalSplitting ambientLeviCivita.connection
            immersion.hasTangentProjectionLeftInverse second x (direction x)) := by
      rw [directionValue, firstValue, secondValue]
      dsimp only [firstExtension, secondExtension]
      rw [extensions.inducedCovariantDerivative_inner immersion ambientLeviCivita.connection
        first x (direction x) (second x)]
      rw [real_inner_comm
        (ambientLeviCivita.connection
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension second)
          (immersion.toFun x) (mfderiv I I' immersion.toFun x (direction x)))
        (mfderiv I I' immersion.toFun x (first x))]
      rw [← extensions.inducedCovariantDerivative_inner immersion
        ambientLeviCivita.connection second x (direction x) (first x)]
      rw [real_inner_comm (first x)
        (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection
          immersion.hasTangentProjectionLeftInverse second x (direction x))]

/-- The induced connection of an isometric immersion is Levi-Civita once the chosen extension
operator satisfies the standard `f`-related bracket identity.  Metric compatibility and
torsion-freeness are theorems assembled here, not fields copied from the ambient package. -/
def inducedLeviCivitaConnection
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (bracketCompatibility :
      extensions.HasBracketCompatibility immersion.toSmoothImmersionData) :
    LeviCivitaConnection (M := M) I where
  connection :=
    extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentProjectionLeftInverse
  metricCompatible :=
    extensions.inducedCovariantDerivative_metricCompatible immersion ambientLeviCivita
  torsionFree :=
    extensions.inducedCovariantDerivative_torsionFree immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentProjectionLeftInverse ambientLeviCivita.torsionFree
      bracketCompatibility

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The induced covariant derivative is independent of the compatible extension operator on
all differentiable direction and field germs.  Each extension operator constructs a
Levi--Civita connection on the same source metric, so the pointwise uniqueness theorem applies.
This is the precise equality relevant to curvature and differential operators; raw bundled
connections may still differ on unconstrained nondifferentiable sections. -/
theorem inducedCovariantDerivative_independent
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions' :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (bracketCompatibility :
      extensions.HasBracketCompatibility immersion.toSmoothImmersionData)
    (bracketCompatibility' :
      extensions'.HasBracketCompatibility immersion.toSmoothImmersionData)
    {direction field : (x : M) → TangentSpace I x} {x : M}
    (smoothDirection : MDiffAt (T% direction) x)
    (smoothField : MDiffAt (T% field) x) :
    extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection
        immersion.hasTangentProjectionLeftInverse field x (direction x) =
      extensions'.inducedCovariantDerivative immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection
        immersion.hasTangentProjectionLeftInverse field x (direction x) := by
  exact LeviCivitaConnection.eq_on_mdifferentiable I
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita
      bracketCompatibility)
    (extensions'.inducedLeviCivitaConnection immersion ambientLeviCivita
      bracketCompatibility') smoothDirection smoothField

end CovariantSubmanifoldFieldExtensionData

end IsometricImmersion

end

end RiemannianFluids
