import RiemannianFluids.Geometry.Connections
import RiemannianFluids.Geometry.Submanifolds

/-!
# Induced submanifold derivatives from ambient extensions

An embedded-submanifold connection is not an independent geometric oracle.  Once an ambient
connection, tangent/normal projections, and genuine ambient extensions of tangent and normal
fields are fixed, the four derivatives in the Gauss--Weingarten formulas are obtained by
differentiate-then-project.

This module carries out that construction on Mathlib tangent fibers.  The Gauss and Weingarten
splittings are then theorems following from `HasTangentNormalDecomposition`; neither formula is
stored as a hypothesis.  Tensoriality, symmetry of the second fundamental form, and the
Gauss--Codazzi curvature identities require the subsequent regularity and extension-locality
layer and remain intentionally separate.
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

/-- Chosen ambient extensions of tangent fields and fields along an immersion.  The two
agreement laws assert that extension really is a right inverse to restriction on the embedded
submanifold. -/
structure SubmanifoldFieldExtensionData
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)) where
  tangentExtension :
    ((x : M) → TangentSpace I x) →ₗ[ℝ] ((y : N) → TangentSpace I' y)
  alongExtension :
    AmbientVectorFieldAlong immersion →ₗ[ℝ] ((y : N) → TangentSpace I' y)
  tangentExtension_agrees : ∀ field x,
    tangentExtension field (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (field x)
  alongExtension_agrees : ∀ field x,
    alongExtension field (immersion.toFun x) = field x

namespace SubmanifoldFieldExtensionData

variable
  (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
  (splitting : SubmanifoldSplittingData immersion)
  (ambientConnection :
    CovariantDerivative I' E' (TangentSpace I' : N → Type _))
  (extensions : SubmanifoldFieldExtensionData immersion)

/-- Differentiate an extended tangent field in an immersed tangent direction. -/
def ambientDerivativeTangent
    (first second : (x : M) → TangentSpace I x) :
    AmbientVectorFieldAlong immersion :=
  fun x => ambientConnection (extensions.tangentExtension second)
    (immersion.toFun x) (mfderiv I I' immersion.toFun x (first x))

/-- Differentiate an extended field-along-the-immersion in an immersed tangent direction. -/
def ambientDerivativeAlong
    (tangent : (x : M) → TangentSpace I x)
    (field : AmbientVectorFieldAlong immersion) :
    AmbientVectorFieldAlong immersion :=
  fun x => ambientConnection (extensions.alongExtension field)
    (immersion.toFun x) (mfderiv I I' immersion.toFun x (tangent x))

/-- Tangential projection of the ambient derivative gives the induced intrinsic derivative. -/
def intrinsicDerivative
    (first second : (x : M) → TangentSpace I x) :
    (x : M) → TangentSpace I x :=
  fun x => splitting.tangentProjection x
    (extensions.ambientDerivativeTangent immersion ambientConnection first second x)

/-- Normal projection of the ambient derivative is the field-level second fundamental form. -/
def secondFundamentalFormAlong
    (first second : (x : M) → TangentSpace I x) :
    AmbientVectorFieldAlong immersion :=
  fun x => splitting.normalProjection x
    (extensions.ambientDerivativeTangent immersion ambientConnection first second x)

/-- Normal projection of the derivative of a normal field gives the induced normal
connection. -/
def normalDerivative
    (tangent : (x : M) → TangentSpace I x)
    (normal : AmbientVectorFieldAlong immersion) :
    AmbientVectorFieldAlong immersion :=
  fun x => splitting.normalProjection x
    (extensions.ambientDerivativeAlong immersion ambientConnection tangent normal x)

/-- The sign is chosen so that `ambientDerivative = -df (shape) + normalDerivative`, the
Weingarten convention used by CCG25. -/
def shapeOperatorAlong
    (tangent : (x : M) → TangentSpace I x)
    (normal : AmbientVectorFieldAlong immersion) :
    (x : M) → TangentSpace I x :=
  fun x => -splitting.tangentProjection x
    (extensions.ambientDerivativeAlong immersion ambientConnection tangent normal x)

/-- The four differentiate-then-project operations assembled in the repository's common
submanifold-connection carrier. -/
def inducedConnectionData : SubmanifoldConnectionData immersion where
  intrinsicDerivative :=
    extensions.intrinsicDerivative immersion splitting ambientConnection
  normalDerivative :=
    extensions.normalDerivative immersion splitting ambientConnection
  ambientDerivativeTT :=
    extensions.ambientDerivativeTangent immersion ambientConnection
  ambientDerivativeTN :=
    extensions.ambientDerivativeAlong immersion ambientConnection

omit [IsManifold I 2 M] in
/-- Gauss' formula follows directly from the tangent/normal decomposition of the actual ambient
covariant derivative. -/
theorem ambientDerivativeTangent_eq_gauss
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (first second : (x : M) → TangentSpace I x) (x : M) :
    extensions.ambientDerivativeTangent immersion ambientConnection first second x =
      mfderiv I I' immersion.toFun x
          (extensions.intrinsicDerivative immersion splitting ambientConnection first second x) +
        extensions.secondFundamentalFormAlong
          immersion splitting ambientConnection first second x := by
  exact (decomposition x
    (extensions.ambientDerivativeTangent immersion ambientConnection first second x)).symm

omit [IsManifold I 2 M] in
/-- Weingarten's formula follows from the same decomposition and the conventional minus sign in
the induced shape operator. -/
theorem ambientDerivativeAlong_eq_weingarten
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (tangent : (x : M) → TangentSpace I x)
    (normal : AmbientVectorFieldAlong immersion) (x : M) :
    extensions.ambientDerivativeAlong immersion ambientConnection tangent normal x =
      -(mfderiv I I' immersion.toFun x
          (extensions.shapeOperatorAlong
            immersion splitting ambientConnection tangent normal x)) +
        extensions.normalDerivative
          immersion splitting ambientConnection tangent normal x := by
  have reconstructed := (decomposition x
    (extensions.ambientDerivativeAlong immersion ambientConnection tangent normal x)).symm
  change _ = -(mfderiv I I' immersion.toFun x
      (-splitting.tangentProjection x
        (extensions.ambientDerivativeAlong immersion ambientConnection tangent normal x))) + _
  rw [map_neg, neg_neg]
  exact reconstructed

omit [IsManifold I 2 M] in
/-- The constructed second fundamental form is normal-valued whenever the splitting projections
satisfy reconstruction and the tangential left-inverse law. -/
theorem tangentProjection_secondFundamentalFormAlong_eq_zero
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : (x : M) → TangentSpace I x) (x : M) :
    splitting.tangentProjection x
        (extensions.secondFundamentalFormAlong
          immersion splitting ambientConnection first second x) = 0 := by
  exact tangentProjection_normalProjection_eq_zero immersion splitting
    decomposition leftInverse x _

omit [IsManifold I 2 M] in
/-- The constructed normal connection is normal-valued under the same projection laws. -/
theorem tangentProjection_normalDerivative_eq_zero
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (tangent : (x : M) → TangentSpace I x)
    (normal : AmbientVectorFieldAlong immersion) (x : M) :
    splitting.tangentProjection x
        (extensions.normalDerivative
          immersion splitting ambientConnection tangent normal x) = 0 := by
  exact tangentProjection_normalProjection_eq_zero immersion splitting
    decomposition leftInverse x _

/-! ## Pointwise second fundamental form -/

section PointwiseSecondFundamental

/-- A fiber vector extended linearly through the tangent trivialization centered at `x`.  Unlike
the choice-valued `FiberBundle.extend`, this construction is bundled as a linear map in the
initial fiber value, which is exactly what the pointwise second fundamental form needs. -/
def linearFiberExtensionAt (x : M) :
    TangentSpace I x →ₗ[ℝ] ((y : M) → TangentSpace I y) where
  toFun tangent y :=
    let trivialization := trivializationAt E (TangentSpace I : M → Type _) x
    trivialization.symmL ℝ y
      (trivialization.continuousLinearMapAt ℝ x tangent)
  map_add' := by
    intro first second
    funext y
    let trivialization := trivializationAt E (TangentSpace I : M → Type _) x
    change trivialization.symmL ℝ y
        (trivialization.continuousLinearMapAt ℝ x (first + second)) =
      trivialization.symmL ℝ y (trivialization.continuousLinearMapAt ℝ x first) +
        trivialization.symmL ℝ y (trivialization.continuousLinearMapAt ℝ x second)
    rw [map_add, map_add]
  map_smul' := by
    intro scalar tangent
    funext y
    let trivialization := trivializationAt E (TangentSpace I : M → Type _) x
    change trivialization.symmL ℝ y
        (trivialization.continuousLinearMapAt ℝ x (scalar • tangent)) =
      scalar • trivialization.symmL ℝ y
        (trivialization.continuousLinearMapAt ℝ x tangent)
    rw [map_smul, map_smul]

@[simp]
theorem linearFiberExtensionAt_apply_self (x : M) (tangent : TangentSpace I x) :
    linearFiberExtensionAt (I := I) x tangent x = tangent := by
  exact (trivializationAt E (TangentSpace I : M → Type _) x).symmL_continuousLinearMapAt
    (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x) tangent

/-- The canonical linear extension of a tangent vector is differentiable at its base point.
This is a theorem of the smooth tangent-bundle trivialization, so pointwise second-fundamental-form
constructions do not need to receive it as independent regularity data. -/
theorem linearFiberExtensionAt_mdifferentiableAt
    (x : M) (tangent : TangentSpace I x) :
    MDiffAt (T% (linearFiberExtensionAt (I := I) x tangent)) x := by
  let trivialization := trivializationAt E (TangentSpace I : M → Type _) x
  let coordinate : E := trivialization.continuousLinearMapAt ℝ x tangent
  have smoothInverse :
      CMDiffAt 1
        (fun y =>
          (⟨y, trivialization.symmL ℝ y⟩ :
            TotalSpace (E →L[ℝ] E) (fun z : M => E →L[ℝ] TangentSpace I z))) x :=
    trivialization.contMDiffAt_symmL
      (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x)
  have smoothCoordinate :
      CMDiffAt 1
        (fun y : M => (⟨y, coordinate⟩ : TotalSpace E (fun _ : M => E))) x := by
    rw [Bundle.contMDiffAt_totalSpace]
    constructor
    · exact contMDiffAt_id
    · simpa using (contMDiffAt_const : CMDiffAt 1 (fun _ : M => coordinate) x)
  exact (smoothInverse.clm_bundle_apply smoothCoordinate).mdifferentiableAt one_ne_zero

/-- Canonical tangent vectors are extended on the source and then by the chosen ambient
extension; this predicate records the differentiability needed for the connection's additivity
and constant-scalar laws. -/
def HasDifferentiableCanonicalTangentExtensionsAt (x : M) : Prop :=
  ∀ tangent : TangentSpace I x,
    MDiffAt
      (T% (extensions.tangentExtension
        (linearFiberExtensionAt (I := I) x tangent)))
      (immersion.toFun x)

/-- The Lie bracket of the two chosen ambient tangent extensions remains tangent at the
submanifold point.  This is the precise involutivity statement needed to derive symmetry of the
second fundamental form from ambient torsion-freeness.  It is separated from differentiability
so an embedded-submanifold chart theorem can discharge it without changing the construction. -/
def HasTangentCanonicalBracketAt (x : M) : Prop :=
  ∀ first second : TangentSpace I x,
    splitting.normalProjection x
      (VectorField.mlieBracket I'
        (extensions.tangentExtension
          (linearFiberExtensionAt (I := I) x first))
        (extensions.tangentExtension
          (linearFiberExtensionAt (I := I) x second))
        (immersion.toFun x)) = 0

/-- The normal projection of the ambient derivative of canonical tangent extensions, valued in
the actual kernel-normal fiber. -/
def projectedSecondFundamentalValueAt
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (first second : TangentSpace I x) :
    LinearMap.ker (splitting.tangentProjection x).toLinearMap :=
  ⟨splitting.normalProjection x
      (ambientConnection
        (extensions.tangentExtension
          (linearFiberExtensionAt (I := I) x second))
        (immersion.toFun x) (mfderiv I I' immersion.toFun x first)),
    tangentProjection_normalProjection_eq_zero immersion splitting
      decomposition leftInverse x _⟩

/-- Linearity of the projected second fundamental value in its direction argument. -/
theorem projectedSecondFundamentalValueAt_add_first
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (first first' second : TangentSpace I x) :
    projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
        decomposition leftInverse x (first + first') second =
      projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
          decomposition leftInverse x first second +
        projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
          decomposition leftInverse x first' second := by
  apply Subtype.ext
  simp [projectedSecondFundamentalValueAt]

/-- Constant real scalars pull through the direction argument. -/
theorem projectedSecondFundamentalValueAt_smul_first
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (scalar : ℝ) (first second : TangentSpace I x) :
    projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
        decomposition leftInverse x (scalar • first) second =
      scalar • projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
        decomposition leftInverse x first second := by
  apply Subtype.ext
  simp [projectedSecondFundamentalValueAt]

/-- Additivity in the differentiated tangent argument follows from the linear extension maps and
the covariant derivative's additivity on differentiable sections. -/
theorem projectedSecondFundamentalValueAt_add_second
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (regular : extensions.HasDifferentiableCanonicalTangentExtensionsAt immersion x)
    (first second second' : TangentSpace I x) :
    projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
        decomposition leftInverse x first (second + second') =
      projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
          decomposition leftInverse x first second +
        projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
          decomposition leftInverse x first second' := by
  apply Subtype.ext
  have connectionAdd := DFunLike.congr_fun
    (ambientConnection.isCovariantDerivativeOn.add (regular second) (regular second'))
    (mfderiv I I' immersion.toFun x first)
  simpa only [projectedSecondFundamentalValueAt, LinearMap.map_add, map_add,
    Submodule.coe_add, Pi.add_apply, add_apply] using
    congrArg (splitting.normalProjection x) connectionAdd

/-- Constant real scalars pull through the differentiated tangent argument. -/
theorem projectedSecondFundamentalValueAt_smul_second
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (regular : extensions.HasDifferentiableCanonicalTangentExtensionsAt immersion x)
    (scalar : ℝ) (first second : TangentSpace I x) :
    projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
        decomposition leftInverse x first (scalar • second) =
      scalar • projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
        decomposition leftInverse x first second := by
  apply Subtype.ext
  have connectionSmul := DFunLike.congr_fun
    (ambientConnection.isCovariantDerivativeOn.smul_const scalar (regular second))
    (mfderiv I I' immersion.toFun x first)
  simpa only [projectedSecondFundamentalValueAt, LinearMap.map_smul, map_smul,
    Submodule.coe_smul, Pi.smul_apply, smul_apply] using
    congrArg (splitting.normalProjection x) connectionSmul

/-- Ambient torsion-freeness and tangency of brackets make the constructed pointwise second
fundamental form symmetric.  Thus the remaining geometric obligation is exactly involutivity of
the immersed tangent distribution, not an assumed symmetry equation for `II`. -/
theorem projectedSecondFundamentalValueAt_comm
    [CompleteSpace E'] [FiniteDimensional ℝ E']
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (regular : extensions.HasDifferentiableCanonicalTangentExtensionsAt immersion x)
    (tangentBracket : extensions.HasTangentCanonicalBracketAt immersion splitting x)
    (torsionFree : ambientConnection.torsion = 0)
    (first second : TangentSpace I x) :
    projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
        decomposition leftInverse x first second =
      projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
        decomposition leftInverse x second first := by
  apply Subtype.ext
  let firstExtension := extensions.tangentExtension
    (linearFiberExtensionAt (I := I) x first)
  let secondExtension := extensions.tangentExtension
    (linearFiberExtensionAt (I := I) x second)
  have firstValue : firstExtension (immersion.toFun x) =
      mfderiv I I' immersion.toFun x first := by
    simpa only [firstExtension, linearFiberExtensionAt_apply_self] using
      extensions.tangentExtension_agrees
        (linearFiberExtensionAt (I := I) x first) x
  have secondValue : secondExtension (immersion.toFun x) =
      mfderiv I I' immersion.toFun x second := by
    simpa only [secondExtension, linearFiberExtensionAt_apply_self] using
      extensions.tangentExtension_agrees
        (linearFiberExtensionAt (I := I) x second) x
  have torsionIdentity := ambientConnection.torsion_eq_zero_iff.mp torsionFree
    (regular first) (regular second)
  have projectedIdentity := congrArg (splitting.normalProjection x) torsionIdentity
  have bracketZero : splitting.normalProjection x
      (VectorField.mlieBracket I' firstExtension secondExtension (immersion.toFun x)) = 0 := by
    exact tangentBracket first second
  change splitting.normalProjection x
      (ambientConnection secondExtension (immersion.toFun x)
        (mfderiv I I' immersion.toFun x first)) =
    splitting.normalProjection x
      (ambientConnection firstExtension (immersion.toFun x)
        (mfderiv I I' immersion.toFun x second))
  rw [← firstValue, ← secondValue]
  rw [map_sub, bracketZero] at projectedIdentity
  exact sub_eq_zero.mp projectedIdentity

/-- The pointwise second fundamental value as an algebraic bilinear map.  This is the core
construction: continuity is added below under the finite-dimensional hypotheses used throughout
the concrete surfaces in the corpus. -/
def projectedSecondFundamentalLinearMapAt
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (regular : extensions.HasDifferentiableCanonicalTangentExtensionsAt immersion x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ]
      LinearMap.ker (splitting.tangentProjection x).toLinearMap where
  toFun first := {
    toFun := fun second =>
      projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
        decomposition leftInverse x first second
    map_add' := fun second second' =>
      projectedSecondFundamentalValueAt_add_second immersion splitting ambientConnection
        extensions decomposition leftInverse x regular first second second'
    map_smul' := fun scalar second =>
      projectedSecondFundamentalValueAt_smul_second immersion splitting ambientConnection
        extensions decomposition leftInverse x regular scalar first second
  }
  map_add' := by
    intro first first'
    apply LinearMap.ext
    intro second
    exact projectedSecondFundamentalValueAt_add_first immersion splitting ambientConnection
      extensions decomposition leftInverse x first first' second
  map_smul' := by
    intro scalar first
    apply LinearMap.ext
    intro second
    exact projectedSecondFundamentalValueAt_smul_first immersion splitting ambientConnection
      extensions decomposition leftInverse x scalar first second

/-- Symmetry of the algebraic bilinear packaging follows from the geometric torsion/bracket
argument above. -/
theorem projectedSecondFundamentalLinearMapAt_comm
    [CompleteSpace E'] [FiniteDimensional ℝ E']
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (regular : extensions.HasDifferentiableCanonicalTangentExtensionsAt immersion x)
    (tangentBracket : extensions.HasTangentCanonicalBracketAt immersion splitting x)
    (torsionFree : ambientConnection.torsion = 0)
    (first second : TangentSpace I x) :
    projectedSecondFundamentalLinearMapAt immersion splitting ambientConnection extensions
        decomposition leftInverse x regular first second =
      projectedSecondFundamentalLinearMapAt immersion splitting ambientConnection extensions
        decomposition leftInverse x regular second first :=
  projectedSecondFundamentalValueAt_comm immersion splitting ambientConnection extensions
    decomposition leftInverse x regular tangentBracket torsionFree first second

section ContinuousBilinear

variable
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : N => TangentSpace I' x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- The differentiate-then-project construction as an actual continuous bilinear map into the
kernel-normal fiber.  Continuity is automatic from finite dimensionality; both linearity laws
were proved from the ambient connection and the linear extension operator above. -/
def projectedSecondFundamentalFormAt
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (regular : extensions.HasDifferentiableCanonicalTangentExtensionsAt immersion x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      LinearMap.ker (splitting.tangentProjection x).toLinearMap :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (TangentSpace I x →ₗ[ℝ] LinearMap.ker
            (splitting.tangentProjection x).toLinearMap) ≃ₗ[ℝ]
          (TangentSpace I x →L[ℝ] LinearMap.ker
            (splitting.tangentProjection x).toLinearMap)).toLinearMap.comp
      (projectedSecondFundamentalLinearMapAt immersion splitting ambientConnection extensions
        decomposition leftInverse x regular))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] in
@[simp]
theorem projectedSecondFundamentalFormAt_apply
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (regular : extensions.HasDifferentiableCanonicalTangentExtensionsAt immersion x)
    (first second : TangentSpace I x) :
    projectedSecondFundamentalFormAt immersion splitting ambientConnection extensions
        decomposition leftInverse x regular first second =
      projectedSecondFundamentalValueAt immersion splitting ambientConnection extensions
        decomposition leftInverse x first second :=
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The constructed continuous bilinear second fundamental form is symmetric under the same
torsion-free involutivity hypotheses. -/
theorem projectedSecondFundamentalFormAt_comm
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (regular : extensions.HasDifferentiableCanonicalTangentExtensionsAt immersion x)
    (tangentBracket : extensions.HasTangentCanonicalBracketAt immersion splitting x)
    (torsionFree : ambientConnection.torsion = 0)
    (first second : TangentSpace I x) :
    projectedSecondFundamentalFormAt immersion splitting ambientConnection extensions
        decomposition leftInverse x regular first second =
      projectedSecondFundamentalFormAt immersion splitting ambientConnection extensions
        decomposition leftInverse x regular second first :=
  projectedSecondFundamentalValueAt_comm immersion splitting ambientConnection extensions
    decomposition leftInverse x regular tangentBracket torsionFree first second

end ContinuousBilinear

end PointwiseSecondFundamental

end SubmanifoldFieldExtensionData

end

end RiemannianFluids
