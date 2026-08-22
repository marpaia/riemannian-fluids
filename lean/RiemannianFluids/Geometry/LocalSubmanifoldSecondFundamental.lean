import RiemannianFluids.Geometry.LocalSubmanifoldConnection
import RiemannianFluids.Geometry.RelatedVectorFields
import RiemannianFluids.Geometry.SubmanifoldConnection

/-!
# The germ-local second fundamental form

The normal-form extension package determines the second fundamental form without a global
extension oracle.  Canonical source tangent fields are extended through one immersion chart,
differentiated by the ambient Levi--Civita connection, and normally projected.  Germ-local
relatedness makes their ambient Lie bracket tangent, so torsion-freeness proves symmetry.

The resulting bilinear value is independent of the chosen normal-form chart by
`LocalSubmanifoldExtensionDataAt.secondFundamentalFormAlongAt_independent`.
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
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]
  {immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)}
  {x : M}

namespace LocalSubmanifoldExtensionDataAt

/-- The canonical ambient extension of one tangent vector at the center. -/
def canonicalTangentExtensionAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (tangent : TangentSpace I x) : (y : N) → TangentSpace I' y :=
  extensions.tangentExtension
    (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x tangent)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- Canonical ambient tangent extensions constructed from the normal-form chart are `C²`. -/
theorem canonicalTangentExtensionAt_contMDiffAt_two
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (tangent : TangentSpace I x) :
    CMDiffAt 2 (T% (extensions.canonicalTangentExtensionAt tangent))
      (immersion.toFun x) := by
  exact extensions.tangentExtension_contMDiffAt (n := 2) (by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top)
    (SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x tangent)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- The `C²` canonical ambient extension is differentiable at the center. -/
theorem canonicalTangentExtensionAt_mdifferentiableAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (tangent : TangentSpace I x) :
    MDiffAt (T% (extensions.canonicalTangentExtensionAt tangent))
      (immersion.toFun x) :=
  (extensions.canonicalTangentExtensionAt_contMDiffAt_two tangent
    ).mdifferentiableAt (by norm_num)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- The canonical ambient extension has the prescribed immersed tangent value. -/
theorem canonicalTangentExtensionAt_apply
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (tangent : TangentSpace I x) :
    extensions.canonicalTangentExtensionAt tangent (immersion.toFun x) =
      mfderiv I I' immersion.toFun x tangent := by
  simpa only [canonicalTangentExtensionAt,
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self] using
    extensions.tangentExtension_agrees_at
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x tangent)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- Lie brackets of the canonical local ambient extensions are the immersed source brackets. -/
theorem canonicalTangentExtensionAt_mlieBracket
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (first second : TangentSpace I x) :
    VectorField.mlieBracket I'
        (extensions.canonicalTangentExtensionAt first)
        (extensions.canonicalTangentExtensionAt second)
        (immersion.toFun x) =
      mfderiv I I' immersion.toFun x
        (VectorField.mlieBracket I
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first)
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second) x) := by
  exact VectorField.mlieBracket_eq_mfderiv_mlieBracket_of_related
    (immersion.contMDiff.of_le (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top))
    (SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x first)
    (SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x second)
    (extensions.canonicalTangentExtensionAt_mdifferentiableAt first)
    (extensions.canonicalTangentExtensionAt_mdifferentiableAt second)
    (extensions.tangentExtension_agrees
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first))
    (extensions.tangentExtension_agrees
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- The ambient bracket of canonical germ-local tangent extensions has zero normal part. -/
theorem normalProjection_canonicalTangentExtensionAt_mlieBracket_eq_zero
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : TangentSpace I x) :
    splitting.normalProjection x
        (VectorField.mlieBracket I'
          (extensions.canonicalTangentExtensionAt first)
          (extensions.canonicalTangentExtensionAt second)
          (immersion.toFun x)) = 0 := by
  rw [extensions.canonicalTangentExtensionAt_mlieBracket first second]
  exact normalProjection_mfderiv_eq_zero immersion splitting decomposition leftInverse x _

/-- The normal projection of the locally differentiated canonical tangent extensions, valued in
the actual kernel-normal fiber. -/
def projectedSecondFundamentalValueAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : TangentSpace I x) :
    LinearMap.ker (splitting.tangentProjection x).toLinearMap :=
  ⟨splitting.normalProjection x
      (ambientConnection (extensions.canonicalTangentExtensionAt second)
        (immersion.toFun x) (mfderiv I I' immersion.toFun x first)),
    tangentProjection_normalProjection_eq_zero immersion splitting
      decomposition leftInverse x _⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- The germ-local second fundamental value is linear in its direction argument. -/
theorem projectedSecondFundamentalValueAt_add_first
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first first' second : TangentSpace I x) :
    extensions.projectedSecondFundamentalValueAt splitting ambientConnection
        decomposition leftInverse (first + first') second =
      extensions.projectedSecondFundamentalValueAt splitting ambientConnection
          decomposition leftInverse first second +
        extensions.projectedSecondFundamentalValueAt splitting ambientConnection
          decomposition leftInverse first' second := by
  apply Subtype.ext
  simp [projectedSecondFundamentalValueAt]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- The germ-local second fundamental value respects scalars in its direction argument. -/
theorem projectedSecondFundamentalValueAt_smul_first
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (scalar : ℝ) (first second : TangentSpace I x) :
    extensions.projectedSecondFundamentalValueAt splitting ambientConnection
        decomposition leftInverse (scalar • first) second =
      scalar • extensions.projectedSecondFundamentalValueAt splitting ambientConnection
        decomposition leftInverse first second := by
  apply Subtype.ext
  simp [projectedSecondFundamentalValueAt]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- Additivity in the differentiated slot follows from linear extension and the connection law. -/
theorem projectedSecondFundamentalValueAt_add_second
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second second' : TangentSpace I x) :
    extensions.projectedSecondFundamentalValueAt splitting ambientConnection
        decomposition leftInverse first (second + second') =
      extensions.projectedSecondFundamentalValueAt splitting ambientConnection
          decomposition leftInverse first second +
        extensions.projectedSecondFundamentalValueAt splitting ambientConnection
          decomposition leftInverse first second' := by
  apply Subtype.ext
  have connectionAdd := DFunLike.congr_fun
    (ambientConnection.isCovariantDerivativeOn.add
      (extensions.canonicalTangentExtensionAt_mdifferentiableAt second)
      (extensions.canonicalTangentExtensionAt_mdifferentiableAt second'))
    (mfderiv I I' immersion.toFun x first)
  simpa only [projectedSecondFundamentalValueAt, canonicalTangentExtensionAt,
    map_add, Submodule.coe_add, add_apply] using
    congrArg (splitting.normalProjection x) connectionAdd

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- Constant scalars pull through the differentiated slot. -/
theorem projectedSecondFundamentalValueAt_smul_second
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (scalar : ℝ) (first second : TangentSpace I x) :
    extensions.projectedSecondFundamentalValueAt splitting ambientConnection
        decomposition leftInverse first (scalar • second) =
      scalar • extensions.projectedSecondFundamentalValueAt splitting ambientConnection
        decomposition leftInverse first second := by
  apply Subtype.ext
  have connectionSmul := DFunLike.congr_fun
    (ambientConnection.isCovariantDerivativeOn.smul_const scalar
      (extensions.canonicalTangentExtensionAt_mdifferentiableAt second))
    (mfderiv I I' immersion.toFun x first)
  simpa only [projectedSecondFundamentalValueAt, canonicalTangentExtensionAt,
    map_smul, Submodule.coe_smul, smul_apply] using
    congrArg (splitting.normalProjection x) connectionSmul

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- Torsion-freeness and germ-local bracket naturality make the constructed value symmetric. -/
theorem projectedSecondFundamentalValueAt_comm
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : TangentSpace I x) :
    extensions.projectedSecondFundamentalValueAt splitting ambientLeviCivita.connection
        decomposition leftInverse first second =
      extensions.projectedSecondFundamentalValueAt splitting ambientLeviCivita.connection
        decomposition leftInverse second first := by
  apply Subtype.ext
  let firstExtension := extensions.canonicalTangentExtensionAt first
  let secondExtension := extensions.canonicalTangentExtensionAt second
  have firstValue : firstExtension (immersion.toFun x) =
      mfderiv I I' immersion.toFun x first :=
    extensions.canonicalTangentExtensionAt_apply first
  have secondValue : secondExtension (immersion.toFun x) =
      mfderiv I I' immersion.toFun x second :=
    extensions.canonicalTangentExtensionAt_apply second
  have torsionIdentity := ambientLeviCivita.connection.torsion_eq_zero_iff.mp
    ambientLeviCivita.torsionFree
    (extensions.canonicalTangentExtensionAt_mdifferentiableAt first)
    (extensions.canonicalTangentExtensionAt_mdifferentiableAt second)
  have projectedIdentity := congrArg (splitting.normalProjection x) torsionIdentity
  have bracketZero : splitting.normalProjection x
      (VectorField.mlieBracket I' firstExtension secondExtension (immersion.toFun x)) = 0 := by
    exact extensions.normalProjection_canonicalTangentExtensionAt_mlieBracket_eq_zero
      splitting decomposition leftInverse first second
  change splitting.normalProjection x
      (ambientLeviCivita.connection secondExtension (immersion.toFun x)
        (mfderiv I I' immersion.toFun x first)) =
    splitting.normalProjection x
      (ambientLeviCivita.connection firstExtension (immersion.toFun x)
        (mfderiv I I' immersion.toFun x second))
  rw [← firstValue, ← secondValue]
  rw [map_sub, bracketZero] at projectedIdentity
  exact sub_eq_zero.mp projectedIdentity

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [I'.Boundaryless] in
/-- The germ-local second fundamental value is independent of the chosen immersion chart. -/
theorem projectedSecondFundamentalValueAt_independent
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (firstExtensions secondExtensions : LocalSubmanifoldExtensionDataAt immersion x)
    (first second : TangentSpace I x) :
    firstExtensions.projectedSecondFundamentalValueAt
        splitting ambientLeviCivita.connection decomposition leftInverse first second =
      secondExtensions.projectedSecondFundamentalValueAt
        splitting ambientLeviCivita.connection decomposition leftInverse first second := by
  apply Subtype.ext
  have fieldRegular : CMDiffAt 1
      (T% (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second)) x :=
    (SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x second).of_le (by norm_num)
  have independent := secondFundamentalFormAlongAt_independent splitting ambientLeviCivita
    firstExtensions secondExtensions
    (direction := SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first)
    fieldRegular
  simpa only [projectedSecondFundamentalValueAt, secondFundamentalFormAlongAt,
    ambientDerivativeTangentAt,
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self,
    canonicalTangentExtensionAt] using independent

/-- Algebraic bilinear packaging of the constructed germ-local second fundamental form. -/
def projectedSecondFundamentalLinearMapAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ]
      LinearMap.ker (splitting.tangentProjection x).toLinearMap where
  toFun first :=
    { toFun := fun second ↦
        extensions.projectedSecondFundamentalValueAt splitting ambientConnection
          decomposition leftInverse first second
      map_add' := fun second second' ↦
        extensions.projectedSecondFundamentalValueAt_add_second splitting ambientConnection
          decomposition leftInverse first second second'
      map_smul' := fun scalar second ↦
        extensions.projectedSecondFundamentalValueAt_smul_second splitting ambientConnection
          decomposition leftInverse scalar first second }
  map_add' first first' := by
    apply LinearMap.ext
    intro second
    exact extensions.projectedSecondFundamentalValueAt_add_first splitting ambientConnection
      decomposition leftInverse first first' second
  map_smul' scalar first := by
    apply LinearMap.ext
    intro second
    exact extensions.projectedSecondFundamentalValueAt_smul_first splitting ambientConnection
      decomposition leftInverse scalar first second

section ContinuousBilinear

variable
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]

/-- The local construction as a continuous bilinear map into the actual kernel-normal fiber. -/
def projectedSecondFundamentalFormAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      LinearMap.ker (splitting.tangentProjection x).toLinearMap :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (TangentSpace I x →ₗ[ℝ] LinearMap.ker
            (splitting.tangentProjection x).toLinearMap) ≃ₗ[ℝ]
          (TangentSpace I x →L[ℝ] LinearMap.ker
            (splitting.tangentProjection x).toLinearMap)).toLinearMap.comp
      (extensions.projectedSecondFundamentalLinearMapAt splitting ambientConnection
        decomposition leftInverse))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
@[simp]
theorem projectedSecondFundamentalFormAt_apply
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : TangentSpace I x) :
    extensions.projectedSecondFundamentalFormAt splitting ambientConnection
        decomposition leftInverse first second =
      extensions.projectedSecondFundamentalValueAt splitting ambientConnection
        decomposition leftInverse first second :=
  rfl

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- The continuous bilinear form constructed from local extensions is symmetric. -/
theorem projectedSecondFundamentalFormAt_comm
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (first second : TangentSpace I x) :
    extensions.projectedSecondFundamentalFormAt splitting ambientLeviCivita.connection
        decomposition leftInverse first second =
      extensions.projectedSecondFundamentalFormAt splitting ambientLeviCivita.connection
        decomposition leftInverse second first :=
  extensions.projectedSecondFundamentalValueAt_comm splitting ambientLeviCivita
    decomposition leftInverse first second

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [I'.Boundaryless] in
/-- The continuous bilinear form is independent of the chosen normal-form chart. -/
theorem projectedSecondFundamentalFormAt_independent
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (firstExtensions secondExtensions : LocalSubmanifoldExtensionDataAt immersion x) :
    firstExtensions.projectedSecondFundamentalFormAt
        splitting ambientLeviCivita.connection decomposition leftInverse =
      secondExtensions.projectedSecondFundamentalFormAt
        splitting ambientLeviCivita.connection decomposition leftInverse := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  exact projectedSecondFundamentalValueAt_independent splitting ambientLeviCivita
    decomposition leftInverse firstExtensions secondExtensions first second

end ContinuousBilinear

end LocalSubmanifoldExtensionDataAt

namespace SmoothIsometricEmbeddingData

variable
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [∀ q : M, FiniteDimensional ℝ (TangentSpace I q)]
  [∀ q : M, CompleteSpace (TangentSpace I q)]
  [∀ y : N, CompleteSpace (TangentSpace I' y)]

/-- The second fundamental form constructed directly from a smooth isometric embedding and the
ambient Levi--Civita connection.  No extension operator is supplied by the caller. -/
def localProjectedSecondFundamentalFormAt
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I') (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      LinearMap.ker
        (embedding.toSmoothIsometricImmersionData.orthogonalSplitting.tangentProjection x
          ).toLinearMap :=
  (embedding.localSubmanifoldExtensionDataAt x).projectedSecondFundamentalFormAt
    embedding.toSmoothIsometricImmersionData.orthogonalSplitting
    ambientLeviCivita.connection
    embedding.toSmoothIsometricImmersionData.hasTangentNormalDecomposition
    embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse

/-- The second fundamental form constructed from an isometric embedding is symmetric. -/
theorem localProjectedSecondFundamentalFormAt_comm
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I') (x : M)
    (first second : TangentSpace I x) :
    embedding.localProjectedSecondFundamentalFormAt ambientLeviCivita x first second =
      embedding.localProjectedSecondFundamentalFormAt ambientLeviCivita x second first :=
  (embedding.localSubmanifoldExtensionDataAt x).projectedSecondFundamentalFormAt_comm
    embedding.toSmoothIsometricImmersionData.orthogonalSplitting ambientLeviCivita
    embedding.toSmoothIsometricImmersionData.hasTangentNormalDecomposition
    embedding.toSmoothIsometricImmersionData.hasTangentProjectionLeftInverse first second

end SmoothIsometricEmbeddingData

end

end RiemannianFluids
