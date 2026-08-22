import RiemannianFluids.Geometry.Connections
import RiemannianFluids.Geometry.LocalSubmanifoldExtensions

/-!
# Germ-local induced submanifold derivatives

This module differentiates the chart-constructed ambient extensions from
`LocalSubmanifoldExtensions` and projects the result into tangent and normal summands.  The
resulting first-order values are independent of the chosen immersion normal form: a
Levi--Civita derivative in an immersed tangent direction sees only the restricted field germ.

This is the local counterpart of the older global `SubmanifoldFieldExtensionData` engine.  It is
the bridge required to move the CCG25 argument from a global extension oracle to the
neighborhood-level extensions used in the source.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

/-- Differentiate the chosen local ambient extension of a source tangent field at the center. -/
def ambientDerivativeTangentAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (direction field : (q : M) → TangentSpace I q) :
    TangentSpace I' (immersion.toFun x) :=
  ambientConnection (extensions.tangentExtension field) (immersion.toFun x)
    (mfderiv I I' immersion.toFun x (direction x))

/-- Differentiate the chosen local extension of an ambient field along the immersion. -/
def ambientDerivativeAlongAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (direction : (q : M) → TangentSpace I q)
    (field : AmbientVectorFieldAlong immersion) :
    TangentSpace I' (immersion.toFun x) :=
  ambientConnection (extensions.alongExtension field) (immersion.toFun x)
    (mfderiv I I' immersion.toFun x (direction x))

/-- Tangential projection of the germ-local ambient derivative. -/
def intrinsicDerivativeAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (direction field : (q : M) → TangentSpace I q) : TangentSpace I x :=
  splitting.tangentProjection x
    (extensions.ambientDerivativeTangentAt ambientConnection direction field)

/-- Normal projection of the germ-local ambient derivative. -/
def secondFundamentalFormAlongAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (direction field : (q : M) → TangentSpace I q) :
    TangentSpace I' (immersion.toFun x) :=
  splitting.normalProjection x
    (extensions.ambientDerivativeTangentAt ambientConnection direction field)

/-- Normal projection of the derivative of a field along the immersion. -/
def normalDerivativeAt
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (direction : (q : M) → TangentSpace I q)
    (field : AmbientVectorFieldAlong immersion) :
    TangentSpace I' (immersion.toFun x) :=
  splitting.normalProjection x
    (extensions.ambientDerivativeAlongAt ambientConnection direction field)

omit [I.Boundaryless] [CompleteSpace E'] [FiniteDimensional ℝ E']
  [I'.Boundaryless] [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)] in
/-- Gauss' tangent/normal decomposition is already valid for the local ambient derivative. -/
theorem ambientDerivativeTangentAt_eq_gauss
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (direction field : (q : M) → TangentSpace I q) :
    extensions.ambientDerivativeTangentAt ambientConnection direction field =
      mfderiv I I' immersion.toFun x
          (extensions.intrinsicDerivativeAt splitting ambientConnection direction field) +
        extensions.secondFundamentalFormAlongAt splitting ambientConnection direction field := by
  exact (decomposition x
    (extensions.ambientDerivativeTangentAt ambientConnection direction field)).symm

omit [I.Boundaryless] [I'.Boundaryless] in
/-- Two chart-local tangent extensions give the same Levi--Civita derivative at the center. -/
theorem ambientDerivativeTangentAt_independent
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (firstExtensions secondExtensions : LocalSubmanifoldExtensionDataAt immersion x)
    {direction field : (q : M) → TangentSpace I q}
    (fieldRegular : CMDiffAt 1 (T% field) x) :
    firstExtensions.ambientDerivativeTangentAt ambientLeviCivita.connection direction field =
      secondExtensions.ambientDerivativeTangentAt
        ambientLeviCivita.connection direction field := by
  have hfirst : MDiffAt (T% (firstExtensions.tangentExtension field))
      (immersion.toFun x) :=
    (firstExtensions.tangentExtension_contMDiffAt
      (n := 1) (by simp) fieldRegular).mdifferentiableAt one_ne_zero
  have hsecond : MDiffAt (T% (secondExtensions.tangentExtension field))
      (immersion.toFun x) :=
    (secondExtensions.tangentExtension_contMDiffAt
      (n := 1) (by simp) fieldRegular).mdifferentiableAt one_ne_zero
  have agreement :
      (fun q ↦ firstExtensions.tangentExtension field (immersion.toFun q)) =ᶠ[nhds x]
        fun q ↦ secondExtensions.tangentExtension field (immersion.toFun q) :=
    (firstExtensions.tangentExtension_agrees field).trans
      (secondExtensions.tangentExtension_agrees field).symm
  exact ambientLeviCivita.eq_on_mfderiv_of_comp_eventuallyEq I'
    (immersion.contMDiff.mdifferentiableAt (by simp)) hfirst hsecond agreement
    (direction x)

omit [I.Boundaryless] [I'.Boundaryless] in
/-- Two chart-local extensions of a field along the immersion give the same normal derivative
at the center. -/
theorem ambientDerivativeAlongAt_independent
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (firstExtensions secondExtensions : LocalSubmanifoldExtensionDataAt immersion x)
    {direction : (q : M) → TangentSpace I q}
    {field : AmbientVectorFieldAlong immersion}
    (fieldRegular : CMDiffAt 1
      (fun q ↦ (⟨immersion.toFun q, field q⟩ : TangentBundle I' N)) x) :
    firstExtensions.ambientDerivativeAlongAt ambientLeviCivita.connection direction field =
      secondExtensions.ambientDerivativeAlongAt
        ambientLeviCivita.connection direction field := by
  have hfirst : MDiffAt (T% (firstExtensions.alongExtension field))
      (immersion.toFun x) :=
    (firstExtensions.alongExtension_contMDiffAt
      (n := 1) (by simp) fieldRegular).mdifferentiableAt one_ne_zero
  have hsecond : MDiffAt (T% (secondExtensions.alongExtension field))
      (immersion.toFun x) :=
    (secondExtensions.alongExtension_contMDiffAt
      (n := 1) (by simp) fieldRegular).mdifferentiableAt one_ne_zero
  have agreement :
      (fun q ↦ firstExtensions.alongExtension field (immersion.toFun q)) =ᶠ[nhds x]
        fun q ↦ secondExtensions.alongExtension field (immersion.toFun q) :=
    (firstExtensions.alongExtension_agrees field).trans
      (secondExtensions.alongExtension_agrees field).symm
  exact ambientLeviCivita.eq_on_mfderiv_of_comp_eventuallyEq I'
    (immersion.contMDiff.mdifferentiableAt (by simp)) hfirst hsecond agreement
    (direction x)

omit [I.Boundaryless] [I'.Boundaryless] in
/-- The tangential local derivative does not depend on the normal-form chart. -/
theorem intrinsicDerivativeAt_independent
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (firstExtensions secondExtensions : LocalSubmanifoldExtensionDataAt immersion x)
    {direction field : (q : M) → TangentSpace I q}
    (fieldRegular : CMDiffAt 1 (T% field) x) :
    firstExtensions.intrinsicDerivativeAt splitting ambientLeviCivita.connection direction field =
      secondExtensions.intrinsicDerivativeAt
        splitting ambientLeviCivita.connection direction field := by
  exact congrArg (splitting.tangentProjection x)
    (ambientDerivativeTangentAt_independent ambientLeviCivita
      firstExtensions secondExtensions fieldRegular)

omit [I.Boundaryless] [I'.Boundaryless] in
/-- The local second fundamental value does not depend on the normal-form chart. -/
theorem secondFundamentalFormAlongAt_independent
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (firstExtensions secondExtensions : LocalSubmanifoldExtensionDataAt immersion x)
    {direction field : (q : M) → TangentSpace I q}
    (fieldRegular : CMDiffAt 1 (T% field) x) :
    firstExtensions.secondFundamentalFormAlongAt
        splitting ambientLeviCivita.connection direction field =
      secondExtensions.secondFundamentalFormAlongAt
        splitting ambientLeviCivita.connection direction field := by
  exact congrArg (splitting.normalProjection x)
    (ambientDerivativeTangentAt_independent ambientLeviCivita
      firstExtensions secondExtensions fieldRegular)

omit [I.Boundaryless] [I'.Boundaryless] in
/-- The local normal derivative does not depend on the normal-form chart. -/
theorem normalDerivativeAt_independent
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (firstExtensions secondExtensions : LocalSubmanifoldExtensionDataAt immersion x)
    {direction : (q : M) → TangentSpace I q}
    {field : AmbientVectorFieldAlong immersion}
    (fieldRegular : CMDiffAt 1
      (fun q ↦ (⟨immersion.toFun q, field q⟩ : TangentBundle I' N)) x) :
    firstExtensions.normalDerivativeAt
        splitting ambientLeviCivita.connection direction field =
      secondExtensions.normalDerivativeAt
        splitting ambientLeviCivita.connection direction field := by
  exact congrArg (splitting.normalProjection x)
    (ambientDerivativeAlongAt_independent ambientLeviCivita
      firstExtensions secondExtensions fieldRegular)

end LocalSubmanifoldExtensionDataAt

end

end RiemannianFluids
