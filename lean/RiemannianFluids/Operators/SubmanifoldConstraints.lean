import Mathlib.Geometry.Manifold.VectorField.LieBracket
import RiemannianFluids.Geometry.Musical
import RiemannianFluids.Operators.Restriction
import RiemannianFluids.Tensors.VectorCalculus

/-!
# Concrete constraints for ambient and submanifold vector fields

Thin-shell papers impose hypotheses simultaneously on an ambient velocity and its surface
trace.  This module states those hypotheses on Mathlib tangent-bundle sections.  The source
papers may still supply geometric constructions that Mathlib lacks (for example the Lie
derivative of a one-form along a chosen normal), but their types and defining identities are
kept inspectable here.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H']
  (I' : ModelWithCorners ℝ E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 2 N]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [RiemannianBundle (TangentSpace I' : N → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I' 1 E' (TangentSpace I' : N → Type _)]

/-- An ambient velocity together with the intrinsic surface velocity it extends. -/
structure AmbientSurfaceVectorField (regularity : ℕ∞ω) where
  ambient : SmoothVectorField (M := N) I' regularity
  surface : SmoothVectorField (M := M) I regularity

/-- The two fields agree along the immersion before tangential projection. -/
def IsCompatibleAmbientSurfaceVectorField
    (regularity : ℕ∞ω)
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (field : AmbientSurfaceVectorField (M := M) (N := N) I I' regularity) : Prop :=
  ExtendsTangentField immersion field.ambient field.surface

/-- The paired incompressibility hypothesis used in thin-shell restriction results:
ambient divergence vanishes in the shell and intrinsic divergence vanishes on the surface. -/
def IsAmbientAndSurfaceDivergenceFree
    (regularity : ℕ∞ω)
    (ambientConnection : LeviCivitaConnection (M := N) I')
    (ambientSmooth : LeviCivitaConnection.IsContMDiff I' ambientConnection regularity)
    (surfaceConnection : LeviCivitaConnection (M := M) I)
    (surfaceSmooth : LeviCivitaConnection.IsContMDiff I surfaceConnection regularity)
    (field : AmbientSurfaceVectorField (M := M) (N := N) I I' (regularity + 1)) : Prop :=
  IsDivergenceFree I' ambientConnection regularity ambientSmooth field.ambient ∧
    IsDivergenceFree I surfaceConnection regularity surfaceSmooth field.surface

/-- Tangential projection of the Lie bracket of a chosen ambient normal with a velocity. -/
def tangentialNormalLieBracket
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (normal velocity : (y : N) → TangentSpace I' y) :
    (x : M) → TangentSpace I x :=
  tangentialRestriction immersion splitting
    (VectorField.mlieBracket I' normal velocity)

/-- Homogeneous perfect Navier slip in the Lie-bracket form used by CCF25:
the tangential component of `[N,v]` vanishes on the boundary. -/
def HasHomogeneousNavierLieBoundary
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (normal velocity : (y : N) → TangentSpace I' y) : Prop :=
  tangentialNormalLieBracket I I' immersion splitting normal velocity = 0

/-- The missing but geometrically typed operations needed to state the Hodge boundary
condition: a chosen smooth ambient normal, Lie derivative of an ambient one-form along an
arbitrary smooth ambient vector field, and pullback to the hypersurface.  Storing the vector
argument of `lieDerivative` prevents the source's normal derivative from being hidden behind an
unindexed `Form -> Form` observable. -/
structure NormalOneFormLieDerivativeData (regularity : ℕ∞ω) where
  normal : SmoothVectorField (M := N) I' regularity
  lieDerivative :
    SmoothVectorField (M := N) I' regularity →
      SmoothOneForm (M := N) I' regularity → SmoothOneForm (M := N) I' regularity
  pullback :
    SmoothOneForm (M := N) I' regularity → SmoothOneForm (M := M) I regularity

/-- Lie derivative along the selected normal field. -/
def NormalOneFormLieDerivativeData.normalLieDerivative
    (regularity : ℕ∞ω)
    (operations :
      NormalOneFormLieDerivativeData (M := M) (N := N) I I' regularity) :
    SmoothOneForm (M := N) I' regularity → SmoothOneForm (M := N) I' regularity :=
  operations.lieDerivative operations.normal

/-- The supplied pullback is the differential-geometric pullback along the immersion. -/
def IsOneFormPullbackAlongImmersion
    (regularity : ℕ∞ω)
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (operations :
      NormalOneFormLieDerivativeData (M := M) (N := N) I I' regularity) : Prop :=
  ∀ form x tangent,
    operations.pullback form x tangent =
      form (immersion.toFun x) (mfderiv I I' immersion.toFun x tangent)

/-- Homogeneous Hodge slip in CCF25's invariant form:
`i⁺(ℒ_N(v♭)) = 0`.  Metric lowering is the concrete repository operation. -/
def HasHomogeneousHodgeLieBoundary
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I' regularity E'
      (TangentSpace I' : N → Type _)]
  (operations :
      NormalOneFormLieDerivativeData (M := M) (N := N) I I' regularity)
    (velocity : SmoothVectorField (M := N) I' regularity) : Prop :=
  operations.pullback
      (operations.lieDerivative operations.normal (flat I' regularity velocity)) = 0

end

end RiemannianFluids
