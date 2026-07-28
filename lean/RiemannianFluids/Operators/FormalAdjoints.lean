import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Formal adjoints and second-order energy operators -/

namespace RiemannianFluids

open scoped InnerProduct

/-- A bounded adjoint pair on actual Hilbert spaces.  This is an adapter to Mathlib's canonical
continuous-linear-map adjoint, not a second definition of it. -/
structure BoundedHilbertAdjointData
    (Domain Codomain : Type*)
    [NormedAddCommGroup Domain] [InnerProductSpace ℝ Domain] [CompleteSpace Domain]
    [NormedAddCommGroup Codomain] [InnerProductSpace ℝ Codomain] [CompleteSpace Codomain] where
  operator : Domain →L[ℝ] Codomain
  proposedAdjoint : Codomain →L[ℝ] Domain

/-- The proposed bounded adjoint is exactly Mathlib's adjoint. -/
def IsBoundedHilbertAdjointPair
    {Domain Codomain : Type*}
    [NormedAddCommGroup Domain] [InnerProductSpace ℝ Domain] [CompleteSpace Domain]
    [NormedAddCommGroup Codomain] [InnerProductSpace ℝ Codomain] [CompleteSpace Codomain]
    (data : BoundedHilbertAdjointData Domain Codomain) : Prop :=
  data.proposedAdjoint = data.operator†

/-- Mathlib's defining inner-product identity for a registered bounded adjoint pair. -/
theorem boundedHilbertAdjoint_inner
    {Domain Codomain : Type*}
    [NormedAddCommGroup Domain] [InnerProductSpace ℝ Domain] [CompleteSpace Domain]
    [NormedAddCommGroup Codomain] [InnerProductSpace ℝ Codomain] [CompleteSpace Codomain]
    (data : BoundedHilbertAdjointData Domain Codomain)
    (h : IsBoundedHilbertAdjointPair data) (u : Domain) (v : Codomain) :
    inner ℝ (data.operator u) v = inner ℝ u (data.proposedAdjoint v) := by
  rw [h]
  exact (ContinuousLinearMap.adjoint_inner_right data.operator u v).symm

/-- Pairings and a possibly unbounded first-order operator together with its proposed formal
adjoint.  Unlike `BoundedHilbertAdjointData`, this explicitly retains test domains. -/
structure FormalAdjointData (Domain Codomain : Type*) where
  domainPairing : Domain → Domain → ℝ
  codomainPairing : Codomain → Codomain → ℝ
  operator : Domain → Codomain
  adjoint : Codomain → Domain
  isCompactDomainTest : Domain → Prop
  isCompactCodomainTest : Codomain → Prop

def IsFormalAdjointPair
    {Domain Codomain : Type*}
    (data : FormalAdjointData Domain Codomain) : Prop :=
  ∀ u v,
    data.isCompactDomainTest u → data.isCompactCodomainTest v →
      data.codomainPairing (data.operator u) v =
        data.domainPairing u (data.adjoint v)

/-- Covariant derivative and `Def` formal-adjoint data kept separate. -/
structure ViscousFormalAdjoints (Vector CovariantTensor SymmetricTensor : Type*) where
  covariantDerivative : FormalAdjointData Vector CovariantTensor
  deformationTensor : FormalAdjointData Vector SymmetricTensor
  roughLaplacian : Vector → Vector
  deformationLaplacian : Vector → Vector

def HasRoughLaplacianConstruction
    {Vector CovariantTensor SymmetricTensor : Type*}
    (data : ViscousFormalAdjoints Vector CovariantTensor SymmetricTensor) : Prop :=
  ∀ u,
    data.roughLaplacian u =
      data.covariantDerivative.adjoint (data.covariantDerivative.operator u)

def HasDeformationLaplacianConstruction
    {Vector CovariantTensor SymmetricTensor : Type*}
    [AddCommGroup Vector]
    (data : ViscousFormalAdjoints Vector CovariantTensor SymmetricTensor) : Prop :=
  ∀ u,
    data.deformationLaplacian u =
      data.deformationTensor.adjoint (data.deformationTensor.operator u) +
        data.deformationTensor.adjoint (data.deformationTensor.operator u)

end RiemannianFluids
