import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Formal adjoints and second-order energy operators -/

namespace RiemannianFluids

/-- Pairings and a first-order operator together with its proposed formal adjoint. -/
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
