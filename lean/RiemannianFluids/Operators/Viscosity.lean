import RiemannianFluids.Conventions

/-!
# Competing vector Laplacians

The rough/Bochner, Hodge, and deformation operators are kept as distinct
named candidates.  This module contains no default selection.  Concrete
geometric rungs will construct the candidates and prove comparison identities.
-/

namespace RiemannianFluids

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- The three intrinsic viscosity operators compared by the project. -/
inductive ViscosityModel where
  | rough
  | hodge
  | deformation
  deriving DecidableEq, Repr

/-- A family containing each candidate without declaring any one canonical. -/
structure ViscosityCandidates where
  rough : V →ₗ[ℝ] V
  hodge : V →ₗ[ℝ] V
  deformation : V →ₗ[ℝ] V

namespace ViscosityCandidates

/-- Select a candidate only after an explicit `ViscosityModel` is supplied. -/
def operator (operators : ViscosityCandidates V) : ViscosityModel → V →ₗ[ℝ] V
  | .rough => operators.rough
  | .hodge => operators.hodge
  | .deformation => operators.deformation

@[simp] theorem operator_rough (operators : ViscosityCandidates V) :
    operator V operators ViscosityModel.rough = operators.rough := rfl

@[simp] theorem operator_hodge (operators : ViscosityCandidates V) :
    operator V operators ViscosityModel.hodge = operators.hodge := rfl

@[simp] theorem operator_deformation (operators : ViscosityCandidates V) :
    operator V operators ViscosityModel.deformation = operators.deformation := rfl

end ViscosityCandidates

/-- Two operators agree on the fields satisfying `Admissible`. -/
def OperatorsAgreeOn (A B : V →ₗ[ℝ] V) (Admissible : V → Prop) : Prop :=
  ∀ u, Admissible u → A u = B u

theorem operatorsAgreeOn_refl (A : V →ₗ[ℝ] V) (Admissible : V → Prop) :
    OperatorsAgreeOn V A A Admissible := by
  intro u hu
  rfl

theorem operatorsAgreeOn_symm {A B : V →ₗ[ℝ] V} {Admissible : V → Prop}
    (h : OperatorsAgreeOn V A B Admissible) : OperatorsAgreeOn V B A Admissible := by
  intro u hu
  exact (h u hu).symm

theorem operatorsAgreeOn_trans {A B C : V →ₗ[ℝ] V} {Admissible : V → Prop}
    (hAB : OperatorsAgreeOn V A B Admissible)
    (hBC : OperatorsAgreeOn V B C Admissible) :
    OperatorsAgreeOn V A C Admissible := by
  intro u hu
  exact (hAB u hu).trans (hBC u hu)

/--
A convention-neutral comparison identity.  Curvature, grad-div, or boundary
corrections can be supplied as `correction` by later geometric modules.
-/
structure OperatorComparison (lhs rhs correction : V →ₗ[ℝ] V) : Prop where
  identity : lhs = rhs + correction

/-- A comparison identity becomes operator agreement wherever its correction vanishes. -/
theorem OperatorComparison.agreeOn_of_correction_eq_zero
    {lhs rhs correction : V →ₗ[ℝ] V} {Admissible : V → Prop}
    (comparison : OperatorComparison V lhs rhs correction)
    (hCorrection : ∀ u, Admissible u → correction u = 0) :
    OperatorsAgreeOn V lhs rhs Admissible := by
  intro u hu
  rw [comparison.identity]
  simp [hCorrection u hu]

end RiemannianFluids
