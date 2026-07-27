import RiemannianFluids.Conventions

/-!
# Competing vector Laplacians

In flat Euclidean coordinates, several routes to a vector Laplacian give the same componentwise expression. On a curved manifold the commutation of
covariant derivatives produces curvature, and the routes separate:

    rough:         ∇*∇,
    Hodge:         d d* + d* d,
    deformation:   2 Def* Def.

The ambiguity is one of the central observations of CCD17 and the later viscosity-operator literature. Naming all three is therefore part of the
mathematics; choosing one silently would erase the question the repository is trying to study.

## Selection and comparison are different operations

`ViscosityCandidates` stores the three linear maps without a privileged default. `operator` selects one only from an explicit `ViscosityModel`. Its
three simplification lemmas are definitional checks that each selector branch returns the corresponding field.

Two operators can fail to be globally equal but agree after a constraint is imposed. If

    A = B + C

and `C u = 0` for every admissible `u`, then `A u = B u` on that class. The definitions `OperatorComparison` and `OperatorsAgreeOn`, followed by
`agreeOn_of_correction_eq_zero`, formalize exactly this reduction. The CCD17 specialization is the geometric instance: the correction is `d d*`, and
the admissible fields are divergence-free.

This module remains convention- and source-neutral. It supplies the logical vocabulary for comparing operators; `GeometricIdentities` supplies the
actual Ricci and grad-div correction in the CCD17 convention.
-/

namespace RiemannianFluids

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/--
The three intrinsic viscosity constructions compared by the project. The enumeration is a choice of model, not a theorem that the models agree.
-/
inductive ViscosityModel where
  | rough
  | hodge
  | deformation
  deriving DecidableEq, Repr

/--
A family containing each candidate without declaring any one canonical. The shared endomorphism type is appropriate for abstract energy arguments; the
geometric CCD17 layer uses a more precise regularity-losing operator type.
-/
structure ViscosityCandidates where
  rough : V →ₗ[ℝ] V
  hodge : V →ₗ[ℝ] V
  deformation : V →ₗ[ℝ] V

namespace ViscosityCandidates

/--
Select a candidate only after an explicit `ViscosityModel` is supplied. The three equations are deliberately exhaustive and contain no fallback
choice.
-/
def operator (operators : ViscosityCandidates V) : ViscosityModel → V →ₗ[ℝ] V
  | .rough => operators.rough
  | .hodge => operators.hodge
  | .deformation => operators.deformation

/-- Selecting `.rough` is definitionally projection of the rough candidate. -/
@[simp] theorem operator_rough (operators : ViscosityCandidates V) :
    operator V operators ViscosityModel.rough = operators.rough := rfl

/-- Selecting `.hodge` is definitionally projection of the Hodge candidate. -/
@[simp] theorem operator_hodge (operators : ViscosityCandidates V) :
    operator V operators ViscosityModel.hodge = operators.hodge := rfl

/-- Selecting `.deformation` is definitionally projection of the strain candidate. -/
@[simp] theorem operator_deformation (operators : ViscosityCandidates V) :
    operator V operators ViscosityModel.deformation = operators.deformation := rfl

end ViscosityCandidates

/--
Two operators agree on the fields satisfying `Admissible`. Equality on a constraint set is weaker than equality of linear maps and is the right notion
when a correction vanishes only for divergence-free fields.
-/
def OperatorsAgreeOn (A B : V →ₗ[ℝ] V) (Admissible : V → Prop) : Prop :=
  ∀ u, Admissible u → A u = B u

/-- Every operator agrees with itself on every admissible class. -/
theorem operatorsAgreeOn_refl (A : V →ₗ[ℝ] V) (Admissible : V → Prop) :
    OperatorsAgreeOn V A A Admissible := by
  -- Fix an arbitrary admissible field; both sides are literally `A u`.
  intro u hu
  rfl

/-- Agreement on an admissible class is symmetric. -/
theorem operatorsAgreeOn_symm {A B : V →ₗ[ℝ] V} {Admissible : V → Prop}
    (h : OperatorsAgreeOn V A B Admissible) : OperatorsAgreeOn V B A Admissible := by
  -- Specialize the original agreement proof to an admissible field.
  intro u hu
  -- Reverse the resulting equality.
  exact (h u hu).symm

/-- Agreement on an admissible class is transitive. -/
theorem operatorsAgreeOn_trans {A B C : V →ₗ[ℝ] V} {Admissible : V → Prop}
    (hAB : OperatorsAgreeOn V A B Admissible)
    (hBC : OperatorsAgreeOn V B C Admissible) :
    OperatorsAgreeOn V A C Admissible := by
  -- Fix an arbitrary admissible field.
  intro u hu
  -- Chain `A u = B u` and `B u = C u`.
  exact (hAB u hu).trans (hBC u hu)

/--
A convention-neutral comparison identity. Curvature, grad-div, or boundary corrections can be supplied as `correction` by later geometric modules.
-/
structure OperatorComparison (lhs rhs correction : V →ₗ[ℝ] V) : Prop where
  /-- The global operator identity before any admissibility condition is used. -/
  identity : lhs = rhs + correction

/-- A comparison identity becomes operator agreement wherever its correction vanishes. -/
theorem OperatorComparison.agreeOn_of_correction_eq_zero
    {lhs rhs correction : V →ₗ[ℝ] V} {Admissible : V → Prop}
    (comparison : OperatorComparison V lhs rhs correction)
    (hCorrection : ∀ u, Admissible u → correction u = 0) :
    OperatorsAgreeOn V lhs rhs Admissible := by
  -- Fix an admissible input.
  intro u hu
  -- Replace `lhs` by `rhs + correction` using the global comparison identity.
  rw [comparison.identity]
  -- The supplied vanishing theorem removes the correction on this input.
  simp [hCorrection u hu]

end RiemannianFluids
