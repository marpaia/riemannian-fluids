import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Sign and positivity conventions

The sign of a Laplacian is a convention, but not an innocent one. Analysts often prefer the nonnegative operator because its quadratic form measures
dissipation:

    ⟨L u,u⟩ ≥ 0.

Geometers often write the opposite signed differential operator. Either choice is consistent; mixing the two reverses the sign of viscosity in the
energy law.

This repository reserves `L_...` for the analysis-positive choice. In particular,

    L_Hodge = d d* + d* d.

Chan--Czubak--Disconzi, arXiv:1608.05114v2, instead state after equation (1.3)

    Δ_H = -(d d* + d* d),

so the translation used throughout the formal analysis is

    L_Hodge = -Δ_H.

## Positivity needs a domain

A differential operator is usually unbounded. Its quadratic-form inequality is true only on fields with sufficient regularity and the relevant
boundary or constraint conditions. Modeling it as a bare linear endomorphism and asserting positivity for every element would erase that analytical
content.

`IsNonnegativeOn A Admissible` instead says

    Admissible(u) ⇒ 0 ≤ ⟨Au,u⟩.

The predicate can later stand for a Sobolev domain, boundary condition, or incompressibility constraint. `PositiveOperatorOn` merely packages an
operator with this proof. No self-adjointness, coercivity, or closedness is silently included; those are separate mathematical properties when the
analysis needs them.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/--
A linear operator is nonnegative on the fields selected by `Admissible`.

Mathematically this says `⟪Au,u⟫ ≥ 0`, but only for fields in the operator's domain. The predicate argument stands in for domain, boundary, and
constraint hypotheses that an unbounded differential operator cannot encode in the type `V →ₗ[ℝ] V` alone.
-/
def IsNonnegativeOn (A : V →ₗ[ℝ] V) (Admissible : V → Prop) : Prop :=
  ∀ u, Admissible u → 0 ≤ inner ℝ (A u) u

/--
A proof-carrying analysis-positive operator on a specified admissible space. The structure is intentionally small: it packages the operator with
exactly the quadratic-form fact consumed by the energy argument.
-/
structure PositiveOperatorOn (Admissible : V → Prop) where
  operator : V →ₗ[ℝ] V
  nonnegative : IsNonnegativeOn V operator Admissible

end RiemannianFluids
