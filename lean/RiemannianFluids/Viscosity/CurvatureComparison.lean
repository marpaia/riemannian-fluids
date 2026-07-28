import RiemannianFluids.Operators.GeometricIdentities
import RiemannianFluids.Operators.Viscosity

/-!
# Curvature separates the intrinsic viscosity candidates

The rough, Hodge, and deformation Laplacians agree in Euclidean coordinates for reasons that
do not survive commuting covariant derivatives.  The intellectual thread running from the
classical operator comparison to the recent viscosity-selection literature is therefore:

1. construct the three candidates independently;
2. derive the Weitzenbock and symmetric-gradient comparison identities;
3. impose incompressibility only after the full identity is visible; and
4. ask which geometry or physical limiting procedure selects a candidate.

`Operators.GeometricIdentities` carries out the algebraic middle of this program.  Its
geometric Weitzenbock and formal-adjoint inputs remain explicit theorem hypotheses.  This
module records the important consequence for the *space of candidates*: a single
divergence-free field with nonzero Ricci action distinguishes all three operators.

This is stronger and more reusable than a paper census.  It says exactly what a curved
witness must accomplish, while leaving the genuinely geometric existence question visible.
-/

namespace RiemannianFluids

open Bundle
open scoped ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- Pairwise inequivalence of the three intrinsic viscosity candidates. -/
def CandidateOperatorsPairwiseDistinct
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity) : Prop :=
  operators.roughLaplacian ≠ operators.hodgeLaplacian I regularity connection smooth ∧
    operators.roughLaplacian ≠ operators.deformationLaplacian ∧
    operators.hodgeLaplacian I regularity connection smooth ≠
      operators.deformationLaplacian

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/--
A divergence-free field on which Ricci acts nontrivially is a witness that the rough, Hodge,
and deformation candidates are pairwise distinct.
-/
theorem candidateOperators_pairwiseDistinct_of_curvatureWitness
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity)
    (hWeitzenbock : WeitzenbockIdentity I regularity connection smooth operators)
    (hSymmetric : SymmetricGradientIdentity I regularity connection smooth operators)
    (field : SmoothVectorField (M := M) I (SecondOrderRegularity regularity))
    (hdiv : IsDivergenceFree I connection (regularity + 1) smooth field)
    (hRicci : operators.ricci.action I regularity field ≠ 0) :
    CandidateOperatorsPairwiseDistinct I regularity connection smooth operators := by
  have hRoughAt :
      operators.roughLaplacian field =
        operators.hodgeLaplacian I regularity connection smooth field -
          operators.ricci.action I regularity field := by
    rw [hWeitzenbock]
    rfl
  have hDeformationAt :=
    ccd17_divfree_def_hodge I regularity connection smooth operators
      hWeitzenbock hSymmetric field hdiv
  refine ⟨?_, ?_, ?_⟩
  · intro hOperators
    have hAt := congrArg (fun operator => operator field) hOperators
    have hDifference :
        operators.hodgeLaplacian I regularity connection smooth field -
            operators.ricci.action I regularity field =
          operators.hodgeLaplacian I regularity connection smooth field :=
      hRoughAt.symm.trans hAt
    exact hRicci (sub_eq_self.mp hDifference)
  · intro hOperators
    have hAt := congrArg (fun operator => operator field) hOperators
    have hDifference :
        operators.hodgeLaplacian I regularity connection smooth field -
            operators.ricci.action I regularity field =
          operators.hodgeLaplacian I regularity connection smooth field -
            (2 : ℝ) • operators.ricci.action I regularity field :=
      hRoughAt.symm.trans (hAt.trans hDeformationAt)
    have hRicciDouble :
        operators.ricci.action I regularity field =
          (2 : ℝ) • operators.ricci.action I regularity field :=
      sub_right_inj.mp hDifference
    exact hRicci (by
      rw [two_smul] at hRicciDouble
      have hZero :
          (0 : SmoothVectorField (M := M) I regularity) +
              operators.ricci.action I regularity field =
            operators.ricci.action I regularity field +
              operators.ricci.action I regularity field := by
        simpa using hRicciDouble
      exact (add_right_cancel hZero).symm)
  · intro hOperators
    have hAt := congrArg (fun operator => operator field) hOperators
    have hDifference :
        operators.hodgeLaplacian I regularity connection smooth field -
            (2 : ℝ) • operators.ricci.action I regularity field =
          operators.hodgeLaplacian I regularity connection smooth field :=
      hDeformationAt.symm.trans hAt.symm
    have hTwiceRicci :
        (2 : ℝ) • operators.ricci.action I regularity field = 0 :=
      sub_eq_self.mp hDifference
    exact hRicci ((smul_eq_zero.mp hTwiceRicci).resolve_left (by norm_num))

end RiemannianFluids
