import RiemannianFluids.ProofStatus
import RiemannianFluids.Operators.GeometricIdentities

/-!
# CZ24 operator-census contract

Czubak's 2024 Notices survey emphasizes that the rough/Bochner, Hodge, and deformation constructions are not one context-free vector Laplacian on a
curved manifold. The broad survey sentence is made falsifiable here: for a fixed curved witness, the three resulting linear maps are pairwise
distinct.

The current route takes a divergence-free field on which Ricci acts nontrivially. CCD17's Weitzenbock and deformation/Hodge identities then distinguish
all three operators. Constructing such a witness on a concrete curved manifold remains separate from this conditional route; the statement does not
claim that every curved manifold distinguishes all candidates.
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

/-- The precise operator-census conclusion for a fixed geometric realization: all three candidate linear maps are distinct. -/
def cz24OperatorCensusStatement
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity) : Prop :=
  operators.roughLaplacian ≠ operators.hodgeLaplacian I regularity connection smooth ∧
    operators.roughLaplacian ≠ operators.deformationLaplacian ∧
    operators.hodgeLaplacian I regularity connection smooth ≠ operators.deformationLaplacian

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/--
The source-level inequivalence route from a divergence-free curved witness.  This comparison is
pure assembly: CCD17 identifies the three operator values on the witness, and nonvanishing
Ricci action separates them.  A concrete CZ24 reproduction must still construct such a witness;
that geometric existence statement belongs below this interface rather than in this algebraic
comparison.
-/
@[proof_assembly]
theorem cz24_operator_census_of_curved_witness
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity)
    (hWeitzenbock : WeitzenbockIdentity I regularity connection smooth operators)
    (hSymmetric : SymmetricGradientIdentity I regularity connection smooth operators)
    (field : SmoothVectorField (M := M) I (SecondOrderRegularity regularity))
    (hdiv : IsDivergenceFree I connection (regularity + 1) smooth field)
    (hRicci : operators.ricci.action I regularity field ≠ 0) :
    cz24OperatorCensusStatement I regularity connection smooth operators := by
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

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Literature-facing CZ24 route. Its transitive axiom audit remains open until the curved-witness comparison above is proved. -/
@[literature_terminal]
theorem cz24_operator_census_route
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity)
    (hWeitzenbock : WeitzenbockIdentity I regularity connection smooth operators)
    (hSymmetric : SymmetricGradientIdentity I regularity connection smooth operators)
    (field : SmoothVectorField (M := M) I (SecondOrderRegularity regularity))
    (hdiv : IsDivergenceFree I connection (regularity + 1) smooth field)
    (hRicci : operators.ricci.action I regularity field ≠ 0) :
    cz24OperatorCensusStatement I regularity connection smooth operators :=
  cz24_operator_census_of_curved_witness I regularity connection smooth operators hWeitzenbock hSymmetric field hdiv hRicci

end RiemannianFluids
