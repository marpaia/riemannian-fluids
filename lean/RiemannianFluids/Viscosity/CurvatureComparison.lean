import RiemannianFluids.Operators.GeometricIdentities
import RiemannianFluids.Operators.ConstructedHodge
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

/-! ## Constructed pointwise census -/

/-- Pairwise distinction of the actual constructed rough, Hodge, and deformation tangent-vector
outputs at a chosen point and field. -/
def ConstructedCandidateOutputsPairwiseDistinct
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x) : Prop :=
  roughLaplacianAt I connection.connection x regular field hfield ≠
      hodgeLaplacianConstructedAt I connection.connection x regular field hfield ∧
    roughLaplacianAt I connection.connection x regular field hfield ≠
      deformationLaplacianAt I connection.connection x regular field hfield ∧
    hodgeLaplacianConstructedAt I connection.connection x regular field hfield ≠
      deformationLaplacianAt I connection.connection x regular field hfield

/-- Pairwise distinction of the constructed rough, Hodge, and deformation operator tests at a
chosen point, field, and test vector. -/
def ConstructedCandidateTestsPairwiseDistinct
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) : Prop :=
  inner ℝ (roughLaplacianAt I connection.connection x regular field hfield) w ≠
      hodgeLaplacianConstructedTestedAt I connection.connection x regular field hfield w ∧
    inner ℝ (roughLaplacianAt I connection.connection x regular field hfield) w ≠
      deformationLaplacianTestedAt I connection.connection x regular field hfield w ∧
    hodgeLaplacianConstructedTestedAt I connection.connection x regular field hfield w ≠
      deformationLaplacianTestedAt I connection.connection x regular field hfield w

/-- A nonzero Ricci pairing separates the three pointwise tests constructed from a
Levi-Civita connection. -/
theorem constructedCandidateTests_pairwiseDistinct_of_ricciWitness
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x)
    (hdiv : ∀ y, tangentTrace I y (connection.connection field y) = 0)
    (w : TangentSpace I x)
    (hRicci : connectionRicciFormAt I connection.connection x regular w (field x) ≠ 0) :
    ConstructedCandidateTestsPairwiseDistinct I connection x regular field hfield w := by
  have hHodge := weitzenbock_constructedAt I connection x regular hfield w
  have hDeformation :=
    deformationLaplacian_rough_ricci_comparisonAt_of_divergenceFree
      I connection x regular hfield hdiv w
  unfold ConstructedCandidateTestsPairwiseDistinct
  refine ⟨?_, ?_, ?_⟩
  · intro hEqual
    rw [hHodge] at hEqual
    apply hRicci
    linarith
  · intro hEqual
    rw [hDeformation] at hEqual
    apply hRicci
    linarith
  · intro hEqual
    rw [hHodge, hDeformation] at hEqual
    apply hRicci
    linarith

/-- A nonzero Ricci pairing separates the actual tangent-vector outputs of all three independently
constructed candidates.  Equality of two vectors would force equality of their metric tests
against the Ricci witness, contradicting the tested comparison theorem. -/
theorem constructedCandidateOutputs_pairwiseDistinct_of_ricciWitness
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x)
    (hdiv : ∀ y, tangentTrace I y (connection.connection field y) = 0)
    (w : TangentSpace I x)
    (hRicci : connectionRicciFormAt I connection.connection x regular w (field x) ≠ 0) :
    ConstructedCandidateOutputsPairwiseDistinct I connection x regular field hfield := by
  have htests := constructedCandidateTests_pairwiseDistinct_of_ricciWitness
    I connection x regular hfield hdiv w hRicci
  unfold ConstructedCandidateTestsPairwiseDistinct at htests
  unfold ConstructedCandidateOutputsPairwiseDistinct
  refine ⟨?_, ?_, ?_⟩
  · intro hEqual
    apply htests.1
    have hTest := congrArg (fun value ↦ inner ℝ value w) hEqual
    simpa only [inner_hodgeLaplacianConstructedAt] using hTest
  · intro hEqual
    apply htests.2.1
    have hTest := congrArg (fun value ↦ inner ℝ value w) hEqual
    simpa only [inner_deformationLaplacianAt] using hTest
  · intro hEqual
    apply htests.2.2
    have hTest := congrArg (fun value ↦ inner ℝ value w) hEqual
    simpa only [inner_hodgeLaplacianConstructedAt, inner_deformationLaplacianAt] using hTest

end RiemannianFluids
