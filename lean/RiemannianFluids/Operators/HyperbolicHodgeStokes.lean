import RiemannianFluids.Analysis.ResolventGeneratedOperator
import RiemannianFluids.FunctionSpaces.HyperbolicL2HodgeDecomposition
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The Hodge--Stokes operator on the complete hyperbolic plane

This module constructs the unbounded Hodge--Stokes operator on the concrete divergence-free
`L²` carrier.  Its closed form domain is the Hilbert sum of the source-normalized coexact
`H¹` sector and the actual distributional harmonic `L²` sector.  This formulation keeps the
harmonic kernel visible and constructs the operator independently of the global regularity
theorem identifying every harmonic `L²` form with a source `H¹` representative.

The form-domain embedding has dense range in divergence-free `L²`.  The form

    B(u,v) = ⟨j u, j v⟩ + ⟨D u, D v⟩

is the resolvent form for `I + A`: `D` is the packed weak Hodge derivative on the coexact
component and vanishes on the harmonic component.  Lax--Milgram therefore gives the concrete
resolvent, from which the densely defined closed nonnegative self-adjoint operator is recovered.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

/-! ## Closed sectors and the dense form-domain embedding -/

theorem isClosed_hyperbolicDivergenceFreeL2 :
    IsClosed (HyperbolicDivergenceFreeL2 : Set HyperbolicOneFormL2) := by
  exact hyperbolicExactL2.isClosed_orthogonal

noncomputable instance hyperbolicDivergenceFreeL2Complete :
    CompleteSpace HyperbolicDivergenceFreeL2 :=
  isClosed_hyperbolicDivergenceFreeL2.completeSpace_coe

/-- The source coexact `H¹` sector maps continuously into the closed coexact `L²` sector. -/
noncomputable def hyperbolicCoexactH1ToL2 :
    hyperbolicCoexactH1 →L[ℝ] hyperbolicCoexactL2 :=
  ContinuousLinearMap.codRestrict
    (hyperbolicOneFormH1ToL2.comp (Submodule.subtypeL hyperbolicCoexactH1))
    hyperbolicCoexactL2 (by
      intro u
      have hu : (u : HyperbolicOneFormH1) ∈ hyperbolicCoexactH1 := u.property
      change (u : HyperbolicOneFormH1) ∈
        hyperbolicCoexactCoreH1.topologicalClosure at hu
      have hle : hyperbolicCoexactCoreH1.topologicalClosure ≤
          hyperbolicCoexactL2.comap hyperbolicOneFormH1ToL2.toLinearMap :=
        hyperbolicCoexactCoreH1.topologicalClosure_minimal (by
          rintro _ ⟨f, rfl⟩
          change hyperbolicDeltaTwoCoreL2 f ∈ hyperbolicCoexactL2
          exact Submodule.le_topologicalClosure
            (s := hyperbolicCoexactCoreL2) ⟨f, rfl⟩) (by
          exact isClosed_hyperbolicCoexactL2.preimage
            hyperbolicOneFormH1ToL2.continuous)
      exact hle hu)

@[simp] theorem hyperbolicCoexactH1ToL2_coe
    (u : hyperbolicCoexactH1) :
    (hyperbolicCoexactH1ToL2 u : HyperbolicOneFormL2) =
      hyperbolicOneFormH1ToL2 u :=
  rfl

/-- The compact coexact core, viewed in its closed `L²` sector. -/
noncomputable def hyperbolicCoexactCoreToCoexactL2 :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] hyperbolicCoexactL2 :=
  LinearMap.codRestrict hyperbolicCoexactL2 hyperbolicDeltaTwoCoreL2 fun f ↦
    Submodule.le_topologicalClosure (s := hyperbolicCoexactCoreL2) ⟨f, rfl⟩

theorem hyperbolicCoexactCoreToCoexactL2_denseRange :
    DenseRange hyperbolicCoexactCoreToCoexactL2 := by
  let s : Set HyperbolicOneFormL2 := Set.range hyperbolicDeltaTwoCoreL2
  let t : Set HyperbolicOneFormL2 := closure s
  have hi : s ⊆ t := subset_closure
  have hinc : DenseRange (Set.inclusion hi) :=
    (denseRange_inclusion_iff hi).2 subset_rfl
  have hfactor : DenseRange
      (Set.rangeFactorization
        (hyperbolicDeltaTwoCoreL2 :
          HyperbolicSmoothCompactScalar → HyperbolicOneFormL2)) :=
    Set.rangeFactorization_surjective.denseRange
  exact hinc.comp hfactor (continuous_inclusion hi)

/-- The coexact `H¹` embedding is dense in the coexact `L²` sector. -/
theorem hyperbolicCoexactH1ToL2_denseRange :
    DenseRange hyperbolicCoexactH1ToL2 := by
  let coreInclusion : HyperbolicSmoothCompactScalar → hyperbolicCoexactH1 :=
    fun f ↦
      (⟨hyperbolicCoexactCoreToH1 f,
        Submodule.le_topologicalClosure
          (s := hyperbolicCoexactCoreH1) ⟨f, rfl⟩⟩ : hyperbolicCoexactH1)
  apply DenseRange.of_comp (g := coreInclusion)
  have hmaps :
      (hyperbolicCoexactH1ToL2 ∘ coreInclusion) =
        hyperbolicCoexactCoreToCoexactL2 := by
    funext f
    apply Subtype.ext
    simp only [Function.comp_apply, coreInclusion,
      hyperbolicCoexactH1ToL2_coe, hyperbolicCoexactCoreToH1,
      LinearMap.comp_apply, hyperbolicOneFormH1ToL2_core]
    rfl
  rw [hmaps]
  exact hyperbolicCoexactCoreToCoexactL2_denseRange

/-- The closed form domain: coexact source `H¹` plus the actual harmonic `L²` kernel. -/
abbrev HyperbolicHodgeStokesFormDomain :=
  WithLp 2 (hyperbolicCoexactH1 × hyperbolicHarmonicL2)

/-- Coexact component of the Hodge--Stokes form domain. -/
noncomputable def hyperbolicHodgeStokesCoexact :
    HyperbolicHodgeStokesFormDomain →L[ℝ] hyperbolicCoexactH1 :=
  WithLp.fstL 2 ℝ hyperbolicCoexactH1 hyperbolicHarmonicL2

/-- Harmonic component of the Hodge--Stokes form domain. -/
noncomputable def hyperbolicHodgeStokesHarmonic :
    HyperbolicHodgeStokesFormDomain →L[ℝ] hyperbolicHarmonicL2 :=
  WithLp.sndL 2 ℝ hyperbolicCoexactH1 hyperbolicHarmonicL2

/-- Weak Hodge derivative on the form domain; its harmonic summand has zero energy. -/
noncomputable def hyperbolicHodgeStokesDerivative :
    HyperbolicHodgeStokesFormDomain →L[ℝ] HyperbolicOneFormL2 :=
  hyperbolicOneFormH1Hodge.comp
    ((Submodule.subtypeL hyperbolicCoexactH1).comp
      hyperbolicHodgeStokesCoexact)

/-- The coexact and harmonic `L²` sectors are orthogonal. -/
theorem hyperbolicCoexactL2_isOrtho_hyperbolicHarmonicL2 :
    hyperbolicCoexactL2 ⟂ hyperbolicHarmonicL2 :=
  (Submodule.isOrtho_orthogonal_right hyperbolicCoexactL2).mono_right inf_le_right

/-- Hilbert direct sum of the coexact and harmonic `L²` sectors. -/
abbrev HyperbolicCoexactHarmonicL2 :=
  WithLp 2 (hyperbolicCoexactL2 × hyperbolicHarmonicL2)

/-- Add the orthogonal coexact and harmonic sectors inside divergence-free `L²`. -/
noncomputable def hyperbolicCoexactHarmonicSum :
    HyperbolicCoexactHarmonicL2 →L[ℝ] HyperbolicDivergenceFreeL2 :=
  ContinuousLinearMap.codRestrict
    (((Submodule.subtypeL hyperbolicCoexactL2).coprod
      (Submodule.subtypeL hyperbolicHarmonicL2)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ
          hyperbolicCoexactL2 hyperbolicHarmonicL2).toContinuousLinearMap)
    HyperbolicDivergenceFreeL2 (by
      intro u
      exact HyperbolicDivergenceFreeL2.add_mem
        (hyperbolicExactL2_isOrtho_hyperbolicCoexactL2.ge u.ofLp.1.property)
        u.ofLp.2.property.1)

@[simp] theorem hyperbolicCoexactHarmonicSum_coe
    (u : HyperbolicCoexactHarmonicL2) :
    (hyperbolicCoexactHarmonicSum u : HyperbolicOneFormL2) =
      (u.ofLp.1 : HyperbolicOneFormL2) +
        (u.ofLp.2 : HyperbolicOneFormL2) :=
  rfl

theorem hyperbolicCoexactHarmonicSum_injective :
    Function.Injective hyperbolicCoexactHarmonicSum := by
  intro u v huv
  have hsum :
      (u.ofLp.1 : HyperbolicOneFormL2) +
          (u.ofLp.2 : HyperbolicOneFormL2) =
        (v.ofLp.1 : HyperbolicOneFormL2) +
          (v.ofLp.2 : HyperbolicOneFormL2) := by
    exact congrArg Subtype.val huv
  have hcross :
      (u.ofLp.1 : HyperbolicOneFormL2) - v.ofLp.1 =
        (v.ofLp.2 : HyperbolicOneFormL2) - u.ofLp.2 := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using hsum
  have hcoexact :
      (u.ofLp.1 : HyperbolicOneFormL2) - v.ofLp.1 ∈
        hyperbolicCoexactL2 :=
    hyperbolicCoexactL2.sub_mem u.ofLp.1.property v.ofLp.1.property
  have hharmonic :
      (u.ofLp.1 : HyperbolicOneFormL2) - v.ofLp.1 ∈
        hyperbolicHarmonicL2 := by
    rw [hcross]
    exact hyperbolicHarmonicL2.sub_mem v.ofLp.2.property u.ofLp.2.property
  have hzero :
      (u.ofLp.1 : HyperbolicOneFormL2) - v.ofLp.1 = 0 :=
    (Submodule.mem_bot ℝ).1
      (hyperbolicCoexactL2_isOrtho_hyperbolicHarmonicL2.disjoint.le_bot
        ⟨hcoexact, hharmonic⟩)
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ
    hyperbolicCoexactL2 hyperbolicHarmonicL2).injective
  apply Prod.ext
  · apply Subtype.ext
    exact sub_eq_zero.mp hzero
  · apply Subtype.ext
    have hfirst :
        (u.ofLp.1 : HyperbolicOneFormL2) = v.ofLp.1 := sub_eq_zero.mp hzero
    rw [hfirst] at hsum
    exact add_left_cancel hsum

theorem hyperbolicCoexactHarmonicSum_surjective :
    Function.Surjective hyperbolicCoexactHarmonicSum := by
  intro u
  let c : hyperbolicCoexactL2 :=
    ⟨hyperbolicCoexactL2Projector u,
      hyperbolicCoexactL2Projector_mem u⟩
  let h : hyperbolicHarmonicL2 :=
    ⟨hyperbolicHarmonicL2Projector u,
      hyperbolicHarmonicL2Projector_mem u⟩
  refine ⟨WithLp.toLp 2 (c, h), ?_⟩
  apply Subtype.ext
  change hyperbolicCoexactL2Projector u +
      hyperbolicHarmonicL2Projector u = u
  have hexact : hyperbolicExactL2Projector u = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff hyperbolicExactL2).2 u.property
  have hsum := hyperbolicL2_exact_add_coexact_add_harmonic
    (u : HyperbolicOneFormL2)
  rw [hexact, zero_add] at hsum
  exact hsum.symm

/-- Orthogonal coexact-plus-harmonic coordinates are exactly divergence-free `L²`. -/
noncomputable def hyperbolicCoexactHarmonicEquiv :
    HyperbolicCoexactHarmonicL2 ≃L[ℝ] HyperbolicDivergenceFreeL2 :=
  ContinuousLinearEquiv.ofBijective hyperbolicCoexactHarmonicSum
    ((LinearMap.ker_eq_bot).2 hyperbolicCoexactHarmonicSum_injective)
    ((LinearMap.range_eq_top).2 hyperbolicCoexactHarmonicSum_surjective)

/-- Replace the coexact `H¹` coordinate by its `L²` representative, retaining the harmonic
coordinate unchanged. -/
noncomputable def hyperbolicHodgeStokesSectorMap :
    HyperbolicHodgeStokesFormDomain →L[ℝ] HyperbolicCoexactHarmonicL2 :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ
      hyperbolicCoexactL2 hyperbolicHarmonicL2).symm.toContinuousLinearMap.comp
    ((hyperbolicCoexactH1ToL2.prodMap
        (ContinuousLinearMap.id ℝ hyperbolicHarmonicL2)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ
        hyperbolicCoexactH1 hyperbolicHarmonicL2).toContinuousLinearMap)

/-- Dense continuous embedding of the form domain into divergence-free `L²`. -/
noncomputable def hyperbolicHodgeStokesEmbedding :
    HyperbolicHodgeStokesFormDomain →L[ℝ] HyperbolicDivergenceFreeL2 :=
  hyperbolicCoexactHarmonicEquiv.toContinuousLinearMap.comp
    hyperbolicHodgeStokesSectorMap

@[simp] theorem hyperbolicHodgeStokesSectorMap_apply
    (u : HyperbolicHodgeStokesFormDomain) :
    hyperbolicHodgeStokesSectorMap u = WithLp.toLp 2
      (hyperbolicCoexactH1ToL2 u.ofLp.1, u.ofLp.2) :=
  rfl

@[simp] theorem hyperbolicHodgeStokesEmbedding_coe
    (u : HyperbolicHodgeStokesFormDomain) :
    (hyperbolicHodgeStokesEmbedding u : HyperbolicOneFormL2) =
      hyperbolicOneFormH1ToL2 u.ofLp.1 + u.ofLp.2 :=
  rfl

theorem hyperbolicCoexactH1ToL2_injective :
    Function.Injective hyperbolicCoexactH1ToL2 := by
  intro u v huv
  apply Subtype.ext
  apply hyperbolicOneFormH1ToL2_injective
  exact congrArg Subtype.val huv

theorem hyperbolicHodgeStokesSectorMap_denseRange :
    DenseRange hyperbolicHodgeStokesSectorMap := by
  let domainEquiv := WithLp.prodContinuousLinearEquiv 2 ℝ
    hyperbolicCoexactH1 hyperbolicHarmonicL2
  let sectorProd := hyperbolicCoexactH1ToL2.prodMap
    (ContinuousLinearMap.id ℝ hyperbolicHarmonicL2)
  let targetEquiv := WithLp.prodContinuousLinearEquiv 2 ℝ
    hyperbolicCoexactL2 hyperbolicHarmonicL2
  have hdomain : DenseRange domainEquiv :=
    domainEquiv.surjective.denseRange
  have hprod : DenseRange sectorProd := by
    have hid : DenseRange
        (ContinuousLinearMap.id ℝ hyperbolicHarmonicL2) :=
      by simpa using
        (Function.surjective_id.denseRange :
          DenseRange (id : hyperbolicHarmonicL2 → hyperbolicHarmonicL2))
    simpa only [sectorProd, ContinuousLinearMap.coe_prodMap'] using
      hyperbolicCoexactH1ToL2_denseRange.prodMap hid
  have hmiddle : DenseRange
      (sectorProd ∘ domainEquiv) :=
    hprod.comp hdomain sectorProd.continuous
  have htarget : DenseRange targetEquiv.symm :=
    targetEquiv.symm.surjective.denseRange
  have hall : DenseRange
      (targetEquiv.symm ∘ (sectorProd ∘ domainEquiv)) :=
    htarget.comp hmiddle targetEquiv.symm.continuous
  change DenseRange
    (fun u ↦ targetEquiv.symm (sectorProd (domainEquiv u)))
  change DenseRange
    (fun u ↦ targetEquiv.symm (sectorProd (domainEquiv u))) at hall
  exact hall

theorem hyperbolicHodgeStokesSectorMap_injective :
    Function.Injective hyperbolicHodgeStokesSectorMap := by
  let domainEquiv := WithLp.prodContinuousLinearEquiv 2 ℝ
    hyperbolicCoexactH1 hyperbolicHarmonicL2
  let targetEquiv := WithLp.prodContinuousLinearEquiv 2 ℝ
    hyperbolicCoexactL2 hyperbolicHarmonicL2
  have hprod : Function.Injective
      (hyperbolicCoexactH1ToL2.prodMap
        (ContinuousLinearMap.id ℝ hyperbolicHarmonicL2)) :=
    hyperbolicCoexactH1ToL2_injective.prodMap Function.injective_id
  exact targetEquiv.symm.injective.comp
    (hprod.comp domainEquiv.injective)

theorem hyperbolicHodgeStokesEmbedding_denseRange :
    DenseRange hyperbolicHodgeStokesEmbedding := by
  exact hyperbolicCoexactHarmonicEquiv.surjective.denseRange.comp
    hyperbolicHodgeStokesSectorMap_denseRange
    hyperbolicCoexactHarmonicEquiv.continuous

theorem hyperbolicHodgeStokesEmbedding_injective :
    Function.Injective hyperbolicHodgeStokesEmbedding :=
  hyperbolicCoexactHarmonicEquiv.injective.comp
    hyperbolicHodgeStokesSectorMap_injective

/-- The form-domain embedding with the divergence-free subtype forgotten. -/
noncomputable def hyperbolicHodgeStokesEmbeddingAmbient :
    HyperbolicHodgeStokesFormDomain →L[ℝ] HyperbolicOneFormL2 :=
  (Submodule.subtypeL HyperbolicDivergenceFreeL2).comp
    hyperbolicHodgeStokesEmbedding

@[simp] theorem hyperbolicHodgeStokesEmbeddingAmbient_apply
    (u : HyperbolicHodgeStokesFormDomain) :
    hyperbolicHodgeStokesEmbeddingAmbient u =
      (hyperbolicHodgeStokesEmbedding u : HyperbolicOneFormL2) :=
  rfl

/-! ## The closed coercive resolvent form -/

theorem norm_sq_hyperbolicHodgeStokesEmbedding
    (u : HyperbolicHodgeStokesFormDomain) :
    ‖hyperbolicHodgeStokesEmbedding u‖ ^ 2 =
      ‖hyperbolicOneFormH1ToL2 u.ofLp.1‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 := by
  change ‖(hyperbolicOneFormH1ToL2 u.ofLp.1 +
      (u.ofLp.2 : HyperbolicOneFormL2) : HyperbolicOneFormL2)‖ ^ 2 = _
  simpa only [pow_two, Submodule.norm_coe] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (hyperbolicOneFormH1ToL2 u.ofLp.1)
      (u.ofLp.2 : HyperbolicOneFormL2)
      (u.ofLp.2.property.2 _
        (hyperbolicCoexactH1ToL2 u.ofLp.1).property)

@[simp] theorem hyperbolicHodgeStokesDerivative_apply
    (u : HyperbolicHodgeStokesFormDomain) :
    hyperbolicHodgeStokesDerivative u =
      hyperbolicOneFormH1Hodge u.ofLp.1 :=
  rfl

theorem norm_sq_hyperbolicHodgeStokesFormDomain
    (u : HyperbolicHodgeStokesFormDomain) :
    ‖u‖ ^ 2 =
      2 * ‖hyperbolicOneFormH1ToL2 u.ofLp.1‖ ^ 2 +
        ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 := by
  calc
    ‖u‖ ^ 2 = ‖u.ofLp.1‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 :=
      WithLp.prod_norm_sq_eq_of_L2 u
    _ = 2 * ‖hyperbolicOneFormH1ToL2 u.ofLp.1‖ ^ 2 +
          ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 := by
      rw [← Submodule.norm_coe u.ofLp.1]
      rw [norm_sq_hyperbolicOneFormH1]
      rfl

theorem norm_hyperbolicHodgeStokesEmbedding_le
    (u : HyperbolicHodgeStokesFormDomain) :
    ‖hyperbolicHodgeStokesEmbedding u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖hyperbolicHodgeStokesEmbedding u‖ ^ 2 =
        ‖hyperbolicOneFormH1ToL2 u.ofLp.1‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 :=
      norm_sq_hyperbolicHodgeStokesEmbedding u
    _ ≤ 2 * ‖hyperbolicOneFormH1ToL2 u.ofLp.1‖ ^ 2 +
          ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 := by
      nlinarith [sq_nonneg ‖hyperbolicOneFormH1ToL2 u.ofLp.1‖,
        sq_nonneg ‖hyperbolicHodgeStokesDerivative u‖]
    _ = ‖u‖ ^ 2 := (norm_sq_hyperbolicHodgeStokesFormDomain u).symm

theorem norm_hyperbolicHodgeStokesDerivative_le
    (u : HyperbolicHodgeStokesFormDomain) :
    ‖hyperbolicHodgeStokesDerivative u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 ≤
        2 * ‖hyperbolicOneFormH1ToL2 u.ofLp.1‖ ^ 2 +
          ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 := by
      nlinarith [sq_nonneg ‖hyperbolicOneFormH1ToL2 u.ofLp.1‖,
        sq_nonneg ‖u.ofLp.2‖]
    _ = ‖u‖ ^ 2 := (norm_sq_hyperbolicHodgeStokesFormDomain u).symm

/-- Algebraic form underlying the continuous resolvent form. -/
noncomputable def hyperbolicHodgeStokesResolventFormLinear :
    HyperbolicHodgeStokesFormDomain →ₗ[ℝ]
      HyperbolicHodgeStokesFormDomain →ₗ[ℝ] ℝ :=
  (innerₗ HyperbolicOneFormL2).compl₁₂
      hyperbolicHodgeStokesEmbeddingAmbient.toLinearMap
      hyperbolicHodgeStokesEmbeddingAmbient.toLinearMap +
    (innerₗ HyperbolicOneFormL2).compl₁₂
      hyperbolicHodgeStokesDerivative.toLinearMap
      hyperbolicHodgeStokesDerivative.toLinearMap

@[simp] theorem hyperbolicHodgeStokesResolventFormLinear_apply
    (u v : HyperbolicHodgeStokesFormDomain) :
    hyperbolicHodgeStokesResolventFormLinear u v =
      inner ℝ (hyperbolicHodgeStokesEmbeddingAmbient u)
          (hyperbolicHodgeStokesEmbeddingAmbient v) +
        inner ℝ (hyperbolicHodgeStokesDerivative u)
          (hyperbolicHodgeStokesDerivative v) :=
  rfl

/-- Resolvent form for `I + A` on the Hodge--Stokes form domain. -/
noncomputable def hyperbolicHodgeStokesResolventForm :
    HyperbolicHodgeStokesFormDomain →L[ℝ]
      HyperbolicHodgeStokesFormDomain →L[ℝ] ℝ :=
  @LinearMap.mkContinuous₂ ℝ ℝ ℝ
    HyperbolicHodgeStokesFormDomain HyperbolicHodgeStokesFormDomain ℝ
    _ _ _ _ _ _
    (WithLp.instProdNormedSpace 2 ℝ
      hyperbolicCoexactH1 hyperbolicHarmonicL2)
    (WithLp.instProdNormedSpace 2 ℝ
      hyperbolicCoexactH1 hyperbolicHarmonicL2)
    _ (RingHom.id ℝ) (RingHom.id ℝ) _
    hyperbolicHodgeStokesResolventFormLinear 2 (by
      intro u v
      calc
        ‖hyperbolicHodgeStokesResolventFormLinear u v‖
            ≤ ‖inner ℝ (hyperbolicHodgeStokesEmbeddingAmbient u)
                (hyperbolicHodgeStokesEmbeddingAmbient v)‖ +
              ‖inner ℝ (hyperbolicHodgeStokesDerivative u)
                (hyperbolicHodgeStokesDerivative v)‖ := norm_add_le _ _
        _ ≤ ‖hyperbolicHodgeStokesEmbeddingAmbient u‖ *
                ‖hyperbolicHodgeStokesEmbeddingAmbient v‖ +
              ‖hyperbolicHodgeStokesDerivative u‖ *
                ‖hyperbolicHodgeStokesDerivative v‖ := by
            exact add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
        _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ := by
            exact add_le_add
              (mul_le_mul (by simpa [hyperbolicHodgeStokesEmbeddingAmbient]
                  using norm_hyperbolicHodgeStokesEmbedding_le u)
                (by simpa [hyperbolicHodgeStokesEmbeddingAmbient]
                  using norm_hyperbolicHodgeStokesEmbedding_le v)
                (norm_nonneg _) (norm_nonneg _))
              (mul_le_mul (norm_hyperbolicHodgeStokesDerivative_le u)
                (norm_hyperbolicHodgeStokesDerivative_le v)
                (norm_nonneg _) (norm_nonneg _))
        _ = 2 * ‖u‖ * ‖v‖ := by ring)

@[simp] theorem hyperbolicHodgeStokesResolventForm_apply
    (u v : HyperbolicHodgeStokesFormDomain) :
    hyperbolicHodgeStokesResolventForm u v =
      inner ℝ (hyperbolicHodgeStokesEmbeddingAmbient u)
          (hyperbolicHodgeStokesEmbeddingAmbient v) +
        inner ℝ (hyperbolicHodgeStokesDerivative u)
          (hyperbolicHodgeStokesDerivative v) :=
  rfl

theorem hyperbolicHodgeStokesResolventForm_coercive :
    @IsCoercive HyperbolicHodgeStokesFormDomain _
      (WithLp.instProdNormedSpace 2 ℝ
        hyperbolicCoexactH1 hyperbolicHarmonicL2)
      hyperbolicHodgeStokesResolventForm := by
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro u
  have hform :
      hyperbolicHodgeStokesResolventForm u u =
        ‖hyperbolicHodgeStokesEmbedding u‖ ^ 2 +
          ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 := by
    calc
      hyperbolicHodgeStokesResolventForm u u =
          inner ℝ (hyperbolicHodgeStokesEmbeddingAmbient u)
              (hyperbolicHodgeStokesEmbeddingAmbient u) +
            inner ℝ (hyperbolicHodgeStokesDerivative u)
              (hyperbolicHodgeStokesDerivative u) :=
        hyperbolicHodgeStokesResolventForm_apply u u
      _ = ‖hyperbolicHodgeStokesEmbeddingAmbient u‖ ^ 2 +
            ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 :=
        congrArg₂ (· + ·)
          (real_inner_self_eq_norm_sq _)
          (real_inner_self_eq_norm_sq _)
      _ = ‖hyperbolicHodgeStokesEmbedding u‖ ^ 2 +
            ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 := by rfl
  calc
    (1 / 2 : ℝ) * ‖u‖ * ‖u‖ = (1 / 2 : ℝ) * ‖u‖ ^ 2 := by ring
    _ = (1 / 2 : ℝ) *
          (2 * ‖hyperbolicOneFormH1ToL2 u.ofLp.1‖ ^ 2 +
            ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 + ‖u.ofLp.2‖ ^ 2) := by
        rw [norm_sq_hyperbolicHodgeStokesFormDomain]
    _ ≤ ‖hyperbolicOneFormH1ToL2 u.ofLp.1‖ ^ 2 +
          ‖u.ofLp.2‖ ^ 2 + ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 := by
        nlinarith [sq_nonneg ‖hyperbolicHodgeStokesDerivative u‖,
          sq_nonneg ‖u.ofLp.2‖]
    _ = ‖hyperbolicHodgeStokesEmbedding u‖ ^ 2 +
          ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 := by
        exact congrArg
          (fun x : ℝ ↦ x + ‖hyperbolicHodgeStokesDerivative u‖ ^ 2)
          (norm_sq_hyperbolicHodgeStokesEmbedding u).symm
    _ = hyperbolicHodgeStokesResolventForm u u := hform.symm

/-! ## Lax--Milgram resolvent -/

/-- The Hilbert structure on the form domain is the `L²` product of the source coexact `H¹`
sector and the distributional harmonic `L²` sector.  The named instance makes that structure
available to the Lax--Milgram construction without changing the already-fixed graph norm. -/
noncomputable instance (priority := 2000)
    hyperbolicHodgeStokesFormDomainInnerProductSpace :
    InnerProductSpace ℝ HyperbolicHodgeStokesFormDomain :=
  @WithLp.instProdInnerProductSpace ℝ
    hyperbolicCoexactH1 hyperbolicHarmonicL2 _ _
    hyperbolicCoexactH1InnerProductSpace _ inferInstance

/-- Riesz--Lax--Milgram equivalence representing the coercive resolvent form. -/
noncomputable def hyperbolicHodgeStokesLaxEquiv :
    HyperbolicHodgeStokesFormDomain ≃L[ℝ]
      HyperbolicHodgeStokesFormDomain :=
  @IsCoercive.continuousLinearEquivOfBilin
    HyperbolicHodgeStokesFormDomain _
    hyperbolicHodgeStokesFormDomainInnerProductSpace inferInstance
    hyperbolicHodgeStokesResolventForm
    hyperbolicHodgeStokesResolventForm_coercive

/-- Hilbert adjoint of the dense form-domain embedding. -/
noncomputable def hyperbolicHodgeStokesEmbeddingAdjoint :
    HyperbolicDivergenceFreeL2 →L[ℝ] HyperbolicHodgeStokesFormDomain :=
  @ContinuousLinearMap.adjoint ℝ
    HyperbolicHodgeStokesFormDomain HyperbolicDivergenceFreeL2
    _ _ _ hyperbolicHodgeStokesFormDomainInnerProductSpace
    inferInstance inferInstance inferInstance
    hyperbolicHodgeStokesEmbedding

/-- Variational solution map for `(I + A)u = f`, valued in the form domain. -/
noncomputable def hyperbolicHodgeStokesSolution :
    HyperbolicDivergenceFreeL2 →L[ℝ] HyperbolicHodgeStokesFormDomain :=
  hyperbolicHodgeStokesLaxEquiv.symm.toContinuousLinearMap.comp
    hyperbolicHodgeStokesEmbeddingAdjoint

/-- The bounded resolvent `(I + A)⁻¹` on divergence-free `L²`. -/
noncomputable def hyperbolicHodgeStokesResolvent :
    HyperbolicDivergenceFreeL2 →L[ℝ] HyperbolicDivergenceFreeL2 :=
  hyperbolicHodgeStokesEmbedding.comp hyperbolicHodgeStokesSolution

@[simp] theorem hyperbolicHodgeStokesResolvent_apply
    (f : HyperbolicDivergenceFreeL2) :
    hyperbolicHodgeStokesResolvent f =
      hyperbolicHodgeStokesEmbedding (hyperbolicHodgeStokesSolution f) :=
  rfl

/-- The solution map satisfies the defining variational resolvent equation. -/
theorem hyperbolicHodgeStokesSolution_variational
    (f : HyperbolicDivergenceFreeL2)
    (v : HyperbolicHodgeStokesFormDomain) :
    hyperbolicHodgeStokesResolventForm
        (hyperbolicHodgeStokesSolution f) v =
      inner ℝ f (hyperbolicHodgeStokesEmbedding v) := by
  calc
    hyperbolicHodgeStokesResolventForm
          (hyperbolicHodgeStokesSolution f) v =
        inner ℝ
          (hyperbolicHodgeStokesLaxEquiv
            (hyperbolicHodgeStokesSolution f)) v := by
      symm
      exact @IsCoercive.continuousLinearEquivOfBilin_apply
        HyperbolicHodgeStokesFormDomain _
        hyperbolicHodgeStokesFormDomainInnerProductSpace inferInstance
        hyperbolicHodgeStokesResolventForm
        hyperbolicHodgeStokesResolventForm_coercive _ _
    _ = inner ℝ (hyperbolicHodgeStokesEmbeddingAdjoint f) v := by
      change inner ℝ
        (hyperbolicHodgeStokesLaxEquiv
          (hyperbolicHodgeStokesLaxEquiv.symm
            (hyperbolicHodgeStokesEmbeddingAdjoint f))) v = _
      rw [hyperbolicHodgeStokesLaxEquiv.apply_symm_apply]
    _ = inner ℝ f (hyperbolicHodgeStokesEmbedding v) := by
      exact @ContinuousLinearMap.adjoint_inner_left ℝ
        HyperbolicHodgeStokesFormDomain HyperbolicDivergenceFreeL2
        _ _ _ hyperbolicHodgeStokesFormDomainInnerProductSpace
        inferInstance inferInstance inferInstance
        hyperbolicHodgeStokesEmbedding v f

/-- The Lax--Milgram equivalence represents the resolvent form in the form-domain inner
product. -/
theorem hyperbolicHodgeStokesLaxEquiv_inner
    (u v : HyperbolicHodgeStokesFormDomain) :
    inner ℝ (hyperbolicHodgeStokesLaxEquiv u) v =
      hyperbolicHodgeStokesResolventForm u v := by
  exact @IsCoercive.continuousLinearEquivOfBilin_apply
    HyperbolicHodgeStokesFormDomain _
    hyperbolicHodgeStokesFormDomainInnerProductSpace inferInstance
    hyperbolicHodgeStokesResolventForm
    hyperbolicHodgeStokesResolventForm_coercive u v

/-- Adjoint identity for the dense form-domain embedding. -/
theorem hyperbolicHodgeStokesEmbeddingAdjoint_inner
    (f : HyperbolicDivergenceFreeL2)
    (v : HyperbolicHodgeStokesFormDomain) :
    inner ℝ (hyperbolicHodgeStokesEmbeddingAdjoint f) v =
      inner ℝ f (hyperbolicHodgeStokesEmbedding v) := by
  exact @ContinuousLinearMap.adjoint_inner_left ℝ
    HyperbolicHodgeStokesFormDomain HyperbolicDivergenceFreeL2
    _ _ _ hyperbolicHodgeStokesFormDomainInnerProductSpace
    inferInstance inferInstance inferInstance
    hyperbolicHodgeStokesEmbedding v f

/-- Symmetry of the real resolvent form. -/
theorem hyperbolicHodgeStokesResolventForm_symmetric
    (u v : HyperbolicHodgeStokesFormDomain) :
    hyperbolicHodgeStokesResolventForm u v =
      hyperbolicHodgeStokesResolventForm v u := by
  calc
    hyperbolicHodgeStokesResolventForm u v =
        inner ℝ (hyperbolicHodgeStokesEmbeddingAmbient u)
            (hyperbolicHodgeStokesEmbeddingAmbient v) +
          inner ℝ (hyperbolicHodgeStokesDerivative u)
            (hyperbolicHodgeStokesDerivative v) :=
      hyperbolicHodgeStokesResolventForm_apply u v
    _ = inner ℝ (hyperbolicHodgeStokesEmbeddingAmbient v)
            (hyperbolicHodgeStokesEmbeddingAmbient u) +
          inner ℝ (hyperbolicHodgeStokesDerivative v)
            (hyperbolicHodgeStokesDerivative u) :=
      congrArg₂ (· + ·) (real_inner_comm _ _) (real_inner_comm _ _)
    _ = hyperbolicHodgeStokesResolventForm v u :=
      (hyperbolicHodgeStokesResolventForm_apply v u).symm

/-- Diagonal value of the resolvent form. -/
theorem hyperbolicHodgeStokesResolventForm_self
    (u : HyperbolicHodgeStokesFormDomain) :
    hyperbolicHodgeStokesResolventForm u u =
      ‖hyperbolicHodgeStokesEmbedding u‖ ^ 2 +
        ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 := by
  calc
    hyperbolicHodgeStokesResolventForm u u =
        inner ℝ (hyperbolicHodgeStokesEmbeddingAmbient u)
            (hyperbolicHodgeStokesEmbeddingAmbient u) +
          inner ℝ (hyperbolicHodgeStokesDerivative u)
            (hyperbolicHodgeStokesDerivative u) :=
      hyperbolicHodgeStokesResolventForm_apply u u
    _ = ‖hyperbolicHodgeStokesEmbeddingAmbient u‖ ^ 2 +
          ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 :=
      congrArg₂ (· + ·) (real_inner_self_eq_norm_sq _)
        (real_inner_self_eq_norm_sq _)
    _ = ‖hyperbolicHodgeStokesEmbedding u‖ ^ 2 +
          ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 := by rfl

/-- Density of the form-domain embedding makes its Hilbert adjoint injective. -/
theorem hyperbolicHodgeStokesEmbeddingAdjoint_injective :
    Function.Injective hyperbolicHodgeStokesEmbeddingAdjoint := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply hyperbolicHodgeStokesEmbedding_denseRange.eq_zero_of_inner_left ℝ
  intro v
  calc
    inner ℝ (f - g) (hyperbolicHodgeStokesEmbedding v) =
        inner ℝ (hyperbolicHodgeStokesEmbeddingAdjoint (f - g)) v := by
      symm
      exact @ContinuousLinearMap.adjoint_inner_left ℝ
        HyperbolicHodgeStokesFormDomain HyperbolicDivergenceFreeL2
        _ _ _ hyperbolicHodgeStokesFormDomainInnerProductSpace
        inferInstance inferInstance inferInstance
        hyperbolicHodgeStokesEmbedding v (f - g)
    _ = 0 := by
      rw [map_sub, hfg, sub_self]
      exact @inner_zero_left ℝ HyperbolicHodgeStokesFormDomain
        _ _ hyperbolicHodgeStokesFormDomainInnerProductSpace v

theorem hyperbolicHodgeStokesSolution_injective :
    Function.Injective hyperbolicHodgeStokesSolution :=
  hyperbolicHodgeStokesLaxEquiv.symm.injective.comp
    hyperbolicHodgeStokesEmbeddingAdjoint_injective

/-- The bounded resolvent is injective. -/
theorem hyperbolicHodgeStokesResolvent_injective :
    Function.Injective hyperbolicHodgeStokesResolvent :=
  hyperbolicHodgeStokesEmbedding_injective.comp
    hyperbolicHodgeStokesSolution_injective

/-- The variational resolvent is a symmetric bounded operator on divergence-free `L²`. -/
theorem hyperbolicHodgeStokesResolvent_isSymmetric :
    hyperbolicHodgeStokesResolvent.toLinearMap.IsSymmetric := by
  intro f g
  calc
    inner ℝ (hyperbolicHodgeStokesResolvent f) g =
        inner ℝ g (hyperbolicHodgeStokesResolvent f) := real_inner_comm _ _
    _ = hyperbolicHodgeStokesResolventForm
          (hyperbolicHodgeStokesSolution g)
          (hyperbolicHodgeStokesSolution f) :=
      (hyperbolicHodgeStokesSolution_variational g
        (hyperbolicHodgeStokesSolution f)).symm
    _ = hyperbolicHodgeStokesResolventForm
          (hyperbolicHodgeStokesSolution f)
          (hyperbolicHodgeStokesSolution g) :=
      hyperbolicHodgeStokesResolventForm_symmetric _ _
    _ = inner ℝ f (hyperbolicHodgeStokesResolvent g) :=
      hyperbolicHodgeStokesSolution_variational f
        (hyperbolicHodgeStokesSolution g)

/-- The resolvent has dense range, hence its range is a valid dense operator domain. -/
theorem hyperbolicHodgeStokesResolvent_denseRange :
    DenseRange hyperbolicHodgeStokesResolvent := by
  exact symmetric_injective_denseRange hyperbolicHodgeStokesResolvent
    hyperbolicHodgeStokesResolvent_isSymmetric
    hyperbolicHodgeStokesResolvent_injective

/-- Resolvent energy identity. -/
theorem hyperbolicHodgeStokesResolvent_energy
    (f : HyperbolicDivergenceFreeL2) :
    inner ℝ f (hyperbolicHodgeStokesResolvent f) =
      ‖hyperbolicHodgeStokesResolvent f‖ ^ 2 +
        ‖hyperbolicHodgeStokesDerivative
          (hyperbolicHodgeStokesSolution f)‖ ^ 2 := by
  calc
    inner ℝ f (hyperbolicHodgeStokesResolvent f) =
        hyperbolicHodgeStokesResolventForm
          (hyperbolicHodgeStokesSolution f)
          (hyperbolicHodgeStokesSolution f) :=
      (hyperbolicHodgeStokesSolution_variational f
        (hyperbolicHodgeStokesSolution f)).symm
    _ = ‖hyperbolicHodgeStokesResolvent f‖ ^ 2 +
          ‖hyperbolicHodgeStokesDerivative
            (hyperbolicHodgeStokesSolution f)‖ ^ 2 :=
      hyperbolicHodgeStokesResolventForm_self _

/-! ## The closed unbounded Hodge--Stokes operator -/

/-- Core-coordinate action recovered from the resolvent: `A(Rf) = f - Rf`. -/
noncomputable def hyperbolicHodgeStokesCoreOperator :
    HyperbolicDivergenceFreeL2 →ₗ[ℝ] HyperbolicDivergenceFreeL2 :=
  resolventGeneratedCoreOperator hyperbolicHodgeStokesResolvent

/-- The Hodge--Stokes operator on divergence-free `L²`, with domain equal to the actual range of
its variational resolvent. -/
noncomputable def hyperbolicHodgeStokesOperator :
    HyperbolicDivergenceFreeL2 →ₗ.[ℝ] HyperbolicDivergenceFreeL2 :=
  resolventGeneratedOperator hyperbolicHodgeStokesResolvent
    hyperbolicHodgeStokesResolvent_injective

@[simp] theorem hyperbolicHodgeStokesOperator_domain :
    hyperbolicHodgeStokesOperator.domain =
      hyperbolicHodgeStokesResolvent.toLinearMap.range :=
  rfl

/-- Canonical domain element represented by a resolvent input. -/
noncomputable def hyperbolicHodgeStokesResolventDomainElement
    (f : HyperbolicDivergenceFreeL2) :
    hyperbolicHodgeStokesOperator.domain :=
  resolventGeneratedDomainElement hyperbolicHodgeStokesResolvent
    hyperbolicHodgeStokesResolvent_injective f

@[simp] theorem hyperbolicHodgeStokesResolventDomainElement_coe
    (f : HyperbolicDivergenceFreeL2) :
    (hyperbolicHodgeStokesResolventDomainElement f :
      HyperbolicDivergenceFreeL2) = hyperbolicHodgeStokesResolvent f :=
  rfl

/-- Exact recovery formula `A(Rf) = f - Rf`. -/
@[simp] theorem hyperbolicHodgeStokesOperator_resolvent
    (f : HyperbolicDivergenceFreeL2) :
    hyperbolicHodgeStokesOperator
        (hyperbolicHodgeStokesResolventDomainElement f) =
      f - hyperbolicHodgeStokesResolvent f := by
  exact resolventGeneratedOperator_apply_resolvent
    hyperbolicHodgeStokesResolvent
    hyperbolicHodgeStokesResolvent_injective f

/-- Every domain element has a unique resolvent coordinate; existence is exposed here for
downstream graph and energy arguments. -/
theorem hyperbolicHodgeStokesOperator_exists_resolvent_representation
    (x : hyperbolicHodgeStokesOperator.domain) :
    ∃ f : HyperbolicDivergenceFreeL2,
      x = hyperbolicHodgeStokesResolventDomainElement f := by
  exact resolventGeneratedOperator_exists_resolvent_representation
    hyperbolicHodgeStokesResolvent
    hyperbolicHodgeStokesResolvent_injective x

/-- The graph is the closed resolvent equation `R(u + v) = u`. -/
theorem hyperbolicHodgeStokes_pair_mem_graph_iff
    (u v : HyperbolicDivergenceFreeL2) :
    (u, v) ∈ hyperbolicHodgeStokesOperator.graph ↔
      hyperbolicHodgeStokesResolvent (u + v) = u := by
  exact resolventGeneratedOperator_pair_mem_graph_iff
    hyperbolicHodgeStokesResolvent
    hyperbolicHodgeStokesResolvent_injective u v

/-- The variationally recovered operator has closed graph. -/
theorem hyperbolicHodgeStokesOperator_isClosed :
    hyperbolicHodgeStokesOperator.IsClosed := by
  exact resolventGeneratedOperator_isClosed
    hyperbolicHodgeStokesResolvent
    hyperbolicHodgeStokesResolvent_injective

/-- The recovered operator domain is dense in divergence-free `L²`. -/
theorem hyperbolicHodgeStokesOperator_dense_domain :
    Dense (hyperbolicHodgeStokesOperator.domain :
      Set HyperbolicDivergenceFreeL2) :=
  resolventGeneratedOperator_dense_domain hyperbolicHodgeStokesResolvent
    hyperbolicHodgeStokesResolvent_injective
    hyperbolicHodgeStokesResolvent_denseRange

/-- The complete closed, densely defined Hodge--Stokes operator package. -/
noncomputable def hyperbolicHodgeStokes :
    DenselyDefinedClosedLinearOperator ℝ
      HyperbolicDivergenceFreeL2 HyperbolicDivergenceFreeL2 where
  operator := hyperbolicHodgeStokesOperator
  isClosed := hyperbolicHodgeStokesOperator_isClosed
  dense_domain := hyperbolicHodgeStokesOperator_dense_domain

/-- Surjectivity of `I + A`, witnessed by the variational resolvent. -/
theorem hyperbolicHodgeStokes_one_add_surjective
    (f : HyperbolicDivergenceFreeL2) :
    (hyperbolicHodgeStokesResolventDomainElement f :
        HyperbolicDivergenceFreeL2) +
      hyperbolicHodgeStokesOperator
        (hyperbolicHodgeStokesResolventDomainElement f) = f := by
  rw [hyperbolicHodgeStokesOperator_resolvent]
  change hyperbolicHodgeStokesResolvent f +
      (f - hyperbolicHodgeStokesResolvent f) = f
  abel

/-- The operator represents the Hodge energy form on its resolvent coordinates. -/
theorem hyperbolicHodgeStokesOperator_weak_identity
    (f : HyperbolicDivergenceFreeL2)
    (v : HyperbolicHodgeStokesFormDomain) :
    inner ℝ
        (hyperbolicHodgeStokesOperator
          (hyperbolicHodgeStokesResolventDomainElement f))
        (hyperbolicHodgeStokesEmbedding v) =
      inner ℝ
        (hyperbolicHodgeStokesDerivative
          (hyperbolicHodgeStokesSolution f))
        (hyperbolicHodgeStokesDerivative v) := by
  have hvar := hyperbolicHodgeStokesSolution_variational f v
  have hform :
      hyperbolicHodgeStokesResolventForm
          (hyperbolicHodgeStokesSolution f) v =
        inner ℝ (hyperbolicHodgeStokesResolvent f)
            (hyperbolicHodgeStokesEmbedding v) +
          inner ℝ
            (hyperbolicHodgeStokesDerivative
              (hyperbolicHodgeStokesSolution f))
            (hyperbolicHodgeStokesDerivative v) := by
    calc
      hyperbolicHodgeStokesResolventForm
            (hyperbolicHodgeStokesSolution f) v =
          inner ℝ
              (hyperbolicHodgeStokesEmbeddingAmbient
                (hyperbolicHodgeStokesSolution f))
              (hyperbolicHodgeStokesEmbeddingAmbient v) +
            inner ℝ
              (hyperbolicHodgeStokesDerivative
                (hyperbolicHodgeStokesSolution f))
              (hyperbolicHodgeStokesDerivative v) :=
        hyperbolicHodgeStokesResolventForm_apply _ _
      _ = inner ℝ (hyperbolicHodgeStokesResolvent f)
              (hyperbolicHodgeStokesEmbedding v) +
            inner ℝ
              (hyperbolicHodgeStokesDerivative
                (hyperbolicHodgeStokesSolution f))
              (hyperbolicHodgeStokesDerivative v) := by rfl
  calc
    inner ℝ
          (hyperbolicHodgeStokesOperator
            (hyperbolicHodgeStokesResolventDomainElement f))
          (hyperbolicHodgeStokesEmbedding v) =
        inner ℝ (f - hyperbolicHodgeStokesResolvent f)
          (hyperbolicHodgeStokesEmbedding v) :=
      congrArg
        (fun z : HyperbolicDivergenceFreeL2 ↦
          inner ℝ z (hyperbolicHodgeStokesEmbedding v))
        (hyperbolicHodgeStokesOperator_resolvent f)
    _ = inner ℝ f (hyperbolicHodgeStokesEmbedding v) -
          inner ℝ (hyperbolicHodgeStokesResolvent f)
            (hyperbolicHodgeStokesEmbedding v) :=
      inner_sub_left _ _ _
    _ = inner ℝ
          (hyperbolicHodgeStokesDerivative
            (hyperbolicHodgeStokesSolution f))
          (hyperbolicHodgeStokesDerivative v) := by
      linarith only [hvar, hform]

/-- The Hodge--Stokes operator is symmetric on its dense domain. -/
theorem hyperbolicHodgeStokesOperator_isFormalAdjoint :
    hyperbolicHodgeStokesOperator.IsFormalAdjoint
      hyperbolicHodgeStokesOperator := by
  exact resolventGeneratedOperator_isFormalAdjoint
    hyperbolicHodgeStokesResolvent
    hyperbolicHodgeStokesResolvent_injective
    hyperbolicHodgeStokesResolvent_isSymmetric

/-- The concrete Hodge--Stokes operator is self-adjoint, not merely symmetric.  Maximality of
the domain follows from the generic adjoint-resolvent equation for `R⁻¹ - I`. -/
theorem hyperbolicHodgeStokesOperator_isSelfAdjoint :
    IsSelfAdjoint hyperbolicHodgeStokesOperator := by
  exact resolventGeneratedOperator_isSelfAdjoint
    hyperbolicHodgeStokesResolvent
    hyperbolicHodgeStokesResolvent_injective
    hyperbolicHodgeStokesResolvent_isSymmetric

/-- The quadratic form of `A` is exactly the squared weak Hodge derivative. -/
theorem hyperbolicHodgeStokesOperator_quadratic_resolvent
    (f : HyperbolicDivergenceFreeL2) :
    inner ℝ
        (hyperbolicHodgeStokesOperator
          (hyperbolicHodgeStokesResolventDomainElement f))
        (hyperbolicHodgeStokesResolventDomainElement f :
          HyperbolicDivergenceFreeL2) =
      ‖hyperbolicHodgeStokesDerivative
        (hyperbolicHodgeStokesSolution f)‖ ^ 2 := by
  rw [hyperbolicHodgeStokesOperator_resolvent]
  change inner ℝ (f - hyperbolicHodgeStokesResolvent f)
      (hyperbolicHodgeStokesResolvent f) = _
  calc
    inner ℝ (f - hyperbolicHodgeStokesResolvent f)
          (hyperbolicHodgeStokesResolvent f) =
        inner ℝ f (hyperbolicHodgeStokesResolvent f) -
          inner ℝ (hyperbolicHodgeStokesResolvent f)
            (hyperbolicHodgeStokesResolvent f) :=
      inner_sub_left _ _ _
    _ = (‖hyperbolicHodgeStokesResolvent f‖ ^ 2 +
            ‖hyperbolicHodgeStokesDerivative
              (hyperbolicHodgeStokesSolution f)‖ ^ 2) -
          ‖hyperbolicHodgeStokesResolvent f‖ ^ 2 :=
      congrArg₂ (· - ·) (hyperbolicHodgeStokesResolvent_energy f)
        (real_inner_self_eq_norm_sq _)
    _ = ‖hyperbolicHodgeStokesDerivative
          (hyperbolicHodgeStokesSolution f)‖ ^ 2 := by ring

/-- Nonnegativity of the closed Hodge--Stokes operator. -/
theorem hyperbolicHodgeStokesOperator_nonnegative
    (x : hyperbolicHodgeStokesOperator.domain) :
    0 ≤ inner ℝ (hyperbolicHodgeStokesOperator x)
      (x : HyperbolicDivergenceFreeL2) := by
  rcases hyperbolicHodgeStokesOperator_exists_resolvent_representation x with
    ⟨f, rfl⟩
  rw [hyperbolicHodgeStokesOperator_quadratic_resolvent]
  exact sq_nonneg _

/-! ## Harmonic kernel -/

/-- The distributional harmonic `L²` sector included into divergence-free `L²`. -/
noncomputable def hyperbolicHarmonicToDivergenceFreeL2 :
    hyperbolicHarmonicL2 →L[ℝ] HyperbolicDivergenceFreeL2 :=
  ContinuousLinearMap.codRestrict
    (Submodule.subtypeL hyperbolicHarmonicL2)
    HyperbolicDivergenceFreeL2 (fun h ↦ h.property.1)

@[simp] theorem hyperbolicHarmonicToDivergenceFreeL2_coe
    (h : hyperbolicHarmonicL2) :
    (hyperbolicHarmonicToDivergenceFreeL2 h : HyperbolicOneFormL2) = h :=
  rfl

/-- A harmonic `L²` form as a zero-energy form-domain element. -/
noncomputable def hyperbolicHodgeStokesHarmonicForm
    (h : hyperbolicHarmonicL2) : HyperbolicHodgeStokesFormDomain :=
  WithLp.toLp 2 (0, h)

@[simp] theorem hyperbolicHodgeStokesEmbedding_harmonicForm
    (h : hyperbolicHarmonicL2) :
    hyperbolicHodgeStokesEmbedding (hyperbolicHodgeStokesHarmonicForm h) =
      hyperbolicHarmonicToDivergenceFreeL2 h := by
  apply Subtype.ext
  change hyperbolicOneFormH1ToL2 (0 : hyperbolicCoexactH1) +
      (h : HyperbolicOneFormL2) = h
  have hzero : ((0 : hyperbolicCoexactH1) : HyperbolicOneFormH1) = 0 := rfl
  rw [hzero, map_zero, zero_add]

@[simp] theorem hyperbolicHodgeStokesDerivative_harmonicForm
    (h : hyperbolicHarmonicL2) :
    hyperbolicHodgeStokesDerivative (hyperbolicHodgeStokesHarmonicForm h) = 0 := by
  change hyperbolicOneFormH1Hodge (0 : hyperbolicCoexactH1) = 0
  exact map_zero _

theorem hyperbolicHodgeStokesResolventForm_harmonicForm
    (h : hyperbolicHarmonicL2)
    (v : HyperbolicHodgeStokesFormDomain) :
    hyperbolicHodgeStokesResolventForm
        (hyperbolicHodgeStokesHarmonicForm h) v =
      inner ℝ (hyperbolicHarmonicToDivergenceFreeL2 h)
        (hyperbolicHodgeStokesEmbedding v) := by
  calc
    hyperbolicHodgeStokesResolventForm
          (hyperbolicHodgeStokesHarmonicForm h) v =
        inner ℝ
            (hyperbolicHodgeStokesEmbeddingAmbient
              (hyperbolicHodgeStokesHarmonicForm h))
            (hyperbolicHodgeStokesEmbeddingAmbient v) +
          inner ℝ
            (hyperbolicHodgeStokesDerivative
              (hyperbolicHodgeStokesHarmonicForm h))
            (hyperbolicHodgeStokesDerivative v) :=
      hyperbolicHodgeStokesResolventForm_apply _ _
    _ = inner ℝ (hyperbolicHarmonicToDivergenceFreeL2 h)
          (hyperbolicHodgeStokesEmbedding v) := by
      have hfirst :
          inner ℝ
              (hyperbolicHodgeStokesEmbeddingAmbient
                (hyperbolicHodgeStokesHarmonicForm h))
              (hyperbolicHodgeStokesEmbeddingAmbient v) =
            inner ℝ (hyperbolicHarmonicToDivergenceFreeL2 h)
              (hyperbolicHodgeStokesEmbedding v) := by
        change inner ℝ
            (hyperbolicHodgeStokesEmbedding
              (hyperbolicHodgeStokesHarmonicForm h))
            (hyperbolicHodgeStokesEmbedding v) = _
        exact congrArg
          (fun z : HyperbolicDivergenceFreeL2 ↦
            inner ℝ z (hyperbolicHodgeStokesEmbedding v))
          (hyperbolicHodgeStokesEmbedding_harmonicForm h)
      have hsecond :
          inner ℝ
              (hyperbolicHodgeStokesDerivative
                (hyperbolicHodgeStokesHarmonicForm h))
              (hyperbolicHodgeStokesDerivative v) = 0 := by
        rw [hyperbolicHodgeStokesDerivative_harmonicForm]
        exact inner_zero_left _
      calc
        inner ℝ
              (hyperbolicHodgeStokesEmbeddingAmbient
                (hyperbolicHodgeStokesHarmonicForm h))
              (hyperbolicHodgeStokesEmbeddingAmbient v) +
            inner ℝ
              (hyperbolicHodgeStokesDerivative
                (hyperbolicHodgeStokesHarmonicForm h))
              (hyperbolicHodgeStokesDerivative v) =
            inner ℝ (hyperbolicHarmonicToDivergenceFreeL2 h)
                (hyperbolicHodgeStokesEmbedding v) + 0 :=
          congrArg₂ (· + ·) hfirst hsecond
        _ = inner ℝ (hyperbolicHarmonicToDivergenceFreeL2 h)
              (hyperbolicHodgeStokesEmbedding v) := add_zero _

/-- The variational solution of a harmonic forcing is that same zero-energy harmonic form. -/
theorem hyperbolicHodgeStokesSolution_harmonic
    (h : hyperbolicHarmonicL2) :
    hyperbolicHodgeStokesSolution
        (hyperbolicHarmonicToDivergenceFreeL2 h) =
      hyperbolicHodgeStokesHarmonicForm h := by
  apply hyperbolicHodgeStokesLaxEquiv.injective
  calc
    hyperbolicHodgeStokesLaxEquiv
          (hyperbolicHodgeStokesSolution
            (hyperbolicHarmonicToDivergenceFreeL2 h)) =
        hyperbolicHodgeStokesEmbeddingAdjoint
          (hyperbolicHarmonicToDivergenceFreeL2 h) := by
      simpa only [hyperbolicHodgeStokesSolution,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_apply] using
        hyperbolicHodgeStokesLaxEquiv.apply_symm_apply
          (hyperbolicHodgeStokesEmbeddingAdjoint
            (hyperbolicHarmonicToDivergenceFreeL2 h))
    _ = hyperbolicHodgeStokesLaxEquiv
          (hyperbolicHodgeStokesHarmonicForm h) := by
      apply @ext_inner_right ℝ HyperbolicHodgeStokesFormDomain
        _ _ hyperbolicHodgeStokesFormDomainInnerProductSpace
      intro v
      calc
        inner ℝ
              (hyperbolicHodgeStokesEmbeddingAdjoint
                (hyperbolicHarmonicToDivergenceFreeL2 h)) v =
            inner ℝ (hyperbolicHarmonicToDivergenceFreeL2 h)
              (hyperbolicHodgeStokesEmbedding v) :=
          hyperbolicHodgeStokesEmbeddingAdjoint_inner _ _
        _ = hyperbolicHodgeStokesResolventForm
              (hyperbolicHodgeStokesHarmonicForm h) v :=
          (hyperbolicHodgeStokesResolventForm_harmonicForm h v).symm
        _ = inner ℝ
              (hyperbolicHodgeStokesLaxEquiv
                (hyperbolicHodgeStokesHarmonicForm h)) v :=
          (hyperbolicHodgeStokesLaxEquiv_inner _ _).symm

/-- The resolvent fixes the harmonic sector pointwise. -/
theorem hyperbolicHodgeStokesResolvent_harmonic
    (h : hyperbolicHarmonicL2) :
    hyperbolicHodgeStokesResolvent
        (hyperbolicHarmonicToDivergenceFreeL2 h) =
      hyperbolicHarmonicToDivergenceFreeL2 h := by
  change hyperbolicHodgeStokesEmbedding
      (hyperbolicHodgeStokesSolution
        (hyperbolicHarmonicToDivergenceFreeL2 h)) = _
  rw [hyperbolicHodgeStokesSolution_harmonic,
    hyperbolicHodgeStokesEmbedding_harmonicForm]

/-- A resolvent fixed point is exactly a distributional harmonic `L²` one-form. -/
theorem hyperbolicHodgeStokesResolvent_eq_self_iff_harmonic
    (f : HyperbolicDivergenceFreeL2) :
    hyperbolicHodgeStokesResolvent f = f ↔
      (f : HyperbolicOneFormL2) ∈ hyperbolicHarmonicL2 := by
  constructor
  · intro hfixed
    let u := hyperbolicHodgeStokesSolution f
    have henergy :
        inner ℝ f f = ‖f‖ ^ 2 +
          ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 := by
      simpa only [u, hfixed] using hyperbolicHodgeStokesResolvent_energy f
    have hinner : inner ℝ f f = ‖f‖ ^ 2 :=
      real_inner_self_eq_norm_sq f
    have hderivativeSq : ‖hyperbolicHodgeStokesDerivative u‖ ^ 2 = 0 := by
      linarith only [henergy, hinner]
    have hderivative : hyperbolicHodgeStokesDerivative u = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hderivativeSq)
    have hcoexactHarmonic :
        hyperbolicOneFormH1ToL2 u.ofLp.1 ∈ hyperbolicHarmonicL2 := by
      apply (hyperbolicOneFormH1ToL2_mem_harmonic_iff u.ofLp.1).2
      exact hderivative
    have hcoexactZeroL2 : hyperbolicOneFormH1ToL2 u.ofLp.1 = 0 :=
      (Submodule.mem_bot ℝ).1
        (hyperbolicCoexactL2_isOrtho_hyperbolicHarmonicL2.disjoint.le_bot
          ⟨(hyperbolicCoexactH1ToL2 u.ofLp.1).property,
            hcoexactHarmonic⟩)
    have hcoexactZero : u.ofLp.1 = 0 := by
      apply Subtype.ext
      apply hyperbolicOneFormH1ToL2_injective
      simpa using hcoexactZeroL2
    have hf : (f : HyperbolicOneFormL2) = u.ofLp.2 := by
      calc
        (f : HyperbolicOneFormL2) =
            (hyperbolicHodgeStokesResolvent f :
              HyperbolicDivergenceFreeL2) :=
          congrArg Subtype.val hfixed.symm
        _ = hyperbolicOneFormH1ToL2 u.ofLp.1 + u.ofLp.2 := by rfl
        _ = u.ofLp.2 := by rw [hcoexactZero]; simp
    rw [hf]
    exact u.ofLp.2.property
  · intro hf
    let h : hyperbolicHarmonicL2 := ⟨(f : HyperbolicOneFormL2), hf⟩
    have hcoe : hyperbolicHarmonicToDivergenceFreeL2 h = f := by
      apply Subtype.ext
      rfl
    calc
      hyperbolicHodgeStokesResolvent f =
          hyperbolicHodgeStokesResolvent
            (hyperbolicHarmonicToDivergenceFreeL2 h) :=
        congrArg hyperbolicHodgeStokesResolvent hcoe.symm
      _ = hyperbolicHarmonicToDivergenceFreeL2 h :=
        hyperbolicHodgeStokesResolvent_harmonic h
      _ = f := hcoe

/-- Exact kernel identification for the closed Hodge--Stokes operator. -/
theorem hyperbolicHodgeStokesOperator_eq_zero_iff_harmonic
    (x : hyperbolicHodgeStokesOperator.domain) :
    hyperbolicHodgeStokesOperator x = 0 ↔
      (x : HyperbolicDivergenceFreeL2).1 ∈ hyperbolicHarmonicL2 := by
  constructor
  · intro hzero
    rcases hyperbolicHodgeStokesOperator_exists_resolvent_representation x with
      ⟨f, rfl⟩
    have hsub : f - hyperbolicHodgeStokesResolvent f = 0 := by
      calc
        f - hyperbolicHodgeStokesResolvent f =
            hyperbolicHodgeStokesOperator
              (hyperbolicHodgeStokesResolventDomainElement f) :=
          (hyperbolicHodgeStokesOperator_resolvent f).symm
        _ = 0 := hzero
    have hfixed : hyperbolicHodgeStokesResolvent f = f :=
      (sub_eq_zero.mp hsub).symm
    have hf := (hyperbolicHodgeStokesResolvent_eq_self_iff_harmonic f).1 hfixed
    simpa only [hyperbolicHodgeStokesResolventDomainElement_coe, hfixed] using hf
  · intro hx
    have hfixed : hyperbolicHodgeStokesResolvent
        (x : HyperbolicDivergenceFreeL2) = x :=
      (hyperbolicHodgeStokesResolvent_eq_self_iff_harmonic
        (x : HyperbolicDivergenceFreeL2)).2 hx
    have hcanonical :
        x = hyperbolicHodgeStokesResolventDomainElement
          (x : HyperbolicDivergenceFreeL2) := by
      apply Subtype.ext
      exact hfixed.symm
    rw [hcanonical, hyperbolicHodgeStokesOperator_resolvent, hfixed, sub_self]

/-- Compatibility with the concrete Leray projector: it fixes every vector in the ambient
Hodge--Stokes Hilbert space. -/
@[simp] theorem hyperbolicLerayProjector_divergenceFree
    (u : HyperbolicDivergenceFreeL2) :
    hyperbolicLerayProjector (u : HyperbolicOneFormL2) = u := by
  rw [hyperbolicLerayProjector,
    Submodule.starProjection_eq_self_iff]
  exact u.property

end RiemannianFluids.HyperbolicPlane
