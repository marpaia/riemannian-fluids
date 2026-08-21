import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Closed operators and their graph Hilbert spaces

The global Hodge--Stokes construction is built from unbounded operators on concrete `L²`
spaces.  This module packages Mathlib's `LinearPMap` closed-operator theory without weakening it
to a project-specific predicate.

For a closed operator `A : E → F`, `A.GraphSpace` is the actual closed subspace

    {(u, A u)} ⊆ E ×₂ F

of the Hilbert `L²` product `WithLp 2 (E × F)`.  It is therefore complete, its inner product
is exactly the graph inner product, and the base and operator-value coordinates are bounded maps.
This will be the concrete Sobolev carrier for the closed hyperbolic covariant derivative.
-/

noncomputable section

namespace RiemannianFluids

open Set
open scoped ENNReal

/-- A genuinely closed, possibly unbounded linear operator between inner-product spaces. -/
structure ClosedLinearOperator (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] where
  operator : E →ₗ.[𝕜] F
  isClosed : operator.IsClosed

/-- A closed operator with dense domain, the hypothesis needed for a genuine Hilbert adjoint. -/
structure DenselyDefinedClosedLinearOperator (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    extends ClosedLinearOperator 𝕜 E F where
  dense_domain : Dense (operator.domain : Set E)

namespace ClosedLinearOperator

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable (A : ClosedLinearOperator 𝕜 E F)

/-- The graph transported from the ordinary product to the Hilbert `L²` product.  The
transport is a continuous linear equivalence, so it preserves closedness. -/
noncomputable def graphSubmodule : Submodule 𝕜 (WithLp 2 (E × F)) :=
  A.operator.graph.comap (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).toLinearMap

/-- The graph-norm Hilbert carrier of a closed operator. -/
abbrev GraphSpace := A.graphSubmodule

instance graphSubmodule_isClosed :
    IsClosed (A.graphSubmodule : Set (WithLp 2 (E × F))) :=
  A.isClosed.preimage (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).continuous

variable [CompleteSpace E] [CompleteSpace F]

/-- A closed graph in the Hilbert product is complete. -/
noncomputable instance graphSpaceCompleteSpace : CompleteSpace A.GraphSpace :=
  inferInstance

omit [CompleteSpace E] [CompleteSpace F] in
/-- Bounded projection from the graph carrier to the base Hilbert space. -/
noncomputable def base : A.GraphSpace →L[𝕜] E :=
  (WithLp.fstL 2 𝕜 E F).comp (Submodule.subtypeL A.graphSubmodule)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Bounded projection from the graph carrier to the operator-value Hilbert space. -/
noncomputable def value : A.GraphSpace →L[𝕜] F :=
  (WithLp.sndL 2 𝕜 E F).comp (Submodule.subtypeL A.graphSubmodule)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem base_apply (u : A.GraphSpace) :
    A.base u = (WithLp.ofLp u.1).1 :=
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem value_apply (u : A.GraphSpace) :
    A.value u = (WithLp.ofLp u.1).2 :=
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- Insert a domain element into the graph carrier. -/
noncomputable def graphMk (u : A.operator.domain) : A.GraphSpace :=
  ⟨WithLp.toLp 2 ((u : E), A.operator u), by
    change ((u : E), A.operator u) ∈ A.operator.graph
    exact A.operator.mem_graph u⟩

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem base_graphMk (u : A.operator.domain) :
    A.base (A.graphMk u) = u :=
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem value_graphMk (u : A.operator.domain) :
    A.value (A.graphMk u) = A.operator u :=
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- Recover the uniquely determined domain element from a point of the graph. -/
noncomputable def domainElement (u : A.GraphSpace) : A.operator.domain :=
  ⟨A.base u, by
    apply A.operator.mem_domain_of_mem_graph
    exact u.property⟩

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem coe_domainElement (u : A.GraphSpace) :
    (A.domainElement u : E) = A.base u :=
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem domainElement_graphMk (u : A.operator.domain) :
    A.domainElement (A.graphMk u) = u := by
  apply Subtype.ext
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem operator_domainElement (u : A.GraphSpace) :
    A.operator (A.domainElement u) = A.value u := by
  rcases A.operator.mem_graph_iff.mp u.property with ⟨v, hvbase, hvvalue⟩
  have hdomain : A.domainElement u = v := by
    apply Subtype.ext
    exact hvbase.symm
  rw [hdomain]
  calc
    A.operator v = ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F) u.1).2 := hvvalue
    _ = (WithLp.ofLp u.1).2 := by rw [WithLp.prodContinuousLinearEquiv_apply]
    _ = A.value u := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem graphMk_domainElement (u : A.GraphSpace) :
    A.graphMk (A.domainElement u) = u := by
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 𝕜 (E × F)).injective
  apply Prod.ext
  · rfl
  · exact A.operator_domainElement u

omit [CompleteSpace E] [CompleteSpace F] in
/-- The operator domain and the graph carrier are linearly equivalent.  The latter carries the
graph norm and, for a closed operator between Hilbert spaces, a `CompleteSpace` instance. -/
noncomputable def domainGraphLinearEquiv :
    A.operator.domain ≃ₗ[𝕜] A.GraphSpace where
  toFun := A.graphMk
  invFun := A.domainElement
  map_add' u v := by
    apply Subtype.ext
    apply (WithLp.linearEquiv 2 𝕜 (E × F)).injective
    change (((u + v : A.operator.domain) : E), A.operator (u + v)) =
      ((u : E), A.operator u) + ((v : E), A.operator v)
    exact Prod.ext (by simp) (A.operator.map_add u v)
  map_smul' c u := by
    apply Subtype.ext
    apply (WithLp.linearEquiv 2 𝕜 (E × F)).injective
    change (((c • u : A.operator.domain) : E), A.operator (c • u)) =
      c • ((u : E), A.operator u)
    exact Prod.ext (by simp) (A.operator.map_smul c u)
  left_inv := A.domainElement_graphMk
  right_inv := A.graphMk_domainElement

omit [CompleteSpace E] [CompleteSpace F] in
/-- The graph inner product is the sum of the base and operator-value inner products. -/
@[simp] theorem inner_graph (u v : A.GraphSpace) :
    inner 𝕜 u v =
      inner 𝕜 (A.base u) (A.base v) + inner 𝕜 (A.value u) (A.value v) :=
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The norm on the graph carrier is exactly the graph norm. -/
@[simp] theorem norm_sq_graph (u : A.GraphSpace) :
    ‖u‖ ^ 2 = ‖A.base u‖ ^ 2 + ‖A.value u‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

/-- Close a closable partially defined operator. -/
noncomputable def ofClosable (T : E →ₗ.[𝕜] F) (hT : T.IsClosable) :
    ClosedLinearOperator 𝕜 E F :=
  ⟨T.closure, hT.closure_isClosed⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- The original domain is a core for the closed operator obtained from it. -/
theorem ofClosable_hasCore (T : E →ₗ.[𝕜] F) (hT : T.IsClosable) :
    (ofClosable T hT).operator.HasCore T.domain :=
  T.closureHasCore

end ClosedLinearOperator

namespace DenselyDefinedClosedLinearOperator

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Closing a closable densely defined operator preserves density of the domain. -/
noncomputable def ofClosable (T : E →ₗ.[𝕜] F) (hT : T.IsClosable)
    (hDense : Dense (T.domain : Set E)) : DenselyDefinedClosedLinearOperator 𝕜 E F where
  operator := T.closure
  isClosed := hT.closure_isClosed
  dense_domain := hDense.mono T.le_closure.1

variable [CompleteSpace E]

/-- The Hilbert adjoint of a densely defined operator is closed. -/
noncomputable def adjoint (A : DenselyDefinedClosedLinearOperator 𝕜 E F) :
    ClosedLinearOperator 𝕜 F E :=
  ⟨A.operator.adjoint, A.operator.adjoint_isClosed A.dense_domain⟩

end DenselyDefinedClosedLinearOperator

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A densely defined formal adjoint makes an operator closable.  This is the exact functional-
analytic bridge that an integration-by-parts theorem must supply for the hyperbolic core
operators; no closability assumption has to be postulated separately. -/
theorem isClosable_of_formalAdjoint {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}
    [CompleteSpace F] (h : T.IsFormalAdjoint S)
    (hS : Dense (S.domain : Set F)) : T.IsClosable := by
  rw [LinearPMap.isClosable_iff_exists_closed_extension]
  exact ⟨S.adjoint, S.adjoint_isClosed hS, h.symm.le_adjoint hS⟩

variable {C : Type*} [AddCommGroup C] [Module 𝕜 C]

/-- Turn a linear operator on an abstract core into a `LinearPMap` on the ambient Hilbert space.
Injectivity of the core inclusion makes the representative unique; the domain is its actual
linear range. -/
noncomputable def linearPMapOfInjectiveCore (inclusion : C →ₗ[𝕜] E)
    (hinclusion : Function.Injective inclusion) (coreOperator : C →ₗ[𝕜] F) :
    E →ₗ.[𝕜] F where
  domain := inclusion.range
  toFun := coreOperator.comp (LinearEquiv.ofInjective inclusion hinclusion).symm.toLinearMap

@[simp] theorem linearPMapOfInjectiveCore_domain (inclusion : C →ₗ[𝕜] E)
    (hinclusion : Function.Injective inclusion) (coreOperator : C →ₗ[𝕜] F) :
    (linearPMapOfInjectiveCore inclusion hinclusion coreOperator).domain = inclusion.range :=
  rfl

/-- On an included core element, `linearPMapOfInjectiveCore` is the original core operator. -/
@[simp] theorem linearPMapOfInjectiveCore_apply (inclusion : C →ₗ[𝕜] E)
    (hinclusion : Function.Injective inclusion) (coreOperator : C →ₗ[𝕜] F) (u : C) :
    linearPMapOfInjectiveCore inclusion hinclusion coreOperator
      ⟨inclusion u, ⟨u, rfl⟩⟩ = coreOperator u := by
  change coreOperator ((LinearEquiv.ofInjective inclusion hinclusion).symm
    ⟨inclusion u, ⟨u, rfl⟩⟩) = coreOperator u
  congr 1
  apply hinclusion
  rw [LinearEquiv.ofInjective_symm_apply]

/-- Density of the embedded core is exactly density of the partial operator's domain. -/
theorem linearPMapOfInjectiveCore_dense_domain (inclusion : C →ₗ[𝕜] E)
    (hinclusion : Function.Injective inclusion) (coreOperator : C →ₗ[𝕜] F)
    (hDense : Dense (Set.range (inclusion : C → E))) :
    Dense ((linearPMapOfInjectiveCore inclusion hinclusion coreOperator).domain : Set E) := by
  change Dense (inclusion.range : Set E)
  simpa only [LinearMap.coe_range] using hDense

end RiemannianFluids
