import RiemannianFluids.Geometry.Manifolds
import RiemannianFluids.Tensors.SmoothSections

/-!
# Natural symmetry operations on covariant two-tensors

The operation in this file is almost insultingly simple on one vector space. If `T` is a covariant two-tensor, transpose exchanges its arguments and
symmetrization averages the result with the original tensor:

    Tᵀ(X,Y) = T(Y,X),
    Sym(T)   = 1/2 (T + Tᵀ).

The point of formalizing it is not to discover either formula. The point is to understand what the word *tensorial* commits us to when the vector
space is the moving tangent fiber `T_xM`.

## The geometric issue: the fibers move

A smooth covariant two-tensor is not an ordinary function into one fixed space of bilinear forms. At `x` it belongs to

    T_x*M ⊗ T_x*M = Hom(T_xM, Hom(T_xM, ℝ)).

To say that `x ↦ T_xᵀ` is smooth, Lean asks us to move the tensor into a fixed model fiber using a local trivialization and prove smoothness there.
This is legitimate only if transpose commutes with the change of coordinates. For a tangent-coordinate isomorphism `P`, the two coordinate procedures
are

    coordinates(Tᵀ)              and              transpose(coordinates(T)).

Both evaluate model vectors `u,v` by sending them back through `P⁻¹` and then asking for `T(P⁻¹v, P⁻¹u)`. Their equality is the naturality calculation
in `transposeCovariantTwoTensor`; it is the mathematical center of the otherwise long bundle proof.

## Why this matters for the fluid operator

Chan--Czubak--Disconzi define the deformation tensor in equation (1.2) of arXiv:1608.05114v2 by

    (Def u)ᵢⱼ = 1/2 (∇ᵢuⱼ + ∇ⱼuᵢ).

Invariantly, first lower the vector-valued output of `∇u` to obtain

    T(X,Y) = g(∇_X u,Y),

and then apply `Sym`. Thus this small algebraic construction is the bridge between the connection and the strain tensor used by the deformation
Laplacian.

## The argument encoded below

There are three movements.

1. Construct fiberwise transpose and prove its coordinate expression is smooth. The proof restricts to a neighborhood where tangent and cotangent
   trivializations are genuine equivalences, expands both coordinate maps, and checks equality on two arbitrary model vectors.
2. Define symmetrization as the linear-map expression `(2 : ℝ)⁻¹ • (id + transpose)`. Because transpose is already known to preserve smooth sections,
   no second bundle-coordinate proof is needed.
3. Prove the expected algebra: transpose is involutive, symmetrization is symmetric, and symmetrization is idempotent. Once the bundle construction
   has been discharged, these are scalar identities proved by extensionality and commutative-ring normalization.

So the ratio of prose to Lean is intentionally uneven. The mathematics is a two-line definition; the formal analysis exposes the otherwise tacit claim
that this definition is independent of coordinates and preserves regularity.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]

set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
/--
Coordinate-natural transposition of a covariant two-tensor: `Tᵀ(X,Y) = T(Y,X)`.

The output is packaged as a linear map on `C^k` sections. The central obligation is `contMDiff_toFun`, which proves the pointwise `flip` varies
smoothly and is independent of the local trivialization used in that proof.
-/
noncomputable def transposeCovariantTwoTensor (regularity : ℕ∞ω) :
    SmoothCovariantTwoTensor (M := M) I regularity →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity where
  toFun field :=
    -- Algebraically, transpose is just `ContinuousLinearMap.flip` in each fiber.
    { toFun := fun x => (field x).flip
      contMDiff_toFun := by
        -- Check smoothness at an arbitrary point `x₀`.
        intro x₀
        -- Use mathlib's coordinate characterization for hom-bundle sections.
        rw [contMDiffAt_hom_bundle]
        -- The section lies over the identity map; only its coordinate value is nontrivial.
        refine ⟨contMDiffAt_id, ?_⟩
        -- Extract smoothness of the original tensor in the same coordinates.
        have hfield :
            ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) regularity
              (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (field x)) x₀ :=
          field.contMDiff.contMDiffAt
        rw [contMDiffAt_hom_bundle] at hfield
        -- First prove that flipping the *coordinate* bilinear map is smooth.
        have hflip : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) regularity
            (fun x : M => ContinuousLinearMap.flip
              (ContinuousLinearMap.inCoordinates
                E (TangentSpace I : M → Type _)
                (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)
                x₀ x x₀ x (field x))) x₀ := by
          -- It suffices to know that `flip` is a smooth map between the model normed spaces of continuous bilinear maps.
          have hflipAt : ContMDiffAt 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)
              𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) regularity ContinuousLinearMap.flip
              (ContinuousLinearMap.inCoordinates
                E (TangentSpace I : M → Type _)
                (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)
                x₀ x₀ x₀ x₀ (field x₀)) := by
            -- Ordinary smoothness on a normed space implies smoothness for its identity manifold model.
            apply ContDiffAt.contMDiffAt
            apply ContDiff.contDiffAt
            -- A bounded linear map is smooth. We prove `flip` is bounded and linear directly to avoid relying on an incompatible instance path.
            apply IsBoundedLinearMap.contDiff
            refine IsBoundedLinearMap.mk (IsLinearMap.mk ?_ ?_) ?_
            -- Swapping arguments commutes with addition.
            · exact ContinuousLinearMap.flip_add
            -- Swapping arguments commutes with scalar multiplication.
            · exact ContinuousLinearMap.flip_smul
            -- `flip` has operator norm one because it preserves the bilinear operator norm.
            · refine ⟨1, zero_lt_one, ?_⟩
              intro tensor
              rw [ContinuousLinearMap.opNorm_flip, one_mul]
          -- Compose smooth `flip` with the smooth coordinate tensor field.
          exact hflipAt.comp x₀ hfield.2
        -- Relate “flip after taking coordinates” to “take coordinates after fiberwise transpose”. This is the naturality calculation.
        apply hflip.congr_of_eventuallyEq
        -- Work on neighborhoods where both tangent and cotangent trivializations are represented by genuine linear equivalences.
        have hT :
            (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ 𝓝 x₀ :=
          (trivializationAt _ _ _).open_baseSet.mem_nhds
            (FiberBundle.mem_baseSet_trivializationAt' _)
        have hTstar :
            (trivializationAt (E →L[ℝ] ℝ)
              (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀).baseSet ∈ 𝓝 x₀ :=
          (trivializationAt _ _ _).open_baseSet.mem_nhds
            (FiberBundle.mem_baseSet_trivializationAt' _)
        filter_upwards [hT, hTstar] with x hx hxstar
        -- Expand both coordinate maps using those local equivalences.
        rw [ContinuousLinearMap.inCoordinates_eq hx hxstar,
          ContinuousLinearMap.inCoordinates_eq hx hxstar]
        -- Bilinear maps are equal if they agree on arbitrary model vectors.
        ext u v
        simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
        -- Unfold the induced cotangent chart. The left side now evaluates the intrinsic tensor on the two inverse-coordinate tangent vectors in
        -- swapped order, exactly as the right side does.
        simp [ContinuousLinearMap.flip_apply, hom_trivializationAt,
          Bundle.Trivialization.continuousLinearMap_apply]
        -- Replace the “always-defined” inverse chart maps by the actual local inverse equivalences. Both sides are then definitionally equal.
        rw [(trivializationAt E (TangentSpace I : M → Type _) x₀).symmL_apply hx v,
          (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL_apply hx u] }
  map_add' first second := by
    -- Fiberwise flip is additive.
    ext x u v
    simp
  map_smul' scalar field := by
    -- Fiberwise flip is homogeneous.
    ext x u v
    simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Pointwise evaluation exposes transpose as the exchange of two arguments. -/
@[simp]
theorem transposeCovariantTwoTensor_apply (regularity : ℕ∞ω)
    (field : SmoothCovariantTwoTensor (M := M) I regularity)
    (x : M) (u v : TangentSpace I x) :
    transposeCovariantTwoTensor I regularity field x u v = field x v u :=
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Swapping both covariant arguments twice returns the original tensor field. -/
@[simp]
theorem transposeCovariantTwoTensor_involutive (regularity : ℕ∞ω)
    (field : SmoothCovariantTwoTensor (M := M) I regularity) :
    transposeCovariantTwoTensor I regularity
      (transposeCovariantTwoTensor I regularity field) = field := by
  -- Equality of tensor fields reduces to a point and two tangent arguments.
  ext x u v
  -- Swapping the two arguments twice is definitionally the identity.
  rfl

set_option synthInstance.maxHeartbeats 100000 in
/--
Fiberwise symmetrization `T ↦ (T + Tᵀ) / 2`. Because transpose has already been constructed as a linear map on smooth sections, symmetrization is
simply a linear combination of section maps; no new coordinate proof is required.
-/
noncomputable def symmetrizeCovariantTwoTensor (regularity : ℕ∞ω) :
    SmoothCovariantTwoTensor (M := M) I regularity →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity :=
  (2 : ℝ)⁻¹ • (LinearMap.id + transposeCovariantTwoTensor I regularity)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
set_option synthInstance.maxHeartbeats 100000 in
/-- Pointwise evaluation recovers the familiar average `1/2 (T(X,Y) + T(Y,X))`. -/
@[simp]
theorem symmetrizeCovariantTwoTensor_apply (regularity : ℕ∞ω)
    (field : SmoothCovariantTwoTensor (M := M) I regularity)
    (x : M) (u v : TangentSpace I x) :
    symmetrizeCovariantTwoTensor I regularity field x u v =
      (2 : ℝ)⁻¹ * (field x u v + field x v u) := by
  -- Expand linear-map addition, scalar multiplication, and transpose at the chosen point and arguments.
  simp [symmetrizeCovariantTwoTensor, transposeCovariantTwoTensor_apply]
  -- Normalize the elementary scalar algebra into the displayed `1/2` formula.
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The symmetrized tensor is fixed by transpose. -/
theorem symmetrizeCovariantTwoTensor_symmetric (regularity : ℕ∞ω)
    (field : SmoothCovariantTwoTensor (M := M) I regularity) :
    transposeCovariantTwoTensor I regularity
        (symmetrizeCovariantTwoTensor I regularity field) =
      symmetrizeCovariantTwoTensor I regularity field := by
  -- Check equality pointwise on two arbitrary tangent vectors.
  ext x u v
  -- Expand transpose and both evaluations of symmetrization.
  rw [transposeCovariantTwoTensor_apply,
    symmetrizeCovariantTwoTensor_apply, symmetrizeCovariantTwoTensor_apply]
  -- The two summands differ only by commutativity of addition.
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Symmetrization is a projection: applying it twice changes nothing. -/
@[simp]
theorem symmetrizeCovariantTwoTensor_idempotent (regularity : ℕ∞ω)
    (field : SmoothCovariantTwoTensor (M := M) I regularity) :
    symmetrizeCovariantTwoTensor I regularity
        (symmetrizeCovariantTwoTensor I regularity field) =
      symmetrizeCovariantTwoTensor I regularity field := by
  -- Again reduce tensor equality to scalar equality on arbitrary arguments.
  ext x u v
  -- Expand the outer symmetrization and its two inner evaluations.
  rw [symmetrizeCovariantTwoTensor_apply, symmetrizeCovariantTwoTensor_apply,
    symmetrizeCovariantTwoTensor_apply]
  -- Averaging an already averaged pair changes nothing.
  ring

end RiemannianFluids
