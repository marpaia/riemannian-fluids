import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import RiemannianFluids.Geometry.Musical

/-!
# Differential and gradient of a scalar field

The scalar differential loses one derivative.  The Riemannian gradient is its
metric dual and therefore has the same explicit regularity loss.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
  (regularity : ℕ∞ω)
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]

set_option backward.isDefEq.respectTransparency false in
/-- Exterior differentiation in degree zero: `C^(k+1)(M) -> C^k(T*M)`. -/
noncomputable def scalarDifferential :
    SmoothScalarField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothOneForm (M := M) I regularity where
  toFun scalar :=
    { toFun := fun x => d% scalar x
      contMDiff_toFun := by
        intro x₀
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_id, ?_⟩
        have hscalar : ContMDiffAt I 𝓘(ℝ) (regularity + 1) scalar x₀ :=
          scalar.contMDiff.contMDiffAt
        have h := hscalar.mfderiv_const (m := regularity) le_rfl
        convert h using 1
        ext x direction
        simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv]
        rfl }
  map_add' first second := by
    ext x direction
    simp [mvfderiv_add (first.mdifferentiable' (by simp) x)
      (second.mdifferentiable' (by simp) x)]
  map_smul' scalar field := by
    ext x direction
    change d% (fun y => scalar * field y) x direction =
      scalar * d% field x direction
    rw [show (fun y : M => scalar * field y) =
      (fun _ : M => scalar) * (fun y => field y) from rfl]
    rw [mvfderiv_mul (I := I) (x := x) (f := fun _ : M => scalar)
      (g := fun y => field y) (mdifferentiableAt_const (x := x))
      (field.mdifferentiable' (by simp) x)]
    simp [mvfderiv_const]

omit [FiniteDimensional ℝ E]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)] in
@[simp]
theorem scalarDifferential_apply
    (scalar : SmoothScalarField (M := M) I (regularity + 1)) (x : M) :
    scalarDifferential I regularity scalar x = d% scalar x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The Riemannian gradient, with its loss of one derivative visible. -/
noncomputable def gradient :
    SmoothScalarField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothVectorField (M := M) I regularity :=
  (sharp I regularity).comp (scalarDifferential I regularity)

@[simp]
theorem gradient_characterization
    (scalar : SmoothScalarField (M := M) I (regularity + 1))
    (x : M) (direction : TangentSpace I x) :
    inner ℝ (gradient I regularity scalar x) direction = d% scalar x direction := by
  change inner ℝ (sharp I regularity (scalarDifferential I regularity scalar) x) direction = _
  calc
    _ = flat I regularity (sharp I regularity (scalarDifferential I regularity scalar)) x
        direction := (flat_apply I regularity _ x direction).symm
    _ = scalarDifferential I regularity scalar x direction := by rw [flat_sharp]
    _ = d% scalar x direction := rfl

end RiemannianFluids
