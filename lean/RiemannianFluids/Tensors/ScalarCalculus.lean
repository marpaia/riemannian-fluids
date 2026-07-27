import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import RiemannianFluids.Geometry.Musical

/-!
# Differential and gradient of a scalar field

For a scalar field `f`, the differential and gradient contain the same first-order information in dual forms:

    df_x(X) = X(f),
    g_x(grad f,X) = df_x(X).

The first is naturally a one-form. The second is the vector field obtained by raising that one-form with the metric:

    grad f = (df)♯.

This is standard Riemannian calculus rather than a claim peculiar to CCD17, but it enters that paper in two places. It supplies the pressure gradient
in the Navier--Stokes equation, and `d` in degree zero supplies the outer differential in the exact Hodge correction `d d*`.

## What differentiation costs

An informal formula rarely advertises regularity. Lean's bundled smooth maps make the loss visible:

    d : C^(k+1)(M,ℝ) → C^k(T*M),
    grad : C^(k+1)(M,ℝ) → C^k(TM).

`scalarDifferential` uses mathlib's manifold Fréchet derivative `d%`. The nontrivial obligation is showing that the pointwise derivatives assemble
into a `C^k` cotangent section. In local coordinates this is precisely mathlib's theorem that the derivative of a `C^(k+1)` map is a `C^k` derivative
field.

## The proof of the gradient characterization

The final theorem follows the definition rather than recomputing derivatives:

    g(grad f,X)
      = (grad f)♭(X)       by the definition of metric lowering,
      = df(X)                because flat and sharp are inverse,
      = X(f)                 by the definition of `df`.

The three lines of the Lean `calc` block are exactly those three mathematical equalities. This is the style of the development: the prose presents the
argument, and the term confirms that the library representations really have the promised relationship.
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
/--
Exterior differentiation in degree zero: `C^(k+1)(M) -> C^k(T*M)`.

For a scalar field `f`, mathlib's manifold derivative `d% f x` is a continuous linear functional on `T_xM`, hence a one-form. The implementation below
proves that these pointwise derivatives form a `C^k` section.
-/
noncomputable def scalarDifferential :
    SmoothScalarField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothOneForm (M := M) I regularity where
  toFun scalar :=
    -- Pointwise, `df` is exactly mathlib's manifold Fréchet derivative.
    { toFun := fun x => d% scalar x
      contMDiff_toFun := by
        -- Smoothness of a hom-bundle section is checked in bundle coordinates.
        intro x₀
        rw [contMDiffAt_hom_bundle]
        -- The base point is the identity map; only the coordinate value remains.
        refine ⟨contMDiffAt_id, ?_⟩
        -- Extract the `C^(k+1)` hypothesis carried by the bundled scalar field.
        have hscalar : ContMDiffAt I 𝓘(ℝ) (regularity + 1) scalar x₀ :=
          scalar.contMDiff.contMDiffAt
        -- Mathlib proves that differentiating a `C^(k+1)` map gives a `C^k` derivative field in local coordinates.
        have h := hscalar.mfderiv_const (m := regularity) le_rfl
        -- The theorem's coordinate expression is definitionally the one used by the cotangent-bundle chart, after expanding the notation.
        convert h using 1
        ext x direction
        simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv]
        rfl }
  map_add' first second := by
    -- Equality of one-forms is pointwise and then tested on a tangent vector.
    ext x direction
    -- Apply the manifold derivative's sum rule; bundled regularity supplies the differentiability side conditions.
    simp [mvfderiv_add (first.mdifferentiable' (by simp) x)
      (second.mdifferentiable' (by simp) x)]
  map_smul' scalar field := by
    ext x direction
    -- Rewrite scalar multiplication into ordinary multiplication of functions so that mathlib's product rule applies.
    change d% (fun y => scalar * field y) x direction =
      scalar * d% field x direction
    rw [show (fun y : M => scalar * field y) =
      (fun _ : M => scalar) * (fun y => field y) from rfl]
    rw [mvfderiv_mul (I := I) (x := x) (f := fun _ : M => scalar)
      (g := fun y => field y) (mdifferentiableAt_const (x := x))
      (field.mdifferentiable' (by simp) x)]
    -- The derivative of the constant factor vanishes.
    simp [mvfderiv_const]

omit [FiniteDimensional ℝ E]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)] in
/-- Evaluating the bundled scalar differential gives mathlib's manifold derivative. -/
@[simp]
theorem scalarDifferential_apply
    (scalar : SmoothScalarField (M := M) I (regularity + 1)) (x : M) :
    scalarDifferential I regularity scalar x = d% scalar x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The Riemannian gradient, with its loss of one derivative visible. The definition is the coordinate-free identity `grad f = (df)♯`.
-/
noncomputable def gradient :
    SmoothScalarField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothVectorField (M := M) I regularity :=
  (sharp I regularity).comp (scalarDifferential I regularity)

@[simp]
theorem gradient_characterization
    (scalar : SmoothScalarField (M := M) I (regularity + 1))
    (x : M) (direction : TangentSpace I x) :
    inner ℝ (gradient I regularity scalar x) direction = d% scalar x direction := by
  -- Unfold only the composition defining the gradient; keep the musical maps abstract so their inverse theorem can be used.
  change inner ℝ (sharp I regularity (scalarDifferential I regularity scalar) x) direction = _
  calc
    -- Express the inner product as evaluation of the lowered vector.
    _ = flat I regularity (sharp I regularity (scalarDifferential I regularity scalar)) x
        direction := (flat_apply I regularity _ x direction).symm
    -- Lowering after raising is the identity on one-forms.
    _ = scalarDifferential I regularity scalar x direction := by rw [flat_sharp]
    -- The scalar differential was defined pointwise as `d% scalar`.
    _ = d% scalar x direction := rfl

end RiemannianFluids
