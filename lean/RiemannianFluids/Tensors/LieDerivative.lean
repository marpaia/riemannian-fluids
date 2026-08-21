import Mathlib.Geometry.Manifold.VectorField.LieBracket
import RiemannianFluids.Tensors.VectorCalculus

/-!
# The Lie derivative of the metric

The Lie derivative of the Riemannian metric along a velocity field `u` measures the rate at
which the flow of `u` deforms lengths and angles.  Its flow-free algebraic characterization on
vector fields `X`, `Y` is

    (L_u g)(X,Y) = u ⟨X,Y⟩ - g([u,X],Y) - g(X,[u,Y]),

where the first term differentiates the scalar function `y ↦ g(X(y),Y(y))` in the direction
`u`.  This expression involves no connection and no flow: it uses only the manifold Lie bracket,
which mathlib supplies as `VectorField.mlieBracket`.

The central identity of this module is the kinematic origin of deformation viscosity used by
Wang--Braunstein, arXiv:2605.17502v2, equations (22)--(24): for a Levi-Civita connection,

    (L_u g)(X,Y) = g(∇_X u, Y) + g(∇_Y u, X) = 2 Def u (X,Y).

The proof is the classical two-step cancellation.  Metric compatibility rewrites the directional
derivative as `g(∇_u X,Y) + g(X,∇_u Y)`; vanishing torsion rewrites each bracket as
`[u,X] = ∇_u X - ∇_X u`; the `∇_u` terms cancel, leaving the symmetrized covariant derivative.
Both connection properties enter as the fields of `LeviCivitaConnection`, and the vector fields
carry pointwise `MDiffAt` hypotheses, so the theorem's assumptions are exactly the two defining
Levi-Civita properties plus one derivative of each field at the base point.

The identity is a theorem about `metricLieDerivativeAt`, not a definition: the left-hand side is
built from the Lie bracket alone, while the right-hand side is built from the connection alone.
Identifying `metricLieDerivativeAt` with the derivative of an actual flow pullback awaits an
integral-curve theory for manifold vector fields.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The Lie derivative of the metric along `u`, evaluated on raw tangent fields at a point.

This is the flow-free characterization `u ⟨X,Y⟩ - g([u,X],Y) - g(X,[u,Y])`.  No regularity is
imposed by the definition; the theorems below attach the pointwise differentiability needed by
each identity. -/
noncomputable def metricLieDerivativeAt
    (u X Y : (y : M) → TangentSpace I y) (x : M) : ℝ :=
  d% (fun y => inner ℝ (X y) (Y y)) x (u x) -
    inner ℝ (VectorField.mlieBracket I u X x) (Y x) -
    inner ℝ (X x) (VectorField.mlieBracket I u Y x)

/-- For a Levi-Civita connection, the metric Lie derivative is the symmetrized metric-lowered
covariant derivative:

`(L_u g)(X,Y) = g(∇_X u, Y) + g(∇_Y u, X)`.

Metric compatibility converts the directional derivative of `g(X,Y)` into `g(∇_u X,Y) +
g(X,∇_u Y)`, torsion-freeness converts each Lie bracket into a difference of covariant
derivatives, and the `∇_u` terms cancel. -/
theorem metricLieDerivativeAt_leviCivita
    (connection : LeviCivitaConnection (M := M) I)
    {u X Y : (y : M) → TangentSpace I y} {x : M}
    (hu : MDiffAt (T% u) x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    metricLieDerivativeAt I u X Y x =
      inner ℝ (connection.connection u x (X x)) (Y x) +
        inner ℝ (connection.connection u x (Y x)) (X x) := by
  -- Metric compatibility: `u ⟨X,Y⟩ = g(∇_u X,Y) + g(X,∇_u Y)` at `x`.
  have compat := connection.metricCompatible hu hX hY
  -- Torsion-freeness in bracket form: `[u,X] = ∇_u X - ∇_X u` for differentiable fields.
  have bracketX : VectorField.mlieBracket I u X x =
      connection.connection X x (u x) - connection.connection u x (X x) :=
    (connection.connection.torsion_eq_zero_iff.mp connection.torsionFree hu hX).symm
  have bracketY : VectorField.mlieBracket I u Y x =
      connection.connection Y x (u x) - connection.connection u x (Y x) :=
    (connection.connection.torsion_eq_zero_iff.mp connection.torsionFree hu hY).symm
  -- Substitute both rewrites into the flow-free formula and expand bilinearly.
  simp only [metricLieDerivativeAt]
  rw [compat, bracketX, bracketY, inner_sub_left, inner_sub_right]
  -- The second summand appears with its arguments transposed; the real metric is symmetric.
  rw [real_inner_comm (X x) (connection.connection u x (Y x))]
  -- The remaining identity is linear arithmetic in four inner products.
  ring

/-- The Lie-derivative identity in deformation-tensor form: `L_u g = 2 Def u` pointwise on
differentiable test fields, for a bundled `C^(k+1)` velocity field. -/
theorem metricLieDerivativeAt_eq_two_deformationTensor
    [Nontrivial E]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    {X Y : (y : M) → TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    metricLieDerivativeAt I field X Y x =
      2 * deformationTensor I regularity connection smooth field x (X x) (Y x) := by
  -- A `C^(k+1)` section is differentiable at every point.
  rw [metricLieDerivativeAt_leviCivita I connection
    (field.mdifferentiable' (by simp) x) hX hY, deformationTensor_apply]
  ring

end RiemannianFluids
