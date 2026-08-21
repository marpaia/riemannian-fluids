import Mathlib.Analysis.ODE.Gronwall

/-!
# Exponential energy decay from a differential inequality

The decay conclusion of Wang--Braunstein Theorem 6.1 (arXiv:2605.17502v2, equations (39)--(45))
is `‖u(t)‖² ≤ e^(-2μκ²t) ‖u₀‖²` for weak solutions of the deformation-viscosity Navier--Stokes
equation on a complete surface with Gaussian curvature at most `-κ² < 0`.  In the source, that
bound follows from two analytic inputs: the energy identity `dE/dt = -2μ · D(u)` produced by
testing the equation against the solution, and the hyperbolic coercivity estimate
`D(u) = ⟨L_Def u, u⟩ ≥ κ² ‖u‖²`.

This module isolates the decay step from the existence and compactness machinery.
`energy_exponential_decay` is the Grönwall comparison: a real energy that is continuous on
`[0,T]`, right differentiable on `[0,T)`, and satisfies `E' ≤ -c E` there is bounded by
`E 0 · e^(-ct)` on `[0,T]`.  `energy_exponential_decay_of_coercive_dissipation` composes that
comparison with the energy-identity form `E' = -2μ · D` and the coercivity bound `D ≥ κ² E`, so
the source theorem's decay conclusion follows once an energy identity and the coercivity
estimate are supplied.  Both remain explicit hypotheses here: existence, uniqueness, pressure
recovery, the energy identity for weak solutions, and hyperbolic coercivity are not proved in
this repository.

The proofs specialize mathlib's `le_gronwallBound_of_liminf_deriv_right_le` with vanishing
inhomogeneity.  Neither nonnegativity of the energy nor positivity of the decay rate is needed
for the comparison itself; the composed statement uses `0 ≤ μ` exactly once, to keep the sign
of the dissipation term when the coercivity estimate is inserted.
-/

namespace RiemannianFluids

open Set

/-- Grönwall comparison for a decaying energy: a continuous energy with right derivative at
most `-c` times itself on `[0,T)` is bounded by `E 0 · e^(-ct)` on `[0,T]`. -/
theorem energy_exponential_decay
    {energy energy' : ℝ → ℝ} {c T : ℝ}
    (continuous : ContinuousOn energy (Icc 0 T))
    (derivative : ∀ t ∈ Ico 0 T, HasDerivWithinAt energy (energy' t) (Ici t) t)
    (bound : ∀ t ∈ Ico 0 T, energy' t ≤ -c * energy t) :
    ∀ t ∈ Icc 0 T, energy t ≤ energy 0 * Real.exp (-c * t) := by
  intro t ht
  -- Grönwall with rate `-c`, inhomogeneity `0`, and initial bound `E 0 ≤ E 0`.
  have gronwall := le_gronwallBound_of_liminf_deriv_right_le (f := energy) (f' := energy')
    (δ := energy 0) (K := -c) (ε := 0) continuous
    (fun s hs r hr => (derivative s hs).liminf_right_slope_le hr)
    le_rfl (fun s hs => by simpa using bound s hs) t ht
  -- With vanishing inhomogeneity the Grönwall bound is the exponential envelope.
  simpa [gronwallBound_ε0] using gronwall

/-- The Grönwall comparison for an energy differentiable on all of `[0,T]`. -/
theorem energy_exponential_decay_of_hasDerivAt
    {energy energy' : ℝ → ℝ} {c T : ℝ}
    (derivative : ∀ t ∈ Icc 0 T, HasDerivAt energy (energy' t) t)
    (bound : ∀ t ∈ Ico 0 T, energy' t ≤ -c * energy t) :
    ∀ t ∈ Icc 0 T, energy t ≤ energy 0 * Real.exp (-c * t) :=
  energy_exponential_decay
    -- Differentiability on the closed interval supplies continuity there.
    (fun t ht => (derivative t ht).continuousAt.continuousWithinAt)
    -- A two-sided derivative restricts to a right derivative.
    (fun t ht => (derivative t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    bound

/-- The decay step of the negative-curvature energy argument: an energy identity
`E' = -2μ · D` together with the coercivity estimate `D ≥ κ² E` forces the exponential decay
`E t ≤ E 0 · e^(-2μκ²t)`.

The energy identity and the coercivity estimate are the two analytic inputs of the source
argument; both appear here as explicit hypotheses. -/
theorem energy_exponential_decay_of_coercive_dissipation
    {energy dissipation : ℝ → ℝ} {μ κ T : ℝ}
    (viscosity : 0 ≤ μ)
    (continuous : ContinuousOn energy (Icc 0 T))
    (identity : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt energy (-(2 * μ) * dissipation t) (Ici t) t)
    (coercive : ∀ t ∈ Ico 0 T, κ ^ 2 * energy t ≤ dissipation t) :
    ∀ t ∈ Icc 0 T, energy t ≤ energy 0 * Real.exp (-(2 * μ * κ ^ 2) * t) := by
  refine energy_exponential_decay continuous identity fun t ht => ?_
  -- Multiplying the coercivity estimate by the nonnegative factor `2μ` and negating gives
  -- the Grönwall differential inequality with rate `2μκ²`.
  nlinarith [mul_le_mul_of_nonneg_left (coercive t ht)
    (by linarith : (0 : ℝ) ≤ 2 * μ)]

end RiemannianFluids
