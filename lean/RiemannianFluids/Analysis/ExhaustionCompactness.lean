import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exhaustion and compactness for noncompact evolution equations

WBK26 Theorem 6.1, proof Steps 2--4, uses a specific chain: compact-domain solutions,
uniform energy bounds after zero extension, global `L4` control, a fractional
time-translation estimate (47), local Rellich--Simon compactness, diagonal extraction, and
passage through the quadratic term.  The definitions below keep every gate distinct.
-/

namespace RiemannianFluids

/-- Observables for a compact-domain exhaustion argument. -/
structure ExhaustionCompactnessData
    (Point Domain Initial Approximation Limit : Type*) where
  domain : ℕ → Domain
  contains : Domain → Point → Prop
  isSmoothBoundedDomain : Domain → Prop
  initialApproximation : ℕ → Initial
  approximateSolution : ℕ → Approximation
  candidateLimit : Limit
  isCompactDomainWeakSolution : ℕ → Initial → Approximation → Prop
  initialError : ℕ → ℝ
  initialNorm : Initial → ℝ
  energySup : Approximation → ℝ
  dissipationIntegral : Approximation → ℝ
  spacetimeL4Integral : Approximation → ℝ
  timeDerivativeDualL2 : Approximation → ℝ
  timeTranslationError : Approximation → ℝ → ℝ
  locallyStronglyConverges : (ℕ → Approximation) → Limit → Prop
  weakStarEnergyConverges : (ℕ → Approximation) → Limit → Prop
  weakDissipationConverges : (ℕ → Approximation) → Limit → Prop
  nonlinearTermConverges : (ℕ → Approximation) → Limit → Prop

/-- WBK26 Step 2: smooth nested domains exhaust every point of the manifold. -/
def HasSmoothExhaustion
    {Point Domain Initial Approximation Limit : Type*}
    (data : ExhaustionCompactnessData Point Domain Initial Approximation Limit) : Prop :=
  (∀ n, data.isSmoothBoundedDomain (data.domain n)) ∧
    (∀ n point, data.contains (data.domain n) point →
      data.contains (data.domain (n + 1)) point) ∧
    ∀ point, ∃ n, data.contains (data.domain n) point

/-- WBK26 Step 2: approximating initial data converge without increasing the energy norm. -/
def HasInitialApproximation
    {Point Domain Initial Approximation Limit : Type*}
    (data : ExhaustionCompactnessData Point Domain Initial Approximation Limit)
    (initial : Initial) : Prop :=
  Filter.Tendsto data.initialError Filter.atTop (nhds 0) ∧
    ∀ n, data.initialNorm (data.initialApproximation n) ≤ data.initialNorm initial

/-- Existence of the bounded-domain Galerkin solutions used in WBK26 Step 2. -/
def HasCompactDomainSolutions
    {Point Domain Initial Approximation Limit : Type*}
    (data : ExhaustionCompactnessData Point Domain Initial Approximation Limit) : Prop :=
  ∀ n,
    data.isCompactDomainWeakSolution n
      (data.initialApproximation n) (data.approximateSolution n)

/-- Equation (46): uniform energy and integrated dissipation after zero extension. -/
def HasUniformEnergyBounds
    {Point Domain Initial Approximation Limit : Type*}
    (data : ExhaustionCompactnessData Point Domain Initial Approximation Limit)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ n,
      data.energySup (data.approximateSolution n) ≤ bound ∧
        data.dissipationIntegral (data.approximateSolution n) ≤ bound

/-- The global two-dimensional Ladyzhenskaya estimate yields a uniform spacetime `L4` bound. -/
def HasUniformSpacetimeL4Bound
    {Point Domain Initial Approximation Limit : Type*}
    (data : ExhaustionCompactnessData Point Domain Initial Approximation Limit)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ n, data.spacetimeL4Integral (data.approximateSolution n) ≤ bound

/-- WBK26 Step 3: the equation bounds the time derivative in the dual energy space. -/
def HasUniformTimeDerivativeBound
    {Point Domain Initial Approximation Limit : Type*}
    (data : ExhaustionCompactnessData Point Domain Initial Approximation Limit)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ n, data.timeDerivativeDualL2 (data.approximateSolution n) ≤ bound

/-- WBK26 equation (47): the global fractional time-translation estimate. -/
def HasFractionalTimeTranslationBound
    {Point Domain Initial Approximation Limit : Type*}
    (data : ExhaustionCompactnessData Point Domain Initial Approximation Limit)
    (constant : ℝ) : Prop :=
  0 ≤ constant ∧
    ∀ n : ℕ, ∀ h : ℝ, 0 < h →
      data.timeTranslationError (data.approximateSolution n) h ≤
        constant * Real.sqrt h

/-- The diagonal subsequence produced by local Rellich--Simon compactness. -/
def HasLocallyStrongSubsequence
    {Point Domain Initial Approximation Limit : Type*}
    (data : ExhaustionCompactnessData Point Domain Initial Approximation Limit) : Prop :=
  ∃ subsequence : ℕ → ℕ,
    StrictMono subsequence ∧
      let selected := fun n => data.approximateSolution (subsequence n)
      data.locallyStronglyConverges selected data.candidateLimit ∧
        data.weakStarEnergyConverges selected data.candidateLimit ∧
        data.weakDissipationConverges selected data.candidateLimit

/-- Strong local convergence plus the global `L4` bound passes through `u_n tensor u_n`. -/
def HasNonlinearLimitPassage
    {Point Domain Initial Approximation Limit : Type*}
    (data : ExhaustionCompactnessData Point Domain Initial Approximation Limit) : Prop :=
  ∃ subsequence : ℕ → ℕ,
    StrictMono subsequence ∧
      data.nonlinearTermConverges
        (fun n => data.approximateSolution (subsequence n))
        data.candidateLimit

end RiemannianFluids
