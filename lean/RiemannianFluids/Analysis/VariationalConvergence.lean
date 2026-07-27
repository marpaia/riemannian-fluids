import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Variational-convergence contracts

This module is deliberately independent of a particular thin-shell geometry.  It records the
observable data needed to state Mosco convergence on varying spaces and the operator-level
consequences used in WBS26.  No convergence result is stored as a field of the framework.
-/

namespace RiemannianFluids

/-- Observable data for a sequence of quadratic forms on varying spaces. -/
structure VaryingQuadraticFormData (Bulk Limit : Type*) where
  thinScale : ℕ → ℝ
  bulkEnergy : ℕ → Bulk → ℝ
  limitEnergy : Limit → ℝ
  weaklyConverges : (ℕ → Bulk) → Limit → Prop
  stronglyConverges : (ℕ → Bulk) → Limit → Prop
  liminfEnergy : (ℕ → Bulk) → ℝ
  isSmoothLimit : Limit → Prop
  hasQuadraticRecoveryRate : (ℕ → Bulk) → Limit → Prop

/-- The Mosco lower-bound condition (M1). -/
def MoscoLiminf
    {Bulk Limit : Type*} (data : VaryingQuadraticFormData Bulk Limit) : Prop :=
  ∀ sequence limit,
    data.weaklyConverges sequence limit →
      data.limitEnergy limit ≤ data.liminfEnergy sequence

/-- The recovery-sequence condition (M2), including WBS26's sharp smooth-data rate. -/
def MoscoRecovery
    {Bulk Limit : Type*} (data : VaryingQuadraticFormData Bulk Limit) : Prop :=
  ∀ limit,
    ∃ sequence,
      data.stronglyConverges sequence limit ∧
        Filter.Tendsto
          (fun n => data.bulkEnergy n (sequence n))
          Filter.atTop
          (nhds (data.limitEnergy limit)) ∧
        (data.isSmoothLimit limit → data.hasQuadraticRecoveryRate sequence limit)

/-- Mosco convergence is exactly the conjunction of (M1) and (M2). -/
def MoscoConverges
    {Bulk Limit : Type*} (data : VaryingQuadraticFormData Bulk Limit) : Prop :=
  MoscoLiminf data ∧ MoscoRecovery data

/-- Numerical observables needed to state strong resolvent, semigroup, and modewise spectral convergence. -/
structure OperatorConvergenceData where
  resolventError : ℝ → ℕ → ℝ
  semigroupError : ℝ → ℕ → ℝ
  semigroupCompactTimeSupError : ℝ → ℕ → ℝ
  bulkEigenvalue : ℤ → ℕ → ℕ → ℝ
  limitEigenvalue : ℤ → ℕ → ℝ
  bulkFullEigenvalue : ℕ → ℕ → ℝ
  limitFullEigenvalue : ℕ → ℝ
  modeCoercivityLowerBound : ℤ → ℕ → ℝ

/-- Strong resolvent convergence for every positive spectral parameter. -/
def StrongResolventConvergence (data : OperatorConvergenceData) : Prop :=
  ∀ spectralParameter : ℝ, 0 < spectralParameter →
    Filter.Tendsto (data.resolventError spectralParameter) Filter.atTop (nhds 0)

/-- Strong semigroup convergence uniformly on every compact time interval, as in WBS26 Corollary 4.6. -/
def StrongSemigroupConvergence (data : OperatorConvergenceData) : Prop :=
  ∀ terminalTime : ℝ, 0 ≤ terminalTime →
    Filter.Tendsto (data.semigroupCompactTimeSupError terminalTime) Filter.atTop (nhds 0)

/-- Eigenvalue convergence with multiplicity after restriction to one fixed azimuthal mode. -/
def ModewiseSpectralConvergence (data : OperatorConvergenceData) : Prop :=
  ∀ mode : ℤ, ∀ eigenIndex : ℕ,
    Filter.Tendsto
      (fun n => data.bulkEigenvalue mode eigenIndex n)
      Filter.atTop
      (nhds (data.limitEigenvalue mode eigenIndex))

/-- The uniform quadratic high-mode gap used to exclude spectral pollution. -/
def UniformHighModeGap (data : OperatorConvergenceData) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ (mode : ℤ) (n : ℕ),
      c * (mode : ℝ) ^ 2 - C ≤ data.modeCoercivityLowerBound mode n

/-- Convergence with multiplicity of the full ordered spectrum. -/
def FullSpectralConvergence (data : OperatorConvergenceData) : Prop :=
  ∀ eigenIndex : ℕ,
    Filter.Tendsto
      (fun n => data.bulkFullEigenvalue eigenIndex n)
      Filter.atTop
      (nhds (data.limitFullEigenvalue eigenIndex))

end RiemannianFluids
