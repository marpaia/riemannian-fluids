import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Semicontinuity.Defs

/-!
# Variational-convergence contracts

This module is deliberately independent of a particular thin-shell geometry.  It records the
observable data needed to state Mosco convergence on varying spaces and the operator-level
consequences used in WBS26.  No convergence result is stored as a field of the framework.
-/

namespace RiemannianFluids

open scoped LinearPMap

/-- A varying family of quadratic energies on actual Hilbert spaces.  Identification and lifting
maps make the varying-space comparison explicit rather than reducing it to error scalars. -/
structure HilbertQuadraticFormData
    (Bulk : ℕ → Type*) (Limit : Type*)
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit] where
  thinScale : ℕ → ℝ
  bulkEnergy : (n : ℕ) → QuadraticMap ℝ (Bulk n) ℝ
  limitEnergy : QuadraticMap ℝ Limit ℝ
  identify : (n : ℕ) → Bulk n →L[ℝ] Limit
  lift : (n : ℕ) → Limit →L[ℝ] Bulk n
  weaklyConvergesAfterIdentification : ((n : ℕ) → Bulk n) → Limit → Prop
  isSmoothLimit : Limit → Prop
  hasQuadraticRecoveryRate : ((n : ℕ) → Bulk n) → Limit → Prop

/-- Strong convergence after applying the varying-space identification maps. -/
def StronglyConvergesAfterIdentification
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertQuadraticFormData Bulk Limit)
    (sequence : (n : ℕ) → Bulk n) (limitVector : Limit) : Prop :=
  Filter.Tendsto (fun n => data.identify n (sequence n))
    Filter.atTop (nhds limitVector)

/-- Mosco lower bound, written by its eventual-lower-bound characterization so no artificial
stored `liminf` observable is needed. -/
def HilbertMoscoLiminf
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertQuadraticFormData Bulk Limit) : Prop :=
  ∀ sequence limitVector,
    data.weaklyConvergesAfterIdentification sequence limitVector →
      ∀ lowerBound, lowerBound < data.limitEnergy limitVector →
        ∀ᶠ n in Filter.atTop, lowerBound ≤ data.bulkEnergy n (sequence n)

/-- Mosco recovery on the concrete Hilbert carriers, including the source's sharp smooth-data
rate as a separate conjunct. -/
def HilbertMoscoRecovery
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertQuadraticFormData Bulk Limit) : Prop :=
  ∀ limitVector,
    ∃ sequence,
      StronglyConvergesAfterIdentification data sequence limitVector ∧
        Filter.Tendsto (fun n => data.bulkEnergy n (sequence n))
          Filter.atTop (nhds (data.limitEnergy limitVector)) ∧
        (data.isSmoothLimit limitVector →
          data.hasQuadraticRecoveryRate sequence limitVector)

/-- The explicit `O(epsilon^2)` energy estimate used for smooth WBS26 recovery sequences.
Unlike the legacy observable on `HilbertQuadraticFormData`, this definition exposes the
constant, the thin scale, and the eventual inequality. -/
def HasQuadraticEnergyRecoveryRate
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertQuadraticFormData Bulk Limit)
    (sequence : (n : ℕ) → Bulk n) (limitVector : Limit) : Prop :=
  ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ᶠ n in Filter.atTop,
      |data.bulkEnergy n (sequence n) - data.limitEnergy limitVector| ≤
        constant * data.thinScale n ^ 2

/-- Mosco convergence for the Mathlib-backed Hilbert-space formulation. -/
def HilbertMoscoConverges
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertQuadraticFormData Bulk Limit) : Prop :=
  HilbertMoscoLiminf data ∧ HilbertMoscoRecovery data

/-- Resolvents and semigroups acting on the actual bulk and limit Hilbert spaces. -/
structure HilbertOperatorConvergenceData
    (Bulk : ℕ → Type*) (Limit : Type*)
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit] where
  identify : (n : ℕ) → Bulk n →L[ℝ] Limit
  lift : (n : ℕ) → Limit →L[ℝ] Bulk n
  bulkResolvent : ℝ → (n : ℕ) → Bulk n →L[ℝ] Bulk n
  limitResolvent : ℝ → Limit →L[ℝ] Limit
  bulkSemigroup : ℝ → (n : ℕ) → Bulk n →L[ℝ] Bulk n
  limitSemigroup : ℝ → Limit →L[ℝ] Limit
  bulkEigenvalue : ℤ → ℕ → ℕ → ℝ
  limitEigenvalue : ℤ → ℕ → ℝ
  bulkFullEigenvalue : ℕ → ℕ → ℝ
  limitFullEigenvalue : ℕ → ℝ
  modeCoercivityLowerBound : ℤ → ℕ → ℝ

/-- Data connecting one varying family of closed quadratic forms to the generators,
resolvents, semigroups, and eigenvalues that it induces.  Generators are Mathlib unbounded
linear operators (`LinearPMap`), while resolvents and semigroups remain bounded continuous
linear maps. -/
structure HilbertFormOperatorAssociationData
    (Bulk : ℕ → Type*) (Limit : Type*)
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit] where
  forms : HilbertQuadraticFormData Bulk Limit
  operators : HilbertOperatorConvergenceData Bulk Limit
  bulkFormDomain : (n : ℕ) → Submodule ℝ (Bulk n)
  limitFormDomain : Submodule ℝ Limit
  bulkGenerator : (n : ℕ) → (Bulk n →ₗ.[ℝ] Bulk n)
  limitGenerator : Limit →ₗ.[ℝ] Limit
  bulkModeEigenvector : ℤ → ℕ → (n : ℕ) → Bulk n
  limitModeEigenvector : ℤ → ℕ → Limit
  bulkFullEigenvector : ℕ → (n : ℕ) → Bulk n
  limitFullEigenvector : ℕ → Limit

/-- Closedness of the extended quadratic form, expressed by closed sublevel sets on its
form domain. -/
def IsClosedNonnegativeQuadraticForm
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (form : QuadraticMap ℝ Space ℝ) (domain : Submodule ℝ Space) : Prop :=
  (∀ vector, vector ∈ domain → 0 ≤ form vector) ∧
    ∀ level : ℝ, IsClosed {vector | vector ∈ domain ∧ form vector ≤ level}

/-- The complete association contract for a varying closed-form family.  It prevents a paper
package from pairing a Mosco-convergent form with unrelated operator observables: comparison
maps agree, generators represent the polar forms, resolvents solve the generator equations,
semigroups solve their Cauchy problems, and the recorded spectral values have nonzero
eigenvectors of those same generators. -/
def IsHilbertFormOperatorAssociation
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertFormOperatorAssociationData Bulk Limit) : Prop :=
  (∀ n, data.forms.identify n = data.operators.identify n) ∧
  (∀ n, data.forms.lift n = data.operators.lift n) ∧
  (∀ n, IsClosedNonnegativeQuadraticForm
    (data.forms.bulkEnergy n) (data.bulkFormDomain n)) ∧
  IsClosedNonnegativeQuadraticForm data.forms.limitEnergy data.limitFormDomain ∧
  (∀ n, IsSelfAdjoint (data.bulkGenerator n)) ∧
  IsSelfAdjoint data.limitGenerator ∧
  (∀ n (vector : (data.bulkGenerator n).domain) test,
    (vector : Bulk n) ∈ data.bulkFormDomain n → test ∈ data.bulkFormDomain n →
      QuadraticMap.associated (data.forms.bulkEnergy n) (vector : Bulk n) test =
        inner ℝ (data.bulkGenerator n vector) test) ∧
  (∀ (vector : data.limitGenerator.domain) test,
    (vector : Limit) ∈ data.limitFormDomain → test ∈ data.limitFormDomain →
      QuadraticMap.associated data.forms.limitEnergy (vector : Limit) test =
        inner ℝ (data.limitGenerator vector) test) ∧
  (∀ spectralParameter, 0 < spectralParameter → ∀ n forcing,
    ∃ inDomain : data.operators.bulkResolvent spectralParameter n forcing ∈
        (data.bulkGenerator n).domain,
      data.bulkGenerator n
          ⟨data.operators.bulkResolvent spectralParameter n forcing, inDomain⟩ +
          spectralParameter • data.operators.bulkResolvent spectralParameter n forcing = forcing) ∧
  (∀ spectralParameter, 0 < spectralParameter → ∀ forcing,
    ∃ inDomain : data.operators.limitResolvent spectralParameter forcing ∈
        data.limitGenerator.domain,
      data.limitGenerator
          ⟨data.operators.limitResolvent spectralParameter forcing, inDomain⟩ +
          spectralParameter • data.operators.limitResolvent spectralParameter forcing = forcing) ∧
  (∀ n initial, data.operators.bulkSemigroup 0 n initial = initial) ∧
  (∀ initial, data.operators.limitSemigroup 0 initial = initial) ∧
  (∀ n time, 0 < time → ∀ initial,
    ∃ inDomain : data.operators.bulkSemigroup time n initial ∈
        (data.bulkGenerator n).domain,
      HasDerivAt (fun parameter => data.operators.bulkSemigroup parameter n initial)
        (-(data.bulkGenerator n
          ⟨data.operators.bulkSemigroup time n initial, inDomain⟩)) time) ∧
  (∀ time, 0 < time → ∀ initial,
    ∃ inDomain : data.operators.limitSemigroup time initial ∈ data.limitGenerator.domain,
      HasDerivAt (fun parameter => data.operators.limitSemigroup parameter initial)
        (-data.limitGenerator
          ⟨data.operators.limitSemigroup time initial, inDomain⟩) time) ∧
  (∀ mode eigenIndex n,
    data.bulkModeEigenvector mode eigenIndex n ≠ 0 ∧
      ∃ inDomain : data.bulkModeEigenvector mode eigenIndex n ∈
          (data.bulkGenerator n).domain,
        data.bulkGenerator n ⟨data.bulkModeEigenvector mode eigenIndex n, inDomain⟩ =
          data.operators.bulkEigenvalue mode eigenIndex n •
            data.bulkModeEigenvector mode eigenIndex n) ∧
  (∀ mode eigenIndex,
    data.limitModeEigenvector mode eigenIndex ≠ 0 ∧
      ∃ inDomain : data.limitModeEigenvector mode eigenIndex ∈ data.limitGenerator.domain,
        data.limitGenerator ⟨data.limitModeEigenvector mode eigenIndex, inDomain⟩ =
          data.operators.limitEigenvalue mode eigenIndex •
            data.limitModeEigenvector mode eigenIndex) ∧
  (∀ eigenIndex n,
    data.bulkFullEigenvector eigenIndex n ≠ 0 ∧
      ∃ inDomain : data.bulkFullEigenvector eigenIndex n ∈
          (data.bulkGenerator n).domain,
        data.bulkGenerator n ⟨data.bulkFullEigenvector eigenIndex n, inDomain⟩ =
          data.operators.bulkFullEigenvalue eigenIndex n •
            data.bulkFullEigenvector eigenIndex n) ∧
  ∀ eigenIndex,
    data.limitFullEigenvector eigenIndex ≠ 0 ∧
      ∃ inDomain : data.limitFullEigenvector eigenIndex ∈ data.limitGenerator.domain,
        data.limitGenerator ⟨data.limitFullEigenvector eigenIndex, inDomain⟩ =
          data.operators.limitFullEigenvalue eigenIndex •
            data.limitFullEigenvector eigenIndex

/-- Mosco recovery for every vector in the limit form domain, with each recovery vector in
the corresponding bulk form domain.  This exposes the domain restriction in WBS26 (M2), which
the earlier carrier-wide compatibility predicate does not record. -/
def HilbertMoscoFormDomainRecovery
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertFormOperatorAssociationData Bulk Limit) : Prop :=
  ∀ limitVector, limitVector ∈ data.limitFormDomain →
    ∃ sequence,
      (∀ n, sequence n ∈ data.bulkFormDomain n) ∧
        StronglyConvergesAfterIdentification data.forms sequence limitVector ∧
        Filter.Tendsto (fun n => data.forms.bulkEnergy n (sequence n))
          Filter.atTop (nhds (data.forms.limitEnergy limitVector))

/-- The nontrivial finite-energy part of the Mosco lower bound for densely defined forms.  A
sequence outside a bulk form domain has infinite extended energy; this definition states the
remaining lower bound on sequences whose terms lie in every bulk form domain. -/
def HilbertMoscoFormDomainLiminf
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertFormOperatorAssociationData Bulk Limit) : Prop :=
  ∀ sequence limitVector,
    (∀ n, sequence n ∈ data.bulkFormDomain n) →
    data.forms.weaklyConvergesAfterIdentification sequence limitVector →
      ∀ lowerBound, lowerBound < data.forms.limitEnergy limitVector →
        ∀ᶠ n in Filter.atTop,
          lowerBound ≤ data.forms.bulkEnergy n (sequence n)

/-- The sharp smooth-data clause of WBS26 (M2), including domain membership, strong recovery,
energy convergence, and the explicit eventual `O(epsilon^2)` estimate. -/
def HilbertMoscoSmoothRecoveryRate
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertFormOperatorAssociationData Bulk Limit) : Prop :=
  ∀ limitVector,
    limitVector ∈ data.limitFormDomain → data.forms.isSmoothLimit limitVector →
      ∃ sequence,
        (∀ n, sequence n ∈ data.bulkFormDomain n) ∧
          StronglyConvergesAfterIdentification data.forms sequence limitVector ∧
          Filter.Tendsto (fun n => data.forms.bulkEnergy n (sequence n))
            Filter.atTop (nhds (data.forms.limitEnergy limitVector)) ∧
          HasQuadraticEnergyRecoveryRate data.forms sequence limitVector

/-- Strong resolvent convergence after lifting limit data and identifying bulk solutions. -/
def HilbertStrongResolventConvergence
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertOperatorConvergenceData Bulk Limit) : Prop :=
  ∀ spectralParameter, 0 < spectralParameter → ∀ forcing : Limit,
    Filter.Tendsto
      (fun n => data.identify n
        (data.bulkResolvent spectralParameter n (data.lift n forcing)))
      Filter.atTop
      (nhds (data.limitResolvent spectralParameter forcing))

/-- Pointwise strong semigroup convergence for every nonnegative time.  The paper's stronger
compact-time uniformity is kept as a separate source node. -/
def HilbertStrongSemigroupConvergence
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertOperatorConvergenceData Bulk Limit) : Prop :=
  ∀ time, 0 ≤ time → ∀ initial : Limit,
    Filter.Tendsto
      (fun n => data.identify n (data.bulkSemigroup time n (data.lift n initial)))
      Filter.atTop
      (nhds (data.limitSemigroup time initial))

/-- Strong semigroup convergence uniformly on every compact nonnegative time interval.
This is the precise uniformity asserted by WBS26 Corollary 4.6. -/
def HilbertCompactTimeSemigroupConvergence
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertOperatorConvergenceData Bulk Limit) : Prop :=
  ∀ terminalTime, 0 ≤ terminalTime → ∀ initial : Limit, ∀ tolerance, 0 < tolerance →
    ∀ᶠ n in Filter.atTop, ∀ time ∈ Set.Icc (0 : ℝ) terminalTime,
      ‖data.identify n (data.bulkSemigroup time n (data.lift n initial)) -
          data.limitSemigroup time initial‖ < tolerance

/-- Mode subspaces used to state compactness and high-mode exclusion without storing either
conclusion as framework data.  The quadratic forms and spectral observables are the associated
objects from `HilbertFormOperatorAssociationData`. -/
structure HilbertModeConvergenceData
    (Bulk : ℕ → Type*) (Limit : Type*)
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit] where
  association : HilbertFormOperatorAssociationData Bulk Limit
  bulkMode : ℤ → (n : ℕ) → Submodule ℝ (Bulk n)
  limitMode : ℤ → Submodule ℝ Limit

/-- Precompactness of every norm-and-form-bounded sequence in one fixed azimuthal mode,
expressed by a strongly convergent subsequence after varying-space identification. -/
def HilbertFixedModePrecompact
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertModeConvergenceData Bulk Limit) : Prop :=
  ∀ (mode : ℤ) (sequence : (n : ℕ) → Bulk n),
    (∀ n, sequence n ∈ data.bulkMode mode n ∧
      sequence n ∈ data.association.bulkFormDomain n) →
    (∃ bound : ℝ, 0 ≤ bound ∧ ∀ n,
      ‖sequence n‖ ^ 2 +
          data.association.forms.bulkEnergy n (sequence n) ≤ bound) →
    ∃ subsequence : ℕ → ℕ, ∃ limitVector : Limit,
      StrictMono subsequence ∧ limitVector ∈ data.limitMode mode ∧
        Filter.Tendsto
          (fun n => data.association.forms.identify (subsequence n)
            (sequence (subsequence n))) Filter.atTop (nhds limitVector)

/-- Eigenvalues in every fixed azimuthal mode converge with their enumerated multiplicities. -/
def HilbertModewiseSpectralConvergence
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertOperatorConvergenceData Bulk Limit) : Prop :=
  ∀ mode eigenIndex,
    Filter.Tendsto (fun n => data.bulkEigenvalue mode eigenIndex n)
      Filter.atTop (nhds (data.limitEigenvalue mode eigenIndex))

/-- The WBS26 high-mode lower bound on the actual shell quadratic form. -/
def HilbertUniformHighModeGap
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertModeConvergenceData Bulk Limit) (maximumRadius : ℝ) : Prop :=
  0 < maximumRadius ∧
    ∃ c C epsilonZero : ℝ,
      0 < c ∧ 0 ≤ C ∧ 0 < epsilonZero ∧
        ∀ n, data.association.forms.thinScale n ≤ epsilonZero →
          ∀ mode vector, vector ∈ data.bulkMode mode n →
            (c * (mode : ℝ) ^ 2 / maximumRadius ^ 2 - C) * ‖vector‖ ^ 2 ≤
              data.association.forms.bulkEnergy n vector

/-- Below each positive threshold, all sufficiently thin shell spectra are confined to a
threshold-dependent finite range of azimuthal modes. -/
def HilbertNoHighModeSpectralPollution
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertOperatorConvergenceData Bulk Limit) : Prop :=
  ∀ threshold, 0 < threshold →
    ∃ maximumMode : ℕ, ∀ᶠ n in Filter.atTop, ∀ mode eigenIndex,
      maximumMode < Int.natAbs mode →
        threshold < data.bulkEigenvalue mode eigenIndex n

/-- Convergence with multiplicity of the full ordered spectra on the actual Hilbert carriers. -/
def HilbertFullSpectralConvergence
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : HilbertOperatorConvergenceData Bulk Limit) : Prop :=
  ∀ eigenIndex,
    Filter.Tendsto (fun n => data.bulkFullEigenvalue eigenIndex n)
      Filter.atTop (nhds (data.limitFullEigenvalue eigenIndex))

/-- Source-observable compatibility layer retained for paper statements not yet migrated to the
Hilbert carriers above. -/
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
