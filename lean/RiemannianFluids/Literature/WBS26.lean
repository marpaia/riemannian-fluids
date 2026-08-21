import RiemannianFluids.Analysis.VariationalConvergence
import RiemannianFluids.Geometry.SurfacesOfRevolution
import RiemannianFluids.Viscosity.BoundarySelection

/-!
# WBS26: wall-selected thin-shell viscosity

The convention and endpoint crosswalk is proved.  The remaining source conclusions are exposed
as proposition-valued definitions over actual varying Hilbert carriers; they are formal targets,
not theorem aliases or proofs.
-/

namespace RiemannianFluids.Literature.WBS26

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The two endpoint wall laws treated by WBS26 Theorem 4.5 and Corollary 4.6. -/
inductive WallEndpoint where
  | deformation
  | hodge
  deriving DecidableEq

/-- The zeroth, first, and quadratic coefficients in Proposition 3.2 together with the shape
operator and its square.  `quadraticCoefficient` is the coefficient of `r^2`, so the second
radial derivative at the mid-surface is twice this vector. -/
structure TwoWallProfileJet (V : Type*) [AddCommGroup V] [Module ℝ V] where
  zerothCoefficient : V
  firstCoefficient : V
  quadraticCoefficient : V
  shape : V →ₗ[ℝ] V
  shapeSquare : V →ₗ[ℝ] V

/-- The even and odd coefficient equations obtained by imposing
`partial_r U = 2 alpha S(r) U` on both symmetric walls to the two leading matched orders. -/
def MatchesTwoWallLawToSecondOrder
    (jet : TwoWallProfileJet V) (alpha : ℝ) : Prop :=
  jet.firstCoefficient = (2 * alpha) • jet.shape jet.zerothCoefficient ∧
    (2 : ℝ) • jet.quadraticCoefficient =
      (2 * alpha) •
        (jet.shapeSquare jet.zerothCoefficient + jet.shape jet.firstCoefficient)

/-- Source signature for WBS26 Proposition 3.2, including both radial Taylor coefficients. -/
def two_wall_profile_statement
    (jet : TwoWallProfileJet V) (alpha : ℝ) : Prop :=
  0 ≤ alpha → alpha ≤ 1 → MatchesTwoWallLawToSecondOrder jet alpha →
    jet.firstCoefficient = (2 * alpha) • jet.shape jet.zerothCoefficient ∧
      (2 : ℝ) • jet.quadraticCoefficient =
        (2 * alpha * (1 + 2 * alpha)) • jet.shapeSquare jet.zerothCoefficient

/-- Both endpoint form/operator packages on one source surface of revolution. -/
structure EndpointConvergenceData
    (Bulk : ℕ → Type*) (Limit : Type*)
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit] where
  surface : ClosedRevolutionProfile
  maximumRadius : ℝ
  endpoint : WallEndpoint → HilbertModeConvergenceData Bulk Limit

/-- The geometric and thin-parameter assumptions common to Theorem 4.5 and Corollary 4.6. -/
def IsWBS26ThinLimitSetting
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : EndpointConvergenceData Bulk Limit) : Prop :=
  IsSmoothClosedUnitSpeedRevolutionProfile data.surface ∧
    0 < data.maximumRadius ∧
    (∀ meridian, data.surface.radius meridian ≤ data.maximumRadius) ∧
    (∃ meridian, data.surface.radius meridian = data.maximumRadius) ∧
    ∀ endpoint,
      (∀ n, 0 < (data.endpoint endpoint).association.forms.thinScale n) ∧
        Filter.Tendsto (data.endpoint endpoint).association.forms.thinScale
          Filter.atTop (nhds 0)

/-- Source signature for WBS26 Theorem 4.5 (M1), for both endpoint form pairs. -/
def mosco_liminf_statement
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : EndpointConvergenceData Bulk Limit) : Prop :=
  IsWBS26ThinLimitSetting data → ∀ endpoint,
    HilbertMoscoFormDomainLiminf (data.endpoint endpoint).association

/-- Source signature for WBS26 Theorem 4.5 (M2), including both form domains. -/
def mosco_recovery_statement
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : EndpointConvergenceData Bulk Limit) : Prop :=
  IsWBS26ThinLimitSetting data → ∀ endpoint,
    HilbertMoscoFormDomainRecovery (data.endpoint endpoint).association

/-- Source signature for the sharp smooth-data `O(epsilon^2)` clause in Theorem 4.5. -/
def mosco_smooth_recovery_rate_statement
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : EndpointConvergenceData Bulk Limit) : Prop :=
  IsWBS26ThinLimitSetting data → ∀ endpoint,
    HilbertMoscoSmoothRecoveryRate (data.endpoint endpoint).association

/-- Source signature for the closed nonnegative self-adjoint form/operator associations at
both wall-law endpoints. -/
def form_operator_association_statement
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : EndpointConvergenceData Bulk Limit) : Prop :=
  IsWBS26ThinLimitSetting data → ∀ endpoint,
    IsHilbertFormOperatorAssociation (data.endpoint endpoint).association

/-- Source signature for strong resolvent convergence in WBS26 Corollary 4.6. -/
def strong_resolvent_convergence_statement
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : EndpointConvergenceData Bulk Limit) : Prop :=
  IsWBS26ThinLimitSetting data → ∀ endpoint,
    HilbertStrongResolventConvergence
      (data.endpoint endpoint).association.operators

/-- Source signature for compact-time-uniform strong semigroup convergence. -/
def compact_time_semigroup_convergence_statement
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : EndpointConvergenceData Bulk Limit) : Prop :=
  IsWBS26ThinLimitSetting data → ∀ endpoint,
    HilbertCompactTimeSemigroupConvergence
      (data.endpoint endpoint).association.operators

/-- Source signature for fixed-mode precompactness and eigenvalue convergence with multiplicity. -/
def fixed_mode_spectral_convergence_statement
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : EndpointConvergenceData Bulk Limit) : Prop :=
  IsWBS26ThinLimitSetting data → ∀ endpoint,
    HilbertFixedModePrecompact (data.endpoint endpoint) ∧
      HilbertModewiseSpectralConvergence
        (data.endpoint endpoint).association.operators

/-- Source signature for the uniform quadratic azimuthal-mode gap. -/
def uniform_high_mode_gap_statement
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : EndpointConvergenceData Bulk Limit) : Prop :=
  IsWBS26ThinLimitSetting data → ∀ endpoint,
    HilbertUniformHighModeGap (data.endpoint endpoint) data.maximumRadius

/-- Source signature for full spectral convergence with multiplicity and exclusion of
high-mode spectral pollution below every positive threshold. -/
def full_spectrum_convergence_no_pollution_statement
    {Bulk : ℕ → Type*} {Limit : Type*}
    [∀ n, NormedAddCommGroup (Bulk n)]
    [∀ n, InnerProductSpace ℝ (Bulk n)]
    [∀ n, CompleteSpace (Bulk n)]
    [NormedAddCommGroup Limit] [InnerProductSpace ℝ Limit] [CompleteSpace Limit]
    (data : EndpointConvergenceData Bulk Limit) : Prop :=
  IsWBS26ThinLimitSetting data → ∀ endpoint,
    HilbertFullSpectralConvergence
        (data.endpoint endpoint).association.operators ∧
      HilbertNoHighModeSpectralPollution
        (data.endpoint endpoint).association.operators

/-- Translation of the paper's signed local interpolating family to analysis-positive convention. -/
abbrev local_interpolating_family_analysisPositive
    (signedDeformation ricci shapeSquare : V →ₗ[ℝ] V) (a : ℝ) :=
  _root_.RiemannianFluids.wbs26_analysisPositive_crosswalk
    signedDeformation ricci shapeSquare a

end RiemannianFluids.Literature.WBS26
