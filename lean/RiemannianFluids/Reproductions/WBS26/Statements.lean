import RiemannianFluids.Analysis.VariationalConvergence
import RiemannianFluids.ProofStatus

/-!
# WBS26 proof route

Source: Wang--Braunstein, *Boundary conditions select the viscous operator on Riemannian
hypersurfaces: formal analysis and rigorous thin-shell limits*, arXiv:2605.20589v3.

The formal identities apply to a smooth closed orientable hypersurface.  The rigorous Mosco
theorem is narrower: Theorem 4.5 treats torus-type surfaces of revolution and both wall
conditions; Corollary 4.6 gives strong resolvent and semigroup convergence and eigenvalue
convergence with multiplicity on each fixed azimuthal mode.  This module keeps those scopes
separate.
-/

namespace RiemannianFluids

/-- The two wall conditions compared by WBS26. -/
inductive WBS26WallCondition where
  | stressFree
  | vorticityFree
  deriving DecidableEq

/-- Terms in the arbitrary-hypersurface interpolating identity of equations (12)--(17). -/
structure WBS26InterpolatingData (Field : Type*) where
  isSmoothClosedOrientableHypersurface : Prop
  tangentialAmbientOperator : ℝ → Field → Field
  deformationLaplacian : Field → Field
  ricciTerm : Field → Field
  shapeSquareTerm : Field → Field
  hasFermiMetricEvolution : Prop
  hasWallReduction13 : Prop
  hasFormalCoefficientIdentities16To18 : Prop

/-- `L_a = L_Def + 2 a Ric + 4 a (1-a) S^2`. -/
def wbs26LocalInterpolatingFamilyStatement
    {Field : Type*} [AddCommGroup Field] [Module ℝ Field]
    (data : WBS26InterpolatingData Field) : Prop :=
  data.isSmoothClosedOrientableHypersurface →
  ∀ a field,
    data.tangentialAmbientOperator a field =
      data.deformationLaplacian field +
        (2 * a) • data.ricciTerm field +
        (4 * a * (1 - a)) • data.shapeSquareTerm field

/-- Observable finite-thickness profile and wall traces. -/
structure WBS26WallProfileData (SurfaceField Profile : Type*) where
  isSmoothClosedOrientableHypersurface : Prop
  profile : WBS26WallCondition → ℝ → SurfaceField → Profile
  matchesSurfaceField : Profile → SurfaceField → Prop
  isSolenoidal : Profile → Prop
  satisfiesLowerWall : WBS26WallCondition → Profile → Prop
  satisfiesUpperWall : WBS26WallCondition → Profile → Prop
  hasQuadraticNormalExpansion : WBS26WallCondition → ℝ → SurfaceField → Prop
  hasSolenoidalCorrector19 : WBS26WallCondition → ℝ → SurfaceField → Prop

/-- For either wall law, the matched profile is solenoidal, has the prescribed slow field, and satisfies that law at both walls. -/
def wbs26TwoWallProfileStatement
    {SurfaceField Profile : Type*}
    (data : WBS26WallProfileData SurfaceField Profile) : Prop :=
  data.isSmoothClosedOrientableHypersurface →
  ∀ wall thickness field,
    0 < thickness →
      let profile := data.profile wall thickness field
      data.matchesSurfaceField profile field ∧
        data.isSolenoidal profile ∧
        data.satisfiesLowerWall wall profile ∧
        data.satisfiesUpperWall wall profile

/-- All observables required by Theorem 4.5 and Corollary 4.6. -/
structure WBS26ConvergenceData (Bulk Limit : Type*) where
  isTorusTypeSurfaceOfRevolution : Prop
  forms : WBS26WallCondition → VaryingQuadraticFormData Bulk Limit
  operators : WBS26WallCondition → OperatorConvergenceData
  bulkL2Norm : Bulk → ℝ
  anisotropicH1Norm : ℕ → Bulk → ℝ
  deformationNorm : ℕ → Bulk → ℝ
  hodgeGraphNorm : ℕ → Bulk → ℝ
  /-- Slow-field observable used in the compactness identification in the proof of (M1). -/
  slowFieldOf : (ℕ → Bulk) → Limit
  /-- Tangentiality and solenoidality of the identified slow field. -/
  isTangential : Limit → Prop
  isSolenoidal : Limit → Prop
  /-- Equation (25), retained as an observable equality until concrete form operators exist. -/
  ricciShiftHolds : Limit → Prop
  /-- The matched two-wall ansatz used first on the smooth core in (M2). -/
  smoothRecoverySequence : WBS26WallCondition → Limit → ℕ → Bulk
  /-- The exact solenoidal correction from Appendix A.2. -/
  correctedRecoverySequence : WBS26WallCondition → Limit → ℕ → Bulk
  /-- The diagonal recovery sequence for a general form-domain element. -/
  diagonalRecoverySequence : WBS26WallCondition → Limit → ℕ → Bulk

/-- Uniform Korn estimate used for the stress-free form. -/
def WBS26UniformKorn
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ n field,
      c * data.anisotropicH1Norm n field ^ 2 - C * data.bulkL2Norm field ^ 2 ≤
        data.deformationNorm n field ^ 2

/-- Uniform Gaffney estimate used for the vorticity-free form. -/
def WBS26UniformGaffney
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ n field,
      c * data.anisotropicH1Norm n field ^ 2 - C * data.bulkL2Norm field ^ 2 ≤
        data.hodgeGraphNorm n field ^ 2

/-- Exact source contract for Theorem 4.5 and Corollary 4.6. -/
def wbs26MoscoResolventSpectrumStatement
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit) : Prop :=
  data.isTorusTypeSurfaceOfRevolution →
    ∀ wall,
      MoscoConverges (data.forms wall) ∧
        StrongResolventConvergence (data.operators wall) ∧
        StrongSemigroupConvergence (data.operators wall) ∧
        ModewiseSpectralConvergence (data.operators wall) ∧
        FullSpectralConvergence (data.operators wall)

/-- Exact conclusion of WBS26 Theorem 4.5. -/
def wbs26Theorem4_5Statement
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit) : Prop :=
  data.isTorusTypeSurfaceOfRevolution →
    ∀ wall, MoscoConverges (data.forms wall)

/-- Exact operator and spectral conclusions of WBS26 Corollary 4.6. -/
def wbs26Corollary4_6Statement
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit) : Prop :=
  data.isTorusTypeSurfaceOfRevolution →
    ∀ wall,
      StrongResolventConvergence (data.operators wall) ∧
        StrongSemigroupConvergence (data.operators wall) ∧
        ModewiseSpectralConvergence (data.operators wall) ∧
        FullSpectralConvergence (data.operators wall)


end RiemannianFluids
