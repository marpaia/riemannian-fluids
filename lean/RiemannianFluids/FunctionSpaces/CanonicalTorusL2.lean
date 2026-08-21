import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import RiemannianFluids.Analysis.LpMultipliers

/-!
# Concrete varying `L²` carriers on the canonical torus shell

WBS26 Theorem 4.5 compares genuinely different weighted Hilbert spaces as the shell thickness
changes.  This module realizes those spaces as Mathlib `Lp` quotients.  Surface and shell vector
fields are represented in their global orthonormal frames, so the fiber norm is Euclidean and all
geometry lives in the measure and in the coordinate/frame conversion maps.

The shell is pulled back to the fixed cylinder `T(2,1) × [-1,1]` by `sigma = epsilon * z`.
The normal interval carries normalized Lebesgue probability measure, and the shell measure is
the reference product weighted by the exact tube Jacobian.  Thus it is precisely physical volume
divided by the full thickness `2 * epsilon`.

The comparison maps are genuine bounded maps between the `Lp` quotients.  In particular, the
flux identification is defined as the Hilbert adjoint of the reciprocal-frame test lift; its
smooth representatives are the weighted coordinate averages used by the symbolic recovery
theorem.
-/

namespace RiemannianFluids
namespace CanonicalTorus

open MeasureTheory Set
open scoped ENNReal InnerProduct

noncomputable section

/-- Positivity of the period required by the additive-circle topology and Haar measure. -/
instance twoPiPositive : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- One angular coordinate with period `2*pi`. -/
abbrev Circle := AddCircle (2 * Real.pi)

/-- Global coordinate carrier of the canonical torus `T(2,1)`. -/
abbrev Point := Circle × Circle

/-- Closed rescaled normal interval.  Encoding the interval in the type makes all tube bounds
pointwise rather than merely almost everywhere. -/
def NormalPoint := Set.Icc (-1 : ℝ) 1

/-- The subtype inherits restricted Lebesgue measure. -/
noncomputable instance normalPointMeasureSpace : MeasureSpace NormalPoint :=
  Measure.Subtype.measureSpace

/-- Fixed rescaled cylinder carrying every pulled-back shell. -/
abbrev CylinderPoint := Point × NormalPoint

/-- Orthonormal-frame components of a tangential surface field. -/
abbrev SurfaceComponents := EuclideanSpace ℝ (Fin 2)

/-- Orthonormal-frame components of a three-dimensional shell field. -/
abbrev ShellComponents := EuclideanSpace ℝ (Fin 3)

/-- Coordinate components used by the exact recovery formulas. -/
abbrev SurfaceCoordinateComponents := Fin 2 → ℝ

/-- Coordinate components used by the exact shell recovery formulas. -/
abbrev ShellCoordinateComponents := Fin 3 → ℝ

/-- The half-thickness range on which the canonical tube and recovery denominators are uniformly
nondegenerate. -/
def Thickness := {epsilon : ℝ // 0 < epsilon ∧ epsilon ≤ (1 / 4 : ℝ)}

/-- Cosine of the meridional additive-circle coordinate. -/
def meridionalCos (point : Point) : ℝ :=
  Real.Angle.cos point.1

/-- Radius of the azimuthal circle in the mid-surface metric. -/
def radius (point : Point) : ℝ :=
  2 + meridionalCos point

theorem neg_one_le_meridionalCos (point : Point) :
    -1 ≤ meridionalCos point := by
  rw [meridionalCos, ← Real.Angle.cos_toReal]
  exact Real.neg_one_le_cos _

theorem meridionalCos_le_one (point : Point) :
    meridionalCos point ≤ 1 := by
  rw [meridionalCos, ← Real.Angle.cos_toReal]
  exact Real.cos_le_one _

theorem abs_meridionalCos_le_one (point : Point) :
    |meridionalCos point| ≤ 1 :=
  abs_le.2 ⟨neg_one_le_meridionalCos point, meridionalCos_le_one point⟩

theorem one_le_radius (point : Point) : 1 ≤ radius point := by
  unfold radius
  linarith [neg_one_le_meridionalCos point]

theorem radius_le_three (point : Point) : radius point ≤ 3 := by
  unfold radius
  linarith [meridionalCos_le_one point]

theorem radius_pos (point : Point) : 0 < radius point :=
  lt_of_lt_of_le zero_lt_one (one_le_radius point)

theorem abs_normal_le_one (normal : NormalPoint) : |(normal.1 : ℝ)| ≤ 1 := by
  exact abs_le.2 ⟨normal.2.1, normal.2.2⟩

theorem abs_curvatureRatio_le_one (point : Point) :
    |meridionalCos point / radius point| ≤ 1 := by
  rw [abs_div, abs_of_pos (radius_pos point)]
  exact (div_le_one (radius_pos point)).2
    ((abs_meridionalCos_le_one point).trans (one_le_radius point))

theorem abs_scaledNormal_le_quarter (epsilon : Thickness) (normal : NormalPoint) :
    |epsilon.1 * normal.1| ≤ (1 / 4 : ℝ) := by
  rw [abs_mul, abs_of_pos epsilon.2.1]
  exact (mul_le_of_le_one_right epsilon.2.1.le (abs_normal_le_one normal)).trans epsilon.2.2

theorem abs_scaledCurvatureNormal_le_quarter
    (epsilon : Thickness) (point : CylinderPoint) :
    |epsilon.1 * point.2.1 * meridionalCos point.1 / radius point.1| ≤ (1 / 4 : ℝ) := by
  rw [mul_div_assoc, abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg (epsilon.1 * point.2.1))
    (abs_curvatureRatio_le_one point.1)).trans
      (abs_scaledNormal_le_quarter epsilon point.2)

theorem firstTubeFactor_bounds (epsilon : Thickness) (point : CylinderPoint) :
    (3 / 4 : ℝ) ≤ 1 + epsilon.1 * point.2.1 ∧
      1 + epsilon.1 * point.2.1 ≤ (5 / 4 : ℝ) := by
  have h := abs_le.1 (abs_scaledNormal_le_quarter epsilon point.2)
  constructor <;> linarith

theorem secondTubeFactor_bounds (epsilon : Thickness) (point : CylinderPoint) :
    (3 / 4 : ℝ) ≤
        1 + epsilon.1 * point.2.1 * meridionalCos point.1 / radius point.1 ∧
      1 + epsilon.1 * point.2.1 * meridionalCos point.1 / radius point.1 ≤
        (5 / 4 : ℝ) := by
  have h := abs_le.1 (abs_scaledCurvatureNormal_le_quarter epsilon point)
  constructor <;> linarith

/-- Exact Jacobian `det(Id - sigma*S)` after `sigma = epsilon*z`. -/
def jacobian (epsilon : ℝ) (point : CylinderPoint) : ℝ :=
  let thetaCos := meridionalCos point.1
  let rho := radius point.1
  (1 + epsilon * point.2.1) * (1 + epsilon * point.2.1 * thetaCos / rho)

theorem jacobian_lower_bound (epsilon : Thickness) (point : CylinderPoint) :
    (9 / 16 : ℝ) ≤ jacobian epsilon.1 point := by
  rw [jacobian]
  calc
    (9 / 16 : ℝ) = (3 / 4 : ℝ) * (3 / 4 : ℝ) := by norm_num
    _ ≤ (1 + epsilon.1 * point.2.1) *
        (1 + epsilon.1 * point.2.1 * meridionalCos point.1 / radius point.1) :=
      mul_le_mul (firstTubeFactor_bounds epsilon point).1
        (secondTubeFactor_bounds epsilon point).1 (by norm_num)
        (by linarith [firstTubeFactor_bounds epsilon point])

theorem jacobian_upper_bound (epsilon : Thickness) (point : CylinderPoint) :
    jacobian epsilon.1 point ≤ (25 / 16 : ℝ) := by
  rw [jacobian]
  calc
    (1 + epsilon.1 * point.2.1) *
        (1 + epsilon.1 * point.2.1 * meridionalCos point.1 / radius point.1) ≤
        (5 / 4 : ℝ) * (5 / 4 : ℝ) :=
      mul_le_mul (firstTubeFactor_bounds epsilon point).2
        (secondTubeFactor_bounds epsilon point).2
        (by linarith [secondTubeFactor_bounds epsilon point]) (by norm_num)
    _ = (25 / 16 : ℝ) := by norm_num

theorem jacobian_pos (epsilon : Thickness) (point : CylinderPoint) :
    0 < jacobian epsilon.1 point :=
  lt_of_lt_of_le (by norm_num) (jacobian_lower_bound epsilon point)

/-- The canonical torus area measure `rho(theta) dtheta dphi`. -/
def surfaceMeasure : Measure Point :=
  (volume : Measure Point).withDensity fun point ↦ ENNReal.ofReal (radius point)

/-- Lebesgue probability measure on `[-1,1]`. -/
def normalMeasure : Measure NormalPoint :=
  (2 : ℝ≥0∞)⁻¹ • (volume : Measure NormalPoint)

theorem normalMeasure_univ : normalMeasure Set.univ = 1 := by
  have hvolume : (volume : Measure NormalPoint) Set.univ =
      (volume : Measure ℝ) (Set.Icc (-1 : ℝ) 1) :=
    Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet
  rw [normalMeasure, Measure.smul_apply, hvolume, Real.volume_Icc]
  norm_num only [sub_neg_eq_add, one_add_one_eq_two, ENNReal.ofReal_ofNat, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance normalMeasureProbability : IsProbabilityMeasure normalMeasure :=
  ⟨normalMeasure_univ⟩

/-- Probability-fiber product reference measure on the fixed cylinder. -/
def cylinderReferenceMeasure : Measure CylinderPoint :=
  surfaceMeasure.prod normalMeasure

/-- Normalized physical shell volume on the rescaled cylinder. -/
def shellMeasure (epsilon : Thickness) : Measure CylinderPoint :=
  cylinderReferenceMeasure.withDensity fun point ↦
    ENNReal.ofReal (jacobian epsilon.1 point)

/-- The physical shell measure is uniformly dominated by the reference cylinder measure. -/
theorem shellMeasure_le_reference (epsilon : Thickness) :
    shellMeasure epsilon ≤ (ENNReal.ofReal (25 / 16 : ℝ)) • cylinderReferenceMeasure := by
  rw [shellMeasure, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [] with point
  exact ENNReal.ofReal_le_ofReal (jacobian_upper_bound epsilon point)

/-- A fixed half of the reference measure is dominated by every admissible physical shell
measure.  Together with `shellMeasure_le_reference`, this is the uniform norm-equivalence input
for compactness on the fixed cylinder. -/
theorem half_reference_le_shellMeasure (epsilon : Thickness) :
    (2 : ℝ≥0∞)⁻¹ • cylinderReferenceMeasure ≤ shellMeasure epsilon := by
  rw [shellMeasure, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [] with point
  calc
    (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 : ℝ)⁻¹) := by
      simpa using (ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)).symm
    _ ≤ ENNReal.ofReal (jacobian epsilon.1 point) :=
      ENNReal.ofReal_le_ofReal (by
        nlinarith [jacobian_lower_bound epsilon point])

/-- The reference measure is uniformly dominated by twice every admissible shell measure. -/
theorem reference_le_two_shellMeasure (epsilon : Thickness) :
    cylinderReferenceMeasure ≤ (2 : ℝ≥0∞) • shellMeasure epsilon := by
  calc
    cylinderReferenceMeasure =
        (2 : ℝ≥0∞) • ((2 : ℝ≥0∞)⁻¹ • cylinderReferenceMeasure) := by
      rw [smul_smul]
      nth_rw 1 [← one_smul ℝ≥0∞ cylinderReferenceMeasure]
      congr 1
      exact (ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).symm
    _ ≤ (2 : ℝ≥0∞) • shellMeasure epsilon := by
      gcongr
      exact half_reference_le_shellMeasure epsilon

/-- Actual surface `L²(TT)` Hilbert carrier in the global orthonormal frame. -/
abbrev SurfaceL2 :=
  Lp SurfaceComponents 2 surfaceMeasure

/-- Actual normalized weighted shell `L²` Hilbert carrier at one admissible half-thickness. -/
abbrev ShellL2 (epsilon : Thickness) :=
  Lp ShellComponents 2 (shellMeasure epsilon)

/-- The surface carrier is complete by the concrete Mathlib `Lp` instance. -/
theorem surfaceL2_complete : IsComplete (Set.univ : Set SurfaceL2) :=
  complete_univ

/-- Every member of the genuinely varying shell family is a complete Hilbert space. -/
theorem shellL2_complete (epsilon : Thickness) :
    IsComplete (Set.univ : Set (ShellL2 epsilon)) :=
  complete_univ

/-- Surface-frame fields on the unweighted fixed reference cylinder. -/
abbrev ReferenceSurfaceL2 :=
  Lp SurfaceComponents 2 cylinderReferenceMeasure

/-- Three-component fields on the unweighted fixed reference cylinder. -/
abbrev ReferenceShellL2 :=
  Lp ShellComponents 2 cylinderReferenceMeasure

/-- Projection from the probability-fiber cylinder preserves the surface measure. -/
theorem cylinderProjectionMeasurePreserving :
    MeasurePreserving Prod.fst cylinderReferenceMeasure surfaceMeasure :=
  measurePreserving_fst

/-- Linear pullback of a surface field to a field constant along the normalized normal fiber. -/
def surfacePullbackLinear : SurfaceL2 →ₗ[ℝ] ReferenceSurfaceL2 where
  toFun field :=
    Lp.compMeasurePreserving Prod.fst cylinderProjectionMeasurePreserving field
  map_add' := by
    intro left right
    exact (Lp.compMeasurePreserving Prod.fst cylinderProjectionMeasurePreserving).map_add
      left right
  map_smul' := by
    intro scalar field
    apply Lp.ext
    have hsurface := cylinderProjectionMeasurePreserving.quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_smul scalar field)
    filter_upwards [Lp.coeFn_compMeasurePreserving (scalar • field)
        cylinderProjectionMeasurePreserving,
        Lp.coeFn_compMeasurePreserving field cylinderProjectionMeasurePreserving,
        hsurface,
        Lp.coeFn_smul scalar
          (Lp.compMeasurePreserving Prod.fst cylinderProjectionMeasurePreserving field)] with
        point hleft hfield hsurface hright
    rw [hleft]
    simp only [RingHom.id_apply]
    rw [hright, hsurface, Pi.smul_apply, hfield]
    rfl

/-- Isometric surface pullback to the probability-fiber reference cylinder. -/
def surfacePullback : SurfaceL2 →L[ℝ] ReferenceSurfaceL2 :=
  LinearMap.mkContinuous surfacePullbackLinear 1 (fun field ↦ by
    change ‖Lp.compMeasurePreserving Prod.fst cylinderProjectionMeasurePreserving field‖ ≤
      1 * ‖field‖
    simpa using
      (Lp.norm_compMeasurePreserving field cylinderProjectionMeasurePreserving).le)

/-- The isometric pullback is represented by composition with the cylinder projection. -/
theorem surfacePullback_ae (field : SurfaceL2) :
    surfacePullback field =ᵐ[cylinderReferenceMeasure]
      (field : Point → SurfaceComponents) ∘ Prod.fst := by
  simpa [surfacePullback, surfacePullbackLinear] using
    (Lp.coeFn_compMeasurePreserving field cylinderProjectionMeasurePreserving)

theorem norm_surfacePullback_le_one : ‖surfacePullback‖ ≤ 1 := by
  apply surfacePullback.opNorm_le_bound zero_le_one
  intro field
  change ‖Lp.compMeasurePreserving Prod.fst cylinderProjectionMeasurePreserving field‖ ≤
    1 * ‖field‖
  simpa using
    (Lp.norm_compMeasurePreserving field cylinderProjectionMeasurePreserving).le

/-- Canonical identity-on-representatives inclusion from reference-cylinder `L²` to physical
shell `L²`.  Uniform Jacobian control supplies boundedness. -/
def referenceToShell (epsilon : Thickness) :
    ReferenceShellL2 →L[ℝ] ShellL2 epsilon :=
  Lp.LpToLpOfMeasureLeSMul (by simp) (shellMeasure_le_reference epsilon)

/-- Canonical identity-on-representatives pullback from one physical shell carrier to the fixed
reference cylinder.  The bound is uniform in thickness. -/
def shellToReference (epsilon : Thickness) :
    ShellL2 epsilon →L[ℝ] ReferenceShellL2 :=
  Lp.LpToLpOfMeasureLeSMul (by simp) (reference_le_two_shellMeasure epsilon)

theorem referenceToShell_ae (epsilon : Thickness) (field : ReferenceShellL2) :
    referenceToShell epsilon field =ᵐ[shellMeasure epsilon] field :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
    (shellMeasure_le_reference epsilon) field

theorem shellToReference_ae (epsilon : Thickness) (field : ShellL2 epsilon) :
    shellToReference epsilon field =ᵐ[cylinderReferenceMeasure] field :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
    (reference_le_two_shellMeasure epsilon) field

/-- The reference-to-physical identity maps have one thickness-independent operator bound. -/
theorem norm_referenceToShell_le_two (epsilon : Thickness) :
    ‖referenceToShell epsilon‖ ≤ 2 := by
  unfold referenceToShell
  calc
    ‖(Lp.LpToLpOfMeasureLeSMul (by simp) (shellMeasure_le_reference epsilon) :
        ReferenceShellL2 →L[ℝ] ShellL2 epsilon)‖ ≤
        (ENNReal.ofReal (25 / 16 : ℝ)).toReal ^
          (1 / (2 : ℝ≥0∞)).toReal :=
      Lp.norm_LpToLpOfMeasureLeSMul_le _ _
    _ ≤ 2 := by norm_num

/-- Insert the first tangential component into a three-component shell frame. -/
def firstTangentialEmbedding : SurfaceComponents →L[ℝ] ShellComponents :=
  (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single (0 : Fin 3) 1)) ∘L
    EuclideanSpace.proj (0 : Fin 2)

/-- Insert the second tangential component into a three-component shell frame. -/
def secondTangentialEmbedding : SurfaceComponents →L[ℝ] ShellComponents :=
  (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single (1 : Fin 3) 1)) ∘L
    EuclideanSpace.proj (1 : Fin 2)

theorem surfaceComponent_norm_le (field : SurfaceComponents) (index : Fin 2) :
    ‖field index‖ ≤ ‖field‖ := by
  have h := norm_inner_le_norm (𝕜 := ℝ)
    (EuclideanSpace.single index (1 : ℝ)) field
  simpa [EuclideanSpace.inner_single_left, PiLp.norm_single] using h

theorem firstTangentialEmbedding_apply (field : SurfaceComponents) :
    firstTangentialEmbedding field =
      EuclideanSpace.single (0 : Fin 3) (field 0) := by
  ext index
  fin_cases index <;> simp [firstTangentialEmbedding]

theorem secondTangentialEmbedding_apply (field : SurfaceComponents) :
    secondTangentialEmbedding field =
      EuclideanSpace.single (1 : Fin 3) (field 1) := by
  ext index
  fin_cases index <;> simp [secondTangentialEmbedding]

theorem firstTangentialEmbedding_norm_le : ‖firstTangentialEmbedding‖ ≤ 1 := by
  apply firstTangentialEmbedding.opNorm_le_bound zero_le_one
  intro field
  rw [firstTangentialEmbedding_apply, PiLp.norm_single]
  simpa using surfaceComponent_norm_le field 0

theorem secondTangentialEmbedding_norm_le : ‖secondTangentialEmbedding‖ ≤ 1 := by
  apply secondTangentialEmbedding.opNorm_le_bound zero_le_one
  intro field
  rw [secondTangentialEmbedding_apply, PiLp.norm_single]
  simpa using surfaceComponent_norm_le field 1

/-- Diagonal tangential frame conversion with zero normal component. -/
def tangentialFiberMap (first second : ℝ) :
    SurfaceComponents →L[ℝ] ShellComponents :=
  first • firstTangentialEmbedding + second • secondTangentialEmbedding

theorem tangentialFiberMap_norm_le_four
    (first second : ℝ) (hfirst : |first| ≤ 2) (hsecond : |second| ≤ 2) :
    ‖tangentialFiberMap first second‖ ≤ 4 := by
  calc
    ‖tangentialFiberMap first second‖ ≤
        ‖first • firstTangentialEmbedding‖ +
          ‖second • secondTangentialEmbedding‖ :=
      norm_add_le _ _
    _ = |first| * ‖firstTangentialEmbedding‖ +
        |second| * ‖secondTangentialEmbedding‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ 2 * 1 + 2 * 1 := by
      gcongr
      · exact firstTangentialEmbedding_norm_le
      · exact secondTangentialEmbedding_norm_le
    _ = 4 := by norm_num

/-- Coordinate-constant lift expressed in physical orthonormal shell frames. -/
def firstFrameScale (epsilon : Thickness) (point : CylinderPoint) : ℝ :=
  1 + epsilon.1 * point.2.1

/-- Azimuthal coordinate-constant scale in physical orthonormal shell frames. -/
def secondFrameScale (epsilon : Thickness) (point : CylinderPoint) : ℝ :=
  1 + epsilon.1 * point.2.1 * meridionalCos point.1 / radius point.1

/-- Reciprocal meridional scale entering the adjoint representation of flux averaging. -/
def firstReciprocalScale (epsilon : Thickness) (point : CylinderPoint) : ℝ :=
  (firstFrameScale epsilon point)⁻¹

/-- Reciprocal azimuthal scale entering the adjoint representation of flux averaging. -/
def secondReciprocalScale (epsilon : Thickness) (point : CylinderPoint) : ℝ :=
  (secondFrameScale epsilon point)⁻¹

theorem firstFrameScale_abs_le_two (epsilon : Thickness) (point : CylinderPoint) :
    |firstFrameScale epsilon point| ≤ 2 := by
  have hbounds : (3 / 4 : ℝ) ≤ firstFrameScale epsilon point ∧
      firstFrameScale epsilon point ≤ (5 / 4 : ℝ) := by
    simpa [firstFrameScale] using firstTubeFactor_bounds epsilon point
  rw [abs_of_pos (by linarith [hbounds.1])]
  linarith [hbounds.2]

theorem secondFrameScale_abs_le_two (epsilon : Thickness) (point : CylinderPoint) :
    |secondFrameScale epsilon point| ≤ 2 := by
  have hbounds : (3 / 4 : ℝ) ≤ secondFrameScale epsilon point ∧
      secondFrameScale epsilon point ≤ (5 / 4 : ℝ) := by
    simpa [secondFrameScale] using secondTubeFactor_bounds epsilon point
  rw [abs_of_pos (by linarith [hbounds.1])]
  linarith [hbounds.2]

theorem firstReciprocalScale_abs_le_two (epsilon : Thickness) (point : CylinderPoint) :
    |firstReciprocalScale epsilon point| ≤ 2 := by
  have hbounds : (3 / 4 : ℝ) ≤ firstFrameScale epsilon point := by
    simpa [firstFrameScale] using (firstTubeFactor_bounds epsilon point).1
  have hpos : 0 < firstFrameScale epsilon point := by linarith
  rw [firstReciprocalScale, abs_inv, abs_of_pos hpos]
  exact (inv_le_iff_one_le_mul₀' hpos).2 (by nlinarith)

theorem secondReciprocalScale_abs_le_two (epsilon : Thickness) (point : CylinderPoint) :
    |secondReciprocalScale epsilon point| ≤ 2 := by
  have hbounds : (3 / 4 : ℝ) ≤ secondFrameScale epsilon point := by
    simpa [secondFrameScale] using (secondTubeFactor_bounds epsilon point).1
  have hpos : 0 < secondFrameScale epsilon point := by linarith
  rw [secondReciprocalScale, abs_inv, abs_of_pos hpos]
  exact (inv_le_iff_one_le_mul₀' hpos).2 (by nlinarith)

theorem continuous_meridionalCos : Continuous meridionalCos :=
  Real.Angle.continuous_cos.comp continuous_fst

theorem continuous_radius : Continuous radius :=
  continuous_const.add continuous_meridionalCos

theorem continuous_firstFrameScale (epsilon : Thickness) :
    Continuous (firstFrameScale epsilon) := by
  unfold firstFrameScale
  fun_prop

theorem continuous_secondFrameScale (epsilon : Thickness) :
    Continuous (secondFrameScale epsilon) := by
  unfold secondFrameScale
  have hnormal : Continuous (fun point : CylinderPoint ↦ (point.2.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hcos : Continuous (fun point : CylinderPoint ↦ meridionalCos point.1) :=
    continuous_meridionalCos.comp continuous_fst
  have hradius : Continuous (fun point : CylinderPoint ↦ radius point.1) :=
    continuous_radius.comp continuous_fst
  exact continuous_const.add
    (((continuous_const.mul hnormal).mul hcos).div hradius
      (fun point ↦ (radius_pos point.1).ne'))

theorem continuous_firstReciprocalScale (epsilon : Thickness) :
    Continuous (firstReciprocalScale epsilon) := by
  unfold firstReciprocalScale
  exact (continuous_firstFrameScale epsilon).inv₀
    (fun point ↦ (by
      have h : (3 / 4 : ℝ) ≤ firstFrameScale epsilon point := by
        simpa [firstFrameScale] using (firstTubeFactor_bounds epsilon point).1
      linarith : firstFrameScale epsilon point ≠ 0))

theorem continuous_secondReciprocalScale (epsilon : Thickness) :
    Continuous (secondReciprocalScale epsilon) := by
  unfold secondReciprocalScale
  exact (continuous_secondFrameScale epsilon).inv₀
    (fun point ↦ (by
      have h : (3 / 4 : ℝ) ≤ secondFrameScale epsilon point := by
        simpa [secondFrameScale] using (secondTubeFactor_bounds epsilon point).1
      linarith : secondFrameScale epsilon point ≠ 0))

/-- Bounded coordinate-constant frame lift on the reference cylinder. -/
def constantFramePointwise (epsilon : Thickness) :
    BoundedPointwiseLinearMap CylinderPoint SurfaceComponents ShellComponents
      cylinderReferenceMeasure where
  toFun point := tangentialFiberMap
    (firstFrameScale epsilon point) (secondFrameScale epsilon point)
  bound := 4
  bound_nonneg := by norm_num
  stronglyMeasurable := by
    apply Continuous.aestronglyMeasurable
    exact ((continuous_firstFrameScale epsilon).smul continuous_const).add
      ((continuous_secondFrameScale epsilon).smul continuous_const)
  norm_le := by
    filter_upwards [] with point
    exact tangentialFiberMap_norm_le_four _ _
      (firstFrameScale_abs_le_two epsilon point)
      (secondFrameScale_abs_le_two epsilon point)

/-- Bounded reciprocal-frame lift whose Hilbert adjoint is the coordinate-flux average. -/
def reciprocalFramePointwise (epsilon : Thickness) :
    BoundedPointwiseLinearMap CylinderPoint SurfaceComponents ShellComponents
      cylinderReferenceMeasure where
  toFun point := tangentialFiberMap
    (firstReciprocalScale epsilon point) (secondReciprocalScale epsilon point)
  bound := 4
  bound_nonneg := by norm_num
  stronglyMeasurable := by
    apply Continuous.aestronglyMeasurable
    exact ((continuous_firstReciprocalScale epsilon).smul continuous_const).add
      ((continuous_secondReciprocalScale epsilon).smul continuous_const)
  norm_le := by
    filter_upwards [] with point
    exact tangentialFiberMap_norm_le_four _ _
      (firstReciprocalScale_abs_le_two epsilon point)
      (secondReciprocalScale_abs_le_two epsilon point)

def constantFrameLiftReference (epsilon : Thickness) :
    SurfaceL2 →L[ℝ] ReferenceShellL2 :=
  ((constantFramePointwise epsilon).toContinuousLinearMap :
      ReferenceSurfaceL2 →L[ℝ] ReferenceShellL2) ∘L surfacePullback

def reciprocalFrameLiftReference (epsilon : Thickness) :
    SurfaceL2 →L[ℝ] ReferenceShellL2 :=
  ((reciprocalFramePointwise epsilon).toContinuousLinearMap :
      ReferenceSurfaceL2 →L[ℝ] ReferenceShellL2) ∘L surfacePullback

/-- Representatives of the coordinate-constant reference lift are the expected physical-frame
conversion of a surface field, point by point on the fixed cylinder. -/
theorem constantFrameLiftReference_ae (epsilon : Thickness) (field : SurfaceL2) :
    constantFrameLiftReference epsilon field =ᵐ[cylinderReferenceMeasure]
      fun point ↦ (constantFramePointwise epsilon).toFun point (field point.1) := by
  filter_upwards [
      (constantFramePointwise epsilon).coeFn_apply (surfacePullback field),
      surfacePullback_ae field] with point happly hpullback
  rw [show constantFrameLiftReference epsilon field =
      (constantFramePointwise epsilon).apply (surfacePullback field) from rfl,
    happly, hpullback]
  rfl

/-- Representatives of the reciprocal test lift are the expected inverse-frame conversion.
This identity is the quotient-level bridge to the weighted coordinate-flux average. -/
theorem reciprocalFrameLiftReference_ae (epsilon : Thickness) (field : SurfaceL2) :
    reciprocalFrameLiftReference epsilon field =ᵐ[cylinderReferenceMeasure]
      fun point ↦ (reciprocalFramePointwise epsilon).toFun point (field point.1) := by
  filter_upwards [
      (reciprocalFramePointwise epsilon).coeFn_apply (surfacePullback field),
      surfacePullback_ae field] with point happly hpullback
  rw [show reciprocalFrameLiftReference epsilon field =
      (reciprocalFramePointwise epsilon).apply (surfacePullback field) from rfl,
    happly, hpullback]
  rfl

theorem norm_constantFrameLiftReference_le_four (epsilon : Thickness) :
    ‖constantFrameLiftReference epsilon‖ ≤ 4 := by
  calc
    ‖constantFrameLiftReference epsilon‖ ≤
        ‖(constantFramePointwise epsilon).toContinuousLinearMap‖ * ‖surfacePullback‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 4 * 1 := by
      gcongr
      · exact (constantFramePointwise epsilon).norm_toContinuousLinearMap_le
      · exact norm_surfacePullback_le_one
    _ = 4 := by norm_num

theorem norm_reciprocalFrameLiftReference_le_four (epsilon : Thickness) :
    ‖reciprocalFrameLiftReference epsilon‖ ≤ 4 := by
  calc
    ‖reciprocalFrameLiftReference epsilon‖ ≤
        ‖(reciprocalFramePointwise epsilon).toContinuousLinearMap‖ * ‖surfacePullback‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 4 * 1 := by
      gcongr
      · exact (reciprocalFramePointwise epsilon).norm_toContinuousLinearMap_le
      · exact norm_surfacePullback_le_one
    _ = 4 := by norm_num

/-- Actual bounded coordinate-constant lift from the surface carrier to one shell carrier. -/
def constantCoordinateLiftL2 (epsilon : Thickness) :
    SurfaceL2 →L[ℝ] ShellL2 epsilon :=
  referenceToShell epsilon ∘L constantFrameLiftReference epsilon

/-- Reciprocal-frame test lift used to realize the coordinate-flux average by duality. -/
def fluxTestLiftL2 (epsilon : Thickness) :
    SurfaceL2 →L[ℝ] ShellL2 epsilon :=
  referenceToShell epsilon ∘L reciprocalFrameLiftReference epsilon

/-- The actual shell lift is represented by the coordinate-constant field in physical
orthonormal components. -/
theorem constantCoordinateLiftL2_ae (epsilon : Thickness) (field : SurfaceL2) :
    constantCoordinateLiftL2 epsilon field =ᵐ[shellMeasure epsilon]
      fun point ↦ (constantFramePointwise epsilon).toFun point (field point.1) := by
  have href := (Measure.absolutelyContinuous_of_le_smul
    (shellMeasure_le_reference epsilon)).ae_eq
      (constantFrameLiftReference_ae epsilon field)
  filter_upwards [referenceToShell_ae epsilon (constantFrameLiftReference epsilon field),
      href] with point hphysical hreference
  rw [show constantCoordinateLiftL2 epsilon field =
      referenceToShell epsilon (constantFrameLiftReference epsilon field) from rfl,
    hphysical, hreference]

/-- The actual shell test lift is represented by reciprocal frame scaling.  Pairing against
this representative with the weighted shell measure produces the normalized coordinate-flux
average characterized by `inner_fluxIdentifyL2_left`. -/
theorem fluxTestLiftL2_ae (epsilon : Thickness) (field : SurfaceL2) :
    fluxTestLiftL2 epsilon field =ᵐ[shellMeasure epsilon]
      fun point ↦ (reciprocalFramePointwise epsilon).toFun point (field point.1) := by
  have href := (Measure.absolutelyContinuous_of_le_smul
    (shellMeasure_le_reference epsilon)).ae_eq
      (reciprocalFrameLiftReference_ae epsilon field)
  filter_upwards [referenceToShell_ae epsilon (reciprocalFrameLiftReference epsilon field),
      href] with point hphysical hreference
  rw [show fluxTestLiftL2 epsilon field =
      referenceToShell epsilon (reciprocalFrameLiftReference epsilon field) from rfl,
    hphysical, hreference]

/-- Bounded normalized coordinate-flux identification on the actual weighted `L²` quotient. -/
def fluxIdentifyL2 (epsilon : Thickness) :
    ShellL2 epsilon →L[ℝ] SurfaceL2 :=
  (fluxTestLiftL2 epsilon)†

/-- Characterizing duality identity for the bounded flux identification. -/
theorem inner_fluxIdentifyL2_left (epsilon : Thickness)
    (field : ShellL2 epsilon) (test : SurfaceL2) :
    inner ℝ (fluxIdentifyL2 epsilon field) test =
      inner ℝ field (fluxTestLiftL2 epsilon test) :=
  ContinuousLinearMap.adjoint_inner_left (fluxTestLiftL2 epsilon) test field

/-- Integral form of the identification duality.  The inverse frame factors cancel the physical
parallel-surface frame factors, while `shellMeasure` contributes the tube Jacobian; this is
exactly the weighted coordinate-flux map used by the smooth recovery construction. -/
theorem inner_fluxIdentifyL2_integral (epsilon : Thickness)
    (field : ShellL2 epsilon) (test : SurfaceL2) :
    inner ℝ (fluxIdentifyL2 epsilon field) test =
      ∫ point, inner ℝ (field point)
        ((reciprocalFramePointwise epsilon).toFun point (test point.1))
        ∂shellMeasure epsilon := by
  rw [inner_fluxIdentifyL2_left, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fluxTestLiftL2_ae epsilon test] with point htest
  rw [htest]

theorem norm_fluxIdentifyL2_eq_norm_fluxTestLiftL2 (epsilon : Thickness) :
    ‖fluxIdentifyL2 epsilon‖ = ‖fluxTestLiftL2 epsilon‖ :=
  ContinuousLinearMap.adjoint.norm_map _

/-- The coordinate lifts are uniformly bounded along the whole admissible shell family. -/
theorem norm_constantCoordinateLiftL2_le_eight (epsilon : Thickness) :
    ‖constantCoordinateLiftL2 epsilon‖ ≤ 8 := by
  calc
    ‖constantCoordinateLiftL2 epsilon‖ ≤
        ‖referenceToShell epsilon‖ * ‖constantFrameLiftReference epsilon‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * 4 := by
      gcongr
      · exact norm_referenceToShell_le_two epsilon
      · exact norm_constantFrameLiftReference_le_four epsilon
    _ = 8 := by norm_num

/-- The reciprocal test lifts, and hence their flux-identification adjoints, are uniformly
bounded along the whole admissible shell family. -/
theorem norm_fluxTestLiftL2_le_eight (epsilon : Thickness) :
    ‖fluxTestLiftL2 epsilon‖ ≤ 8 := by
  calc
    ‖fluxTestLiftL2 epsilon‖ ≤
        ‖referenceToShell epsilon‖ * ‖reciprocalFrameLiftReference epsilon‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * 4 := by
      gcongr
      · exact norm_referenceToShell_le_two epsilon
      · exact norm_reciprocalFrameLiftReference_le_four epsilon
    _ = 8 := by norm_num

theorem norm_fluxIdentifyL2_le_eight (epsilon : Thickness) :
    ‖fluxIdentifyL2 epsilon‖ ≤ 8 := by
  rw [norm_fluxIdentifyL2_eq_norm_fluxTestLiftL2]
  exact norm_fluxTestLiftL2_le_eight epsilon

/-- A concrete vanishing half-thickness sequence for the varying-space Mosco formulation. -/
def thicknessAt (n : ℕ) : Thickness :=
  ⟨1 / (4 * ((n : ℝ) + 1)), by
    constructor
    · positivity
    · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      exact (div_le_iff₀' (by positivity : (0 : ℝ) < 4 * ((n : ℝ) + 1))).2 (by
        nlinarith)⟩

/-- The genuinely varying weighted shell Hilbert family sampled along `thicknessAt`. -/
abbrev ShellFamily (n : ℕ) := ShellL2 (thicknessAt n)

/-- Identification maps for the concrete varying shell family. -/
def identifyAt (n : ℕ) : ShellFamily n →L[ℝ] SurfaceL2 :=
  fluxIdentifyL2 (thicknessAt n)

/-- Coordinate-constant lifts for the concrete varying shell family. -/
def liftAt (n : ℕ) : SurfaceL2 →L[ℝ] ShellFamily n :=
  constantCoordinateLiftL2 (thicknessAt n)

theorem thicknessAt_tendsto_zero :
    Filter.Tendsto (fun n ↦ (thicknessAt n).1) Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun n : ℕ ↦ 1 / (4 * ((n : ℝ) + 1)))
    Filter.atTop (nhds 0)
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹))
      Filter.atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((Filter.tendsto_add_atTop_iff_nat 1).2
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  simpa only [one_div, mul_inv_rev, mul_zero, zero_mul] using
    (hinv.mul_const (4 : ℝ)⁻¹)

/-- Convert surface coordinate components into the orthonormal frame used by `SurfaceL2`. -/
def surfaceCoordinateToFrame
    (point : Point) (field : SurfaceCoordinateComponents) : SurfaceComponents :=
  !₂[field 0, radius point * field 1]

/-- Convert physical-shell coordinate components into the orthonormal parallel-surface frame. -/
def shellCoordinateToFrame
    (epsilon : ℝ) (point : CylinderPoint)
    (field : ShellCoordinateComponents) : ShellComponents :=
  let thetaCos := meridionalCos point.1
  !₂[(1 + epsilon * point.2.1) * field 0,
    (radius point.1 + epsilon * point.2.1 * thetaCos) * field 1,
    field 2]

/-- The coordinate-constant tangential lift used as the strong-convergence reference. -/
def constantCoordinateLift
    (field : Point → SurfaceCoordinateComponents) :
    CylinderPoint → ShellCoordinateComponents :=
  fun point ↦ ![field point.1 0, field point.1 1, 0]

/-- The exact normalized flux identification used by the canonical-torus recovery theorem.
Normal components are discarded; tangential coordinate components are averaged with the tube
Jacobian before being returned to the mid-surface. -/
def fluxIdentifyCoordinate
    (epsilon : Thickness)
    (field : CylinderPoint → ShellCoordinateComponents) :
    Point → SurfaceCoordinateComponents :=
  fun point index ↦
    ∫ z : NormalPoint,
      jacobian epsilon.1 (point, z) * field (point, z) index.castSucc ∂normalMeasure

@[simp] theorem jacobian_zero (point : CylinderPoint) :
    jacobian 0 point = 1 := by
  simp [jacobian]

end

end CanonicalTorus
end RiemannianFluids
