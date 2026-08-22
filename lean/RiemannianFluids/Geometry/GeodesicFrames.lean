import RiemannianFluids.Geometry.SubmanifoldConnection

/-!
# Pointwise geodesic frames for covariant derivatives

A covariant derivative on the tangent bundle admits a frame whose covariant derivative vanishes
at any prescribed point.  The construction here is explicit and local at the level of germs.
Starting from the canonical smooth tangent-bundle trivialization, it subtracts chart-affine
scalar multiples whose differentials are the connection coefficients of that frame at the base
point.

This is the pointwise normal-frame construction used implicitly in submanifold calculations.  It
does not require an exponential map, geodesic completeness, or a tubular neighborhood.
-/

namespace RiemannianFluids

open Bundle
open scoped BigOperators Bundle ContDiff InnerProductSpace Manifold

noncomputable section

variable
  {ι : Type*} [Fintype ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Regard a covector on the Riemannian tangent fiber as a continuous covector on the model
space.  These are the same linear map; finite dimensionality makes it continuous for the model
norm as well. -/
def tangentCovectorInModelAt (x : M) (covector : TangentSpace I x →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  ({
    toFun := fun direction : E ↦ covector direction
    map_add' := fun first second ↦ covector.map_add first second
    map_smul' := fun scalar direction ↦ covector.map_smul scalar direction
  } : E →ₗ[ℝ] ℝ).toContinuousLinearMap

omit [IsManifold I 3 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
@[simp]
theorem tangentCovectorInModelAt_apply
    (x : M) (covector : TangentSpace I x →L[ℝ] ℝ) (direction : E) :
    tangentCovectorInModelAt (I := I) x covector direction = covector direction := by
  rfl

/-- A chart-affine scalar function with prescribed differential at `x` and value zero there. -/
def manifoldLinearCoordinateAt (x : M) (covector : TangentSpace I x →L[ℝ] ℝ) : M → ℝ :=
  (fun y ↦ tangentCovectorInModelAt (I := I) x covector (extChartAt I x y)) -
    fun _ ↦ tangentCovectorInModelAt (I := I) x covector (extChartAt I x x)

omit [IsManifold I 3 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
@[simp]
theorem manifoldLinearCoordinateAt_apply_self
    (x : M) (covector : TangentSpace I x →L[ℝ] ℝ) :
    manifoldLinearCoordinateAt (I := I) x covector x = 0 := by
  simp [manifoldLinearCoordinateAt]

omit [IsManifold I 3 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- The chart-affine coordinate is as smooth at the base point as the manifold atlas. -/
theorem manifoldLinearCoordinateAt_contMDiffAt
    (x : M) (covector : TangentSpace I x →L[ℝ] ℝ) :
    CMDiffAt 2 (manifoldLinearCoordinateAt (I := I) x covector) x := by
  exact ((tangentCovectorInModelAt (I := I) x covector).contMDiffAt.comp x
    (contMDiffAt_extChartAt (I := I) (n := 2))).sub contMDiffAt_const

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- The differential of the chart-affine coordinate is the prescribed covector. -/
theorem mfderiv_manifoldLinearCoordinateAt
    (x : M) (covector : TangentSpace I x →L[ℝ] ℝ) :
    mfderiv I 𝓘(ℝ) (manifoldLinearCoordinateAt (I := I) x covector) x = covector := by
  have hchart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (I := I) (x := x) (y := x) (by simp)
  have hraw := (tangentCovectorInModelAt (I := I) x covector).hasMFDerivAt.comp x
    hchart.hasMFDerivAt
  have hrawDerivative :
      (tangentCovectorInModelAt (I := I) x covector).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x) = covector := by
    rw [mfderiv_extChartAt_self]
    ext direction
    simp only [ContinuousLinearMap.comp_apply, tangentCovectorInModelAt_apply]
    change covector direction = covector direction
    rfl
  have hlinear : HasMFDerivAt I 𝓘(ℝ)
      (fun y ↦ tangentCovectorInModelAt (I := I) x covector (extChartAt I x y)) x
      covector := hraw.congr_mfderiv hrawDerivative
  have hcoordinate := hlinear.sub
    (hasMFDerivAt_const (x := x)
      (c := tangentCovectorInModelAt (I := I) x covector (extChartAt I x x)))
  exact (hcoordinate.congr_mfderiv (sub_zero covector)).mfderiv

/-- The canonical trivialization section through the `i`th frame vector. -/
def canonicalFrameFieldAt (x : M) (frame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (i : ι) : (y : M) → TangentSpace I y :=
  SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (frame i)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem canonicalFrameFieldAt_apply_self
    (x : M) (frame : OrthonormalBasis ι ℝ (TangentSpace I x)) (i : ι) :
    canonicalFrameFieldAt (I := I) x frame i x = frame i := by
  exact SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self
    (I := I) x (frame i)

/-- The connection coefficient of the canonical frame, viewed as a covector in its direction
argument. -/
def canonicalFrameConnectionCoefficientAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (frame : OrthonormalBasis ι ℝ (TangentSpace I x)) (i j : ι) :
    TangentSpace I x →L[ℝ] ℝ :=
  (innerSL ℝ (frame j)).comp (connection (canonicalFrameFieldAt (I := I) x frame i) x)

/-- Correct the canonical trivialization frame by its chart-affine connection coefficients. -/
def geodesicFrameFieldAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (frame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (i : ι) : (y : M) → TangentSpace I y :=
  canonicalFrameFieldAt (I := I) x frame i -
    ∑ j, manifoldLinearCoordinateAt (I := I) x
        (canonicalFrameConnectionCoefficientAt connection x frame i j) •
      canonicalFrameFieldAt (I := I) x frame j

/-- The corrected frame still has the prescribed value at the base point. -/
@[simp]
theorem geodesicFrameFieldAt_apply_self
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (frame : OrthonormalBasis ι ℝ (TangentSpace I x)) (i : ι) :
    geodesicFrameFieldAt connection x frame i x = frame i := by
  simp [geodesicFrameFieldAt]

/-- Each corrected frame field is `C²` at the base point. -/
theorem geodesicFrameFieldAt_contMDiffAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (frame : OrthonormalBasis ι ℝ (TangentSpace I x)) (i : ι) :
    CMDiffAt 2 (T% (geodesicFrameFieldAt connection x frame i)) x := by
  have hcanonical (j : ι) : CMDiffAt 2
      (T% (canonicalFrameFieldAt (I := I) x frame j)) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x (frame j)
  have hterm (j : ι) : CMDiffAt 2
      (T% (manifoldLinearCoordinateAt (I := I) x
          (canonicalFrameConnectionCoefficientAt connection x frame i j) •
        canonicalFrameFieldAt (I := I) x frame j)) x :=
    (manifoldLinearCoordinateAt_contMDiffAt (I := I) x
      (canonicalFrameConnectionCoefficientAt connection x frame i j)).smul_section
        (hcanonical j)
  exact (hcanonical i).sub_section
    (by
      simpa only [Finset.sum_apply] using
        (ContMDiffAt.sum_section (s := (Finset.univ : Finset ι)) fun j _ ↦ hterm j))

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- A covariant derivative passes through a finite sum of differentiable sections at a point. -/
theorem covariantDerivative_apply_sum_at
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    {field : ι → (y : M) → TangentSpace I y} {x : M}
    (hfield : ∀ i, MDiffAt (T% (field i)) x) :
    connection (∑ i, field i) x = ∑ i, connection (field i) x := by
  classical
  let h (s : Finset ι) :
      connection (∑ i ∈ s, field i) x = ∑ i ∈ s, connection (field i) x := by
    induction s using Finset.induction_on with
    | empty => simp [connection.zero]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        rw [connection.isCovariantDerivativeOn.add (hfield i)
          (by
            simpa only [Finset.sum_apply] using
              (MDifferentiableAt.sum_section (s := s) fun j _ ↦ hfield j))]
        rw [ih]
  exact h Finset.univ

/-- The corrected frame is geodesic at `x`: its full covariant derivative there is zero. -/
theorem geodesicFrameFieldAt_covariantDerivative_eq_zero
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (frame : OrthonormalBasis ι ℝ (TangentSpace I x)) (i : ι) :
    connection (geodesicFrameFieldAt connection x frame i) x = 0 := by
  classical
  let canonical (j : ι) := canonicalFrameFieldAt (I := I) x frame j
  let coefficient (j : ι) := canonicalFrameConnectionCoefficientAt connection x frame i j
  let scalar (j : ι) := manifoldLinearCoordinateAt (I := I) x (coefficient j)
  have hcanonical (j : ι) : MDiffAt (T% (canonical j)) x :=
    (SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x (frame j)).mdifferentiableAt (by norm_num)
  have hscalar (j : ι) : MDiffAt (scalar j) x :=
    (manifoldLinearCoordinateAt_contMDiffAt (I := I) x (coefficient j)
      ).mdifferentiableAt (by norm_num)
  have hterm (j : ι) : MDiffAt (T% (scalar j • canonical j)) x :=
    (hscalar j).smul_section (hcanonical j)
  have derivativeTerm (j : ι) :
      connection (scalar j • canonical j) x =
        (coefficient j).smulRight (frame j) := by
    rw [connection.isCovariantDerivativeOn.leibniz (hcanonical j) (hscalar j)]
    simp only [scalar, manifoldLinearCoordinateAt_apply_self, zero_smul, zero_add,
      canonical, canonicalFrameFieldAt_apply_self]
    have hscalarDerivative : d% (scalar j) x = coefficient j :=
      mfderiv_manifoldLinearCoordinateAt (I := I) x (coefficient j)
    rw [hscalarDerivative]
  have derivativeSum :
      connection (∑ j, scalar j • canonical j) x =
        ∑ j, (coefficient j).smulRight (frame j) := by
    rw [covariantDerivative_apply_sum_at connection hterm]
    exact Finset.sum_congr rfl fun j _ ↦ derivativeTerm j
  have coefficientSum :
      ∑ j, (coefficient j).smulRight (frame j) = connection (canonical i) x := by
    ext direction
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
      coefficient, canonicalFrameConnectionCoefficientAt, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, canonical]
    exact frame.sum_repr' (connection (canonicalFrameFieldAt (I := I) x frame i) x direction)
  change connection (canonical i - ∑ j, scalar j • canonical j) x = 0
  have hsum : MDiffAt (T% (∑ j, scalar j • canonical j)) x :=
    by
      simpa only [Finset.sum_apply] using
        (MDifferentiableAt.sum_section (s := (Finset.univ : Finset ι)) fun j _ ↦ hterm j)
  have hneg : MDiffAt (T% (-∑ j, scalar j • canonical j)) x :=
    mdifferentiableAt_neg_section hsum
  rw [sub_eq_add_neg]
  rw [connection.isCovariantDerivativeOn.add (hcanonical i) hneg]
  have derivativeNeg :
      connection (-∑ j, scalar j • canonical j) x =
        -connection (∑ j, scalar j • canonical j) x := by
    simpa only [neg_one_smul] using
      connection.isCovariantDerivativeOn.smul_const (-1 : ℝ) hsum
  rw [derivativeNeg, derivativeSum, coefficientSum]
  exact add_neg_cancel _

end

end RiemannianFluids
