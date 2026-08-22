import RiemannianFluids.Geometry.Connections
import RiemannianFluids.Geometry.Curvature

/-!
# Curvature symmetries of a Levi--Civita connection

The connection curvature constructed in `Geometry.Curvature` is alternating in its first two
slots for every connection.  A Levi--Civita connection supplies the two additional ingredients
needed by the Riemannian operator theory:

* the first Bianchi identity, from vanishing torsion and the Jacobi identity; and
* skew-adjointness in the differentiated-field/output pair, from metric compatibility.

Together these imply symmetry of the connection-derived Ricci form.  This module keeps the
geometric proof separate from the trace construction so downstream Hodge formulas can consume a
theorem rather than carry Ricci symmetry as an independent premise.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

noncomputable section

/-- The cyclic first Bianchi identity for the connection curvature tensor at one point. -/
def ConnectionCurvatureFirstBianchiAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x) : Prop :=
  ∀ first second field : TangentSpace I x,
    connectionCurvatureTensorAt I connection x regular first second field +
        connectionCurvatureTensorAt I connection x regular second field first +
        connectionCurvatureTensorAt I connection x regular field first second = 0

/-- Metric skew-adjointness of the connection curvature tensor in its last two slots. -/
def ConnectionCurvatureMetricSkewAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x) : Prop :=
  ∀ first second field test : TangentSpace I x,
    inner ℝ (connectionCurvatureTensorAt I connection x regular first second field) test =
      -inner ℝ field
        (connectionCurvatureTensorAt I connection x regular first second test)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 3 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- Vector-valued manifold derivatives depend only on the germ of the function. -/
private theorem mvfderiv_eq_of_eventuallyEq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f g : M → F} {x : M} (h : f =ᶠ[𝓝 x] g) :
    d% f x = d% g x := by
  ext direction
  show mfderiv I 𝓘(ℝ, F) f x direction = mfderiv I 𝓘(ℝ, F) g x direction
  rw [h.mfderiv_eq]
  rfl

omit [FiniteDimensional ℝ E]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- Scalar directional derivatives commute according to the Lie bracket.  This is the scalar
form of `scalarLieCommutator_smul`; the zero-dimensional tangent fiber is handled separately so
no nontriviality assumption is hidden in the statement. -/
theorem scalarLieCommutator_eq_zero
    {x : M} {f : M → ℝ}
    {first second : (y : M) → TangentSpace I y}
    (hf : CMDiffAt 2 f x)
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x) :
    d% (scalarDirectionalDerivative I f second) x (first x) -
          d% (scalarDirectionalDerivative I f first) x (second x) -
          d% f x (VectorField.mlieBracket I first second x) = 0 := by
  classical
  by_cases hsubsingleton : Subsingleton (TangentSpace I x)
  · letI : Subsingleton (TangentSpace I x) := hsubsingleton
    have hfirstValue : first x = 0 := Subsingleton.elim _ _
    have hsecondValue : second x = 0 := Subsingleton.elim _ _
    have hbracketValue : VectorField.mlieBracket I first second x = 0 :=
      Subsingleton.elim _ _
    simp [hfirstValue, hsecondValue, hbracketValue]
  · letI : Nontrivial (TangentSpace I x) :=
      not_subsingleton_iff_nontrivial.mp hsubsingleton
    obtain ⟨value, hvalue⟩ := exists_ne (0 : TangentSpace I x)
    let witness := FiberBundle.extend E value
    have hwitness : CMDiffAt 2 (T% witness) x :=
      FiberBundle.contMDiffAt_extend (k := 2) I E value
    have hsmul := scalarLieCommutator_smul I hf hfirst hsecond hwitness
    change _ • witness x = 0 at hsmul
    rw [show witness x = value by simp [witness]] at hsmul
    exact (smul_eq_zero.mp hsmul).resolve_right hvalue

omit [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- The field-level cyclic curvature sum vanishes for a Levi--Civita connection.  The proof
groups the six iterated derivatives by their outer direction, applies torsion-freeness twice,
and finishes with the Jacobi identity for the manifold Lie bracket. -/
theorem LeviCivitaConnection.connectionCurvatureAction_cyclic_eq_zero
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {first second field : (y : M) → TangentSpace I y}
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x)
    (hfield : CMDiffAt 2 (T% field) x) :
    connectionCurvatureAction I connection.connection first second field x +
        connectionCurvatureAction I connection.connection second field first x +
        connectionCurvatureAction I connection.connection field first second x = 0 := by
  letI : IsManifold I (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold I 2 M)
  letI : IsManifold I (minSmoothness ℝ 3) M := by
    simpa using (inferInstance : IsManifold I 3 M)
  letI : IsManifold I ((2 : ℕ∞ω) + 1) M := by
    norm_num
    infer_instance
  letI : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  letI : IsManifold I.tangent 2 (TangentBundle I M) := inferInstance
  let cov := connection.connection
  have outerTorsion
      (outer left right : (y : M) → TangentSpace I y)
      (hleft : CMDiffAt 2 (T% left) x)
      (hright : CMDiffAt 2 (T% right) x) :
      covariantDerivativeAlong I cov outer
            (covariantDerivativeAlong I cov left right) x -
          covariantDerivativeAlong I cov outer
            (covariantDerivativeAlong I cov right left) x =
        covariantDerivativeAlong I cov outer
          (VectorField.mlieBracket I left right) x := by
    let leftRight := covariantDerivativeAlong I cov left right
    let rightLeft := covariantDerivativeAlong I cov right left
    let bracket := VectorField.mlieBracket I left right
    have hleftOne : MDiffAt (T% left) x :=
      hleft.mdifferentiableAt (by norm_num)
    have hrightOne : MDiffAt (T% right) x :=
      hright.mdifferentiableAt (by norm_num)
    have hleftRight : MDiffAt (T% leftRight) x :=
      regular left right hleftOne hright
    have hrightLeft : MDiffAt (T% rightLeft) x :=
      regular right left hrightOne hleft
    have hbracket : MDiffAt (T% bracket) x := by
      exact (hleft.mlieBracket_vectorField hright
        (m := 1) (n := (2 : ℕ∞)) (by norm_num)).mdifferentiableAt (by norm_num)
    have hleftEventually : ∀ᶠ y in 𝓝 x, CMDiffAt 2 (T% left) y :=
      (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hleft
    have hrightEventually : ∀ᶠ y in 𝓝 x, CMDiffAt 2 (T% right) y :=
      (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hright
    have htorsion : leftRight - rightLeft =ᶠ[𝓝 x] bracket := by
      filter_upwards [hleftEventually, hrightEventually] with y hly hry
      exact connection.connection.torsion_eq_zero_iff.mp connection.torsionFree
        (hly.mdifferentiableAt (by norm_num)) (hry.mdifferentiableAt (by norm_num))
    have hsub : MDiffAt (T% (leftRight - rightLeft)) x :=
      mdifferentiableAt_sub_section hleftRight hrightLeft
    have hconnectionSub : cov (leftRight - rightLeft) x =
        cov leftRight x - cov rightLeft x := by
      have hneg : MDiffAt (T% (-rightLeft)) x :=
        mdifferentiableAt_neg_section hrightLeft
      rw [sub_eq_add_neg, cov.isCovariantDerivativeOn.add hleftRight hneg]
      have hmapNeg : cov (-rightLeft) x = -cov rightLeft x := by
        simpa only [neg_smul, one_smul] using
          (cov.isCovariantDerivativeOn.smul_const (-1 : ℝ) hrightLeft)
      rw [hmapNeg]
      rw [sub_eq_add_neg]
    have hcongr : cov (leftRight - rightLeft) x = cov bracket x :=
      cov.isCovariantDerivativeOn.congr_of_eventuallyEq hsub hbracket
        Filter.univ_mem htorsion
    change cov leftRight x (outer x) - cov rightLeft x (outer x) =
      cov bracket x (outer x)
    rw [← sub_apply, ← hconnectionSub, hcongr]
  have torsionPair
      (left right : (y : M) → TangentSpace I y)
      (hleft : MDiffAt (T% left) x) (hright : MDiffAt (T% right) x) :
      covariantDerivativeAlong I cov left right x -
          covariantDerivativeAlong I cov right left x =
        VectorField.mlieBracket I left right x := by
    exact connection.connection.torsion_eq_zero_iff.mp connection.torsionFree hleft hright
  have hbracketFirstSecond : MDiffAt
      (T% (VectorField.mlieBracket I first second)) x :=
    (hfirst.mlieBracket_vectorField hsecond
      (m := 1) (n := (2 : ℕ∞)) (by norm_num)).mdifferentiableAt (by norm_num)
  have hbracketSecondField : MDiffAt
      (T% (VectorField.mlieBracket I second field)) x :=
    (hsecond.mlieBracket_vectorField hfield
      (m := 1) (n := (2 : ℕ∞)) (by norm_num)).mdifferentiableAt (by norm_num)
  have hbracketFieldFirst : MDiffAt
      (T% (VectorField.mlieBracket I field first)) x :=
    (hfield.mlieBracket_vectorField hfirst
      (m := 1) (n := (2 : ℕ∞)) (by norm_num)).mdifferentiableAt (by norm_num)
  have hpairFirst := torsionPair first (VectorField.mlieBracket I second field)
    (hfirst.mdifferentiableAt (by norm_num)) hbracketSecondField
  have hpairSecond := torsionPair second (VectorField.mlieBracket I field first)
    (hsecond.mdifferentiableAt (by norm_num)) hbracketFieldFirst
  have hpairField := torsionPair field (VectorField.mlieBracket I first second)
    (hfield.mdifferentiableAt (by norm_num)) hbracketFirstSecond
  have hjacobi := VectorField.leibniz_identity_mlieBracket_apply
    (I := I) (U := first) (V := second) (W := field)
    (by simpa using hfirst) (by simpa using hsecond) (by simpa using hfield)
  have houterFirst := outerTorsion first second field hsecond hfield
  have houterSecond := outerTorsion second field first hfield hfirst
  have houterField := outerTorsion field first second hfirst hsecond
  simp only [connectionCurvatureAction, Pi.sub_apply]
  have hswapOuter :
      VectorField.mlieBracket I (VectorField.mlieBracket I first second) field x =
        -VectorField.mlieBracket I field
          (VectorField.mlieBracket I first second) x :=
    VectorField.mlieBracket_swap_apply
  have hswapInner : VectorField.mlieBracket I first field =
      -VectorField.mlieBracket I field first :=
    VectorField.mlieBracket_swap
  rw [hswapInner] at hjacobi
  have hnegInner :
      VectorField.mlieBracket I second
          (-VectorField.mlieBracket I field first) x =
        -VectorField.mlieBracket I second
          (VectorField.mlieBracket I field first) x := by
    simpa only [neg_smul, one_smul] using
      (VectorField.mlieBracket_const_smul_right
        (I := I) (V := second) (W := VectorField.mlieBracket I field first)
        (c := (-1 : ℝ)) hbracketFieldFirst)
  rw [hnegInner, hswapOuter] at hjacobi
  calc
    _ =
        (covariantDerivativeAlong I cov first
              (covariantDerivativeAlong I cov second field) x -
            covariantDerivativeAlong I cov first
              (covariantDerivativeAlong I cov field second) x) +
          (covariantDerivativeAlong I cov second
              (covariantDerivativeAlong I cov field first) x -
            covariantDerivativeAlong I cov second
              (covariantDerivativeAlong I cov first field) x) +
          (covariantDerivativeAlong I cov field
              (covariantDerivativeAlong I cov first second) x -
            covariantDerivativeAlong I cov field
              (covariantDerivativeAlong I cov second first) x) -
          covariantDerivativeAlong I cov
            (VectorField.mlieBracket I first second) field x -
          covariantDerivativeAlong I cov
            (VectorField.mlieBracket I second field) first x -
          covariantDerivativeAlong I cov
            (VectorField.mlieBracket I field first) second x := by abel
    _ = covariantDerivativeAlong I cov first
            (VectorField.mlieBracket I second field) x +
          covariantDerivativeAlong I cov second
            (VectorField.mlieBracket I field first) x +
          covariantDerivativeAlong I cov field
            (VectorField.mlieBracket I first second) x -
          covariantDerivativeAlong I cov
            (VectorField.mlieBracket I first second) field x -
          covariantDerivativeAlong I cov
            (VectorField.mlieBracket I second field) first x -
          covariantDerivativeAlong I cov
            (VectorField.mlieBracket I field first) second x := by
      rw [houterFirst, houterSecond, houterField]
    _ =
        (covariantDerivativeAlong I cov first
              (VectorField.mlieBracket I second field) x -
            covariantDerivativeAlong I cov
              (VectorField.mlieBracket I second field) first x) +
          (covariantDerivativeAlong I cov second
              (VectorField.mlieBracket I field first) x -
            covariantDerivativeAlong I cov
              (VectorField.mlieBracket I field first) second x) +
          (covariantDerivativeAlong I cov field
              (VectorField.mlieBracket I first second) x -
            covariantDerivativeAlong I cov
              (VectorField.mlieBracket I first second) field x) := by abel
    _ = VectorField.mlieBracket I first
            (VectorField.mlieBracket I second field) x +
          VectorField.mlieBracket I second
            (VectorField.mlieBracket I field first) x +
          VectorField.mlieBracket I field
            (VectorField.mlieBracket I first second) x := by
      rw [hpairFirst, hpairSecond, hpairField]
    _ = 0 := by rw [hjacobi]; abel

omit [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- The pointwise curvature tensor of a Levi--Civita connection satisfies first Bianchi. -/
theorem LeviCivitaConnection.connectionCurvatureFirstBianchiAt
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x) :
    ConnectionCurvatureFirstBianchiAt I connection.connection x regular := by
  intro first second field
  rw [connectionCurvatureTensorAt_apply_extend,
    connectionCurvatureTensorAt_apply_extend,
    connectionCurvatureTensorAt_apply_extend]
  exact LeviCivitaConnection.connectionCurvatureAction_cyclic_eq_zero
    (I := I) connection x regular
    (FiberBundle.contMDiffAt_extend (k := 2) I E first)
    (FiberBundle.contMDiffAt_extend (k := 2) I E second)
    (FiberBundle.contMDiffAt_extend (k := 2) I E field)

/-- Metric compatibility makes the field-level curvature action skew-adjoint in its field and
test slots.  Expanding the scalar commutator of `y ↦ ⟨field y, test y⟩` by metric compatibility
twice cancels the four mixed first-derivative pairings and leaves precisely the two curvature
terms. -/
theorem LeviCivitaConnection.inner_connectionCurvatureAction_add_swap_eq_zero
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {first second field test : (y : M) → TangentSpace I y}
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x)
    (hfield : CMDiffAt 2 (T% field) x)
    (htest : CMDiffAt 2 (T% test) x) :
    inner ℝ (connectionCurvatureAction I connection.connection first second field x)
          (test x) +
        inner ℝ (field x)
          (connectionCurvatureAction I connection.connection first second test x) = 0 := by
  letI : IsManifold I (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold I 2 M)
  letI : IsManifold I ((2 : ℕ∞ω) + 1) M := by
    norm_num
    infer_instance
  letI : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  letI : IsManifold I.tangent 2 (TangentBundle I M) := inferInstance
  let cov := connection.connection
  let pair : M → ℝ := fun y ↦ inner ℝ (field y) (test y)
  let firstField := covariantDerivativeAlong I cov first field
  let secondField := covariantDerivativeAlong I cov second field
  let firstTest := covariantDerivativeAlong I cov first test
  let secondTest := covariantDerivativeAlong I cov second test
  let bracket := VectorField.mlieBracket I first second
  let firstPair := scalarDirectionalDerivative I pair first
  let secondPair := scalarDirectionalDerivative I pair second
  have hfirstOne : MDiffAt (T% first) x :=
    hfirst.mdifferentiableAt (by norm_num)
  have hsecondOne : MDiffAt (T% second) x :=
    hsecond.mdifferentiableAt (by norm_num)
  have hfieldOne : MDiffAt (T% field) x :=
    hfield.mdifferentiableAt (by norm_num)
  have htestOne : MDiffAt (T% test) x :=
    htest.mdifferentiableAt (by norm_num)
  have hfirstField : MDiffAt (T% firstField) x :=
    regular first field hfirstOne hfield
  have hsecondField : MDiffAt (T% secondField) x :=
    regular second field hsecondOne hfield
  have hfirstTest : MDiffAt (T% firstTest) x :=
    regular first test hfirstOne htest
  have hsecondTest : MDiffAt (T% secondTest) x :=
    regular second test hsecondOne htest
  have hbracket : MDiffAt (T% bracket) x :=
    (hfirst.mlieBracket_vectorField hsecond
      (m := 1) (n := (2 : ℕ∞)) (by norm_num)).mdifferentiableAt (by norm_num)
  have hpair : CMDiffAt 2 pair x :=
    ContMDiffAt.inner_bundle (F := E) (E := (TangentSpace I : M → Type _)) hfield htest
  have hfirstEventually : ∀ᶠ y in 𝓝 x, CMDiffAt 2 (T% first) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hfirst
  have hsecondEventually : ∀ᶠ y in 𝓝 x, CMDiffAt 2 (T% second) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hsecond
  have hfieldEventually : ∀ᶠ y in 𝓝 x, CMDiffAt 2 (T% field) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hfield
  have htestEventually : ∀ᶠ y in 𝓝 x, CMDiffAt 2 (T% test) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp htest
  have hmetricFirst : firstPair =ᶠ[𝓝 x]
      fun y ↦ inner ℝ (firstField y) (test y) + inner ℝ (field y) (firstTest y) := by
    filter_upwards [hfirstEventually, hfieldEventually, htestEventually] with y hxy hfy hty
    exact connection.metricCompatible
      (hxy.mdifferentiableAt (by norm_num))
      (hfy.mdifferentiableAt (by norm_num))
      (hty.mdifferentiableAt (by norm_num))
  have hmetricSecond : secondPair =ᶠ[𝓝 x]
      fun y ↦ inner ℝ (secondField y) (test y) + inner ℝ (field y) (secondTest y) := by
    filter_upwards [hsecondEventually, hfieldEventually, htestEventually] with y hyy hfy hty
    exact connection.metricCompatible
      (hyy.mdifferentiableAt (by norm_num))
      (hfy.mdifferentiableAt (by norm_num))
      (hty.mdifferentiableAt (by norm_num))
  have hinnerSecondFieldTest : MDiffAt
      (fun y ↦ inner ℝ (secondField y) (test y)) x :=
    MDifferentiableAt.inner_bundle (F := E) (E := (TangentSpace I : M → Type _))
      hsecondField htestOne
  have hinnerFieldSecondTest : MDiffAt
      (fun y ↦ inner ℝ (field y) (secondTest y)) x :=
    MDifferentiableAt.inner_bundle (F := E) (E := (TangentSpace I : M → Type _))
      hfieldOne hsecondTest
  have hinnerFirstFieldTest : MDiffAt
      (fun y ↦ inner ℝ (firstField y) (test y)) x :=
    MDifferentiableAt.inner_bundle (F := E) (E := (TangentSpace I : M → Type _))
      hfirstField htestOne
  have hinnerFieldFirstTest : MDiffAt
      (fun y ↦ inner ℝ (field y) (firstTest y)) x :=
    MDifferentiableAt.inner_bundle (F := E) (E := (TangentSpace I : M → Type _))
      hfieldOne hfirstTest
  have hsecondPairDerivative :
      d% secondPair x (first x) =
        inner ℝ (cov secondField x (first x)) (test x) +
          inner ℝ (secondField x) (firstTest x) +
          inner ℝ (firstField x) (secondTest x) +
          inner ℝ (field x) (cov secondTest x (first x)) := by
    rw [mvfderiv_eq_of_eventuallyEq I hmetricSecond,
      mvfderiv_fun_add hinnerSecondFieldTest hinnerFieldSecondTest, add_apply]
    rw [connection.metricCompatible hfirstOne hsecondField htestOne,
      connection.metricCompatible hfirstOne hfieldOne hsecondTest]
    simp only [cov, firstField, secondField, firstTest, secondTest,
      covariantDerivativeAlong]
    ring
  have hfirstPairDerivative :
      d% firstPair x (second x) =
        inner ℝ (cov firstField x (second x)) (test x) +
          inner ℝ (firstField x) (secondTest x) +
          inner ℝ (secondField x) (firstTest x) +
          inner ℝ (field x) (cov firstTest x (second x)) := by
    rw [mvfderiv_eq_of_eventuallyEq I hmetricFirst,
      mvfderiv_fun_add hinnerFirstFieldTest hinnerFieldFirstTest, add_apply]
    rw [connection.metricCompatible hsecondOne hfirstField htestOne,
      connection.metricCompatible hsecondOne hfieldOne hfirstTest]
    simp only [cov, firstField, secondField, firstTest, secondTest,
      covariantDerivativeAlong]
    ring
  have hbracketPairDerivative :
      d% pair x (bracket x) =
        inner ℝ (cov field x (bracket x)) (test x) +
          inner ℝ (field x) (cov test x (bracket x)) := by
    exact connection.metricCompatible hbracket hfieldOne htestOne
  have hscalar := scalarLieCommutator_eq_zero I hpair hfirst hsecond
  change d% secondPair x (first x) - d% firstPair x (second x) -
      d% pair x (bracket x) = 0 at hscalar
  rw [hsecondPairDerivative, hfirstPairDerivative, hbracketPairDerivative] at hscalar
  simp only [connectionCurvatureAction, Pi.sub_apply, inner_sub_left, inner_sub_right]
  change
    (inner ℝ (cov secondField x (first x)) (test x) -
          inner ℝ (cov firstField x (second x)) (test x) -
          inner ℝ (cov field x (bracket x)) (test x)) +
        (inner ℝ (field x) (cov secondTest x (first x)) -
          inner ℝ (field x) (cov firstTest x (second x)) -
          inner ℝ (field x) (cov test x (bracket x))) = 0
  linarith

/-- The curvature tensor of a Levi--Civita connection is skew-adjoint in its last two slots. -/
theorem LeviCivitaConnection.connectionCurvatureMetricSkewAt
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x) :
    ConnectionCurvatureMetricSkewAt I connection.connection x regular := by
  intro first second field test
  rw [connectionCurvatureTensorAt_apply_extend,
    connectionCurvatureTensorAt_apply_extend]
  have hzero := LeviCivitaConnection.inner_connectionCurvatureAction_add_swap_eq_zero
    (I := I) connection x regular
    (FiberBundle.contMDiffAt_extend (k := 2) I E first)
    (FiberBundle.contMDiffAt_extend (k := 2) I E second)
    (FiberBundle.contMDiffAt_extend (k := 2) I E field)
    (FiberBundle.contMDiffAt_extend (k := 2) I E test)
  simp only [FiberBundle.extend_apply_self] at hzero
  linarith

omit [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- First Bianchi plus metric skew-adjointness imply symmetry of the Ricci contraction. -/
theorem connectionRicciSymmetricAt_of_firstBianchi_metricSkew
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (bianchi : ConnectionCurvatureFirstBianchiAt I connection x regular)
    (metricSkew : ConnectionCurvatureMetricSkewAt I connection x regular) :
    ConnectionRicciSymmetricAt I connection x regular := by
  intro first second
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  let basis := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [connectionRicciFormAt_eq_sum_inner I connection x regular basis,
    connectionRicciFormAt_eq_sum_inner I connection x regular basis]
  apply Finset.sum_congr rfl
  intro i _
  let curvature := connectionCurvatureTensorAt I connection x regular
  have hmiddle : inner ℝ (basis i) (curvature first second (basis i)) = 0 := by
    have hskew := metricSkew first second (basis i) (basis i)
    change inner ℝ (curvature first second (basis i)) (basis i) =
      -inner ℝ (basis i) (curvature first second (basis i)) at hskew
    rw [real_inner_comm (basis i) (curvature first second (basis i))] at hskew
    linarith
  have hcyclic := congrArg (fun value ↦ inner ℝ (basis i) value)
    (bianchi (basis i) first second)
  have hswap := connectionCurvatureTensorAt_swap I connection x regular
    second (basis i) first
  change curvature second (basis i) first = -curvature (basis i) second first at hswap
  rw [inner_add_right, inner_add_right, inner_zero_right, hmiddle, hswap,
    inner_neg_right] at hcyclic
  linarith

/-- The Ricci form constructed from a `C²` Riemannian metric and its Levi--Civita connection is
symmetric.  No curvature symmetry or Ricci identity is accepted as an additional premise. -/
theorem LeviCivitaConnection.connectionRicciSymmetricAt
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x) :
    ConnectionRicciSymmetricAt I connection.connection x regular :=
  connectionRicciSymmetricAt_of_firstBianchi_metricSkew I connection.connection x regular
    (LeviCivitaConnection.connectionCurvatureFirstBianchiAt
      (I := I) connection x regular)
    (LeviCivitaConnection.connectionCurvatureMetricSkewAt
      (I := I) connection x regular)

end

end RiemannianFluids
