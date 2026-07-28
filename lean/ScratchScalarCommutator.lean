import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.LieBracket

open Bundle
open scoped Bundle ContDiff Manifold

#check ContMDiffAt.mfderiv_const
#check ContMDiffAt.clm_bundle_apply
#check Bundle.contMDiffAt_section
#check contMDiffAt_hom_bundle
#check ContMDiffAt.snd
#check VectorField.fderiv_apply_lieBracket
#check contMDiffAt_iff_contMDiffOn_nhds
#check ContMDiffOn.contMDiffOn_tangentMapWithin
#check ContMDiffWithinAt.comp
#check ContMDiffAt.comp_contMDiffWithinAt
#check contMDiff_snd_tangentBundle_modelSpace
#check tangentMapWithin_eq_tangentMap
#check ContMDiffAt.congr_of_eventuallyEq
#check Filter.EventuallyEq.comp_tendsto
#check ContMDiffAt.mlieBracket_vectorField
#check VectorField.leibniz_identity_mlieBracket_apply

namespace RiemannianFluids

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [IsManifold I 3 M]

noncomputable section

def scalarDirectionalDerivative
    (f : M → ℝ) (direction : (y : M) → TangentSpace I y) : M → ℝ :=
  fun y ↦ d% f y (direction y)

set_option maxHeartbeats 800000 in
theorem contMDiffAt_one_scalarDirectionalDerivative
    {x : M} {f : M → ℝ} {direction : (y : M) → TangentSpace I y}
    (hf : CMDiffAt 2 f x) (hdirection : CMDiffAt 1 (T% direction) x) :
    CMDiffAt 1 (scalarDirectionalDerivative I f direction) x := by
  rcases (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by simp)).mp hf with
    ⟨u, hu, hfu⟩
  rcases mem_nhds_iff.mp hu with ⟨v, hvu, hvopen, hxv⟩
  have hfv : CMDiff[v] 2 f := hfu.mono hvu
  have htmWithin : CMDiff[(π E (TangentSpace I) ⁻¹' v)] 1
      (tangentMap[v] f) :=
    hfv.contMDiffOn_tangentMapWithin (by norm_num) hvopen.uniqueMDiffOn
  have hcompWithin : CMDiffAt[v] 1
      ((tangentMap[v] f) ∘ fun y ↦ (T% direction y)) x := by
    exact (htmWithin (T% direction x) hxv).comp x hdirection.contMDiffWithinAt
      (by intro y hy; exact hy)
  have hcompAt : CMDiffAt 1
      ((tangentMap[v] f) ∘ fun y ↦ (T% direction y)) x :=
    hcompWithin.contMDiffAt (hvopen.mem_nhds hxv)
  have heq :
      ((tangentMap% f) ∘ fun y ↦ (T% direction y)) =ᶠ[nhds x]
        ((tangentMap[v] f) ∘ fun y ↦ (T% direction y)) := by
    filter_upwards [hvopen.mem_nhds hxv] with y hy
    simp only [Function.comp_apply, tangentMapWithin, tangentMap,
      mfderivWithin_of_isOpen hvopen hy]
  have hcomp : CMDiffAt 1
      ((tangentMap% f) ∘ fun y ↦ (T% direction y)) x :=
    hcompAt.congr_of_eventuallyEq heq
  have hsnd := contMDiff_snd_tangentBundle_modelSpace (n := 1) ℝ 𝓘(ℝ, ℝ)
  have heval :
      ((fun p : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ p.snd) ∘
        (tangentMap% f) ∘ fun y ↦ (T% direction y)) =
        scalarDirectionalDerivative I f direction := by
    rfl
  rw [← heval]
  exact hsnd.contMDiffAt.comp x hcomp

set_option maxHeartbeats 800000 in
theorem scalarLieCommutator_smul
    {x : M} {f : M → ℝ}
    {first second field : (y : M) → TangentSpace I y}
    (hf : CMDiffAt 2 f x)
    (hfirst : CMDiffAt 2 (T% first) x)
    (hsecond : CMDiffAt 2 (T% second) x)
    (hfield : CMDiffAt 2 (T% field) x) :
    (d% (scalarDirectionalDerivative I f second) x (first x) -
          d% (scalarDirectionalDerivative I f first) x (second x) -
          d% f x (VectorField.mlieBracket I first second x)) • field x = 0 := by
  letI : IsManifold I (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold I 2 M)
  letI : IsManifold I (minSmoothness ℝ 3) M := by
    simpa using (inferInstance : IsManifold I 3 M)
  let firstF := scalarDirectionalDerivative I f first
  let secondF := scalarDirectionalDerivative I f second
  let firstSecond := VectorField.mlieBracket I first second
  let firstField := VectorField.mlieBracket I first field
  let secondField := VectorField.mlieBracket I second field
  have hfirstF : CMDiffAt 1 firstF x :=
    contMDiffAt_one_scalarDirectionalDerivative I hf (hfirst.of_le (by norm_num))
  have hsecondF : CMDiffAt 1 secondF x :=
    contMDiffAt_one_scalarDirectionalDerivative I hf (hsecond.of_le (by norm_num))
  have hfirstSecond : CMDiffAt 1 (T% firstSecond) x :=
    hfirst.mlieBracket_vectorField hsecond (m := 1) (by norm_num)
  have hfirstField : CMDiffAt 1 (T% firstField) x :=
    hfirst.mlieBracket_vectorField hfield (m := 1) (by norm_num)
  have hsecondField : CMDiffAt 1 (T% secondField) x :=
    hsecond.mlieBracket_vectorField hfield (m := 1) (by norm_num)
  have hf_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 f y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hf
  have hfirst_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 (T% first) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hfirst
  have hsecond_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 (T% second) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hsecond
  have hfield_eventually : ∀ᶠ y in nhds x, CMDiffAt 2 (T% field) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).mp hfield
  have hsecond_smul :
      VectorField.mlieBracket I second (f • field) =ᶠ[nhds x]
        secondF • field + f • secondField := by
    filter_upwards [hf_eventually, hsecond_eventually, hfield_eventually] with y hfy hsy hzy
    change VectorField.mlieBracket I second (f • field) y =
      d% f y (second y) • field y +
        f y • VectorField.mlieBracket I second field y
    exact VectorField.mlieBracket_smul_right (I := I)
      (hfy.mdifferentiableAt (by norm_num))
      (hzy.mdifferentiableAt (by norm_num)) (V := second)
  have hfirst_smul :
      VectorField.mlieBracket I first (f • field) =ᶠ[nhds x]
        firstF • field + f • firstField := by
    filter_upwards [hf_eventually, hfirst_eventually, hfield_eventually] with y hfy hxy hzy
    change VectorField.mlieBracket I first (f • field) y =
      d% f y (first y) • field y +
        f y • VectorField.mlieBracket I first field y
    exact VectorField.mlieBracket_smul_right (I := I)
      (hfy.mdifferentiableAt (by norm_num))
      (hzy.mdifferentiableAt (by norm_num)) (V := first)
  have hfirst_min : CMDiffAt (minSmoothness ℝ 2) (T% first) x := by
    simpa using hfirst
  have hsecond_min : CMDiffAt (minSmoothness ℝ 2) (T% second) x := by
    simpa using hsecond
  have hfield_min : CMDiffAt (minSmoothness ℝ 2) (T% field) x := by
    simpa using hfield
  have hf_field_min : CMDiffAt (minSmoothness ℝ 2) (T% (f • field)) x := by
    simpa using hf.smul_section hfield
  have hjacobiScaled := VectorField.leibniz_identity_mlieBracket_apply
    (I := I) hfirst_min hsecond_min hf_field_min
  rw [EventuallyEq.rfl.mlieBracket_vectorField_eq hsecond_smul,
    hfirst_smul.mlieBracket_vectorField_eq EventuallyEq.rfl] at hjacobiScaled
  have hsecondF_field : CMDiffAt 1 (T% (secondF • field)) x :=
    hsecondF.smul_section (hfield.of_le (by norm_num))
  have hf_secondField : CMDiffAt 1 (T% (f • secondField)) x :=
    (hf.of_le (by norm_num)).smul_section hsecondField
  have hfirstF_field : CMDiffAt 1 (T% (firstF • field)) x :=
    hfirstF.smul_section (hfield.of_le (by norm_num))
  have hf_firstField : CMDiffAt 1 (T% (f • firstField)) x :=
    (hf.of_le (by norm_num)).smul_section hfirstField
  rw [VectorField.mlieBracket_add_right
      hsecondF_field.mdifferentiableAt hf_secondField.mdifferentiableAt,
    VectorField.mlieBracket_add_right
      hfirstF_field.mdifferentiableAt hf_firstField.mdifferentiableAt]
      at hjacobiScaled
  rw [VectorField.mlieBracket_smul_right hsecondF.mdifferentiableAt
      (hfield.of_le (by norm_num)).mdifferentiableAt,
    VectorField.mlieBracket_smul_right (hf.mdifferentiableAt (by norm_num))
      hsecondField.mdifferentiableAt,
    VectorField.mlieBracket_smul_right (hf.mdifferentiableAt (by norm_num))
      (hfield.mdifferentiableAt (by norm_num)),
    VectorField.mlieBracket_smul_right hfirstF.mdifferentiableAt
      (hfield.of_le (by norm_num)).mdifferentiableAt,
    VectorField.mlieBracket_smul_right (hf.mdifferentiableAt (by norm_num))
      hfirstField.mdifferentiableAt] at hjacobiScaled
  have hjacobi := VectorField.leibniz_identity_mlieBracket_apply
    (I := I) hfirst_min hsecond_min hfield_min
  change VectorField.mlieBracket I first secondField x =
      VectorField.mlieBracket I firstSecond field x +
        VectorField.mlieBracket I second firstField x at hjacobi
  dsimp only [firstF, secondF, firstSecond, firstField, secondField] at
    hjacobiScaled hjacobi ⊢
  module at hjacobiScaled ⊢

end

end RiemannianFluids
