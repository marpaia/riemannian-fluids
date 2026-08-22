import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import RiemannianFluids.Geometry.Submanifolds

/-!
# Germ-local extensions along an embedded submanifold

The Gauss--Weingarten calculations in CCG25 choose ambient extensions only on a neighborhood of
the evaluation point.  This module realizes that construction from Mathlib's immersion
normal-form charts.  The chart projection is a genuine local retraction; scalar functions,
tangent fields, and arbitrary ambient fields along the immersion are extended through it.

The resulting operators are linear, agree with the original fields as germs along the immersion,
preserve scalar multiplication exactly, and preserve every finite or smooth differentiability
order supported by the smooth immersion.  No global tubular retraction or global extension
oracle is assumed.
-/

namespace RiemannianFluids

open Bundle Function Set
open scoped ContDiff Manifold Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {f : M → N} {x : M}

noncomputable def immersionChartRetractionAt
    (h : Manifold.IsImmersionAt I I' ∞ f x) : N → M :=
  (h.domChart.extend I).symm ∘ Prod.fst ∘ h.equiv.symm ∘ (h.codChart.extend I')

omit [I.Boundaryless] [IsManifold I ∞ M]
  [I'.Boundaryless] [IsManifold I' ∞ N] in
theorem immersionChartRetractionAt_apply_image_self
    (h : Manifold.IsImmersionAt I I' ∞ f x) :
    immersionChartRetractionAt h (f x) = x := by
  have hxTarget : (h.domChart.extend I) x ∈ (h.domChart.extend I).target := by
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨x, h.mem_domChart_source, rfl⟩
  have hwritten := h.writtenInCharts hxTarget
  have hxExtendSource : x ∈ (h.domChart.extend I).source := by
    simpa using h.mem_domChart_source
  have hsymm : (h.domChart.extend I).symm ((h.domChart.extend I) x) = x :=
    (h.domChart.extend I).left_inv hxExtendSource
  have hnormal :
      (h.codChart.extend I') (f x) =
        h.equiv ((h.domChart.extend I) x, 0) := by
    simpa only [Function.comp_apply, hsymm] using hwritten
  simp only [immersionChartRetractionAt, Function.comp_apply, hnormal,
    ContinuousLinearEquiv.symm_apply_apply, hsymm]

omit [I.Boundaryless] [IsManifold I ∞ M]
  [I'.Boundaryless] [IsManifold I' ∞ N] in
theorem immersionChartRetractionAt_apply_image
    (h : Manifold.IsImmersionAt I I' ∞ f x) {y : M}
    (hy : y ∈ h.domChart.source) :
    immersionChartRetractionAt h (f y) = y := by
  have hyTarget : (h.domChart.extend I) y ∈ (h.domChart.extend I).target := by
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨y, hy, rfl⟩
  have hwritten := h.writtenInCharts hyTarget
  have hyExtendSource : y ∈ (h.domChart.extend I).source := by
    simpa using hy
  have hsymm : (h.domChart.extend I).symm ((h.domChart.extend I) y) = y :=
    (h.domChart.extend I).left_inv hyExtendSource
  have hnormal :
      (h.codChart.extend I') (f y) =
        h.equiv ((h.domChart.extend I) y, 0) := by
    simpa only [Function.comp_apply, hsymm] using hwritten
  simp only [immersionChartRetractionAt, Function.comp_apply, hnormal,
    ContinuousLinearEquiv.symm_apply_apply, hsymm]

omit [I.Boundaryless] [IsManifold I ∞ M]
  [I'.Boundaryless] [IsManifold I' ∞ N] in
theorem immersionChartRetractionAt_comp_eventuallyEq_id
    (h : Manifold.IsImmersionAt I I' ∞ f x) :
    immersionChartRetractionAt h ∘ f =ᶠ[nhds x] id := by
  filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
  exact immersionChartRetractionAt_apply_image h hy

omit [IsManifold I ∞ M] [I'.Boundaryless] [IsManifold I' ∞ N] in
theorem immersionChartRetractionAt_contMDiffAt
    (h : Manifold.IsImmersionAt I I' ∞ f x) :
    CMDiffAt ∞ (immersionChartRetractionAt h) (f x) := by
  let cod : N → E' := h.codChart.extend I'
  let projection : E' → E := Prod.fst ∘ h.equiv.symm
  let domInv : E → M := (h.domChart.extend I).symm
  have hxTarget : (h.domChart.extend I) x ∈ (h.domChart.extend I).target := by
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨x, h.mem_domChart_source, rfl⟩
  have hxExtendSource : x ∈ (h.domChart.extend I).source := by
    simpa using h.mem_domChart_source
  have hsymm : (h.domChart.extend I).symm ((h.domChart.extend I) x) = x :=
    (h.domChart.extend I).left_inv hxExtendSource
  have hwritten := h.writtenInCharts hxTarget
  have hnormal : cod (f x) = h.equiv ((h.domChart.extend I) x, 0) := by
    simpa only [cod, Function.comp_apply, hsymm] using hwritten
  have hprojection : projection (cod (f x)) = (h.domChart.extend I) x := by
    simp only [projection, Function.comp_apply, hnormal,
      ContinuousLinearEquiv.symm_apply_apply]
  have hcod : CMDiffAt ∞ cod (f x) := by
    exact h.codChart.contMDiffAt_extend
      h.codChart_mem_maximalAtlas h.mem_codChart_source
  have hprojectionSmooth : CMDiffAt ∞ projection (cod (f x)) := by
    change CMDiffAt ∞ (fun z : E' ↦ (h.equiv.symm z).1) (cod (f x))
    rw [contMDiffAt_iff_contDiffAt]
    exact h.equiv.symm.contDiff.fst.contDiffAt
  have hprojectCod : CMDiffAt ∞ (projection ∘ cod) (f x) :=
    hprojectionSmooth.comp (f x) hcod
  have hdomOn : CMDiff[I '' h.domChart.target] ∞ domInv := by
    simpa only [domInv] using
      (contMDiffOn_extend_symm (I := I) h.domChart_mem_maximalAtlas)
  have hxImage : (h.domChart.extend I) x ∈ I '' h.domChart.target := by
    exact ⟨h.domChart x, h.domChart.map_source h.mem_domChart_source, rfl⟩
  have hopenImage : IsOpen (I '' h.domChart.target) :=
    I.toHomeomorph.isOpenMap _ h.domChart.open_target
  have hdom : CMDiffAt ∞ domInv ((h.domChart.extend I) x) :=
    hdomOn.contMDiffAt (hopenImage.mem_nhds hxImage)
  have hdomProjection : CMDiffAt ∞ domInv (projection (cod (f x))) := by
    rw [hprojection]
    exact hdom
  have hresult := hdomProjection.comp (f x) hprojectCod
  simpa only [immersionChartRetractionAt, cod, projection, domInv,
    Function.comp_assoc] using hresult

noncomputable def immersionChartScalarExtensionAt
    (h : Manifold.IsImmersionAt I I' ∞ f x) : (M → ℝ) →ₗ[ℝ] (N → ℝ) where
  toFun scalar := scalar ∘ immersionChartRetractionAt h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [I.Boundaryless] [IsManifold I ∞ M]
  [I'.Boundaryless] [IsManifold I' ∞ N] in
theorem immersionChartScalarExtensionAt_comp_eventuallyEq
    (h : Manifold.IsImmersionAt I I' ∞ f x) (scalar : M → ℝ) :
    immersionChartScalarExtensionAt h scalar ∘ f =ᶠ[nhds x] scalar := by
  filter_upwards [immersionChartRetractionAt_comp_eventuallyEq_id h] with y hy
  change scalar (immersionChartRetractionAt h (f y)) = scalar y
  rw [show immersionChartRetractionAt h (f y) = y by simpa using hy]

omit [IsManifold I ∞ M] [I'.Boundaryless] [IsManifold I' ∞ N] in
theorem immersionChartScalarExtensionAt_contMDiffAt
    (h : Manifold.IsImmersionAt I I' ∞ f x) {n : ℕ∞ω}
    (hn : n ≤ (∞ : ℕ∞ω))
    {scalar : M → ℝ} (hscalar : CMDiffAt n scalar x) :
    CMDiffAt n (immersionChartScalarExtensionAt h scalar) (f x) := by
  have hretraction : CMDiffAt n (immersionChartRetractionAt h) (f x) :=
    (immersionChartRetractionAt_contMDiffAt h).of_le hn
  have hscalarAt : CMDiffAt n scalar (immersionChartRetractionAt h (f x)) := by
    rw [immersionChartRetractionAt_apply_image_self h]
    exact hscalar
  exact hscalarAt.comp (f x) hretraction

noncomputable def immersionChartAlongExtensionAt
    (h : Manifold.IsImmersionAt I I' ∞ f x) :
    ((q : M) → TangentSpace I' (f q)) →ₗ[ℝ] ((y : N) → TangentSpace I' y) where
  toFun field y :=
    let retraction := immersionChartRetractionAt h
    let trivialization := trivializationAt E' (TangentSpace I' : N → Type _) (f x)
    trivialization.symmL ℝ y
      (trivialization.continuousLinearMapAt ℝ (f (retraction y)) (field (retraction y)))
  map_add' first second := by
    funext y
    simp only [Pi.add_apply, map_add]
  map_smul' scalar field := by
    funext y
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]

omit [I.Boundaryless] [IsManifold I ∞ M] [I'.Boundaryless] in
theorem immersionChartAlongExtensionAt_apply_image_self
    (h : Manifold.IsImmersionAt I I' ∞ f x)
    (field : (q : M) → TangentSpace I' (f q)) :
    immersionChartAlongExtensionAt h field (f x) = field x := by
  let trivialization := trivializationAt E' (TangentSpace I' : N → Type _) (f x)
  change trivialization.symmL ℝ (f x)
      (trivialization.continuousLinearMapAt ℝ
        (f (immersionChartRetractionAt h (f x)))
        (field (immersionChartRetractionAt h (f x)))) = field x
  rw [immersionChartRetractionAt_apply_image_self h]
  exact trivialization.symmL_continuousLinearMapAt
    (mem_baseSet_trivializationAt E' (TangentSpace I' : N → Type _) (f x)) (field x)

omit [I.Boundaryless] [IsManifold I ∞ M] [I'.Boundaryless] in
theorem immersionChartAlongExtensionAt_comp_eventuallyEq
    (h : Manifold.IsImmersionAt I I' ∞ f x)
    (field : (q : M) → TangentSpace I' (f q)) :
    immersionChartAlongExtensionAt h field ∘ f =ᶠ[nhds x] field := by
  let trivialization := trivializationAt E' (TangentSpace I' : N → Type _) (f x)
  have hbase : ∀ᶠ q in nhds x, f q ∈ trivialization.baseSet :=
    h.continuousAt.eventually
      (trivialization.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E' (TangentSpace I' : N → Type _) (f x)))
  filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source, hbase] with q hq hqbase
  change trivialization.symmL ℝ (f q)
      (trivialization.continuousLinearMapAt ℝ
        (f (immersionChartRetractionAt h (f q)))
        (field (immersionChartRetractionAt h (f q)))) = field q
  rw [immersionChartRetractionAt_apply_image h hq]
  exact trivialization.symmL_continuousLinearMapAt hqbase (field q)

noncomputable def immersionChartTangentExtensionAt
    (h : Manifold.IsImmersionAt I I' ∞ f x) :
    ((q : M) → TangentSpace I q) →ₗ[ℝ] ((y : N) → TangentSpace I' y) where
  toFun field := immersionChartAlongExtensionAt h
    (fun q ↦ mfderiv I I' f q (field q))
  map_add' first second := by
    have hfields :
        (fun q ↦ mfderiv I I' f q ((first + second) q)) =
          (fun q ↦ mfderiv I I' f q (first q)) +
            fun q ↦ mfderiv I I' f q (second q) := by
      funext q
      simp
    rw [hfields, map_add]
  map_smul' scalar field := by
    have hfields :
        (fun q ↦ mfderiv I I' f q ((scalar • field) q)) =
          scalar • fun q ↦ mfderiv I I' f q (field q) := by
      funext q
      simp
    rw [hfields, map_smul]
    rfl

omit [I.Boundaryless] [IsManifold I ∞ M] [I'.Boundaryless] in
theorem immersionChartTangentExtensionAt_comp_eventuallyEq
    (h : Manifold.IsImmersionAt I I' ∞ f x)
    (field : (q : M) → TangentSpace I q) :
    immersionChartTangentExtensionAt h field ∘ f =ᶠ[nhds x]
      fun q ↦ mfderiv I I' f q (field q) := by
  change immersionChartAlongExtensionAt h
      (fun q ↦ mfderiv I I' f q (field q)) ∘ f =ᶠ[nhds x]
    fun q ↦ mfderiv I I' f q (field q)
  exact immersionChartAlongExtensionAt_comp_eventuallyEq h _

omit [I.Boundaryless] [IsManifold I ∞ M] [I'.Boundaryless] in
theorem immersionChartTangentExtensionAt_smul
    (h : Manifold.IsImmersionAt I I' ∞ f x)
    (scalar : M → ℝ) (field : (q : M) → TangentSpace I q) :
    immersionChartTangentExtensionAt h (scalar • field) =
      immersionChartScalarExtensionAt h scalar •
        immersionChartTangentExtensionAt h field := by
  funext y
  let retraction := immersionChartRetractionAt h
  let trivialization := trivializationAt E' (TangentSpace I' : N → Type _) (f x)
  change trivialization.symmL ℝ y
      (trivialization.continuousLinearMapAt ℝ (f (retraction y))
        (mfderiv I I' f (retraction y) (scalar (retraction y) • field (retraction y)))) =
    scalar (retraction y) •
      trivialization.symmL ℝ y
        (trivialization.continuousLinearMapAt ℝ (f (retraction y))
          (mfderiv I I' f (retraction y) (field (retraction y))))
  simp only [map_smul]

omit [IsManifold I ∞ M] [I'.Boundaryless] in
theorem immersionChartAlongExtensionAt_contMDiffAt
    (h : Manifold.IsImmersionAt I I' ∞ f x) {n : ℕ∞ω}
    (hn : n ≤ (∞ : ℕ∞ω))
    {field : (q : M) → TangentSpace I' (f q)}
    (hfield : CMDiffAt n
      (fun q ↦ (⟨f q, field q⟩ : TangentBundle I' N)) x) :
    CMDiffAt n (T% (immersionChartAlongExtensionAt h field)) (f x) := by
  letI : ContMDiffVectorBundle n E' (TangentSpace I' : N → Type _) I' :=
    ContMDiffVectorBundle.of_le hn
  let retraction := immersionChartRetractionAt h
  let trivialization := trivializationAt E' (TangentSpace I' : N → Type _) (f x)
  let along : M → TangentBundle I' N :=
    fun q ↦ ⟨f q, field q⟩
  let input : N → TangentBundle I' N := along ∘ retraction
  have hretraction : CMDiffAt n retraction (f x) :=
    (immersionChartRetractionAt_contMDiffAt h).of_le hn
  have hfieldAt : CMDiffAt n along (retraction (f x)) := by
    rw [show retraction (f x) = x by
      exact immersionChartRetractionAt_apply_image_self h]
    exact hfield
  have hinput : CMDiffAt n input (f x) :=
    hfieldAt.comp (f x) hretraction
  have hinputProj : (input (f x)).proj = f x := by
    simp only [input, along, retraction, Function.comp_apply,
      immersionChartRetractionAt_apply_image_self]
  have hinputMem : input (f x) ∈ trivialization.source := by
    rw [trivialization.mem_source]
    rw [hinputProj]
    exact mem_baseSet_trivializationAt E' (TangentSpace I' : N → Type _) (f x)
  have hcoordinatesRaw : CMDiffAt n (fun y ↦ (trivialization (input y)).2) (f x) :=
    ((trivialization.contMDiffAt_iff hinputMem).mp hinput).2
  let coordinate : N → E' := fun y ↦
    trivialization.continuousLinearMapAt ℝ (f (retraction y)) (field (retraction y))
  have hprojSmooth : CMDiffAt n (fun y ↦ (input y).proj) (f x) :=
    (Bundle.contMDiffAt_totalSpace.mp hinput).1
  have hbase : ∀ᶠ y in nhds (f x), (input y).proj ∈ trivialization.baseSet := by
    apply hprojSmooth.continuousAt
    change trivialization.baseSet ∈ nhds ((input (f x)).proj)
    rw [hinputProj]
    exact trivialization.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E' (TangentSpace I' : N → Type _) (f x))
  have hcoordinateEq : coordinate =ᶠ[nhds (f x)]
      fun y ↦ (trivialization (input y)).2 := by
    filter_upwards [hbase] with y hy
    change trivialization.continuousLinearMapAt ℝ (f (retraction y))
        (field (retraction y)) =
      (trivialization
        (⟨f (retraction y), field (retraction y)⟩ : TangentBundle I' N)).2
    exact trivialization.continuousLinearMapAt_apply_of_mem ℝ hy
      (field (retraction y))
  have hcoordinate : CMDiffAt n coordinate (f x) :=
    hcoordinatesRaw.congr_of_eventuallyEq hcoordinateEq
  rw [Bundle.contMDiffAt_section]
  apply hcoordinate.congr_of_eventuallyEq
  filter_upwards [trivialization.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E' (TangentSpace I' : N → Type _) (f x))] with y hy
  change (trivialization
      (⟨y, trivialization.symmL ℝ y (coordinate y)⟩ : TangentBundle I' N)).2 =
    coordinate y
  rw [← trivialization.continuousLinearMapAt_apply_of_mem ℝ hy]
  exact trivialization.continuousLinearMapAt_symmL hy (coordinate y)

omit [I'.Boundaryless] in
theorem immersionChartTangentExtensionAt_contMDiffAt
    (h : Manifold.IsImmersionAt I I' ∞ f x)
    (hf : CMDiff ∞ f) {n : ℕ∞ω}
    (hn : n ≤ (∞ : ℕ∞ω))
    {field : (q : M) → TangentSpace I q}
    (hfield : CMDiffAt n (T% field) x) :
    CMDiffAt n (T% (immersionChartTangentExtensionAt h field)) (f x) := by
  have htangentMap : CMDiff n (tangentMap I I' f) :=
    hf.contMDiff_tangentMap (m := n)
      (by
        calc
          n + 1 ≤ (∞ : ℕ∞ω) + 1 := by
            simpa [add_comm] using add_le_add_right hn 1
          _ = ∞ := ENat.coe_top_add_one)
  have halong : CMDiffAt n
      (fun q ↦
        (⟨f q, mfderiv I I' f q (field q)⟩ : TangentBundle I' N)) x := by
    have hcomp := htangentMap.contMDiffAt.comp x hfield
    change CMDiffAt n
      (fun q ↦
        (⟨f q, mfderiv I I' f q (field q)⟩ : TangentBundle I' N)) x at hcomp
    exact hcomp
  exact immersionChartAlongExtensionAt_contMDiffAt h hn halong

omit [IsManifold I ∞ M] [I'.Boundaryless] [IsManifold I' ∞ N] in
/-- The scalar extension through an immersion chart preserves pointwise differentiability. -/
theorem immersionChartScalarExtensionAt_mdifferentiableAt
    (h : Manifold.IsImmersionAt I I' ∞ f x)
    {scalar : M → ℝ} (hscalar : MDiffAt scalar x) :
    MDiffAt (immersionChartScalarExtensionAt h scalar) (f x) := by
  have hretraction : MDiffAt (immersionChartRetractionAt h) (f x) :=
    (immersionChartRetractionAt_contMDiffAt h).mdifferentiableAt (by simp)
  have hscalarAt : MDiffAt scalar (immersionChartRetractionAt h (f x)) := by
    rw [immersionChartRetractionAt_apply_image_self h]
    exact hscalar
  exact hscalarAt.comp (f x) hretraction

omit [IsManifold I ∞ M] [I'.Boundaryless] in
/-- The arbitrary field-along extension through an immersion chart preserves pointwise
differentiability. -/
theorem immersionChartAlongExtensionAt_mdifferentiableAt
    (h : Manifold.IsImmersionAt I I' ∞ f x)
    {field : (q : M) → TangentSpace I' (f q)}
    (hfield : MDiffAt
      (fun q ↦ (⟨f q, field q⟩ : TangentBundle I' N)) x) :
    MDiffAt (T% (immersionChartAlongExtensionAt h field)) (f x) := by
  let retraction := immersionChartRetractionAt h
  let trivialization := trivializationAt E' (TangentSpace I' : N → Type _) (f x)
  let along : M → TangentBundle I' N := fun q ↦ ⟨f q, field q⟩
  let input : N → TangentBundle I' N := along ∘ retraction
  have hretraction : MDiffAt retraction (f x) :=
    (immersionChartRetractionAt_contMDiffAt h).mdifferentiableAt (by simp)
  have hfieldAt : MDiffAt along (retraction (f x)) := by
    rw [show retraction (f x) = x by
      exact immersionChartRetractionAt_apply_image_self h]
    exact hfield
  have hinput : MDiffAt input (f x) := hfieldAt.comp (f x) hretraction
  have hinputProj : (input (f x)).proj = f x := by
    simp only [input, along, retraction, Function.comp_apply,
      immersionChartRetractionAt_apply_image_self]
  have hcoordinatesRaw : MDiffAt
      (fun y ↦ (trivialization (input y)).2) (f x) := by
    have hcoordinates := (mdifferentiableAt_totalSpace I' _ |>.mp hinput).2
    rw [hinputProj] at hcoordinates
    exact hcoordinates
  let coordinate : N → E' := fun y ↦
    trivialization.continuousLinearMapAt ℝ (f (retraction y)) (field (retraction y))
  have hprojSmooth : MDiffAt (fun y ↦ (input y).proj) (f x) :=
    (mdifferentiableAt_totalSpace I' _ |>.mp hinput).1
  have hbase : ∀ᶠ y in nhds (f x), (input y).proj ∈ trivialization.baseSet := by
    apply hprojSmooth.continuousAt
    change trivialization.baseSet ∈ nhds ((input (f x)).proj)
    rw [hinputProj]
    exact trivialization.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E' (TangentSpace I' : N → Type _) (f x))
  have hcoordinateEq : coordinate =ᶠ[nhds (f x)]
      fun y ↦ (trivialization (input y)).2 := by
    filter_upwards [hbase] with y hy
    change trivialization.continuousLinearMapAt ℝ (f (retraction y))
        (field (retraction y)) =
      (trivialization
        (⟨f (retraction y), field (retraction y)⟩ : TangentBundle I' N)).2
    exact trivialization.continuousLinearMapAt_apply_of_mem ℝ hy
      (field (retraction y))
  have hcoordinate : MDiffAt coordinate (f x) :=
    hcoordinatesRaw.congr_of_eventuallyEq hcoordinateEq
  rw [mdifferentiableAt_section]
  apply hcoordinate.congr_of_eventuallyEq
  filter_upwards [trivialization.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E' (TangentSpace I' : N → Type _) (f x))] with y hy
  change (trivialization
      (⟨y, trivialization.symmL ℝ y (coordinate y)⟩ : TangentBundle I' N)).2 =
    coordinate y
  rw [← trivialization.continuousLinearMapAt_apply_of_mem ℝ hy]
  exact trivialization.continuousLinearMapAt_symmL hy (coordinate y)

omit [I'.Boundaryless] in
/-- The tangent extension through an immersion chart preserves pointwise differentiability. -/
theorem immersionChartTangentExtensionAt_mdifferentiableAt
    (h : Manifold.IsImmersionAt I I' ∞ f x)
    (hf : CMDiff ∞ f)
    {field : (q : M) → TangentSpace I q}
    (hfield : MDiffAt (T% field) x) :
    MDiffAt (T% (immersionChartTangentExtensionAt h field)) (f x) := by
  have htangentMap : CMDiff 1 (tangentMap I I' f) :=
    hf.contMDiff_tangentMap (m := 1) (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  have halong : MDiffAt
      (fun q ↦
        (⟨f q, mfderiv I I' f q (field q)⟩ : TangentBundle I' N)) x := by
    have hcomp := htangentMap.mdifferentiableAt one_ne_zero |>.comp x hfield
    change MDiffAt
      (fun q ↦
        (⟨f q, mfderiv I I' f q (field q)⟩ : TangentBundle I' N)) x at hcomp
    exact hcomp
  exact immersionChartAlongExtensionAt_mdifferentiableAt h halong

/-- Germ-local ambient extensions centered at one source point.  Agreement is asserted on a
neighborhood of the center, matching the local-extension scope used in submanifold formulas. -/
structure LocalSubmanifoldExtensionDataAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (x : M) where
  tangentExtension :
    ((q : M) → TangentSpace I q) →ₗ[ℝ] ((y : N) → TangentSpace I' y)
  alongExtension :
    AmbientVectorFieldAlong immersion →ₗ[ℝ] ((y : N) → TangentSpace I' y)
  scalarExtension : (M → ℝ) →ₗ[ℝ] (N → ℝ)
  tangentExtension_agrees : ∀ field,
    tangentExtension field ∘ immersion.toFun =ᶠ[nhds x]
      fun q ↦ mfderiv I I' immersion.toFun q (field q)
  alongExtension_agrees : ∀ field,
    alongExtension field ∘ immersion.toFun =ᶠ[nhds x] field
  scalarExtension_agrees : ∀ scalar,
    scalarExtension scalar ∘ immersion.toFun =ᶠ[nhds x] scalar
  tangentExtension_smul : ∀ scalar field,
    tangentExtension (scalar • field) =
      scalarExtension scalar • tangentExtension field
  tangentExtension_mdifferentiableAt : ∀ {field : (q : M) → TangentSpace I q},
    MDiffAt (T% field) x →
      MDiffAt (T% (tangentExtension field)) (immersion.toFun x)
  alongExtension_mdifferentiableAt : ∀ {field : AmbientVectorFieldAlong immersion},
    MDiffAt (fun q ↦
      (⟨immersion.toFun q, field q⟩ : TangentBundle I' N)) x →
      MDiffAt (T% (alongExtension field)) (immersion.toFun x)
  scalarExtension_mdifferentiableAt : ∀ {scalar : M → ℝ},
    MDiffAt scalar x → MDiffAt (scalarExtension scalar) (immersion.toFun x)
  tangentExtension_contMDiffAt : ∀ {n : ℕ∞ω}, n ≤ (∞ : ℕ∞ω) →
    ∀ {field : (q : M) → TangentSpace I q},
      CMDiffAt n (T% field) x →
        CMDiffAt n (T% (tangentExtension field)) (immersion.toFun x)
  alongExtension_contMDiffAt : ∀ {n : ℕ∞ω}, n ≤ (∞ : ℕ∞ω) →
    ∀ {field : AmbientVectorFieldAlong immersion},
      CMDiffAt n
        (fun q ↦ (⟨immersion.toFun q, field q⟩ : TangentBundle I' N)) x →
        CMDiffAt n (T% (alongExtension field)) (immersion.toFun x)
  scalarExtension_contMDiffAt : ∀ {n : ℕ∞ω}, n ≤ (∞ : ℕ∞ω) →
    ∀ {scalar : M → ℝ}, CMDiffAt n scalar x →
      CMDiffAt n (scalarExtension scalar) (immersion.toFun x)

/-- Mathlib's immersion normal-form charts construct the complete local extension package. -/
noncomputable def localSubmanifoldExtensionDataAtOfIsImmersion
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (x : M)
    (h : Manifold.IsImmersionAt I I' ∞ immersion.toFun x) :
    LocalSubmanifoldExtensionDataAt immersion x where
  tangentExtension := immersionChartTangentExtensionAt h
  alongExtension := immersionChartAlongExtensionAt h
  scalarExtension := immersionChartScalarExtensionAt h
  tangentExtension_agrees field :=
    immersionChartTangentExtensionAt_comp_eventuallyEq h field
  alongExtension_agrees field :=
    immersionChartAlongExtensionAt_comp_eventuallyEq h field
  scalarExtension_agrees scalar :=
    immersionChartScalarExtensionAt_comp_eventuallyEq h scalar
  tangentExtension_smul scalar field :=
    immersionChartTangentExtensionAt_smul h scalar field
  tangentExtension_mdifferentiableAt hfield :=
    immersionChartTangentExtensionAt_mdifferentiableAt h immersion.contMDiff hfield
  alongExtension_mdifferentiableAt hfield :=
    immersionChartAlongExtensionAt_mdifferentiableAt h hfield
  scalarExtension_mdifferentiableAt hscalar :=
    immersionChartScalarExtensionAt_mdifferentiableAt h hscalar
  tangentExtension_contMDiffAt := by
    intro n hn field hfield
    exact immersionChartTangentExtensionAt_contMDiffAt h immersion.contMDiff hn hfield
  alongExtension_contMDiffAt := by
    intro n hn field hfield
    exact immersionChartAlongExtensionAt_contMDiffAt h hn hfield
  scalarExtension_contMDiffAt := by
    intro n hn scalar hscalar
    exact immersionChartScalarExtensionAt_contMDiffAt h hn hscalar

namespace LocalSubmanifoldExtensionDataAt

variable
  {immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)}
  {x : M}

omit [I.Boundaryless] [I'.Boundaryless] in
theorem tangentExtension_agrees_at
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (field : (q : M) → TangentSpace I q) :
    extensions.tangentExtension field (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (field x) :=
  extensions.tangentExtension_agrees field |>.self_of_nhds

omit [I.Boundaryless] [I'.Boundaryless] in
theorem alongExtension_agrees_at
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (field : AmbientVectorFieldAlong immersion) :
    extensions.alongExtension field (immersion.toFun x) = field x :=
  extensions.alongExtension_agrees field |>.self_of_nhds

omit [I.Boundaryless] [I'.Boundaryless] in
theorem scalarExtension_agrees_at
    (extensions : LocalSubmanifoldExtensionDataAt immersion x)
    (scalar : M → ℝ) :
    extensions.scalarExtension scalar (immersion.toFun x) = scalar x :=
  extensions.scalarExtension_agrees scalar |>.self_of_nhds

end LocalSubmanifoldExtensionDataAt

namespace SmoothIsometricEmbeddingData

variable
  [RiemannianBundle (fun q : M => TangentSpace I q)]
  [RiemannianBundle (fun y : N => TangentSpace I' y)]

/-- Every smooth isometric embedding supplies the local extension package at each source point;
there is no caller-provided ambient-extension premise. -/
noncomputable def localSubmanifoldExtensionDataAt
    (embedding : RiemannianFluids.SmoothIsometricEmbeddingData
      (I := I) (I' := I') (M := M) (N := N))
    (x : M) : LocalSubmanifoldExtensionDataAt embedding.toSmoothImmersionData x :=
  localSubmanifoldExtensionDataAtOfIsImmersion embedding.toSmoothImmersionData x
    (embedding.isImmersionAt x)

end SmoothIsometricEmbeddingData

end

end RiemannianFluids
