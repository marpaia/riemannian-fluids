import RiemannianFluids.Reproductions.CCY23.Section2

/-! # CCY23 Section 4: ambient divergence-free extension -/

namespace RiemannianFluids

/-- Equation (4.6): integration of the radial divergence ODE with zero trace on the ellipsoid. -/
@[proof_obligation]
theorem ccy23_equation_4_6_radial_extension
    {SurfaceField AmbientField : Type*}
    (data : CCY23DivergenceFreeExtensionData SurfaceField AmbientField)
    (ha : 0 < data.axisScale) :
    ∀ field,
      data.isSmoothSurfaceField field →
      data.isIntrinsicallyDivergenceFree field →
        data.radialComponentSolvesEquation4_6 (data.ambientExtension field) := by
  sorry

/-- Section 4: the field from equation (4.6) has all four required extension properties. -/
@[proof_obligation]
theorem ccy23_section_4_extension_properties
    {SurfaceField AmbientField : Type*}
    (data : CCY23DivergenceFreeExtensionData SurfaceField AmbientField) :
    ∀ field,
      data.isSmoothSurfaceField field →
      data.isIntrinsicallyDivergenceFree field →
      data.radialComponentSolvesEquation4_6 (data.ambientExtension field) →
        data.isSmoothAmbientField (data.ambientExtension field) ∧
          data.restrictsTo (data.ambientExtension field) field ∧
          data.isTangentialOnEllipsoid (data.ambientExtension field) ∧
          data.isAmbientDivergenceFree (data.ambientExtension field) := by
  sorry

@[literature_terminal]
theorem ccy23_section_4_double_divergence_free_extension
    {SurfaceField AmbientField : Type*}
    (data : CCY23DivergenceFreeExtensionData SurfaceField AmbientField) :
    ccy23DivergenceFreeExtensionStatement data := by
  intro ha
  intro field hSmooth hDiv
  have hODE := ccy23_equation_4_6_radial_extension data ha field hSmooth hDiv
  have hProperties := ccy23_section_4_extension_properties data field hSmooth hDiv hODE
  exact ⟨hProperties.1, hProperties.2.1, hProperties.2.2.1, hProperties.2.2.2, hODE⟩


end RiemannianFluids
