import RiemannianFluids.Reproductions.CCD17.Section3

/-! # CCD17 Sections 4--5: restriction and relativistic limits -/

namespace RiemannianFluids

/-- Equations (4.3)--(4.10) in arXiv v1: projector, four-velocity, and thermodynamic nonrelativistic expansions. -/
@[proof_obligation]
theorem ccd17_relativistic_kinematic_expansions
    {Velocity Term : Type*}
    (data : CCD17RelativisticLimitData Velocity Term) :
    ∀ velocity,
      data.hasProjectorExpansion velocity ∧ data.hasFourVelocityExpansion velocity := by
  sorry

/-- Equations (4.11)--(4.16): Eckart's incompressible limit is divergence of twice the deformation tensor. -/
@[proof_obligation]
theorem ccd17_eckart_limit_equation_4_16
    {Velocity Term : Type*}
    (data : CCD17RelativisticLimitData Velocity Term) :
    ∀ velocity,
      data.hasProjectorExpansion velocity →
      data.hasFourVelocityExpansion velocity →
        data.hasIncompressibleLimit velocity ∧
        data.hasEckartLimitEquation4_16 velocity := by
  sorry

/-- Equations (4.17)--(4.18): Lichnerowicz's dynamic velocity reduces to the Eckart velocity. -/
@[proof_obligation]
theorem ccd17_lichnerowicz_enthalpy_limit
    {Velocity Term : Type*}
    (data : CCD17RelativisticLimitData Velocity Term) :
    ∀ velocity,
      data.hasLichnerowiczEnthalpyLimit velocity ∧
        data.nonrelativisticLimit .lichnerowicz velocity = data.deformationViscosity velocity := by
  have hKinematics := ccd17_relativistic_kinematic_expansions data
  have hEckart := fun velocity => ccd17_eckart_limit_equation_4_16 data velocity
    (hKinematics velocity).1 (hKinematics velocity).2
  sorry

/-- Equations (4.19)--(4.21): the Choquet--Bruhat shear term has the same spatial limit. -/
@[proof_obligation]
theorem ccd17_choquet_bruhat_shear_limit
    {Velocity Term : Type*}
    (data : CCD17RelativisticLimitData Velocity Term) :
    ∀ velocity,
      data.hasChoquetBruhatShearLimit velocity ∧
        data.nonrelativisticLimit .choquetBruhat velocity = data.deformationViscosity velocity := by
  have hKinematics := ccd17_relativistic_kinematic_expansions data
  have hEckart := fun velocity => ccd17_eckart_limit_equation_4_16 data velocity
    (hKinematics velocity).1 (hKinematics velocity).2
  sorry

/-- Freistuehler--Temple retains the same projected symmetric shear term in the limit. -/
@[proof_obligation]
theorem ccd17_freistuehler_temple_shear_limit
    {Velocity Term : Type*}
    (data : CCD17RelativisticLimitData Velocity Term) :
    ∀ velocity,
      data.hasFreistuehlerTempleShearLimit velocity ∧
        data.nonrelativisticLimit .freistuehlerTemple velocity = data.deformationViscosity velocity := by
  have hKinematics := ccd17_relativistic_kinematic_expansions data
  have hEckart := fun velocity => ccd17_eckart_limit_equation_4_16 data velocity
    (hKinematics velocity).1 (hKinematics velocity).2
  sorry

@[literature_terminal]
theorem ccd17_relativistic_models_have_deformation_limit
    {Velocity Term : Type*}
    (data : CCD17RelativisticLimitData Velocity Term) :
    ccd17RelativisticLimitStatement data := by
  intro model velocity
  cases model with
  | lichnerowicz => exact (ccd17_lichnerowicz_enthalpy_limit data velocity).2
  | choquetBruhat => exact (ccd17_choquet_bruhat_shear_limit data velocity).2
  | freistuehlerTemple => exact (ccd17_freistuehler_temple_shear_limit data velocity).2


end RiemannianFluids
