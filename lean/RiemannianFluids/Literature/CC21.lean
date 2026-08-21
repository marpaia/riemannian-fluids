import RiemannianFluids.Geometry.SpaceForms
import RiemannianFluids.PDE.Stationary

/-!
# CC21: exterior stationary flows on the hyperbolic plane

The source constructs particular Stokes and Navier--Stokes witnesses and then proves that those
same witnesses are not harmonic potential flows.  Recording the witnesses as data keeps the two
existence/nonpotential obligation pairs linked without storing any conclusion as a field.
-/

namespace RiemannianFluids.Literature.CC21

/-- Observable exterior-domain realization and the two velocities constructed in CC21. -/
structure ExteriorFlowData (Velocity Pressure Potential : Type*) where
  exteriorRadius : ℝ
  framework : StationaryFlowFramework Velocity Pressure
  isHarmonicPotential : Potential → Prop
  differential : Potential → Velocity
  constructedStokesVelocity : Velocity
  constructedStokesPressure : Pressure
  constructedNavierStokesVelocity : Velocity
  constructedNavierStokesPressure : Pressure

/-- A velocity is the differential of a harmonic potential in the source sense. -/
def IsHarmonicPotentialFlow
    {Velocity Pressure Potential : Type*}
    (data : ExteriorFlowData Velocity Pressure Potential) (velocity : Velocity) : Prop :=
  ∃ potential,
    data.isHarmonicPotential potential ∧ data.differential potential = velocity

/-- Source signature for CC21 Theorem 1.2 on the exterior domain `Omega(R0)`. -/
def nontrivial_stokes_exterior_existence_statement
    {Point Velocity Pressure Potential : Type*}
    (geometry : RiemannianGeometryProfile Point)
    (data : ExteriorFlowData Velocity Pressure Potential)
    (radius scale : ℝ) : Prop :=
  IsHyperbolicSpaceForm geometry 2 scale →
    0 < radius →
      data.exteriorRadius = radius →
        IsStationaryStokesSolution data.framework
          data.constructedStokesVelocity data.constructedStokesPressure ∧
          data.framework.isNontrivial data.constructedStokesVelocity

/-- Source signature for Theorem 1.4 applied to the Stokes witness of Theorem 1.2. -/
def nontrivial_stokes_exterior_nonpotential_statement
    {Point Velocity Pressure Potential : Type*}
    (geometry : RiemannianGeometryProfile Point)
    (data : ExteriorFlowData Velocity Pressure Potential)
    (radius scale : ℝ) : Prop :=
  IsHyperbolicSpaceForm geometry 2 scale →
    0 < radius →
      data.exteriorRadius = radius →
        IsStationaryStokesSolution data.framework
          data.constructedStokesVelocity data.constructedStokesPressure →
          data.framework.isNontrivial data.constructedStokesVelocity →
            ¬ IsHarmonicPotentialFlow data data.constructedStokesVelocity

/-- Source signature for CC21 Theorem 1.3 on the exterior domain `Omega(R0)`. -/
def nontrivial_navier_stokes_exterior_existence_statement
    {Point Velocity Pressure Potential : Type*}
    (geometry : RiemannianGeometryProfile Point)
    (data : ExteriorFlowData Velocity Pressure Potential)
    (radius scale : ℝ) : Prop :=
  IsHyperbolicSpaceForm geometry 2 scale →
    0 < radius →
      data.exteriorRadius = radius →
        IsStationaryNavierStokesSolution data.framework
          data.constructedNavierStokesVelocity data.constructedNavierStokesPressure ∧
          data.framework.isNontrivial data.constructedNavierStokesVelocity

/-- Source signature for Theorem 1.4 applied to the Navier--Stokes witness of Theorem 1.3. -/
def nontrivial_navier_stokes_exterior_nonpotential_statement
    {Point Velocity Pressure Potential : Type*}
    (geometry : RiemannianGeometryProfile Point)
    (data : ExteriorFlowData Velocity Pressure Potential)
    (radius scale : ℝ) : Prop :=
  IsHyperbolicSpaceForm geometry 2 scale →
    0 < radius →
      data.exteriorRadius = radius →
        IsStationaryNavierStokesSolution data.framework
          data.constructedNavierStokesVelocity data.constructedNavierStokesPressure →
          data.framework.isNontrivial data.constructedNavierStokesVelocity →
            ¬ IsHarmonicPotentialFlow data data.constructedNavierStokesVelocity

end RiemannianFluids.Literature.CC21
