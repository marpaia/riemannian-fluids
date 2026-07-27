import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

/-! # Curvature tensors and contractions -/

namespace RiemannianFluids

/-- Curvature, Ricci contraction, scalar curvature, and sectional curvature as distinct observables. -/
structure CurvatureData (Vector : Type*) where
  riemann : Vector → Vector → Vector → Vector
  ricciAction : Vector → Vector
  scalarCurvature : ℝ
  sectionalCurvature : Vector → Vector → ℝ

/-- The curvature commutator convention used in CCD17 and CCG25. -/
structure CurvatureCommutatorData (Derivative Vector : Type*) where
  firstThenSecond : Vector → Vector → Vector → Derivative
  secondThenFirst : Vector → Vector → Vector → Derivative
  bracketDerivative : Vector → Vector → Vector → Derivative
  curvatureAction : Vector → Vector → Vector → Derivative

def HasCurvatureCommutator
    {Derivative Vector : Type*} [AddCommGroup Derivative]
    (data : CurvatureCommutatorData Derivative Vector) : Prop :=
  ∀ X Y Z,
    data.firstThenSecond X Y Z - data.secondThenFirst X Y Z -
        data.bracketDerivative X Y Z = data.curvatureAction X Y Z

/-- Constant sectional curvature `K` in arbitrary dimension. -/
def HasConstantSectionalCurvature
    {Vector : Type*} (data : CurvatureData Vector) (K : ℝ) : Prop :=
  ∀ X Y, data.sectionalCurvature X Y = K

/-- In dimension two, the Ricci endomorphism is multiplication by Gaussian curvature. -/
structure SurfaceRicciData (Vector : Type*) where
  gaussianCurvature : ℝ
  ricciAction : Vector → Vector

def HasSurfaceRicciIdentity
    {Vector : Type*} [AddCommGroup Vector] [Module ℝ Vector]
    (data : SurfaceRicciData Vector) : Prop :=
  ∀ vector, data.ricciAction vector = data.gaussianCurvature • vector

end RiemannianFluids
