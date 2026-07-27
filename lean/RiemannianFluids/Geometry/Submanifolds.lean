import Mathlib.Algebra.Module.Basic

/-!
# Embedded-submanifold geometry interfaces

These are the foundational definitions shared by CCG25, CCF25, CCY23, and WBS26.  They keep
the tangential and normal connections, second fundamental form, Weingarten maps, and
mean-curvature vector distinct; arbitrary codimension must not be silently reduced to a
hypersurface with one preferred normal.
-/

namespace RiemannianFluids

/-- Pointwise splitting and the two induced connections for an embedded submanifold. -/
structure SubmanifoldConnectionData
    (AmbientVector TangentVector NormalVector : Type*) where
  tangentProjection : AmbientVector → TangentVector
  normalProjection : AmbientVector → NormalVector
  tangentInclusion : TangentVector → AmbientVector
  normalInclusion : NormalVector → AmbientVector
  intrinsicDerivative : TangentVector → TangentVector → TangentVector
  normalDerivative : TangentVector → NormalVector → NormalVector
  ambientDerivativeTT : TangentVector → TangentVector → AmbientVector
  ambientDerivativeTN : TangentVector → NormalVector → AmbientVector

/-- The Gauss and Weingarten definitions, before curvature identities are invoked. -/
structure SecondFundamentalFormData
    (TangentVector NormalVector : Type*) where
  secondFundamentalForm : TangentVector → TangentVector → NormalVector
  shapeOperator : NormalVector → TangentVector → TangentVector
  meanCurvatureVector : NormalVector
  isSymmetric : Prop
  shapeSecondFundamentalAdjoint : Prop

/-- Gauss' formula splits an ambient tangential derivative into intrinsic and normal parts. -/
def HasGaussFormula
    {AmbientVector TangentVector NormalVector : Type*}
    [AddCommGroup AmbientVector]
    (connection : SubmanifoldConnectionData AmbientVector TangentVector NormalVector)
    (geometry : SecondFundamentalFormData TangentVector NormalVector) : Prop :=
  ∀ X Y,
    connection.ambientDerivativeTT X Y =
      connection.tangentInclusion (connection.intrinsicDerivative X Y) +
        connection.normalInclusion (geometry.secondFundamentalForm X Y)

/-- Weingarten's formula records the tangential shape term and normal connection term. -/
def HasWeingartenFormula
    {AmbientVector TangentVector NormalVector : Type*}
    [AddCommGroup AmbientVector]
    (connection : SubmanifoldConnectionData AmbientVector TangentVector NormalVector)
    (geometry : SecondFundamentalFormData TangentVector NormalVector) : Prop :=
  ∀ X normal,
    connection.ambientDerivativeTN X normal =
      -connection.tangentInclusion (geometry.shapeOperator normal X) +
        connection.normalInclusion (connection.normalDerivative X normal)

/-- The contracted Codazzi identity used in CCG25 Corollary 1.7. -/
structure ContractedCodazziData (TangentVector NormalVector : Type*) where
  traceDerivativeSecondFundamental : TangentVector → NormalVector
  meanCurvatureNormalDerivative : TangentVector → NormalVector
  ambientCurvatureNormalTrace : TangentVector → NormalVector

def HasContractedCodazziIdentity
    {TangentVector NormalVector : Type*} [AddCommGroup NormalVector]
    (data : ContractedCodazziData TangentVector NormalVector) : Prop :=
  ∀ v,
    data.traceDerivativeSecondFundamental v =
      data.meanCurvatureNormalDerivative v + data.ambientCurvatureNormalTrace v

end RiemannianFluids
