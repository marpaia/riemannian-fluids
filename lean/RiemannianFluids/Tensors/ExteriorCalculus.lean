import Mathlib.Data.Real.Basic

/-! # Graded exterior calculus

This module is the permanent leaf API for the degree-indexed de Rham operations needed by
CCD17 and CCP25.  Degree-one `d` and degree-two `d*` must be constructed here rather than
passed downstream as an already-combined Hodge Laplacian.
-/

namespace RiemannianFluids

/-- Degree-indexed exterior derivative, codifferential, Hodge star, and `L2` pairing. -/
structure ExteriorCalculusData (dimension : ℕ) (Form : ℕ → Type*) where
  exterior : ∀ degree, Form degree → Form (degree + 1)
  codifferential : ∀ degree, Form (degree + 1) → Form degree
  hodgeStar : ∀ degree, Form degree → Form (dimension - degree)
  l2Pairing : ∀ degree, Form degree → Form degree → ℝ

/-- The degree-`k` de Rham relation `d_(k+1) d_k = 0`. -/
def ExteriorDerivativeSquaresToZero
    {dimension : ℕ} {Form : ℕ → Type*}
    [∀ degree, Zero (Form degree)]
    (data : ExteriorCalculusData dimension Form) : Prop :=
  ∀ degree form, data.exterior (degree + 1) (data.exterior degree form) = 0

/-- Formal adjointness of `d_k` and `d*_(k+1)` on the compactly supported core. -/
def ExteriorCodifferentialAdjoint
    {dimension : ℕ} {Form : ℕ → Type*}
    (data : ExteriorCalculusData dimension Form)
    (isCompactlySupported : ∀ degree, Form degree → Prop) : Prop :=
  ∀ degree alpha beta,
    isCompactlySupported degree alpha →
    isCompactlySupported (degree + 1) beta →
      data.l2Pairing (degree + 1) (data.exterior degree alpha) beta =
        data.l2Pairing degree alpha (data.codifferential degree beta)

/-- The analysis-positive Hodge Laplacian at degree `k`. -/
structure HodgeLaplacianData (Form : ℕ → Type*) where
  hodgeLaplacian : ∀ degree, Form degree → Form degree
  exactHalf : ∀ degree, Form degree → Form degree
  coexactHalf : ∀ degree, Form degree → Form degree

/-- `L_Hodge = d d* + d* d`, with endpoint degrees handled by the supplied zero maps. -/
def HasHodgeLaplacianDecomposition
    {Form : ℕ → Type*} [∀ degree, AddCommGroup (Form degree)]
    (data : HodgeLaplacianData Form) : Prop :=
  ∀ degree form,
    data.hodgeLaplacian degree form =
      data.exactHalf degree form + data.coexactHalf degree form

end RiemannianFluids
