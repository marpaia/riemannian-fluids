import Mathlib.Algebra.Group.Defs

/-!
# Sobolev Hodge-decomposition contracts

The predicates below separate the three closed `H^1` summands from the theorem asserting
that they span uniquely and orthogonally.  This is the abstraction boundary needed before the
concrete Sobolev spaces and closed-range arguments are implemented.
-/

namespace RiemannianFluids

/-- One proposed exact/coexact/harmonic decomposition of a form. -/
structure HodgePieces (Form : Type*) where
  exactPart : Form
  coexactPart : Form
  harmonicPart : Form

/-- Observable subspaces and the `H^1` orthogonality relation for a fixed form degree. -/
structure H1HodgeData (Form : Type*) where
  isExactClosure : Form → Prop
  isCoexactClosure : Form → Prop
  isL2Harmonic : Form → Prop
  h1Orthogonal : Form → Form → Prop

/-- A valid, pairwise `H^1`-orthogonal decomposition of `alpha`. -/
def IsH1HodgeDecomposition
    {Form : Type*} [AddCommGroup Form]
    (data : H1HodgeData Form) (alpha : Form) (pieces : HodgePieces Form) : Prop :=
  data.isExactClosure pieces.exactPart ∧
    data.isCoexactClosure pieces.coexactPart ∧
    data.isL2Harmonic pieces.harmonicPart ∧
    alpha = pieces.exactPart + pieces.coexactPart + pieces.harmonicPart ∧
    data.h1Orthogonal pieces.exactPart pieces.coexactPart ∧
    data.h1Orthogonal pieces.exactPart pieces.harmonicPart ∧
    data.h1Orthogonal pieces.coexactPart pieces.harmonicPart

/-- Existence and uniqueness of the three Hodge components. -/
def HasH1HodgeDecomposition
    {Form : Type*} [AddCommGroup Form] (data : H1HodgeData Form) : Prop :=
  ∀ alpha : Form,
    ∃ pieces : HodgePieces Form,
      IsH1HodgeDecomposition data alpha pieces ∧
        ∀ other : HodgePieces Form,
          IsH1HodgeDecomposition data alpha other → other = pieces

end RiemannianFluids
