import RiemannianFluids.FunctionSpaces.HodgeDecomposition
import RiemannianFluids.ProofStatus

/-!
# Project FEEC gate associated with CCP25

This is deliberately outside `Reproductions.CCP25`: the discrete realization is a project
validation target, not a theorem or proof step in Chan--Czubak--Pinilla Suarez.
-/

namespace RiemannianFluids

/-- Observable exact/coexact/harmonic components in a discrete de Rham realization. -/
structure CCP25DiscreteHodgeData (Cochain : Type*) where
  isDiscreteExact : Cochain → Prop
  isDiscreteCoexact : Cochain → Prop
  isDiscreteHarmonic : Cochain → Prop

/-- One discrete exact/coexact/harmonic splitting of a cochain. -/
def IsCCP25DiscreteHodgeDecomposition
    {Cochain : Type*} [AddCommGroup Cochain]
    (data : CCP25DiscreteHodgeData Cochain)
    (cochain : Cochain) (pieces : HodgePieces Cochain) : Prop :=
  data.isDiscreteExact pieces.exactPart ∧
    data.isDiscreteCoexact pieces.coexactPart ∧
    data.isDiscreteHarmonic pieces.harmonicPart ∧
    cochain = pieces.exactPart + pieces.coexactPart + pieces.harmonicPart

/-- The discrete gate requires a unique three-component decomposition. -/
def ccp25DiscreteHodgeGateStatement
    {Cochain : Type*} [AddCommGroup Cochain]
    (data : CCP25DiscreteHodgeData Cochain) : Prop :=
  ∀ cochain,
    ∃ pieces : HodgePieces Cochain,
      IsCCP25DiscreteHodgeDecomposition data cochain pieces ∧
        ∀ other : HodgePieces Cochain,
          IsCCP25DiscreteHodgeDecomposition data cochain other →
            other = pieces

/-- Project FEEC gate: a mesh realization supplies exact, coexact, and harmonic pieces. -/
@[proof_obligation]
theorem ccp25_discrete_hodge_pieces_exist
    {Cochain : Type*} [AddCommGroup Cochain]
    (data : CCP25DiscreteHodgeData Cochain) :
    ∀ cochain,
      ∃ pieces : HodgePieces Cochain,
        IsCCP25DiscreteHodgeDecomposition data cochain pieces := by
  sorry

/-- Project FEEC gate: independence of the summands makes the pieces unique. -/
@[proof_obligation]
theorem ccp25_discrete_hodge_pieces_unique
    {Cochain : Type*} [AddCommGroup Cochain]
    (data : CCP25DiscreteHodgeData Cochain) :
    ∀ cochain first second,
      IsCCP25DiscreteHodgeDecomposition data cochain first →
      IsCCP25DiscreteHodgeDecomposition data cochain second →
        first = second := by
  sorry

/-- Assemble the project-level discrete gate. -/
@[proof_assembly]
theorem ccp25_discrete_hodge_gate
    {Cochain : Type*} [AddCommGroup Cochain]
    (data : CCP25DiscreteHodgeData Cochain) :
    ccp25DiscreteHodgeGateStatement data := by
  intro cochain
  obtain ⟨pieces, hPieces⟩ := ccp25_discrete_hodge_pieces_exist data cochain
  exact ⟨pieces, hPieces, fun other hOther =>
    ccp25_discrete_hodge_pieces_unique data cochain other pieces hOther hPieces⟩

end RiemannianFluids
