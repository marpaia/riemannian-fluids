import RiemannianFluids.Operators.GeometricIdentities
import RiemannianFluids.Operators.NavierStokes
import RiemannianFluids.Tensors.DifferentialForms
import RiemannianFluids.Tensors.ExteriorCalculus
import RiemannianFluids.Geometry.Curvature
import RiemannianFluids.Geometry.SpaceForms
import RiemannianFluids.Geometry.Submanifolds
import RiemannianFluids.Geometry.ThinShells
import RiemannianFluids.FunctionSpaces.Evolution
import RiemannianFluids.FunctionSpaces.SobolevForms
import RiemannianFluids.Operators.FormalAdjoints
import RiemannianFluids.Operators.Restriction
import RiemannianFluids.PDE.PressureRecovery
import RiemannianFluids.Numerics.CCP25Discrete
import RiemannianFluids.Numerics.WBS26ResolvedShell
import RiemannianFluids.LiteratureInventory

/-!
# RiemannianFluids

This is the single library root for both checked results and work in progress. It imports the
operator kernel and every permanent literature-facing reproduction module. Unfinished proofs
are permitted only in declarations tagged `proof_obligation`; sorry-free composition nodes are
tagged `proof_assembly`; literature-facing endpoints are tagged `literature_terminal` and
audited transitively by `make lean/progress`.

The source audit rejects untagged `sorry`, `admit`, and project axioms. Thus ordinary Lean
development can proceed in the real module layout without maintaining a second blueprint
library, while the exact unfinished boundary remains machine-readable.

Existing completed declarations continue to receive the separate standard-axiom audit in
`RiemannianFluids/AxiomAudit.lean`.
-/
