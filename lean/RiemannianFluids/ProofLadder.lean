import RiemannianFluids.Conventions
import RiemannianFluids.Geometry.Manifolds
import RiemannianFluids.Tensors.Calculus
import RiemannianFluids.FunctionSpaces.Constraints
import RiemannianFluids.Operators.Viscosity
import RiemannianFluids.Operators.Stokes
import RiemannianFluids.Operators.NavierStokes

/-!
# Differential geometry to surface Navier-Stokes: proof ladder

The import order is the dependency order.  Each theorem in the current kernel
is conditional on visible geometric or analytic hypotheses; later rungs will
replace those hypotheses with constructions and proofs.
-/
