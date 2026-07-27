import RiemannianFluids.Reproductions.CCD17.Core
import RiemannianFluids.Reproductions.Inventory

/-! # CCD17 numbered remarks -/

namespace RiemannianFluids

/-- All six numbered remarks in CCD17, arXiv:1608.05114v2. -/
def ccd17NumberedRemarks : Array LiteratureRemarkRef := #[
  literatureRemark "CCD17" "arXiv:1608.05114v2" "Remark 1.1"
    #[.interpretation, .provenance]
    "Stochastic variational formulations avoid the deterministic ambiguity in the choice of viscous operator."
    .metadataOnly,
  literatureRemark "CCD17" "arXiv:1608.05114v2" "Remark 3.1"
    #[.mathematicalClaim, .limitation]
    "Replacing the H1 norm by the exterior-derivative seminorm fails because a nonzero L2 harmonic gradient has zero exterior derivative."
    .statementPending
    (affects := #[``RiemannianFluids.ccd17_theorem_3_2]),
  literatureRemark "CCD17" "arXiv:1608.05114v2" "Remark 3.4"
    #[.mathematicalClaim, .specialization]
    "On the round sphere, the exterior-derivative norm controls the covariant-derivative norm for co-closed one-forms, so the energy estimate succeeds."
    .statementPending
    (affects := #[``RiemannianFluids.ccd17_theorem_3_2]),
  literatureRemark "CCD17" "arXiv:1608.05114v2" "Remark 3.5"
    #[.mathematicalClaim, .specialization, .provenance]
    "The corresponding global energy equality follows from the weak formulation in Euclidean dimensions two and three."
    .statementPending
    (affects := #[``RiemannianFluids.ccd17_theorem_3_6]),
  literatureRemark "CCD17" "arXiv:1608.05114v2" "Remark 3.7"
    #[.hypothesisScope, .provenance, .limitation]
    "The counterexample does not contradict Ebin--Marsden because their result is compact, short-time, and assumes substantially smoother initial data."
    .metadataOnly
    (affects := #[``RiemannianFluids.ccd17_theorem_3_2,
      ``RiemannianFluids.ccd17_theorem_3_3,
      ``RiemannianFluids.ccd17_theorem_3_6]),
  literatureRemark "CCD17" "arXiv:1608.05114v2" "Remark 5.1"
    #[.provenance, .limitation]
    "Extended irreversible-thermodynamics models treat viscous stresses as independent variables and therefore do not determine the manifold operator through this nonrelativistic limit."
    .metadataOnly
]

end RiemannianFluids
