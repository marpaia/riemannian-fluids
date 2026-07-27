import RiemannianFluids.Reproductions.CCG25.Core
import RiemannianFluids.Reproductions.Inventory

/-! # CCG25 numbered remarks -/

namespace RiemannianFluids

/-- All twenty-three numbered remarks in CCG25, arXiv:2212.11928v2. -/
def ccg25NumberedRemarks : Array LiteratureRemarkRef := #[
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.2"
    #[.hypothesisScope]
    "The Bochner Gauss formulas do not require the vector field to be divergence free."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_theorem_1_1_bochner_gauss]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.3"
    #[.mathematicalClaim, .hypothesisScope]
    "If the extension and intrinsic field are both divergence free, the mean-curvature normal-derivative term is tangential."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_theorem_1_1_bochner_gauss]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.4"
    #[.interpretation, .proofRoute]
    "The first Bochner formulas do not display the Ricci operator explicitly; Corollary 1.12 supplies the desired deformation-Laplacian connection."
    .metadataOnly
    (affects := #[``RiemannianFluids.ccg25_theorem_1_1_bochner_gauss,
      ``RiemannianFluids.ccg25_corollary_1_12_euclidean_bochner]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.5"
    #[.mathematicalClaim, .specialization]
    "The indicated Bochner formulas have the same form for an abstract ambient manifold and for Euclidean ambient space."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_theorem_1_1_bochner_gauss,
      ``RiemannianFluids.ccg25_corollary_1_12_euclidean_bochner]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.6"
    #[.mathematicalClaim, .equivalence]
    "The formulas and their tensorial terms are adapted-frame independent, with the paired normal second-derivative expression treated as one operator."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_theorem_1_1_bochner_gauss]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.8"
    #[.mathematicalClaim, .specialization]
    "For Euclidean hypersurfaces the divergence of the second fundamental form is n times the derivative of mean curvature and vanishes for constant mean curvature."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_corollary_1_7_contracted_codazzi]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.10"
    #[.provenance]
    "The hypersurface Ricci formula is classical; the arbitrary-codimension formulas are claimed as new."
    .metadataOnly
    (affects := #[``RiemannianFluids.ccg25_theorem_1_9_ricci_gauss]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.11"
    #[.mathematicalClaim, .equivalence]
    "The Ricci Gauss formula splits into tangential and normal terms, and every term is independent of the chosen extension of the tangent field."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_theorem_1_9_ricci_gauss]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.13"
    #[.proofRoute, .interpretation]
    "Some Euclidean formulas follow by deleting ambient-curvature terms, while the alternative forms additionally use the Ricci--shape relation; mixed ambient formulas are intentionally not enumerated."
    .metadataOnly
    (affects := #[``RiemannianFluids.ccg25_corollary_1_12_euclidean_bochner]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.14"
    #[.mathematicalClaim, .hypothesisScope]
    "Under ambient and intrinsic divergence freeness, both the mean-curvature normal derivative and the normal Lie bracket in the Euclidean hypersurface formulas are tangential."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_corollary_1_12_euclidean_bochner]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.15"
    #[.mathematicalClaim, .equivalence]
    "For a hypersurface, nH times the normal Lie bracket may equivalently be written using the normal covariant derivative and shape operator."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_corollary_1_12_euclidean_bochner]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.17"
    #[.proofRoute]
    "The hypersurface deformation formula loses the normal component of the double normal derivative by cancellation."
    .metadataOnly
    (affects := #[``RiemannianFluids.ccg25_corollary_1_16_deformation_gauss]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.19"
    #[.mathematicalClaim, .equivalence]
    "The Euclidean divergence-free hypersurface deformation formula agrees with the earlier Euclidean Bochner forms, with divergence freeness making the bracket term tangential."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_corollary_1_18_divergence_free_deformation]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.22"
    #[.mathematicalClaim, .hypothesisScope]
    "The indicated double-normal derivative and normal bracket terms are already tangential before the displayed projections."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_corollary_1_21_projected_laplacians]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.23"
    #[.mathematicalClaim, .equivalence]
    "The tangential mean-curvature bracket term has the equivalent Weingarten expansion through the shape operator and tangential derivative of mean curvature."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_corollary_1_21_projected_laplacians]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.25"
    #[.mathematicalClaim, .equivalence, .hypothesisScope]
    "For divergence-free fields the deformation, Hodge, and Bochner Laplacians agree; in the hypersurface projection formula the bracket term is already tangential."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_corollary_1_24_euclidean_projected_laplacians]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.26"
    #[.mathematicalClaim, .limitation]
    "The projected Gauss formula contains the deformation Laplacian under intrinsic divergence freeness, but generally includes additional terms depending on the ambient extension."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_corollary_1_24_euclidean_projected_laplacians]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.28"
    #[.convention, .proofRoute, .equivalence]
    "In Euclidean three-space the Laplacians agree, so the surface-of-revolution proof may use the Bochner vector-field formulation without ambiguity."
    .metadataOnly
    (affects := #[``RiemannianFluids.ccg25_theorem_1_27_surface_of_revolution]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.29"
    #[.mathematicalClaim, .hypothesisScope, .provenance]
    "The ellipsoid construction of fields divergence free both intrinsically and in Euclidean three-space extends naturally to the surfaces of revolution considered here."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_theorem_1_27_surface_of_revolution]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 1.31"
    #[.interpretation]
    "The Lie-derivative forms expose meridional behavior that is hidden in the direction-neutral projected Gauss formula."
    .metadataOnly
    (affects := #[``RiemannianFluids.ccg25_theorem_1_27_surface_of_revolution,
      ``RiemannianFluids.ccg25_corollary_1_30_surface_comparison]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 2.4"
    #[.mathematicalClaim, .equivalence, .hypothesisScope]
    "The nondegeneracy condition on the generating curve is equivalent to every line through the origin meeting the surface transversally."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_theorem_1_27_surface_of_revolution]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 2.7"
    #[.mathematicalClaim, .limitation, .equivalence]
    "Covariant differentiation commutes with metric duality, but Lie differentiation generally does not; Corollary 2.6 gives the correction relating the two."
    .statementPending
    (affects := #[``RiemannianFluids.ccg25_corollary_2_6_lie_derivative_components]),
  literatureRemark "CCG25" "arXiv:2212.11928v2" "Remark 3.2"
    #[.proofRoute, .provenance]
    "The frame-trace lemma follows from a standard traced identity, but the paper gives a self-contained proof because it is central to Theorem 1.1."
    .metadataOnly
    (affects := #[``RiemannianFluids.ccg25_lemma_3_1_frame_trace])
]

end RiemannianFluids
