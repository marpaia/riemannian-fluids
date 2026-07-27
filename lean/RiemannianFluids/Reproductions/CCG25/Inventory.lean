import RiemannianFluids.Reproductions.CCG25.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # CCG25 source inventory -/

namespace RiemannianFluids

def ccg25NamedResults : Array LiteratureItemRef := #[
  literatureItem "CCG25" "arXiv:2212.11928v2" "Theorem 1.1" .theorem
    ``RiemannianFluids.ccg25_theorem_1_1_bochner_gauss,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Corollary 1.7" .corollary
    ``RiemannianFluids.ccg25_corollary_1_7_contracted_codazzi,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Theorem 1.9" .theorem
    ``RiemannianFluids.ccg25_theorem_1_9_ricci_gauss,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Corollary 1.12" .corollary
    ``RiemannianFluids.ccg25_corollary_1_12_euclidean_bochner,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Corollary 1.16" .corollary
    ``RiemannianFluids.ccg25_corollary_1_16_deformation_gauss,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Corollary 1.18" .corollary
    ``RiemannianFluids.ccg25_corollary_1_18_divergence_free_deformation,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Corollary 1.20" .corollary
    ``RiemannianFluids.ccg25_corollary_1_20_hodge_gauss,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Corollary 1.21" .corollary
    ``RiemannianFluids.ccg25_corollary_1_21_projected_laplacians,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Corollary 1.24" .corollary
    ``RiemannianFluids.ccg25_corollary_1_24_euclidean_projected_laplacians,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Theorem 1.27" .theorem
    ``RiemannianFluids.ccg25_theorem_1_27_surface_of_revolution,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Corollary 1.30" .corollary
    ``RiemannianFluids.ccg25_corollary_1_30_surface_comparison,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Proposition 2.1" .proposition
    ``RiemannianFluids.ccg25_proposition_2_1_gauss_weingarten,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Lemma 2.2" .lemma
    ``RiemannianFluids.ccg25_lemma_2_2_normal_frame_derivatives,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Lemma 2.3" .lemma
    ``RiemannianFluids.ccg25_lemma_2_3_extension_derivative_splitting,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Lemma 2.5" .lemma
    ``RiemannianFluids.ccg25_lemma_2_5_one_form_derivative,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Corollary 2.6" .corollary
    ``RiemannianFluids.ccg25_corollary_2_6_lie_derivative_components,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Lemma 2.8" .lemma
    ``RiemannianFluids.ccg25_lemma_2_8_defining_function_shape,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Lemma 3.1" .lemma
    ``RiemannianFluids.ccg25_lemma_3_1_frame_trace,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Lemma 3.3" .lemma
    ``RiemannianFluids.ccg25_lemma_3_3_mixed_curvature_invariant,
  literatureItem "CCG25" "arXiv:2212.11928v2" "Proposition 4.1" .proposition
    ``RiemannianFluids.ccg25_proposition_4_1_surface_connection_coefficients
]

/-- Numbered definitions in CCG25; populated separately when the source has any. -/
def ccg25NamedDefinitions : Array LiteratureItemRef := #[]

/-- Source-audited named-result count for CCG25. -/
theorem ccg25NamedResultCount : ccg25NamedResults.size = 20 := by
  native_decide

/-- Source-audited numbered-remark count for CCG25. -/
theorem ccg25NumberedRemarkCount : ccg25NumberedRemarks.size = 23 := by
  native_decide

end RiemannianFluids
