import RiemannianFluids.Reproductions.CC13.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # CC13 source inventory -/

namespace RiemannianFluids

def cc13NamedResults : Array LiteratureItemRef := #[
  literatureItem "CC13" "arXiv:1006.2819v1" "Theorem 1.1" .theorem
    ``RiemannianFluids.cc13_theorem_1_1_prodi_serrin_ladyzhenskaya,
  literatureItem "CC13" "arXiv:1006.2819v1" "Theorem 1.2" .theorem
    ``RiemannianFluids.cc13_theorem_1_2,
  literatureItem "CC13" "arXiv:1006.2819v1" "Corollary 1.4" .corollary
    ``RiemannianFluids.cc13_corollary_1_4_hyperbolic_liouville_failure,
  literatureItem "CC13" "arXiv:1006.2819v1" "Theorem 1.6" .theorem
    ``RiemannianFluids.cc13_theorem_1_6_pinched_modified_nonuniqueness,
  literatureItem "CC13" "arXiv:1006.2819v1" "Corollary 1.7" .corollary
    ``RiemannianFluids.cc13_corollary_1_7_pinched_liouville_failure,
  literatureItem "CC13" "arXiv:1006.2819v1" "Lemma 2.2" .lemma
    ``RiemannianFluids.cc13_lemma_2_2_distance_function,
  literatureItem "CC13" "arXiv:1006.2819v1" "Lemma 2.3" .lemma
    ``RiemannianFluids.cc13_lemma_2_3_triangle_comparison,
  literatureItem "CC13" "arXiv:1006.2819v1" "Lemma 2.4" .lemma
    ``RiemannianFluids.cc13_lemma_2_4_caccioppoli,
  literatureItem "CC13" "arXiv:1006.2819v1" "Theorem 2.5" .theorem
    ``RiemannianFluids.cc13_theorem_2_5_gradient_estimate,
  literatureItem "CC13" "arXiv:1006.2819v1" "Lemma 2.6" .lemma
    ``RiemannianFluids.cc13_lemma_2_6_bochner_formula,
  literatureItem "CC13" "arXiv:1006.2819v1" "Theorem 2.7" .theorem
    ``RiemannianFluids.cc13_theorem_2_7_jacobi_comparison,
  literatureItem "CC13" "arXiv:1006.2819v1" "Proposition 3.1" .proposition
    ``RiemannianFluids.cc13_proposition_3_1_gradient_decay,
  literatureItem "CC13" "arXiv:1006.2819v1" "Corollary 3.3" .corollary
    ``RiemannianFluids.cc13_corollary_3_3_l2_gradient,
  literatureItem "CC13" "arXiv:1006.2819v1" "Corollary 3.4" .corollary
    ``RiemannianFluids.cc13_corollary_3_4_pinched_l2_gradient,
  literatureItem "CC13" "arXiv:1006.2819v1" "Lemma 4.1" .lemma
    ``RiemannianFluids.cc13_lemma_4_1_covering,
  literatureItem "CC13" "arXiv:1006.2819v1" "Proposition 4.3" .proposition
    ``RiemannianFluids.cc13_proposition_4_3_gradient_energy_derivative_l1,
  literatureItem "CC13" "arXiv:1006.2819v1" "Lemma 5.1" .lemma
    ``RiemannianFluids.cc13_lemma_5_1_deformation_bound,
  literatureItem "CC13" "arXiv:1006.2819v1" "Proposition 5.2" .proposition
    ``RiemannianFluids.cc13_proposition_5_2_bochner_dissipation,
  literatureItem "CC13" "arXiv:1006.2819v1" "Corollary 5.3" .corollary
    ``RiemannianFluids.cc13_corollary_5_3_exact_hyperbolic_dissipation,
  literatureItem "CC13" "arXiv:1006.2819v1" "Lemma 6.1" .lemma
    ``RiemannianFluids.cc13_lemma_6_1_convective_gradient_identity
]

/-- The numbered definition in CC13. -/
def cc13NamedDefinitions : Array LiteratureItemRef := #[
  literatureItem "CC13" "arXiv:1006.2819v1" "Definition 2.1" .definition
    ``RiemannianFluids.cc13Definition2_1Deformation
]

/-- Source-audited named-result count for CC13. -/
theorem cc13NamedResultCount : cc13NamedResults.size = 20 := by
  native_decide

/-- Source-audited numbered-remark count for CC13. -/
theorem cc13NumberedRemarkCount : cc13NumberedRemarks.size = 5 := by
  native_decide

end RiemannianFluids
