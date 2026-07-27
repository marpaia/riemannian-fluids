import RiemannianFluids.Reproductions.CCP25.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # CCP25 source inventory -/

namespace RiemannianFluids

def ccp25NamedResults : Array LiteratureItemRef := #[
  literatureItem "CCP25" "arXiv:1812.11764v1" "Theorem 1.1" .theorem
    ``RiemannianFluids.ccp25_theorem_1_1_compact_hodge_decomposition,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Theorem 1.2" .theorem
    ``RiemannianFluids.ccp25_theorem_1_2_l2_hodge_kodaira,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Theorem 1.3" .theorem
    ``RiemannianFluids.ccp25_theorem_1_3,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Theorem 1.4" .theorem
    ``RiemannianFluids.ccp25_theorem_1_4,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Lemma 2.1" .lemma
    ``RiemannianFluids.ccp25_lemma_2_1_constant_curvature_weizenbock,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Corollary 2.2" .corollary
    ``RiemannianFluids.ccp25_corollary_2_2_integrated_weizenbock,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Lemma 2.7" .lemma
    ``RiemannianFluids.ccp25_lemma_2_7_h1_has_weak_d_and_dstar,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Theorem 2.10" .theorem
    ``RiemannianFluids.ccp25_theorem_2_10_current_de_rham,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Lemma 2.11" .lemma
    ``RiemannianFluids.ccp25_lemma_2_11_degree_one_current_criterion,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Lemma 2.12" .lemma
    ``RiemannianFluids.ccp25_lemma_2_12_degree_k_current_criterion,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Theorem 3.1" .theorem
    ``RiemannianFluids.ccp25_theorem_3_1_harmonic_iff_closed_coclosed,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Theorem 3.2" .theorem
    ``RiemannianFluids.ccp25_theorem_3_2_l2_harmonic_is_h1,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Lemma 4.1" .lemma
    ``RiemannianFluids.ccp25_lemma_4_1_exact_coexact_orthogonal,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Lemma 4.2" .lemma
    ``RiemannianFluids.ccp25_lemma_4_2_harmonic_in_orthogonal_complement,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Proposition 4.3" .proposition
    ``RiemannianFluids.ccp25_proposition_4_3_orthogonal_complement_is_harmonic,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Lemma 4.4" .lemma
    ``RiemannianFluids.ccp25_lemma_4_4_exact_current_representation,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Lemma 4.5" .lemma
    ``RiemannianFluids.ccp25_lemma_4_5_coexact_current_representation,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Lemma 5.1" .lemma
    ``RiemannianFluids.ccp25_lemma_5_1_solenoidal_closure_eq_coexact_closure
]

/-- The five numbered definitions in CCP25. -/
def ccp25NamedDefinitions : Array LiteratureItemRef := #[
  literatureItem "CCP25" "arXiv:1812.11764v1" "Definition 2.3" .definition
    ``RiemannianFluids.ccp25Definition2_3WeakNabla,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Definition 2.4" .definition
    ``RiemannianFluids.ccp25Definition2_4WeakD,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Definition 2.5" .definition
    ``RiemannianFluids.ccp25Definition2_5WeakDStar,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Definition 2.6" .definition
    ``RiemannianFluids.ccp25Definition2_6SobolevH1,
  literatureItem "CCP25" "arXiv:1812.11764v1" "Definition 2.9" .definition
    ``RiemannianFluids.CCP25Definition2_9Current
]

/-- Source-audited named-result count for CCP25. -/
theorem ccp25NamedResultCount : ccp25NamedResults.size = 18 := by
  native_decide

/-- Source-audited numbered-remark count for CCP25. -/
theorem ccp25NumberedRemarkCount : ccp25NumberedRemarks.size = 1 := by
  native_decide

end RiemannianFluids
