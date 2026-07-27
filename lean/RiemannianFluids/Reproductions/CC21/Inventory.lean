import RiemannianFluids.Reproductions.CC21.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # CC21 source inventory -/

namespace RiemannianFluids

def cc21NamedResults : Array LiteratureItemRef := #[
  literatureItem "CC21" "arXiv:1708.05134v1" "Theorem 1.2" .theorem
    ``RiemannianFluids.cc21_theorem_1_2,
  literatureItem "CC21" "arXiv:1708.05134v1" "Theorem 1.3" .theorem
    ``RiemannianFluids.cc21_theorem_1_3,
  literatureItem "CC21" "arXiv:1708.05134v1" "Theorem 1.4" .theorem
    ``RiemannianFluids.cc21_theorem_1_4,
  literatureItem "CC21" "arXiv:1708.05134v1" "Theorem 3.1" .theorem
    ``RiemannianFluids.cc21_theorem_3_1_divergence_right_inverse,
  literatureItem "CC21" "arXiv:1708.05134v1" "Lemma 3.2" .lemma
    ``RiemannianFluids.cc21_lemma_3_2_annular_corrector,
  literatureItem "CC21" "arXiv:1708.05134v1" "Lemma 3.3" .lemma
    ``RiemannianFluids.cc21_lemma_3_3_riesz_stokes_correction,
  literatureItem "CC21" "arXiv:1708.05134v1" "Lemma 3.4" .lemma
    ``RiemannianFluids.cc21_lemma_3_4_negative_pairing,
  literatureItem "CC21" "arXiv:1708.05134v1" "Lemma 3.5" .lemma
    ``RiemannianFluids.cc21_lemma_3_5_noncancellation,
  literatureItem "CC21" "arXiv:1708.05134v1" "Theorem 3.6" .theorem
    ``RiemannianFluids.cc21_theorem_3_6_stokes_pair,
  literatureItem "CC21" "arXiv:1708.05134v1" "Lemma 4.1" .lemma
    ``RiemannianFluids.cc21_lemma_4_1_harmonic_hessian_estimate,
  literatureItem "CC21" "arXiv:1708.05134v1" "Lemma 4.2" .lemma
    ``RiemannianFluids.cc21_lemma_4_2_h1_l4_estimate,
  literatureItem "CC21" "arXiv:1708.05134v1" "Lemma 4.3" .lemma
    ``RiemannianFluids.cc21_lemma_4_3_h1_poincare_estimate,
  literatureItem "CC21" "arXiv:1708.05134v1" "Lemma 4.4" .lemma
    ``RiemannianFluids.cc21_lemma_4_4_uniform_exterior_energy,
  literatureItem "CC21" "arXiv:1708.05134v1" "Lemma 4.5" .lemma
    ``RiemannianFluids.cc21_lemma_4_5_leray_schauder,
  literatureItem "CC21" "arXiv:1708.05134v1" "Theorem 4.6" .theorem
    ``RiemannianFluids.cc21_theorem_4_6_navier_stokes_pair
]

/-- Numbered definitions in CC21; populated separately when the source has any. -/
def cc21NamedDefinitions : Array LiteratureItemRef := #[]

/-- Source-audited named-result count for CC21. -/
theorem cc21NamedResultCount : cc21NamedResults.size = 15 := by
  native_decide

/-- Source-audited numbered-remark count for CC21. -/
theorem cc21NumberedRemarkCount : cc21NumberedRemarks.size = 1 := by
  native_decide

end RiemannianFluids
