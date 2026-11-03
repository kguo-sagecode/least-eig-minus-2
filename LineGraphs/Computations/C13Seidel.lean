import LineGraphs.Computations.C13
import LineGraphs.Spectral.Positivity

/-! # C13: the paper's Seidel sign in [CGSS], Corollary 5.10

These spectrum statements and `switching_equivalent` supply the matrix data for
the paper's common twelve equiangular lines in dimension six. The geometric
realization of those lines is not a separate statement here.
-/

namespace Computations.C13

/-- C13, [CGSS] Corollary 5.10: negating a real symmetric matrix negates its spectrum. -/
theorem spectrum_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : A.IsHermitian) :
    (-A).spectrumMultiset = A.spectrumMultiset.map (fun μ ↦ -μ) := by
  simpa using h.spectrumMultiset_smul_one_add_smul 0 (-1)

/-- C13, [CGSS] Corollary 5.10: the paper's `2A - J + I` has spectrum `5³, 1³, (-3)⁶`. -/
theorem paper_seidel_spectrum_graph1 : (-graph1.seidelMatrix).spectrumMultiset =
    (([(5, 3), (1, 3), (-3, 6)] : List (ℤ × ℕ)).map
      fun x ↦ Multiset.replicate x.2 (x.1 : ℝ)).sum := by
  have hs : graph1.seidelMatrix.IsHermitian := by
    rw [seidelMatrix_graphOfMatrix]
    apply checkSymmetric_sound
    decide +kernel
  rw [spectrum_neg _ hs, seidel_spectrum_graph1]
  norm_num [seidelSpectralData, Multiset.map_add, Multiset.map_replicate]

/-- C13, [CGSS] Corollary 5.10: the second paper Seidel matrix has the same spectrum. -/
theorem paper_seidel_spectrum_graph2 : (-graph2.seidelMatrix).spectrumMultiset =
    (([(5, 3), (1, 3), (-3, 6)] : List (ℤ × ℕ)).map
      fun x ↦ Multiset.replicate x.2 (x.1 : ℝ)).sum := by
  have hs : graph2.seidelMatrix.IsHermitian := by
    rw [seidelMatrix_graphOfMatrix]
    apply checkSymmetric_sound
    decide +kernel
  rw [spectrum_neg _ hs, seidel_spectrum_graph2]
  norm_num [seidelSpectralData, Multiset.map_add, Multiset.map_replicate]

end Computations.C13
