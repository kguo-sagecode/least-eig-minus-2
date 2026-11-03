import LineGraphs.Computations.C15Factor21
import LineGraphs.Computations.C15Factor22
import LineGraphs.Computations.C15Factor23
import LineGraphs.Computations.C15Factor24
import LineGraphs.Computations.C15Factor25
import LineGraphs.Computations.C15Power21
import LineGraphs.Computations.C15Power22
import LineGraphs.Computations.C15Power23
import LineGraphs.Computations.C15Power24
import LineGraphs.Computations.SpectrumChecker

/-! # C15: the spectral certificate for graph 2, [CGSS], Example 5.13. -/

namespace Computations.C15

open Table2

/-- C15, [CGSS] Example 5.13: table 2 is an adjacency matrix. -/
theorem adjacency2_checked : checkAdjacency 30 adjacency2 = true := by decide +kernel

/-- C15, [CGSS] Example 5.13: the factored annihilator vanishes. -/
theorem annihilator2_checked : checkAnnihilator 30 adjacency2 [6, 4, 1, 0, -2] = true := by
  unfold checkAnnihilator
  simp only [matrixFactors, neg_neg, neg_zero]
  rw [factor1_checked, factor2_checked, factor3_checked, factor4_checked, factor5_checked]
  decide +kernel

/-- C15, [CGSS] Example 5.13: the first five powers are the materialized integer tables. -/
theorem powers2_checked :
    matrixPow 30 adjacency2 0 = power0 ∧
    matrixPow 30 adjacency2 1 = power1 ∧
    matrixPow 30 adjacency2 2 = power2 ∧
    matrixPow 30 adjacency2 3 = power3 ∧
    matrixPow 30 adjacency2 4 = power4 := by
  have h0 : matrixPow 30 adjacency2 0 = power0 := by decide +kernel
  have h1 : matrixPow 30 adjacency2 1 = power1 := by rw [matrixPow, h0, power1_checked]
  have h2 : matrixPow 30 adjacency2 2 = power2 := by rw [matrixPow, h1, power2_checked]
  have h3 : matrixPow 30 adjacency2 3 = power3 := by rw [matrixPow, h2, power3_checked]
  have h4 : matrixPow 30 adjacency2 4 = power4 := by rw [matrixPow, h3, power4_checked]
  exact ⟨h0, h1, h2, h3, h4⟩

/-- C15, [CGSS] Example 5.13: the full annihilator and trace certificate. -/
theorem spectrum2_checked : checkSpectrum 30 adjacency2 spectralData = true := by
  unfold checkSpectrum
  have hp : checkAnnihilator 30 adjacency2 (spectralData.map Prod.fst) = true :=
    annihilator2_checked
  rw [hp]
  have ht : checkTraces 30 adjacency2
      (List.ofFn fun j : Fin spectralData.length ↦ (j.val, spectrumMoment spectralData j.val)) =
      true := by
    unfold checkTraces
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by decide +kernel, ?_⟩
    apply List.all_eq_true.mpr
    intro pair hpair
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hpair
    obtain ⟨h0, h1, h2, h3, h4⟩ := powers2_checked
    fin_cases j
    · change (trace 30 (matrixPow 30 adjacency2 0) == spectrumMoment spectralData 0) = true
      rw [h0]
      decide +kernel
    · change (trace 30 (matrixPow 30 adjacency2 1) == spectrumMoment spectralData 1) = true
      rw [h1]
      decide +kernel
    · change (trace 30 (matrixPow 30 adjacency2 2) == spectrumMoment spectralData 2) = true
      rw [h2]
      decide +kernel
    · change (trace 30 (matrixPow 30 adjacency2 3) == spectrumMoment spectralData 3) = true
      rw [h3]
      decide +kernel
    · change (trace 30 (matrixPow 30 adjacency2 4) == spectrumMoment spectralData 4) = true
      rw [h4]
      decide +kernel
  rw [ht]
  decide +kernel

end Computations.C15
