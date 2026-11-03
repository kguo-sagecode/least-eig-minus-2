import LineGraphs.Computations.C13Spectrum1
import LineGraphs.Computations.C13Spectrum2
import LineGraphs.Spectral.Cospectral

/-!
# Computation C13 for [CGSS], Corollary 5.10

The two exceptional graphs have the prescribed adjacency and Seidel spectra and are switching
equivalent. An induced claw distinguishes them. Vector and flag identifications are in the
companion modules.
-/

namespace Computations.C13

/-- C13, [CGSS] Corollary 5.10: the first exceptional graph. -/
abbrev graph1 := graphOfMatrix adjacency1_checked

/-- C13, [CGSS] Corollary 5.10: the second exceptional graph. -/
abbrev graph2 := graphOfMatrix adjacency2_checked

/-- C13, [CGSS] Corollary 5.10: the first adjacency spectrum is `4¹, 2³, 0³, (-2)⁵`. -/
theorem spectrum_graph1 : graph1.spectrumMultiset =
    (spectralData.map fun x ↦ Multiset.replicate x.2 (x.1 : ℝ)).sum :=
  spectrum_graphOfMatrix_of_checkSpectrum adjacency1_checked spectrum1_checked

/-- C13, [CGSS] Corollary 5.10: the second adjacency spectrum is `4¹, 2³, 0³, (-2)⁵`. -/
theorem spectrum_graph2 : graph2.spectrumMultiset =
    (spectralData.map fun x ↦ Multiset.replicate x.2 (x.1 : ℝ)).sum :=
  spectrum_graphOfMatrix_of_checkSpectrum adjacency2_checked spectrum2_checked

/-- C13, [CGSS] Corollary 5.10: the exceptional graphs are cospectral. -/
theorem cospectral : graph1.Cospectral graph2 := by
  apply SimpleGraph.cospectral_iff_spectrumMultiset_eq.mpr
  rw [spectrum_graph1, spectrum_graph2]

/-- C13, [CGSS] Corollary 5.10: the first Seidel spectrum, for `S = J - I - 2A`. -/
theorem seidel_spectrum_graph1 : graph1.seidelMatrix.spectrumMultiset =
    (seidelSpectralData.map fun x ↦ Multiset.replicate x.2 (x.1 : ℝ)).sum := by
  rw [seidelMatrix_graphOfMatrix]
  exact checkSpectrum_sound seidel1_checked

/-- C13, [CGSS] Corollary 5.10: the second Seidel spectrum, for `S = J - I - 2A`. -/
theorem seidel_spectrum_graph2 : graph2.seidelMatrix.spectrumMultiset =
    (seidelSpectralData.map fun x ↦ Multiset.replicate x.2 (x.1 : ℝ)).sum := by
  rw [seidelMatrix_graphOfMatrix]
  exact checkSpectrum_sound seidel2_checked

/-- C13, [CGSS] Corollary 5.10: switching the last four vertices and relabelling suffices. -/
theorem switching_equivalent : graph1.IsSwitchingEquivalent graph2 :=
  checkSeidelSwitching_sound adjacency1_checked adjacency2_checked
    (d := switchSigns) (p := switchPermutation) (by decide +kernel)

/-- C13, [CGSS] Corollary 5.10: a finite invariant, the absence of an induced claw. -/
theorem graph1_no_claw : ∀ c a b d : Fin 12,
    a ≠ b → a ≠ d → b ≠ d → graph1.Adj c a → graph1.Adj c b → graph1.Adj c d →
      graph1.Adj a b ∨ graph1.Adj a d ∨ graph1.Adj b d := by
  decide +kernel

/-- C13, [CGSS] Corollary 5.10: vertex 4 has the independent neighbours 0, 1, 10. -/
theorem graph2_claw : graph2.Adj 4 0 ∧ graph2.Adj 4 1 ∧ graph2.Adj 4 10 ∧
    ¬ graph2.Adj 0 1 ∧ ¬ graph2.Adj 0 10 ∧ ¬ graph2.Adj 1 10 := by
  decide +kernel

/-- C13, [CGSS] Corollary 5.10, the exception following the proof: non-isomorphism. -/
theorem not_nonempty_iso : ¬ Nonempty (graph1 ≃g graph2) := by
  rintro ⟨e⟩
  have h := graph1_no_claw (e.symm 4) (e.symm 0) (e.symm 1) (e.symm 10)
  simp only [e.symm.injective.ne_iff, e.symm.map_adj_iff] at h
  exact (h (by decide) (by decide) (by decide) graph2_claw.1 graph2_claw.2.1 graph2_claw.2.2.1).elim
    graph2_claw.2.2.2.1 (fun h ↦ h.elim graph2_claw.2.2.2.2.1 graph2_claw.2.2.2.2.2)

end Computations.C13
