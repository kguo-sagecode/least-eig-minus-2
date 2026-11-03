import LineGraphs.Computations.C15Spectrum1
import LineGraphs.Computations.C15Spectrum2
import LineGraphs.Computations.CliqueCertificates
import LineGraphs.Spectral.Cospectral

/-!
# Computation C15 for [CGSS], Example 5.13

The two graphs have spectrum `6¹, 4⁵, 1⁴, 0⁵, (-2)¹⁵`. Four-clique profiles distinguish
them. Companion modules identify the graphs with the design flag graph and `L(L(Petersen))`.
-/

namespace Computations.C15

/-- C15, [CGSS] Example 5.13: the flag graph's adjacency table. -/
abbrev graph1 := graphOfMatrix adjacency1_checked

/-- C15, [CGSS] Example 5.13: the iterated line graph's adjacency table. -/
abbrev graph2 := graphOfMatrix adjacency2_checked

/-- C15, [CGSS] Example 5.13: the first adjacency spectrum. -/
theorem spectrum_graph1 : graph1.spectrumMultiset =
    (spectralData.map fun x ↦ Multiset.replicate x.2 (x.1 : ℝ)).sum :=
  spectrum_graphOfMatrix_of_checkSpectrum adjacency1_checked spectrum1_checked

/-- C15, [CGSS] Example 5.13: the second adjacency spectrum. -/
theorem spectrum_graph2 : graph2.spectrumMultiset =
    (spectralData.map fun x ↦ Multiset.replicate x.2 (x.1 : ℝ)).sum :=
  spectrum_graphOfMatrix_of_checkSpectrum adjacency2_checked spectrum2_checked

/-- C15, [CGSS] Example 5.13: the two certificate graphs are cospectral. -/
theorem cospectral : graph1.Cospectral graph2 := by
  apply SimpleGraph.cospectral_iff_spectrumMultiset_eq.mpr
  rw [spectrum_graph1, spectrum_graph2]

/-- C15, [CGSS] Example 5.13: the flag graph has thirty four-cliques. -/
theorem four_cliques_graph1 : cliqueCount 30 4 adjacency1 = 30 := by decide +kernel

/-- C15, [CGSS] Example 5.13: the iterated line graph has fifteen four-cliques. -/
theorem four_cliques_graph2 : cliqueCount 30 4 adjacency2 = 15 := by decide +kernel

/-- C15, [CGSS] Example 5.13: no graph isomorphism exists. -/
theorem not_nonempty_iso : ¬ Nonempty (graph1 ≃g graph2) := by
  rintro ⟨e⟩
  have hc := congrArg Multiset.card (e.cliqueMultiset_map 4)
  simp only [Multiset.card_map] at hc
  rw [← cliqueCount_sound adjacency1_checked, ← cliqueCount_sound adjacency2_checked,
    four_cliques_graph1, four_cliques_graph2] at hc
  norm_num at hc

end Computations.C15
