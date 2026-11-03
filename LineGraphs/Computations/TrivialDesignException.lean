/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.SpectrumChecker
import LineGraphs.LineGraphSpectra.SmallDesigns
import LineGraphs.LineGraphSpectra.LineGraphCliques
import LineGraphs.Spectral.LineGraphSpectrum
import LineGraphs.Graphs.Basic
import LineGraphs.Seidel.FamilyParameters

/-! # The trivial-design exception in [CGSS], Remark 5.12

The certificates concern the 16 by 16 signless Laplacian of `K₁₀,₆` and the
6 by 6 adjacency matrix of `K₆`. The incidence identity then gives the full
60-vertex spectra, including all 45 copies of `-2`.
-/

namespace Computations.TrivialDesignException

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the trivial `(6,6,10,10,10)` design. -/
def design := Design.trivial 10 6 (by decide) (by decide)

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the signless Laplacian, with the six points first. -/
def incidenceSignless : IntMatrix := [
  [10, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 10, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 0, 10, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 0, 0, 10, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 0, 0, 0, 10, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 0, 0, 0, 0, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 1, 1, 1, 1, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 1, 1, 1, 1, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0],
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0],
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0],
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0],
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0],
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0],
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6]]

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the adjacency matrix of `K₆`. -/
def completeAdjacency : IntMatrix := [
  [0, 1, 1, 1, 1, 1],
  [1, 0, 1, 1, 1, 1],
  [1, 1, 0, 1, 1, 1],
  [1, 1, 1, 0, 1, 1],
  [1, 1, 1, 1, 0, 1],
  [1, 1, 1, 1, 1, 0]]

set_option maxRecDepth 4000

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: a kernel certificate for the incidence signless spectrum. -/
theorem incidence_spectrum_checked :
    checkSpectrum 16 incidenceSignless [(16, 1), (10, 5), (6, 9), (0, 1)] = true := by
  decide +kernel

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: a kernel certificate for the complete-graph spectrum. -/
theorem complete_spectrum_checked :
    checkSpectrum 6 completeAdjacency [(5, 1), (-1, 5)] = true := by
  decide +kernel

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the certificate indices list points before blocks. -/
def incidenceIndex : Fin 16 ≃ Fin 6 ⊕ Fin 10 :=
  (finSumFinEquiv : Fin 6 ⊕ Fin 10 ≃ Fin (6 + 10)).symm

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the certificate is the signless Laplacian of the incidence graph. -/
theorem incidence_signless_eq :
    (design.incidenceGraph.signlessLapMatrix ℝ).submatrix incidenceIndex
      incidenceIndex = toMatrix 16 incidenceSignless := by
  have hi : ∀ i j : Fin 16,
      (if incidenceIndex i = incidenceIndex j then
        (design.incidenceGraph.degree (incidenceIndex i) : ℤ) else 0) +
      (if design.incidenceGraph.Adj (incidenceIndex i) (incidenceIndex j)
        then 1 else 0) = entry incidenceSignless i j := by decide +kernel
  ext i j
  change (if incidenceIndex i = incidenceIndex j then
      (design.incidenceGraph.degree (incidenceIndex i) : ℝ) else 0) +
    (if design.incidenceGraph.Adj (incidenceIndex i) (incidenceIndex j)
      then 1 else 0) = (entry incidenceSignless i j : ℝ)
  exact_mod_cast hi i j

attribute [local instance] Classical.propDecidable

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the signless spectrum of `K₁₀,₆`. -/
theorem spectrum_incidence_signless :
    (design.incidenceGraph.signlessLapMatrix ℝ).spectrumMultiset =
      {16} + Multiset.replicate 5 10 + Multiset.replicate 9 6 + {0} := by
  rw [← Matrix.spectrumMultiset_submatrix_equiv _ incidenceIndex, incidence_signless_eq]
  have h := checkSpectrum_sound incidence_spectrum_checked
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.cast_ofNat,
    Int.cast_zero, Multiset.replicate_one, add_zero] at h
  rw [h]
  abel

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the adjacency spectrum of `K₆`. -/
theorem spectrum_complete : (⊤ : SimpleGraph (Fin 6)).spectrumMultiset =
    {5} + Multiset.replicate 5 (-1) := by
  have ha : ∀ i j : Fin 6, (⊤ : SimpleGraph (Fin 6)).Adj i j ↔
      entry completeAdjacency i j = 1 := by
    change ∀ i j : Fin 6, i ≠ j ↔ entry completeAdjacency i j = 1
    decide +kernel
  have h := spectrum_eq_of_checkSpectrum
    (show checkAdjacency 6 completeAdjacency = true by decide +kernel)
    (⊤ : SimpleGraph (Fin 6)) (Equiv.refl _) ha complete_spectrum_checked
  simpa using h

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: `T(6)` has spectrum `8¹, 2⁵, (-2)⁹`. -/
theorem spectrum_triangular : (⊤ : SimpleGraph (Fin 6)).lineGraph.spectrumMultiset =
    {8} + Multiset.replicate 5 2 + Multiset.replicate 9 (-2) := by
  have hr : (⊤ : SimpleGraph (Fin 6)).IsRegularOfDegree 5 := by
    intro v
    simp
  have hm : (⊤ : SimpleGraph (Fin 6)).edgeFinset.card = 15 := by decide
  rw [SimpleGraph.spectrumMultiset_lineGraph_of_card_le _ (by rw [hm]; decide),
    hr.spectrumMultiset_signlessLapMatrix, spectrum_complete, hm]
  norm_num only [Fintype.card_fin, Multiset.map_add, Multiset.map_singleton,
    Multiset.map_replicate, Multiset.map_map, Function.comp_def]

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the flag-graph spectrum is `14¹, 8⁵, 4⁹, (-2)⁴⁵`. -/
theorem spectrum_flagGraph : design.flagGraph.spectrumMultiset =
    {14} + Multiset.replicate 5 8 + Multiset.replicate 9 4 +
      Multiset.replicate 45 (-2) := by
  have hm : design.incidenceGraph.edgeFinset.card = 60 := by
    simpa only [SimpleGraph.card_edgeSet] using design.card_flagGraph
  change design.incidenceGraph.lineGraph.spectrumMultiset = _
  rw [SimpleGraph.spectrumMultiset_lineGraph_of_card_le _ (by rw [hm]; decide),
    spectrum_incidence_signless, hm]
  norm_num only [Fintype.card_sum, Fintype.card_fin, Multiset.map_add,
    Multiset.map_singleton, Multiset.map_replicate]
  rw [show (45 : ℕ) = 1 + 44 from rfl, Multiset.replicate_add, Multiset.replicate_one]
  abel

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: `L(T(6)) = L(L(K₆))` has the same 60-vertex spectrum. -/
theorem spectrum_double_lineGraph :
    (⊤ : SimpleGraph (Fin 6)).lineGraph.lineGraph.spectrumMultiset =
      {14} + Multiset.replicate 5 8 + Multiset.replicate 9 4 +
        Multiset.replicate 45 (-2) := by
  have hr : (⊤ : SimpleGraph (Fin 6)).lineGraph.IsRegularOfDegree 8 :=
    SimpleGraph.lineGraph_completeGraph_isRegularOfDegree 6
  have hn : Fintype.card (⊤ : SimpleGraph (Fin 6)).edgeSet = 15 := by
    rw [SimpleGraph.card_completeGraph_edgeSet]
    decide
  have hm : (⊤ : SimpleGraph (Fin 6)).lineGraph.edgeFinset.card = 60 := by
    have hh := (⊤ : SimpleGraph (Fin 6)).lineGraph.sum_degrees_eq_twice_card_edges
    simp only [hr.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul, hn] at hh
    omega
  rw [SimpleGraph.spectrumMultiset_lineGraph_of_card_le _ (by omega),
    hr.spectrumMultiset_signlessLapMatrix, spectrum_triangular, hm, hn]
  norm_num only [Multiset.map_add, Multiset.map_singleton, Multiset.map_replicate,
    Multiset.map_map, Function.comp_def]

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the trivial-design flag graph is cospectral with `L(L(K₆))`. -/
theorem flagGraph_cospectral_double_lineGraph :
    design.flagGraph.Cospectral (⊤ : SimpleGraph (Fin 6)).lineGraph.lineGraph := by
  apply SimpleGraph.cospectral_iff_spectrumMultiset_eq.mpr
  rw [spectrum_flagGraph, spectrum_double_lineGraph]

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the complete-bipartite line graph `L(K₁₀,₆)` is
cospectral with `L(L(K₆))`. -/
theorem lineGraph_completeBipartite_cospectral_double_lineGraph :
    (completeBipartiteGraph (Fin 10) (Fin 6)).lineGraph.Cospectral
      (⊤ : SimpleGraph (Fin 6)).lineGraph.lineGraph :=
  design.incidenceGraphCompleteBipartiteIso.lineGraph.symm.cospectral.trans
    flagGraph_cospectral_double_lineGraph

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: the cospectral graphs are not isomorphic. -/
theorem flagGraph_not_nonempty_iso_double_lineGraph :
    ¬ Nonempty (design.flagGraph ≃g (⊤ : SimpleGraph (Fin 6)).lineGraph.lineGraph) := by
  have hr : (⊤ : SimpleGraph (Fin 6)).lineGraph.IsRegularOfDegree 8 :=
    SimpleGraph.lineGraph_completeGraph_isRegularOfDegree 6
  exact design.not_nonempty_iso_flagGraph_lineGraph_of_degree _ (by decide : 3 ≤ 8)
    (fun a => le_of_eq (hr a)) (by decide)

-- Remark 5.12
/-- Remark 5.12 of [CGSS]: no flag graph of replication ten is `L(T(6))`, whose root has
maximum degree eight; in particular the trivial-design flag graph is not characterized. -/
theorem not_flagGraphCharacterized : ¬ design.FlagGraphCharacterized := by
  intro h
  obtain ⟨P, B, _, _, _, _, D, ⟨e⟩⟩ := h _
    (⊤ : SimpleGraph (Fin 6)).lineGraph.lineGraph flagGraph_cospectral_double_lineGraph
  have hr : (⊤ : SimpleGraph (Fin 6)).lineGraph.IsRegularOfDegree 8 :=
    SimpleGraph.lineGraph_completeGraph_isRegularOfDegree 6
  exact D.not_nonempty_iso_flagGraph_lineGraph_of_degree _ (by decide : 3 ≤ 8)
    (fun a => le_of_eq (hr a)) (by decide) ⟨e.symm⟩

end Computations.TrivialDesignException
