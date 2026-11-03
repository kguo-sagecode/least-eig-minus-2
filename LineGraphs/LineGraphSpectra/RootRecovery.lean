/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Biregular
import LineGraphs.LineGraphSpectra.Blocks

/-!
# Recovering bipartite root graphs

The blueprint's `lem:rootgraph` and `lem:tworoot`, used in [CGSS, Lemma 5.6].
The quadratic spectral mapping keeps multiplicities, including zero modes.
-/

open Matrix

namespace SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {X : SimpleGraph V} {Y : SimpleGraph W} [DecidableRel X.Adj] [DecidableRel Y.Adj]

/-- Blueprint steps `s5trCnz` and `s556st` for [CGSS, Lemma 5.6]: cospectral
line graphs determine the nonzero signless eigenvalue multiplicities. -/
theorem Cospectral.eigenvalueMultiplicity_signlessLapMatrix_of_ne_zero
    (h : X.lineGraph.Cospectral Y.lineGraph) {μ : ℝ} (hμ : μ ≠ 0) :
    (X.signlessLapMatrix ℝ).eigenvalueMultiplicity μ =
      (Y.signlessLapMatrix ℝ).eigenvalueMultiplicity μ := by
  have hcol : ((X.edgeIncMatrix ℝ)ᵀ * X.edgeIncMatrix ℝ).spectrumMultiset =
      ((Y.edgeIncMatrix ℝ)ᵀ * Y.edgeIncMatrix ℝ).spectrumMultiset := by
    rw [X.transpose_edgeIncMatrix_mul, Y.transpose_edgeIncMatrix_mul]
    have hX := (X.lineGraph.isHermitian_adjMatrix ℝ).spectrumMultiset_smul_one_add_smul 2 1
    have hY := (Y.lineGraph.isHermitian_adjMatrix ℝ).spectrumMultiset_smul_one_add_smul 2 1
    simp only [one_smul, one_mul] at hX hY
    rw [hX, hY]
    exact congrArg (Multiset.map (fun μ : ℝ ↦ 2 + μ)) h.spectrumMultiset_eq
  rw [← X.edgeIncMatrix_mul_transpose, ← Y.edgeIncMatrix_mul_transpose,
    eigenvalueMultiplicity_mul_comm_of_ne_zero (X.edgeIncMatrix ℝ) _ hμ,
    eigenvalueMultiplicity_mul_comm_of_ne_zero (Y.edgeIncMatrix ℝ) _ hμ]
  exact congrArg (Multiset.count μ) hcol

/-- Blueprint step `s5trC` for [CGSS, Lemma 5.6]: connected bipartite roots
have equal full signless spectra. -/
theorem Cospectral.spectrumMultiset_signlessLapMatrix_of_connected_bipartite
    (h : X.lineGraph.Cospectral Y.lineGraph) (hcX : X.Connected) (hcY : Y.Connected)
    (hbX : X.IsBipartite) (hbY : Y.IsBipartite) :
    (X.signlessLapMatrix ℝ).spectrumMultiset = (Y.signlessLapMatrix ℝ).spectrumMultiset := by
  apply Multiset.ext.mpr
  intro μ
  change (X.signlessLapMatrix ℝ).eigenvalueMultiplicity μ =
    (Y.signlessLapMatrix ℝ).eigenvalueMultiplicity μ
  by_cases hμ : μ = 0
  · subst μ
    rw [hcX.multiplicity_zero_signlessLapMatrix, hcY.multiplicity_zero_signlessLapMatrix,
      ite_eq_left hbX, ite_eq_left hbY]
  · exact h.eigenvalueMultiplicity_signlessLapMatrix_of_ne_zero hμ

/-- Blueprint steps `s5trN` and `s556st` for [CGSS, Lemma 5.6]: line-graph
cospectrality determines the root order after accounting for bipartiteness. -/
theorem Cospectral.card_add_bipartite_eq_of_connected
    (h : X.lineGraph.Cospectral Y.lineGraph) (hcX : X.Connected) (hcY : Y.Connected) :
    Fintype.card V + (if Y.IsBipartite then 1 else 0) =
      Fintype.card W + (if X.IsBipartite then 1 else 0) := by
  have hX := X.multiplicity_neg_two_lineGraph
  have hY := Y.multiplicity_neg_two_lineGraph
  have hm : X.edgeFinset.card = Y.edgeFinset.card := by
    simpa only [card_edgeSet] using h.card_eq
  rw [hcX.card_bipartite_components] at hX
  rw [hcY.card_bipartite_components] at hY
  have he := h.eigenvalueMultiplicity_eq (-2)
  omega

namespace IsBiregularWith

variable {P Q : Set V} {P' Q' : Set W} {k₁ k₂ k₁' k₂' : ℕ}

/-- The blueprint's `lem:rootgraph`, assertion 6, for [CGSS, Lemma 5.6],
first in the equivalent form retaining both full Gram spectra. -/
theorem spectrumMultiset_map_quadratic_signlessLapMatrix_eq_gram_add_gram
    (hb : X.IsBiregularWith P Q k₁ k₂) :
    (X.signlessLapMatrix ℝ).spectrumMultiset.map
        (fun μ ↦ (μ - (k₁ : ℝ)) * (μ - (k₂ : ℝ))) =
      (X.biadjMatrix P Q ℝ * (X.biadjMatrix P Q ℝ)ᵀ).spectrumMultiset +
        ((X.biadjMatrix P Q ℝ)ᵀ * X.biadjMatrix P Q ℝ).spectrumMultiset := by
  rw [← spectrumMultiset_submatrix_equiv (X.signlessLapMatrix ℝ) hb.sumEquiv,
    hb.signlessLapMatrix_eq_fromBlocks]
  exact spectrumMultiset_map_quadratic_fromBlocks _ _ _

/-- The blueprint's `lem:rootgraph`, assertion 6, for [CGSS, Lemma 5.6]:
the quadratic image consists of two positive Gram spectra and the remaining zeros. -/
theorem spectrumMultiset_map_quadratic_signlessLapMatrix
    (hb : X.IsBiregularWith P Q k₁ k₂) :
    let B := X.biadjMatrix P Q ℝ
    let Λ := (B * Bᵀ).spectrumMultiset.filter (0 < ·)
    (X.signlessLapMatrix ℝ).spectrumMultiset.map
        (fun μ ↦ (μ - (k₁ : ℝ)) * (μ - (k₂ : ℝ))) =
      Λ + Λ + Multiset.replicate (Fintype.card V - 2 * B.rank) 0 := by
  dsimp only
  rw [hb.spectrumMultiset_map_quadratic_signlessLapMatrix_eq_gram_add_gram]
  let B := X.biadjMatrix P Q ℝ
  have hg := spectrumMultiset_gram_products B
  conv_lhs =>
    rw [hg.1.spectrumMultiset_eq_filter_pos_add_replicate_zero,
      hg.2.1.spectrumMultiset_eq_filter_pos_add_replicate_zero,
      ← hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2]
  have hp := B.rank_le_card_height
  have hq := B.rank_le_card_width
  have hn := hb.card_add_card
  simp only [Nat.card_eq_fintype_card] at hn
  have hz : Fintype.card P - B.rank + (Fintype.card Q - B.rank) =
      Fintype.card V - 2 * B.rank := by omega
  rw [← hz, Multiset.replicate_add]
  abel

/-- The parameter recovery in blueprint steps `s5trm`–`s5trsize` for
[CGSS, Lemma 5.6]: ordered bipartitions have the same sizes and degrees. -/
theorem parameters_eq_of_lineGraph_cospectral (hb : X.IsBiregularWith P Q k₁ k₂)
    (hb' : Y.IsBiregularWith P' Q' k₁' k₂') (hcX : X.Connected) (hcY : Y.Connected)
    (heX : X.edgeSet.Nonempty) (heY : Y.edgeSet.Nonempty)
    (hpq : Nat.card P ≤ Nat.card Q) (hpq' : Nat.card P' ≤ Nat.card Q')
    (h : X.lineGraph.Cospectral Y.lineGraph) :
    Nat.card P = Nat.card P' ∧ Nat.card Q = Nat.card Q' ∧ k₁ = k₁' ∧ k₂ = k₂' := by
  have : Nonempty X.edgeSet := heX.to_subtype
  have : Nonempty Y.edgeSet := heY.to_subtype
  have hm : X.edgeFinset.card = Y.edgeFinset.card := by
    simpa only [card_edgeSet] using h.card_eq
  have hdeg := hb.degrees_pos heX
  have hdeg' := hb'.degrees_pos heY
  have hs : k₁ + k₂ = k₁' + k₂' := by
    have hs := h.largestEigenvalue_eq
    rw [hb.lineGraph_isRegularOfDegree.largestEigenvalue_eq,
      hb'.lineGraph_isRegularOfDegree.largestEigenvalue_eq] at hs
    have hs' : k₁ + k₂ - 2 = k₁' + k₂' - 2 := by exact_mod_cast hs
    omega
  have hn := h.card_add_bipartite_eq_of_connected hcX hcY
  rw [ite_eq_left hb.isBipartite, ite_eq_left hb'.isBipartite] at hn
  have hsize := hb.card_add_card
  have hsize' := hb'.card_add_card
  have hp := hb.card_mul_degree_left
  have hq := hb.card_mul_degree_right
  have hp' := hb'.card_mul_degree_left
  have hq' := hb'.card_mul_degree_right
  have hord := hb.degree_right_le_left heX hpq
  have hord' := hb'.degree_right_le_left heY hpq'
  have hprod : k₁ * k₂ * Fintype.card V = X.edgeFinset.card * (k₁ + k₂) := by
    rw [← hsize]
    nlinarith [congrArg (· * k₂) hp, congrArg (· * k₁) hq]
  have hprod' : k₁' * k₂' * Fintype.card W = Y.edgeFinset.card * (k₁' + k₂') := by
    rw [← hsize']
    nlinarith [congrArg (· * k₂') hp', congrArg (· * k₁') hq']
  have hN : 0 < Fintype.card V := by
    have : Nonempty V := hcX.nonempty
    exact Fintype.card_pos
  have hmul : k₁ * k₂ = k₁' * k₂' := by
    apply Nat.eq_of_mul_eq_mul_right hN
    have hn' : Fintype.card V = Fintype.card W := by omega
    rw [← hn', ← hm, ← hs] at hprod'
    exact hprod.trans hprod'.symm
  have hk : k₁ = k₁' := by
    have hsZ : (k₁ : ℤ) + k₂ = k₁' + k₂' := by exact_mod_cast hs
    have hpZ : (k₁ : ℤ) * k₂ = k₁' * k₂' := by exact_mod_cast hmul
    have hz : ((k₁ : ℤ) - k₁') * ((k₁ : ℤ) - k₂') = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with hz | hz
    · exact_mod_cast sub_eq_zero.mp hz
    · have hk' : k₁ = k₂' := by exact_mod_cast sub_eq_zero.mp hz
      omega
  have hk' : k₂ = k₂' := by omega
  subst k₁'
  subst k₂'
  exact ⟨Nat.eq_of_mul_eq_mul_right hdeg.1 (by omega),
    Nat.eq_of_mul_eq_mul_right hdeg.2 (by omega), rfl, rfl⟩

/-- The blueprint's `lem:tworoot` for [CGSS, Lemma 5.6]: every pair of ordered
biregular bipartitions of connected roots of cospectral line graphs has equal
part sizes, equal part degrees, and equal left Gram spectra. -/
theorem eq_of_lineGraph_cospectral (hb : X.IsBiregularWith P Q k₁ k₂)
    (hb' : Y.IsBiregularWith P' Q' k₁' k₂') (hcX : X.Connected) (hcY : Y.Connected)
    (heX : X.edgeSet.Nonempty) (heY : Y.edgeSet.Nonempty)
    (hpq : Nat.card P ≤ Nat.card Q) (hpq' : Nat.card P' ≤ Nat.card Q')
    (h : X.lineGraph.Cospectral Y.lineGraph) :
    Nat.card P = Nat.card P' ∧ Nat.card Q = Nat.card Q' ∧ k₁ = k₁' ∧ k₂ = k₂' ∧
      (X.biadjMatrix P Q ℝ * (X.biadjMatrix P Q ℝ)ᵀ).spectrumMultiset =
        (Y.biadjMatrix P' Q' ℝ * (Y.biadjMatrix P' Q' ℝ)ᵀ).spectrumMultiset := by
  obtain ⟨hp, hq, rfl, rfl⟩ :=
    hb.parameters_eq_of_lineGraph_cospectral hb' hcX hcY heX heY hpq hpq' h
  refine ⟨hp, hq, rfl, rfl, ?_⟩
  -- Steps `s5trC` and `s5trmap`: apply the common quadratic to the signless spectra.
  have hs := congrArg (Multiset.map (fun μ : ℝ ↦ (μ - k₁) * (μ - k₂)))
    (h.spectrumMultiset_signlessLapMatrix_of_connected_bipartite hcX hcY
      hb.isBipartite hb'.isBipartite)
  rw [hb.spectrumMultiset_map_quadratic_signlessLapMatrix_eq_gram_add_gram,
    hb'.spectrumMultiset_map_quadratic_signlessLapMatrix_eq_gram_add_gram] at hs
  -- Step `s5trLambda`: the rectangular identities recover each half, with its zero modes.
  have hX := spectrumMultiset_mul_comm_add_zeros
    (X.biadjMatrix P Q ℝ) (X.biadjMatrix P Q ℝ)ᵀ
  have hY := spectrumMultiset_mul_comm_add_zeros
    (Y.biadjMatrix P' Q' ℝ) (Y.biadjMatrix P' Q' ℝ)ᵀ
  apply Multiset.ext.mpr
  intro μ
  have hs' := congrArg (Multiset.count μ) hs
  have hX' := congrArg (Multiset.count μ) hX
  have hY' := congrArg (Multiset.count μ) hY
  simp only [Multiset.count_add, Multiset.count_replicate,
    ← Nat.card_eq_fintype_card, hp, hq] at hs' hX' hY'
  omega

end IsBiregularWith

end SimpleGraph
