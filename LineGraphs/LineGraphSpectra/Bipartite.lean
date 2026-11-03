/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.RootRecovery

/-!
# Cospectral line graphs of bipartite graphs

Lemma 5.6 of [CGSS], in the form of `blueprint/sec5-spectral.tex`.
The bipartite alternative quantifies over every ordered biregular bipartition.
-/

open Matrix

namespace SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {X : SimpleGraph V} {Y : SimpleGraph W} [DecidableRel X.Adj] [DecidableRel Y.Adj]

-- Lemma 5.6
/-- Lemma 5.6 of [CGSS], in the blueprint's form. The second root has no isolated
vertices (Implicit hypothesis 5). In the bipartite alternative the chosen ordered
biregular bipartition of the first root is arbitrary. The nonbipartite degree is
expressed by `2 * κ = h + 2`, without natural-number division. The first root
is required to have an edge, excluding the degenerate connected graph `K₁`. -/
theorem lineGraph_cospectral_bipartite_forall_isBiregularWith
    (hcX : X.Connected) (hbX : X.IsBipartite) (heX : X.edgeSet.Nonempty)
    {h : ℕ} (hrX : X.lineGraph.IsRegularOfDegree h) (hnoY : ∀ v, 0 < Y.degree v)
    (hs : X.lineGraph.Cospectral Y.lineGraph) :
    Y.Connected ∧
      ((Y.IsBipartite ∧ ∀ (P Q : Set V) (k₁ k₂ : ℕ),
          X.IsBiregularWith P Q k₁ k₂ → Nat.card P ≤ Nat.card Q →
          ∃ P' Q' : Set W, Y.IsBiregularWith P' Q' k₁ k₂ ∧
            Nat.card P' = Nat.card P ∧ Nat.card Q' = Nat.card Q ∧
            (X.biadjMatrix P Q ℝ * (X.biadjMatrix P Q ℝ)ᵀ).spectrumMultiset =
              (Y.biadjMatrix P' Q' ℝ * (Y.biadjMatrix P' Q' ℝ)ᵀ).spectrumMultiset) ∨
        (¬ (∃ k, X.IsRegularOfDegree k)) ∧
          (∃ κ, Y.IsRegularOfDegree κ ∧ 2 * κ = h + 2) ∧
          ¬ Y.IsBipartite ∧ Fintype.card V = Fintype.card W + 1) := by
  -- Step `s556L1`: the first root has no isolates and a nonempty connected line graph.
  have hnoX := hcX.degree_pos_of_edgeSet_nonempty heX
  have hcLX := (lineGraph_connected_iff_of_no_isolated heX
    (fun v ↦ (X.degree_pos_iff_exists_adj v).mp (hnoX v))).mpr hcX
  have : Nonempty X.edgeSet := heX.to_subtype
  -- Step `s556L2`: regularity and connectedness transfer across cospectrality.
  have hrY := hs.isRegularOfDegree hrX
  have hcLY := hs.connected_of_regular hrX hcLX
  have heY : Y.edgeSet.Nonempty := by
    obtain ⟨e⟩ := hcLY.nonempty
    exact ⟨e.val, e.property⟩
  have hcY := connected_of_lineGraph_connected
    (fun v ↦ (Y.degree_pos_iff_exists_adj v).mp (hnoY v)) hcLY
  refine ⟨hcY, ?_⟩
  by_cases hbY : Y.IsBipartite
  · -- Steps `s556given`, `s556pick`: choose only the second bipartition.
    left
    refine ⟨hbY, fun P Q k₁ k₂ hbi hpq ↦ ?_⟩
    obtain ⟨P', Q', k₁', k₂', hbi', hpq'⟩ :=
      exists_isBiregularWith_of_lineGraph_regular hbY hnoY hcLY hrY
    obtain ⟨hp, hq, hk₁, hk₂, hgram⟩ :=
      hbi.eq_of_lineGraph_cospectral hbi' hcX hcY heX heY hpq hpq' hs
    subst k₁'
    subst k₂'
    exact ⟨P', Q', hbi', hp.symm, hq.symm, hgram⟩
  · -- Step `s556st`: a nonbipartite root is regular and loses one vertex.
    right
    have hregY : ∃ κ, Y.IsRegularOfDegree κ := by
      rcases regular_or_isBiregularWith_of_lineGraph_regular hnoY hcLY hrY with
        hreg | ⟨P, Q, k₁, k₂, hbi, _⟩
      · exact hreg
      · exact (hbY hbi.isBipartite).elim
    obtain ⟨κ, hκ⟩ := hregY
    have hn := hs.card_add_bipartite_eq_of_connected hcX hcY
    rw [ite_eq_left hbX, ite_eq_right hbY, Nat.add_zero] at hn
    have hnotreg : ¬ (∃ k, X.IsRegularOfDegree k) := by
      rintro ⟨k, hk⟩
      have heq := hk.card_eq_of_lineGraph_cospectral hκ heX heY hs
      omega
    -- Step `s556reg`: read the degree equation at an edge of the second root.
    have hκeq : 2 * κ = h + 2 := by
      obtain ⟨⟨u, v⟩, huv⟩ := heY
      have hdeg := degree_lineGraph huv
      rw [hrY.degree_eq, hκ.degree_eq, hκ.degree_eq] at hdeg
      have hpos := hnoY u
      rw [hκ.degree_eq] at hpos
      omega
    exact ⟨hnotreg, ⟨κ, hκ, hκeq⟩, hbY, hn⟩

end SimpleGraph
