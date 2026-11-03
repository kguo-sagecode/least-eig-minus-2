/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.DesignGraphs

/-!
# The nonbipartite spectrum of a design's rival root

Theorem 5.8 of [CGSS], steps `s558nbrem`, `s558nbfish`, and `s558nbtriv`.
This supplies the spectrum required as input by computation C11. Both the
full-row-rank case and the rank-one full-block case are included.
-/

open Matrix SimpleGraph

namespace Design

attribute [local instance] Classical.propDecidable

variable {P B W : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  [Fintype W] [DecidableEq W] {v k b r lam : ℕ} (D : Design P B v k b r lam)

/-- Step `s558nbtrivrho`, Theorem 5.8 of [CGSS]: the full-block incidence matrix has rank one. -/
theorem rank_realIncMatrix_of_lam_eq_r (hl : lam = r) : D.realIncMatrix.rank = 1 := by
  have hrk : (0 : ℝ) < (r : ℝ) * k := by
    exact_mod_cast Nat.mul_pos D.r_pos (by have := D.one_lt_k; omega)
  have hsym : (D.realIncMatrix * D.realIncMatrixᵀ).IsHermitian := by
    simp [isHermitian_iff_isSymm, Matrix.IsSymm]
  have hr := hsym.rank_add_eigenvalueMultiplicity_zero
  rw [rank_self_mul_transpose, D.card_points] at hr
  have hz : (D.realIncMatrix * D.realIncMatrixᵀ).eigenvalueMultiplicity 0 = v - 1 := by
    change Multiset.count 0 (D.realIncMatrix * D.realIncMatrixᵀ).spectrumMultiset = v - 1
    rw [D.spectrumMultiset_incMatrix_mul_transpose, hl]
    simp [ne_of_lt hrk]
  have := D.one_lt_v
  omega

/-- Steps `s558nbrem`–`s558nbtriv`, Theorem 5.8 of [CGSS]: derive C11's input spectrum
from Remark 5.7, rather than assuming it. The rank-one branch combines the two negative
multiplicities; this is the correction in Error 14. -/
theorem lineGraph_spectrum_of_not_isBipartite (hvb : v ≤ b)
    (Y : SimpleGraph W) [DecidableRel Y.Adj] (hno : ∀ w, 0 < Y.degree w)
    (hnb : ¬ Y.IsBipartite) (hs : D.flagGraph.Cospectral Y.lineGraph) :
    k < r ∧ Y.spectrumMultiset =
      {((r : ℝ) + k) / 2} + Multiset.replicate (b - v) (-(((r : ℝ) - k) / 2)) +
      Multiset.replicate (v - 1) (Real.sqrt (r - lam + (((r : ℝ) - k) / 2) ^ 2)) +
      Multiset.replicate (v - 1) (-Real.sqrt (r - lam + (((r : ℝ) - k) / 2) ^ 2)) := by
  have hneq : r ≠ k := by
    obtain ⟨_, hcases⟩ := lineGraph_cospectral_bipartite_forall_isBiregularWith
      D.incidenceGraph_connected D.incidenceGraph_isBiregularWith.isBipartite
      D.incidenceGraph_edgeSet_nonempty D.flagGraph_isRegularOfDegree hno hs
    exact fun he ↦ (hcases.resolve_left (fun h ↦ hnb h.1)).1
      (D.incidenceGraph_isRegular_iff.mpr he)
  have hpq : Nat.card D.pointPart ≤ Nat.card D.blockPart := by
    simpa only [D.card_pointPart, D.card_blockPart] using hvb
  obtain ⟨hkr, _, _, hspec⟩ :=
    lineGraph_cospectral_bipartite_spectrum_of_not_isBipartite
      D.incidenceGraph_connected D.incidenceGraph_edgeSet_nonempty
      D.incidenceGraph_isBiregularWith hneq hpq hno hnb hs
  refine ⟨hkr, ?_⟩
  dsimp only at hspec
  rw [D.spectrumMultiset_biadjMatrix_mul_transpose, D.card_pointPart,
    D.card_blockPart, D.rank_biadjMatrix] at hspec
  have hrk : (0 : ℝ) < (r : ℝ) * k := by
    exact_mod_cast Nat.mul_pos D.r_pos (by have := D.one_lt_k; omega)
  have hquad : ((r : ℝ) - k) ^ 2 / 4 = (((r : ℝ) - k) / 2) ^ 2 := by ring
  rw [hquad] at hspec
  rcases lt_or_eq_of_le D.lam_le_r with hl | hl
  · -- Steps `s558nbfishrho` and `s558nbfish`.
    have hrl : (0 : ℝ) < (r : ℝ) - lam := sub_pos.mpr (by exact_mod_cast hl)
    have hf : ({(r : ℝ) * k} + Multiset.replicate (v - 1) ((r : ℝ) - lam)).filter
        (0 < ·) = {(r : ℝ) * k} + Multiset.replicate (v - 1) ((r : ℝ) - lam) := by
      apply Multiset.filter_eq_self.mpr
      intro μ hμ
      rcases Multiset.mem_add.mp hμ with hμ | hμ
      · simpa only [Multiset.mem_singleton.mp hμ] using hrk
      · simpa only [(Multiset.mem_replicate.mp hμ).2] using hrl
    rw [hf] at hspec
    simp only [Multiset.singleton_add,
      Multiset.erase_cons_head, Multiset.map_replicate,
      D.rank_realIncMatrix_of_lam_lt_r hl, Nat.sub_self,
      Multiset.replicate_zero, add_zero, neg_div] at hspec
    rw [hspec]
    simp only [← Multiset.singleton_add]
    abel
  · -- Steps `s558nbtrivrho`, `s558nbtrivc`, and `s558nbtriv`.
    have hdelta : 0 ≤ ((r : ℝ) - k) / 2 := by
      have : (k : ℝ) < r := by exact_mod_cast hkr
      linarith
    have hcounts : b - 1 = (b - v) + (v - 1) := by have := D.one_lt_v; omega
    have hf : (Multiset.replicate (v - 1) (0 : ℝ)).filter (0 < ·) = 0 := by
      apply Multiset.filter_eq_nil.mpr
      intro μ hμ
      rw [(Multiset.mem_replicate.mp hμ).2]
      exact lt_irrefl _
    simp only [hl, sub_self, Multiset.filter_add, Multiset.filter_singleton,
      ite_eq_left hrk, hf, add_zero,
      Multiset.erase_singleton, Multiset.map_zero, D.rank_realIncMatrix_of_lam_eq_r hl,
      neg_div] at hspec
    rw [hspec, hl, sub_self, zero_add, Real.sqrt_sq hdelta, hcounts,
      Multiset.replicate_add]
    abel

end Design
