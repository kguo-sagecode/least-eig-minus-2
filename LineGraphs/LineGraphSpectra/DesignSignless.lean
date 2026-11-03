/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.DesignSpectrum

/-!
# Signless spectra and line-graph cospectrality

Steps `s5exC1b` and `s5exnz` of Example 5.13 (`ex:5.13`) of [CGSS].
The full multiplicity formulas include the single zero mode of a connected
bipartite root and the extra zero modes in the edge Gram matrices.
-/

open Matrix

attribute [local instance] Classical.propDecidable

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam : ℕ}

/-- The full signless spectrum in `s5exC1b`, Example 5.13 of [CGSS], before
substituting the example's parameters. -/
theorem spectrumMultiset_signlessLapMatrix_incidenceGraph
    (D : Design P B v k b r lam) (hl : lam < r) (hrk : r ≠ k) :
    (D.incidenceGraph.signlessLapMatrix ℝ).spectrumMultiset =
      {0} + {(r : ℝ) + k} +
      Multiset.replicate (v - 1)
        (((r : ℝ) + k + Real.sqrt (((r : ℝ) - k) ^ 2 + 4 * (r - lam))) / 2) +
      Multiset.replicate (v - 1)
        (((r : ℝ) + k - Real.sqrt (((r : ℝ) - k) ^ 2 + 4 * (r - lam))) / 2) +
      Multiset.replicate (b - v) (k : ℝ) := by
  let hb := D.incidenceGraph_isBiregularWith
  have hp : Fintype.card D.pointPart = v := by
    simpa only [Nat.card_eq_fintype_card] using D.card_pointPart
  have hq : Fintype.card D.blockPart = b := by
    simpa only [Nat.card_eq_fintype_card] using D.card_blockPart
  have hne : (r : ℝ) ≠ k := by exact_mod_cast hrk
  rw [← Matrix.spectrumMultiset_submatrix_equiv _ hb.sumEquiv,
    hb.signlessLapMatrix_eq_fromBlocks,
    Matrix.spectrumMultiset_fromBlocks_scalar_of_ne _ _ _ hne]
  rw [D.spectrumMultiset_biadjMatrix_mul_transpose, D.rank_biadjMatrix,
    D.rank_realIncMatrix_of_lam_lt_r hl, hp, hq]
  have hpos : (0 : ℝ) < (r : ℝ) * k := by
    exact_mod_cast Nat.mul_pos D.r_pos (by have := D.one_lt_k; omega)
  have hrl : (0 : ℝ) < (r : ℝ) - lam := sub_pos.mpr (by exact_mod_cast hl)
  have hf : ({(r : ℝ) * k} + Multiset.replicate (v - 1) ((r : ℝ) - lam)).filter
      (0 < ·) = {(r : ℝ) * k} + Multiset.replicate (v - 1) ((r : ℝ) - lam) := by
    apply Multiset.filter_eq_self.mpr
    intro μ hμ
    rcases Multiset.mem_add.mp hμ with hμ | hμ
    · simpa only [Multiset.mem_singleton.mp hμ] using hpos
    · simpa only [(Multiset.mem_replicate.mp hμ).2] using hrl
  have hsqrt : Real.sqrt (((r : ℝ) - k) ^ 2 + 4 * ((r : ℝ) * k)) = (r : ℝ) + k := by
    rw [show ((r : ℝ) - k) ^ 2 + 4 * ((r : ℝ) * k) = ((r : ℝ) + k) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hf]
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.map_replicate,
    hsqrt, Nat.sub_self, Multiset.replicate_zero, add_zero]
  rw [show ((r : ℝ) + k + ((r : ℝ) + k)) / 2 = (r : ℝ) + k by ring,
    show ((r : ℝ) + k - ((r : ℝ) + k)) / 2 = 0 by ring]
  abel

end Design

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  (X : SimpleGraph V) (Y : SimpleGraph W) [DecidableRel X.Adj] [DecidableRel Y.Adj]

/-- Steps `s5exnz` and `s5exline`, Example 5.13 of [CGSS]: equal edge counts
and signless spectra differing by one zero give cospectral line graphs. -/
theorem lineGraph_cospectral_of_signless_spectrum_add_zero
    (hm : X.edgeFinset.card = Y.edgeFinset.card)
    (hs : (X.signlessLapMatrix ℝ).spectrumMultiset =
      {0} + (Y.signlessLapMatrix ℝ).spectrumMultiset) : X.lineGraph.Cospectral Y.lineGraph := by
  have hn : Fintype.card V = Fintype.card W + 1 := by
    have he := congrArg Multiset.card hs
    rw [X.isHermitian_signlessLapMatrix.card_spectrumMultiset, Multiset.card_add,
      Multiset.card_singleton, Y.isHermitian_signlessLapMatrix.card_spectrumMultiset] at he
    omega
  have hx := Matrix.spectrumMultiset_mul_comm_add_zeros (X.edgeIncMatrix ℝ)
    (X.edgeIncMatrix ℝ)ᵀ
  have hy := Matrix.spectrumMultiset_mul_comm_add_zeros (Y.edgeIncMatrix ℝ)
    (Y.edgeIncMatrix ℝ)ᵀ
  rw [X.edgeIncMatrix_mul_transpose, X.card_edgeSet] at hx
  rw [Y.edgeIncMatrix_mul_transpose, Y.card_edgeSet] at hy
  have he : ((X.edgeIncMatrix ℝ)ᵀ * X.edgeIncMatrix ℝ).spectrumMultiset =
      ((Y.edgeIncMatrix ℝ)ᵀ * Y.edgeIncMatrix ℝ).spectrumMultiset := by
    apply add_left_cancel (a := Multiset.replicate (Fintype.card V) (0 : ℝ))
    calc
      _ = Multiset.replicate X.edgeFinset.card 0 +
          (X.signlessLapMatrix ℝ).spectrumMultiset := hx.symm
      _ = {0} + (Multiset.replicate Y.edgeFinset.card 0 +
          (Y.signlessLapMatrix ℝ).spectrumMultiset) := by rw [hs, hm]; abel
      _ = {0} + (Multiset.replicate (Fintype.card W) 0 +
          ((Y.edgeIncMatrix ℝ)ᵀ * Y.edgeIncMatrix ℝ).spectrumMultiset) := by rw [hy]
      _ = _ := by rw [hn, Multiset.replicate_add, Multiset.replicate_one]; abel
  rw [X.transpose_edgeIncMatrix_mul, Y.transpose_edgeIncMatrix_mul] at he
  have hX := (X.lineGraph.isHermitian_adjMatrix ℝ).spectrumMultiset_smul_one_add_smul 2 1
  have hY := (Y.lineGraph.isHermitian_adjMatrix ℝ).spectrumMultiset_smul_one_add_smul 2 1
  simp only [one_smul, one_mul] at hX hY
  rw [hX, hY] at he
  apply cospectral_iff_spectrumMultiset_eq.mpr
  exact Multiset.map_injective (fun a b hab ↦ add_left_cancel hab) he

end SimpleGraph
