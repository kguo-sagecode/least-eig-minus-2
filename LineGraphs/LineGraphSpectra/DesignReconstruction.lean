/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.DesignGraphs

/-!
# Recovering designs from the Gram spectrum

Theorem 5.8 of [CGSS], steps `s558bipgram` through `s558bipiso`.
The matrix calculation uses real zero-one matrices; the resulting labelled design
has the Hall–Connor interface, whose incidence matrix is integer valued.
-/

open scoped BigOperators Matrix
open Matrix

namespace Matrix

/-- The spectral toolkit's Theorem 7.7, used at `s558bipgram` in Theorem 5.8 of [CGSS].
Constant row and column sums and the stated Gram spectrum force the design identity.
The matrix identity itself does not need the zero-one or positivity hypotheses. -/
theorem gram_eq_of_two_eigenvalues {P B : Type*} [Fintype P] [Fintype B]
    [DecidableEq P] [Nonempty P] (N : Matrix P B ℝ) (r k lam : ℝ)
    (hrow : ∀ p, ∑ label, N p label = r) (hcol : ∀ label, ∑ p, N p label = k)
    (hparam : r * (k - 1) = lam * (Fintype.card P - 1))
    (hspec : (N * Nᵀ).spectrumMultiset =
      {r * k} + Multiset.replicate (Fintype.card P - 1) (r - lam)) :
    N * Nᵀ = (r - lam) • (1 : Matrix P P ℝ) + lam • of (fun _ _ ↦ (1 : ℝ)) := by
  classical
  let A := N * Nᵀ
  have hA : A.IsHermitian := by simp [A, isHermitian_iff_isSymm, IsSymm]
  have hrows : A *ᵥ (fun _ ↦ 1) = (r * k) • (fun _ ↦ 1) := by
    ext p
    simp only [A, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      mul_one, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hcol, ← Finset.sum_mul, hrow]
  let H : Matrix P P ℝ := A + (-(r - lam)) • 1 + (-lam) • of (fun _ _ ↦ (1 : ℝ))
  have hJ : (of (fun _ _ ↦ (1 : ℝ)) : Matrix P P ℝ).IsHermitian := by
    ext p q
    rfl
  have hH : H.IsHermitian :=
    (hA.add (isHermitian_one.smul (IsSelfAdjoint.all _))).add
      (hJ.smul (IsSelfAdjoint.all _))
  have htop : -(r - lam) + r * k + -lam * Fintype.card P = 0 := by nlinarith
  have hs : H.spectrumMultiset = {0} + Multiset.replicate (Fintype.card P - 1) 0 := by
    have hh := hA.spectrumMultiset_smul_add_smul_one_add_smul_allOnes
      hrows (-(r - lam)) 1 (-lam)
    simp only [one_smul, one_mul, show A.spectrumMultiset = _ from hspec,
      Multiset.singleton_add, Multiset.erase_cons_head, Multiset.map_replicate,
      neg_add_cancel, htop] at hh
    exact hh
  have hz : H = 0 := by
    have hz : Polynomial.aeval H Polynomial.X = 0 :=
      (hH.aeval_eq_zero_iff Polynomial.X).mpr (by
        intro μ hμ
        simp only [hs, Multiset.mem_add, Multiset.mem_singleton,
          Multiset.mem_replicate] at hμ
        rcases hμ with hμ | ⟨_, hμ⟩ <;> simpa using hμ)
    simpa using hz
  change A = _
  dsimp only [H] at hz
  rw [neg_smul, neg_smul] at hz
  apply sub_eq_zero.mp
  convert hz using 1
  abel

end Matrix

namespace Design

open SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Step `s558bipD2` of Theorem 5.8 of [CGSS]: recover the shared Hall–Connor design
from a real zero-one matrix. Block membership is `N p label = 1`; the design's
integer incidence matrix therefore casts back to `N`. -/
noncomputable def ofIncMatrix {P B : Type*} [Fintype P] [Fintype B]
    [DecidableEq P] [DecidableEq B] {v k b r lam : ℕ} (N : Matrix P B ℝ)
    (hv : Fintype.card P = v) (hb : Fintype.card B = b)
    (hvpos : 1 < v) (hkpos : 1 < k) (hbpos : 0 < b)
    (hzeroOne : ∀ p label, N p label = 0 ∨ N p label = 1)
    (hrow : ∀ p, ∑ label, N p label = (r : ℝ))
    (hcol : ∀ label, ∑ p, N p label = (k : ℝ))
    (hgram : N * Nᵀ = ((r : ℝ) - lam) • 1 + (lam : ℝ) • of (fun _ _ ↦ 1)) :
    Design P B v k b r lam := by
  have hentry (p : P) (label : B) : N p label = if N p label = 1 then 1 else 0 := by
    rcases hzeroOne p label with h | h <;> simp [h]
  refine {
    card_points := hv
    card_blocks := hb
    block := fun label ↦ Finset.univ.filter (fun p ↦ N p label = 1)
    card_block := ?_
    card_blocksThrough := ?_
    card_blocksThroughPair := ?_
    one_lt_v := hvpos
    one_lt_k := hkpos
    b_pos := hbpos }
  · intro label
    have he : ∑ p, N p label =
        ((Finset.univ.filter (fun p ↦ N p label = 1)).card : ℝ) := by
      calc
        _ = ∑ p, if N p label = 1 then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl (fun p _ ↦ hentry p label)
        _ = _ := by rw [Finset.sum_boole]
    exact_mod_cast he.symm.trans (hcol label)
  · intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have he : ∑ label, N p label =
        ((Finset.univ.filter (fun label ↦ N p label = 1)).card : ℝ) := by
      calc
        _ = ∑ label, if N p label = 1 then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl (fun label _ ↦ hentry p label)
        _ = _ := by rw [Finset.sum_boole]
    exact_mod_cast he.symm.trans (hrow p)
  · intro p q hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have he (label : B) : N p label * N q label =
        if N p label = 1 ∧ N q label = 1 then 1 else 0 := by
      rcases hzeroOne p label with hp | hp <;>
        rcases hzeroOne q label with hq | hq <;> simp [hp, hq]
    have h := congrArg (fun A : Matrix P P ℝ ↦ A p q) hgram
    simp only [Matrix.mul_apply, Matrix.transpose_apply, he, Finset.sum_boole,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hpq,
      smul_eq_mul, mul_zero, Matrix.of_apply, mul_one, zero_add] at h
    exact_mod_cast h

end Design

namespace SimpleGraph.IsBiregularWith

attribute [local instance] Classical.propDecidable

variable {W : Type*} [Fintype W] {Y : SimpleGraph W}
  [DecidableRel Y.Adj] {P Q : Set W} {r k : ℕ} (h : Y.IsBiregularWith P Q r k)

include h

/-- The row count at `s558bippick`, Theorem 5.8 of [CGSS]. -/
theorem biadjMatrix_row_sum (p : P) : ∑ q : Q, Y.biadjMatrix P Q ℝ p q = (r : ℝ) := by
  let e : {q : Q // Y.Adj p q} ≃ Y.neighborSet p :=
    { toFun := fun q ↦ ⟨q.val, q.property⟩
      invFun := fun q ↦ ⟨⟨q.val, h.isBipartiteWith.mem_of_mem_adj p.property q.property⟩,
        q.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hc := Fintype.card_congr e
  rw [Fintype.card_subtype, SimpleGraph.card_neighborSet_eq_degree,
    h.degree_left p p.property] at hc
  change (∑ q : Q, if Y.Adj p q then (1 : ℝ) else 0) = r
  rw [Finset.sum_boole]
  exact_mod_cast hc

/-- The column count at `s558bippick`, Theorem 5.8 of [CGSS]. -/
theorem biadjMatrix_col_sum (q : Q) : ∑ p : P, Y.biadjMatrix P Q ℝ p q = (k : ℝ) := by
  have hh := h.symm.biadjMatrix_row_sum q
  convert hh using 1
  apply Finset.sum_congr rfl
  intro p _
  change (if Y.Adj p q then (1 : ℝ) else 0) = if Y.Adj q p then 1 else 0
  simp only [Y.adj_comm]

end SimpleGraph.IsBiregularWith

namespace Design

open SimpleGraph

attribute [local instance] Classical.propDecidable

variable {P B W : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  [Fintype W] [DecidableEq W] {v k b r lam : ℕ} (D : Design P B v k b r lam)

include D

/-- Steps `s558bipgram`–`s558bipiso`, Theorem 5.8 of [CGSS]: a biregular graph
with the design's part sizes and Gram spectrum is an incidence graph of a design
with exactly the same parameters. -/
theorem exists_design_of_biregular_gram_spectrum (Y : SimpleGraph W) [DecidableRel Y.Adj]
    (S T : Set W) (hbi : Y.IsBiregularWith S T r k)
    (hS : Nat.card S = v) (hT : Nat.card T = b)
    (hspec : (Y.biadjMatrix S T ℝ * (Y.biadjMatrix S T ℝ)ᵀ).spectrumMultiset =
      {(r : ℝ) * k} + Multiset.replicate (v - 1) ((r : ℝ) - lam)) :
    ∃ D₂ : Design S T v k b r lam, Nonempty (D₂.incidenceGraph ≃g Y) := by
  have hS' : Fintype.card S = v := by simpa only [Nat.card_eq_fintype_card] using hS
  have hT' : Fintype.card T = b := by simpa only [Nat.card_eq_fintype_card] using hT
  have : Nonempty S := Fintype.card_pos_iff.mp (by
    rw [hS']
    have := D.one_lt_v
    omega)
  let N := Y.biadjMatrix S T ℝ
  have hrow := hbi.biadjMatrix_row_sum
  have hcol := hbi.biadjMatrix_col_sum
  have hparam : (r : ℝ) * ((k : ℝ) - 1) = (lam : ℝ) * (Fintype.card S - 1) := by
    rw [hS']
    have hp := congrArg (fun n : ℕ ↦ (n : ℝ)) D.r_mul_k_sub_one_eq
    have hk := D.one_lt_k
    have hv := D.one_lt_v
    simpa only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_sub (by omega : 1 ≤ v), Nat.cast_one] using hp
  have hgram := Matrix.gram_eq_of_two_eigenvalues N r k lam hrow hcol hparam
    (by simpa only [hS'] using hspec)
  have h01 (p : S) (label : T) : N p label = 0 ∨ N p label = 1 := by
    change (if Y.Adj p label then (1 : ℝ) else 0) = 0 ∨ _
    by_cases h : Y.Adj p label <;> simp [h, N, SimpleGraph.biadjMatrix]
  let D₂ := ofIncMatrix N hS' hT' D.one_lt_v D.one_lt_k D.b_pos h01 hrow hcol hgram
  have hmem (p : S) (label : T) : p ∈ D₂.block label ↔ Y.Adj p label := by
    change p ∈ Finset.univ.filter (fun p ↦ N p label = 1) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (if Y.Adj p label then (1 : ℝ) else 0) = 1 ↔ _
    by_cases h : Y.Adj p label <;> simp [h]
  refine ⟨D₂, ⟨{ toEquiv := hbi.sumEquiv, map_rel_iff' := ?_ }⟩⟩
  rintro (p | label) (q | other)
  · change Y.Adj p q ↔ False
    refine ⟨fun hpq ↦ ?_, False.elim⟩
    exact Set.disjoint_left.mp hbi.isBipartiteWith.disjoint q.property
      (hbi.isBipartiteWith.mem_of_mem_adj p.property hpq)
  · change Y.Adj p other ↔ p ∈ D₂.block other
    exact (hmem p other).symm
  · change Y.Adj label q ↔ q ∈ D₂.block label
    rw [Y.adj_comm]
    exact (hmem q label).symm
  · change Y.Adj label other ↔ False
    refine ⟨fun hadj ↦ ?_, False.elim⟩
    exact Set.disjoint_left.mp hbi.isBipartiteWith.disjoint
      (hbi.isBipartiteWith.symm.mem_of_mem_adj label.property hadj) other.property

end Design
