/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Models
import Mathlib.Data.Fin.Rev

/-!
# Integer orientations of Dynkin supports

The entry recovery and orientation steps of Theorem A, Remark 3.11.
-/

namespace Matrix.IsFiniteCartan

open Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {M : Matrix ι ι ℤ}

/-- Reindexing preserves finite Cartan matrices (Theorem A, Remark 3.11). -/
theorem submatrix (hM : M.IsFiniteCartan) (e : κ ≃ ι) :
    (M.submatrix e e).IsFiniteCartan := by
  refine ⟨fun i ↦ hM.diag _, fun i j hij ↦ hM.offDiag_nonpos _ _ (e.injective.ne hij),
    fun i j ↦ hM.zero_comm _ _, ?_⟩
  obtain ⟨d, hd, hp⟩ := hM.exists_posDef
  refine ⟨d ∘ e, fun i ↦ hd _, ?_⟩
  rw [← submatrix_diagonal_equiv d e, submatrix_mul_equiv]
  exact hp.submatrix e.injective

/-- Reindexing commutes with canonical weights (Theorem A, Remark 3.11). -/
theorem weightedGraph_submatrix (hM : M.IsFiniteCartan) (e : κ ≃ ι) :
    (hM.submatrix e).weightedGraph = hM.weightedGraph.reindex e.symm := by
  apply WeightedGraph.ext
  funext i j
  change (if i = j then (0 : ℝ) else Real.sqrt ((M (e i) (e j) * M (e j) (e i) : ℤ) : ℝ)) =
    if e i = e j then 0 else Real.sqrt ((M (e i) (e j) * M (e j) (e i) : ℤ) : ℝ)
  simp

/-- The integer product is the square of its canonical weight
(the entry recovery step of Theorem A, Remark 3.11). -/
theorem weightedGraph_weight_sq (hM : M.IsFiniteCartan) {i j : ι} (hij : i ≠ j) :
    hM.weightedGraph.weights i j ^ 2 = (M i j * M j i : ℤ) := by
  simp only [weightedGraph, ite_eq_right hij]
  apply Real.sq_sqrt
  exact_mod_cast mul_nonneg_of_nonpos_of_nonpos (hM.offDiag_nonpos i j hij)
    (hM.offDiag_nonpos j i hij.symm)

/-- A zero weight recovers a zero entry (Theorem A, Remark 3.11). -/
theorem entry_eq_zero_of_weight_eq_zero (hM : M.IsFiniteCartan) {i j : ι} (hij : i ≠ j)
    (hw : hM.weightedGraph.weights i j = 0) : M i j = 0 := by
  have hp := hM.weightedGraph_weight_sq hij
  rw [hw] at hp
  have hp' : M i j * M j i = 0 := by exact_mod_cast hp.symm
  rcases mul_eq_zero.mp hp' with h | h
  · exact h
  · exact (hM.zero_comm i j).mpr h

/-- A unit weight recovers the entry minus one (Theorem A, Remark 3.11). -/
theorem entry_eq_neg_one_of_weight_eq_one (hM : M.IsFiniteCartan) {i j : ι} (hij : i ≠ j)
    (hw : hM.weightedGraph.weights i j = 1) : M i j = -1 := by
  have hp := hM.weightedGraph_weight_sq hij
  rw [hw] at hp
  have hp' : M i j * M j i = 1 := by exact_mod_cast hp.symm
  have hi := hM.offDiag_nonpos i j hij
  have hj := hM.offDiag_nonpos j i hij.symm
  have hi' : M i j < 0 := by nlinarith
  have hj' : M j i < 0 := by nlinarith
  nlinarith

/-- A double edge has the two possible integer orientations
(Theorem A, Remark 3.11). -/
theorem entry_pair_of_weight_eq_sqrt_two (hM : M.IsFiniteCartan) {i j : ι}
    (hij : i ≠ j) (hw : hM.weightedGraph.weights i j = Real.sqrt 2) :
    (M i j = -2 ∧ M j i = -1) ∨ (M i j = -1 ∧ M j i = -2) := by
  have hp := hM.weightedGraph_weight_sq hij
  rw [hw, Real.sq_sqrt (by norm_num)] at hp
  have hp' : M i j * M j i = 2 := by exact_mod_cast hp.symm
  have hi := hM.offDiag_nonpos i j hij
  have hj := hM.offDiag_nonpos j i hij.symm
  have hi' : M i j < 0 := by nlinarith
  have hj' : M j i < 0 := by nlinarith
  have hbound : -2 ≤ M i j := by nlinarith
  have hcases : M i j = -2 ∨ M i j = -1 := by omega
  rcases hcases with h | h <;> rw [h] at hp' <;> omega

/-- A triple edge has the two possible integer orientations
(Theorem A, Remark 3.11). -/
theorem entry_pair_of_weight_eq_sqrt_three (hM : M.IsFiniteCartan) {i j : ι}
    (hij : i ≠ j) (hw : hM.weightedGraph.weights i j = Real.sqrt 3) :
    (M i j = -3 ∧ M j i = -1) ∨ (M i j = -1 ∧ M j i = -3) := by
  have hp := hM.weightedGraph_weight_sq hij
  rw [hw, Real.sq_sqrt (by norm_num)] at hp
  have hp' : M i j * M j i = 3 := by exact_mod_cast hp.symm
  have hi := hM.offDiag_nonpos i j hij
  have hj := hM.offDiag_nonpos j i hij.symm
  have hi' : M i j < 0 := by nlinarith
  have hj' : M j i < 0 := by nlinarith
  have hbound : -3 ≤ M i j := by nlinarith
  have hcases : M i j = -3 ∨ M i j = -2 ∨ M i j = -1 := by omega
  rcases hcases with h | h | h <;> rw [h] at hp' <;> omega

/-- Unit-weight supports determine all their integer entries
(the A, D, E recognition step of Theorem A, Remark 3.11). -/
theorem eq_of_weightedGraph_eq_of_isSimplyLaced (hM : M.IsFiniteCartan)
    {N : Matrix ι ι ℤ} (hdiag : ∀ i, N i i = 2) (hsym : N.IsSymm)
    (hN : N.IsSimplyLaced) (hw : hM.weightedGraph = CartanMatrix.weightedGraph N) : M = N := by
  ext i j
  by_cases hij : i = j
  · subst j; rw [hM.diag, hdiag]
  rcases hN hij with h | h
  · rw [h]
    apply hM.entry_eq_zero_of_weight_eq_zero hij
    rw [hw]
    simp [CartanMatrix.weightedGraph, hij, h]
  · rw [h]
    apply hM.entry_eq_neg_one_of_weight_eq_one hij
    rw [hw]
    simp [CartanMatrix.weightedGraph, hij, hsym.apply i j, h]

/-- Once the ordered entries of the sole multiple edge are fixed, weights recover
the whole matrix (Theorem A, Remark 3.11). -/
theorem eq_of_weightedGraph_eq_of_entry_pair (hM : M.IsFiniteCartan)
    {N : Matrix ι ι ℤ} (hdiag : ∀ i, N i i = 2) {p q : ι}
    (hrest : ∀ i j, i ≠ j → (i, j) ≠ (p, q) → (i, j) ≠ (q, p) →
      N j i = N i j ∧ (N i j = 0 ∨ N i j = -1))
    (hw : hM.weightedGraph = CartanMatrix.weightedGraph N)
    (hpq : M p q = N p q) (hqp : M q p = N q p) : M = N := by
  ext i j
  by_cases hij : i = j
  · subst j; rw [hM.diag, hdiag]
  by_cases hp : (i, j) = (p, q)
  · rcases Prod.mk.inj hp with ⟨rfl, rfl⟩; exact hpq
  by_cases hq : (i, j) = (q, p)
  · rcases Prod.mk.inj hq with ⟨rfl, rfl⟩; exact hqp
  obtain ⟨hs, hz | hu⟩ := hrest i j hij hp hq
  · rw [hz]
    apply hM.entry_eq_zero_of_weight_eq_zero hij
    rw [hw]
    simp [CartanMatrix.weightedGraph, hij, hz]
  · rw [hu]
    apply hM.entry_eq_neg_one_of_weight_eq_one hij
    rw [hw]
    simp [CartanMatrix.weightedGraph, hij, hs, hu]

/-- The two orientations of a sole double edge give a model or its transpose
(Theorem A, Remark 3.11). -/
theorem eq_or_transpose_of_weightedGraph_eq (hM : M.IsFiniteCartan)
    {N : Matrix ι ι ℤ} (hdiag : ∀ i, N i i = 2) {p q : ι} (hne : p ≠ q)
    (hpq : N p q = -2) (hqp : N q p = -1)
    (hrest : ∀ i j, i ≠ j → (i, j) ≠ (p, q) → (i, j) ≠ (q, p) →
      N j i = N i j ∧ (N i j = 0 ∨ N i j = -1))
    (hw : hM.weightedGraph = CartanMatrix.weightedGraph N) : M = N ∨ M = N.transpose := by
  have hweight : hM.weightedGraph.weights p q = Real.sqrt 2 := by
    rw [hw]
    norm_num [CartanMatrix.weightedGraph, hne, hpq, hqp]
  rcases hM.entry_pair_of_weight_eq_sqrt_two hne hweight with h | h
  · exact Or.inl (hM.eq_of_weightedGraph_eq_of_entry_pair hdiag hrest hw
      (h.1.trans hpq.symm) (h.2.trans hqp.symm))
  · refine Or.inr (hM.eq_of_weightedGraph_eq_of_entry_pair hdiag (p := p) (q := q)
      (N := N.transpose) ?_ ?_ (h.1.trans hqp.symm) (h.2.trans hpq.symm))
    · intro i j hij hi hj
      obtain ⟨hs, hv⟩ := hrest i j hij hi hj
      simpa only [transpose_apply, hs] using (And.intro (rfl : N i j = N i j) hv)
    · rwa [CartanMatrix.weightedGraph_transpose]

end Matrix.IsFiniteCartan

namespace WeightedGraph

/-- Reversing a double path moves its exceptional edge to the reflected position
(Theorem A, Remark 3.11). -/
theorem singleDoublePath_reindex_rev (n k : ℕ) (hk : k + 1 < n) :
    (singleDoublePath n k).reindex Fin.revPerm = singleDoublePath n (n - 2 - k) := by
  apply ext
  funext i j
  change (singleDoublePath n k).weights i.rev j.rev =
    (singleDoublePath n (n - 2 - k)).weights i j
  simp only [singleDoublePath, path, Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> first | rfl | omega

end WeightedGraph

namespace Matrix.IsFiniteCartan

open Matrix CartanMatrix

/-- A terminal double edge distinguishes B from C before the rank-two normalization
(Theorem A, Remark 3.11). -/
theorem eq_B_or_C_of_weightedGraph_eq {n : ℕ} (hn : 2 ≤ n)
    {M : Matrix (Fin n) (Fin n) ℤ} (hM : M.IsFiniteCartan)
    (hw : hM.weightedGraph = CartanMatrix.weightedGraph (B n)) : M = B n ∨ M = C n := by
  let p : Fin n := ⟨n - 2, by omega⟩
  let q : Fin n := ⟨n - 1, by omega⟩
  have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; dsimp [p, q] at this; omega
  have hforward : B n p q = -2 := by
    simp only [B, of_apply, ite_eq_right hpq, p, q]
    split_ifs <;> omega
  have hreverse : B n q p = -1 := by
    simp only [B, of_apply, ite_eq_right hpq.symm, p, q]
    split_ifs <;> omega
  have hrest : ∀ i j : Fin n, i ≠ j → (i, j) ≠ (p, q) → (i, j) ≠ (q, p) →
      B n j i = B n i j ∧ (B n i j = 0 ∨ B n i j = -1) := by
    intro i j hij hi hj
    have hi' : ¬(i.val = n - 2 ∧ j.val = n - 1) := by
      rintro ⟨hi', hj'⟩
      exact hi (Prod.ext (Fin.ext hi') (Fin.ext hj'))
    have hj' : ¬(i.val = n - 1 ∧ j.val = n - 2) := by
      rintro ⟨hi', hj'⟩
      exact hj (Prod.ext (Fin.ext hi') (Fin.ext hj'))
    simp only [B, of_apply, ite_eq_right hij, ite_eq_right hij.symm]
    split_ifs <;> norm_num <;> omega
  simpa only [B_transpose] using hM.eq_or_transpose_of_weightedGraph_eq
    (B_diag n) hpq hforward hreverse hrest hw

/-- On the middle double path, the integer matrix is F or its transpose
(Theorem A, Remark 3.11). -/
theorem eq_F₄_or_transpose_of_weightedGraph_eq {M : Matrix (Fin 4) (Fin 4) ℤ}
    (hM : M.IsFiniteCartan) (hw : hM.weightedGraph = CartanMatrix.weightedGraph F₄) :
    M = F₄ ∨ M = F₄.transpose := by
  apply hM.eq_or_transpose_of_weightedGraph_eq F₄_diag (p := 1) (q := 2)
    (by decide) (by decide) (by decide) _ hw
  intro i j hij hi hj
  fin_cases i <;> fin_cases j <;> norm_num [F₄, Fin.ext_iff] at *

/-- A triple edge gives G or its transpose (Theorem A, Remark 3.11). -/
theorem eq_G₂_or_transpose_of_weightedGraph_eq {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M.IsFiniteCartan) (hw : hM.weightedGraph = CartanMatrix.weightedGraph G₂) :
    M = G₂ ∨ M = G₂.transpose := by
  have hv : hM.weightedGraph.weights 0 1 = Real.sqrt 3 := by
    rw [hw]
    norm_num [CartanMatrix.weightedGraph, G₂]
  rcases hM.entry_pair_of_weight_eq_sqrt_three (by decide : (0 : Fin 2) ≠ 1) hv with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> first | exact hM.diag _ | exact h.1 | exact h.2
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> first | exact hM.diag _ | exact h.1 | exact h.2

end Matrix.IsFiniteCartan

namespace CartanMatrix

/-- At rank two, reversing C gives the canonical B model (Theorem A, Remark 3.11). -/
theorem C_two_submatrix_rev : (C 2).submatrix Fin.revPerm Fin.revPerm = B 2 := by
  decide +kernel

/-- Reversing the transpose of F restores Mathlib's orientation (Theorem A, Remark 3.11). -/
theorem F₄_transpose_submatrix_rev : F₄.transpose.submatrix Fin.revPerm Fin.revPerm = F₄ := by
  decide +kernel

/-- Reversing the transpose of G restores Mathlib's orientation (Theorem A, Remark 3.11). -/
theorem G₂_transpose_submatrix_rev : G₂.transpose.submatrix Fin.revPerm Fin.revPerm = G₂ := by
  decide +kernel

end CartanMatrix
