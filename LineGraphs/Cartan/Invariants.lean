/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Converse

/-!
# Intrinsic invariants of the named Cartan matrices

The seven finite counts of `def:rem-invariants`, Remark 3.11. Counts use natural
numbers; their casts give the nonnegative integers in the blueprint's table.
-/

namespace CartanMatrix

open Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Off-diagonal support degree in `def:rem-invariants`, Remark 3.11. -/
def supportDegree (N : Matrix ι ι ℤ) (i : ι) : ℕ :=
  ∑ j, if j ≠ i ∧ N i j ≠ 0 then 1 else 0

/-- The counts `(n,t,u,b,a_in,a_out,s)` of `def:rem-invariants`, Remark 3.11.
The last coordinate counts leaves adjacent to a branch, rather than ordered pairs. -/
def supportInvariants (N : Matrix ι ι ℤ) : Fin 7 → ℕ :=
  ![Fintype.card ι,
    ∑ i, ∑ j, if N i j * N j i = 3 then 1 else 0,
    ∑ i, ∑ j, if N i j * N j i = 2 then 1 else 0,
    ∑ i, if supportDegree N i = 3 then 1 else 0,
    ∑ i, ∑ j, if N i j = -2 ∧ supportDegree N j = 1 then 1 else 0,
    ∑ i, ∑ j, if N i j = -2 ∧ supportDegree N i = 1 then 1 else 0,
    ∑ i, if supportDegree N i = 1 ∧
      (∃ j, N i j ≠ 0 ∧ supportDegree N j = 3) then 1 else 0]

/-- Support degree is unchanged by relabelling (`lem:rem-invariants`, Remark 3.11). -/
theorem supportDegree_submatrix (N : Matrix ι ι ℤ) (e : κ ≃ ι) (i : κ) :
    supportDegree (N.submatrix e e) i = supportDegree N (e i) := by
  unfold supportDegree
  rw [← e.sum_comp (fun j ↦ if j ≠ e i ∧ N (e i) j ≠ 0 then (1 : ℕ) else 0)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [submatrix_apply, ne_eq, e.injective.eq_iff]
  congr 1

/-- All seven counts are invariant under reindexing
(`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_reindex (N : Matrix ι ι ℤ) (e : κ ≃ ι) :
    supportInvariants (N.submatrix e e) = supportInvariants N := by
  have hsum (f : ι → ℕ) : (∑ i, f (e i)) = ∑ i, f i := e.sum_comp f
  have hsum₂ (f : ι → ι → ℕ) : (∑ i, ∑ j, f (e i) (e j)) = ∑ i, ∑ j, f i j := by
    simp_rw [hsum]
    exact hsum (fun i ↦ ∑ j, f i j)
  have hex (i : κ) : (∃ j : κ, N (e i) (e j) ≠ 0 ∧ supportDegree N (e j) = 3) ↔
      ∃ j : ι, N (e i) j ≠ 0 ∧ supportDegree N j = 3 := by
    constructor
    · rintro ⟨j, hj⟩; exact ⟨e j, hj⟩
    · rintro ⟨j, hj⟩
      obtain ⟨j, rfl⟩ := e.surjective j
      exact ⟨j, hj⟩
  ext r
  fin_cases r <;> dsimp [supportInvariants] <;>
    (try simp only [supportDegree_submatrix, hex])
  · exact Fintype.card_congr e
  · exact hsum₂ (fun i j ↦ if N i j * N j i = 3 then 1 else 0)
  · exact hsum₂ (fun i j ↦ if N i j * N j i = 2 then 1 else 0)
  · exact hsum (fun i ↦ if supportDegree N i = 3 then 1 else 0)
  · exact hsum₂ (fun i j ↦ if N i j = -2 ∧ supportDegree N j = 1 then 1 else 0)
  · exact hsum₂ (fun i j ↦ if N i j = -2 ∧ supportDegree N i = 1 then 1 else 0)
  · exact hsum (fun i ↦ if supportDegree N i = 1 ∧
      (∃ j, N i j ≠ 0 ∧ supportDegree N j = 3) then 1 else 0)

/-- Counting a specified index in `Fin n` (`lem:rem-invariants`, Remark 3.11). -/
theorem sum_ite_fin_val_eq (n k : ℕ) :
    (∑ i : Fin n, if i.val = k then (1 : ℕ) else 0) = if k < n then 1 else 0 := by
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    have he (i : Fin n) : i.val = k ↔ i = j :=
      (Fin.ext_iff (a := i) (b := j)).symm
    simp [he, hk]
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (by have hi := i.isLt; omega)]

/-- A path's support degree is its number of existing predecessor and successor indices
(`lem:rem-invariants`, Remark 3.11). -/
theorem supportDegree_A (n : ℕ) (i : Fin n) :
    supportDegree (A n) i = (if 0 < i.val then 1 else 0) +
      (if i.val + 1 < n then 1 else 0) := by
  have hi := i.isLt
  have hentry (j : Fin n) :
      (if j ≠ i ∧ A n i j ≠ 0 then (1 : ℕ) else 0) =
        (if 0 < i.val then (if j.val = i.val - 1 then 1 else 0) else 0) +
        (if j.val = i.val + 1 then 1 else 0) := by
    simp only [A, of_apply, ne_eq, Fin.ext_iff]
    split_ifs <;>
      (try simp only [not_false_eq_true, and_true, not_true_eq_false, and_false] at *) <;> omega
  simp only [supportDegree, hentry, Finset.sum_add_distrib]
  by_cases h : 0 < i.val
  · simp only [h, ite_true, sum_ite_fin_val_eq]
    rw [ite_eq_left (by omega : i.val - 1 < n)]
  · simp only [h, ite_false, Finset.sum_const_zero, zero_add, sum_ite_fin_val_eq]

/-- B has the same support degrees as A (`lem:rem-invariants`, Remark 3.11). -/
theorem supportDegree_B (n : ℕ) (i : Fin n) : supportDegree (B n) i = supportDegree (A n) i := by
  apply Finset.sum_congr rfl
  intro j _
  simp only [B, A, of_apply]
  split_ifs <;> simp_all

/-- C has the same support degrees as A (`lem:rem-invariants`, Remark 3.11). -/
theorem supportDegree_C (n : ℕ) (i : Fin n) : supportDegree (C n) i = supportDegree (A n) i := by
  apply Finset.sum_congr rfl
  intro j _
  simp only [C, A, of_apply]
  split_ifs <;> simp_all

/-- The A row of the invariant table (`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_A (n : ℕ) : supportInvariants (A n) = ![n, 0, 0, 0, 0, 0, 0] := by
  have hentry (i j : Fin n) : A n i j ≠ -2 := by
    simp only [A, of_apply]; split_ifs <;> norm_num
  have hprod (i j : Fin n) : A n i j * A n j i ≠ 2 ∧ A n i j * A n j i ≠ 3 := by
    simp only [A, of_apply]; split_ifs <;> norm_num
  have hbranch (i : Fin n) : supportDegree (A n) i ≠ 3 := by
    rw [supportDegree_A]; split_ifs <;> omega
  simp [supportInvariants, hentry, hbranch, hprod]

/-- Above the diagonal, D has a consecutive edge or the edge to its last leaf.
This is the entry calculation used by `lem:rem-invariants`, Remark 3.11. -/
private theorem D_apply_of_lt (n : ℕ) (i j : Fin n) (hij : i < j) :
    D n i j = if (i.val + 1 = j.val ∧ j.val + 1 < n) ∨
      (i.val + 3 = n ∧ j.val + 1 = n) then -1 else 0 := by
  have hj := j.isLt
  have hlt : i.val < j.val := hij
  have hback : ¬(j.val + 1 = i.val ∧ i.val + 2 < n) := by omega
  have hfork : ¬(j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n)) := by omega
  simp only [D, of_apply, ne_of_lt hij, hback, hfork, ite_false]
  by_cases hn : n ≤ 2
  · rw [ite_eq_left hn, ite_eq_right (by omega)]
  · rw [ite_eq_right hn]
    by_cases hedge : i.val + 1 = j.val ∧ j.val + 2 < n
    · rw [ite_eq_left hedge, ite_eq_left (by omega)]
    · rw [ite_eq_right hedge]
      congr 1
      apply propext
      omega

/-- The four possible neighbours of a D vertex, with the lower entries obtained by symmetry
(`lem:rem-invariants`, Remark 3.11). -/
private theorem D_support_iff (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) :
    (j ≠ i ∧ D n i j ≠ 0) ↔
      (0 < i.val ∧ i.val + 1 < n ∧ j.val = i.val - 1) ∨
      (i.val + 2 < n ∧ j.val = i.val + 1) ∨
      (i.val + 3 = n ∧ j.val = n - 1) ∨
      (i.val + 1 = n ∧ j.val = n - 3) := by
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hlt : i.val < j.val := hij
    rw [D_apply_of_lt n i j hij]
    simp only [ne_eq, Fin.ext_iff]
    split_ifs <;> norm_num <;> omega
  · simp only [ne_eq, not_true_eq_false, false_and, false_iff]
    omega
  · have hlt : j.val < i.val := hji
    rw [(D_isSymm n).apply j i, D_apply_of_lt n j i hji]
    simp only [ne_eq, Fin.ext_iff]
    split_ifs <;> norm_num <;> omega

/-- The D degrees in `lem:rem-invariants`, Remark 3.11: one branch and three leaves. -/
theorem supportDegree_D (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    supportDegree (D n) i =
      if i.val + 3 = n then 3 else if i.val = 0 ∨ i.val + 2 = n ∨ i.val + 1 = n
        then 1 else 2 := by
  have hi := i.isLt
  have hentry (j : Fin n) :
      (if j ≠ i ∧ D n i j ≠ 0 then (1 : ℕ) else 0) =
        (if 0 < i.val ∧ i.val + 1 < n then (if j.val = i.val - 1 then 1 else 0) else 0) +
        (if i.val + 2 < n then (if j.val = i.val + 1 then 1 else 0) else 0) +
        (if i.val + 3 = n then (if j.val = n - 1 then 1 else 0) else 0) +
        (if i.val + 1 = n then (if j.val = n - 3 then 1 else 0) else 0) := by
    simp only [D_support_iff n hn i j, ← ite_and]
    split_ifs <;> omega
  simp only [supportDegree, hentry, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, sum_ite_fin_val_eq, Finset.sum_const_zero]
  split_ifs <;> omega

/-- D has just one branch, at Mathlib index `n-3` (`lem:rem-invariants`, Remark 3.11). -/
theorem supportDegree_D_eq_three (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    supportDegree (D n) i = 3 ↔ i.val = n - 3 := by
  rw [supportDegree_D n hn]
  split_ifs <;> omega

/-- Counting a specified ordered pair (`lem:rem-invariants`, Remark 3.11). -/
theorem sum_ite_pair_eq (p q : ι) (a : ℕ) :
    (∑ i, ∑ j, if i = p ∧ j = q then a else 0) = a := by
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The invariant counts for a path with one oriented double edge
(`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_of_single_double_path {n : ℕ} (N : Matrix (Fin n) (Fin n) ℤ)
    (p q : Fin n) (hpq : p ≠ q) (hdegree : ∀ i, supportDegree N i ≤ 2)
    (hneg : ∀ i j, N i j = -2 ↔ i = p ∧ j = q)
    (hprod₂ : ∀ i j, N i j * N j i = 2 ↔ (i = p ∧ j = q) ∨ (i = q ∧ j = p))
    (hprod₃ : ∀ i j, N i j * N j i ≠ 3) :
    supportInvariants N = ![n, 0, 2, 0,
      if supportDegree N q = 1 then 1 else 0,
      if supportDegree N p = 1 then 1 else 0, 0] := by
  have hbranch (i) : supportDegree N i ≠ 3 := by have := hdegree i; omega
  have hdoubles : (∑ i, ∑ j, if N i j * N j i = 2 then 1 else 0) = (2 : ℕ) := by
    have he (i j) : (if N i j * N j i = 2 then (1 : ℕ) else 0) =
        (if i = p ∧ j = q then 1 else 0) + (if i = q ∧ j = p then 1 else 0) := by
      simp only [hprod₂]
      split_ifs <;> simp_all
    simp only [he, Finset.sum_add_distrib, sum_ite_pair_eq]
  have hin : (∑ i, ∑ j, if N i j = -2 ∧ supportDegree N j = 1 then 1 else 0) =
      (if supportDegree N q = 1 then 1 else 0 : ℕ) := by
    have he (i j) : (if N i j = -2 ∧ supportDegree N j = 1 then (1 : ℕ) else 0) =
        if i = p ∧ j = q then (if supportDegree N q = 1 then 1 else 0) else 0 := by
      simp only [hneg]
      split_ifs <;> simp_all
    simp only [he, sum_ite_pair_eq]
  have hout : (∑ i, ∑ j, if N i j = -2 ∧ supportDegree N i = 1 then 1 else 0) =
      (if supportDegree N p = 1 then 1 else 0 : ℕ) := by
    have he (i j) : (if N i j = -2 ∧ supportDegree N i = 1 then (1 : ℕ) else 0) =
        if i = p ∧ j = q then (if supportDegree N p = 1 then 1 else 0) else 0 := by
      simp only [hneg]
      split_ifs <;> simp_all
    simp only [he, sum_ite_pair_eq]
  simp only [supportInvariants, hprod₃, hbranch, hdoubles, hin, hout, and_false,
    exists_false, ite_false, Finset.sum_const_zero, Fintype.card_fin]

/-- The B rows of the invariant table, including the rank-two exception
(`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_B (n : ℕ) (hn : 2 ≤ n) :
    supportInvariants (B n) = ![n, 0, 2, 0, 1, if n = 2 then 1 else 0, 0] := by
  let p : Fin n := ⟨n - 2, by omega⟩
  let q : Fin n := ⟨n - 1, by omega⟩
  have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; dsimp [p, q] at this; omega
  have hdeg (i) : supportDegree (B n) i ≤ 2 := by
    rw [supportDegree_B, supportDegree_A]; split_ifs <;> omega
  have hneg (i j : Fin n) : B n i j = -2 ↔ i = p ∧ j = q := by
    have hi := i.isLt
    have hj := j.isLt
    have hs : n - 2 + 1 = n - 1 := by omega
    simp only [Fin.ext_iff]
    dsimp only [p, q]
    simp only [B, of_apply, Fin.ext_iff]
    clear hpq p q hdeg
    split_ifs <;> constructor <;> intro h <;>
      first | omega | (exfalso; revert h; decide)
  have hprod₂ (i j : Fin n) : B n i j * B n j i = 2 ↔
      (i = p ∧ j = q) ∨ (i = q ∧ j = p) := by
    have hi := i.isLt
    have hj := j.isLt
    simp only [Fin.ext_iff]
    dsimp only [p, q]
    simp only [B, of_apply, Fin.ext_iff]
    split_ifs <;> omega
  have hprod₃ (i j : Fin n) : B n i j * B n j i ≠ 3 := by
    simp only [B, of_apply]; split_ifs <;> norm_num
  rw [supportInvariants_of_single_double_path (B n) p q hpq hdeg hneg hprod₂ hprod₃]
  have hq : supportDegree (B n) q = 1 := by
    rw [supportDegree_B, supportDegree_A]
    dsimp [q]
    split_ifs <;> omega
  have hp : supportDegree (B n) p = 1 ↔ n = 2 := by
    rw [supportDegree_B, supportDegree_A]
    dsimp [p]
    split_ifs <;> omega
  simp only [hq, hp, ite_true]

/-- The C row of the invariant table (`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_C (n : ℕ) (hn : 3 ≤ n) :
    supportInvariants (C n) = ![n, 0, 2, 0, 0, 1, 0] := by
  let p : Fin n := ⟨n - 1, by omega⟩
  let q : Fin n := ⟨n - 2, by omega⟩
  have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; dsimp [p, q] at this; omega
  have hdeg (i) : supportDegree (C n) i ≤ 2 := by
    rw [supportDegree_C, supportDegree_A]; split_ifs <;> omega
  have hneg (i j : Fin n) : C n i j = -2 ↔ i = p ∧ j = q := by
    have hi := i.isLt
    have hj := j.isLt
    have hs : n - 2 + 1 = n - 1 := by omega
    simp only [Fin.ext_iff]
    dsimp only [p, q]
    simp only [C, of_apply, Fin.ext_iff]
    clear hpq p q hdeg
    split_ifs <;> constructor <;> intro h <;>
      first | omega | (exfalso; revert h; decide)
  have hprod₂ (i j : Fin n) : C n i j * C n j i = 2 ↔
      (i = p ∧ j = q) ∨ (i = q ∧ j = p) := by
    have hi := i.isLt
    have hj := j.isLt
    simp only [Fin.ext_iff]
    dsimp only [p, q]
    simp only [C, of_apply, Fin.ext_iff]
    split_ifs <;> omega
  have hprod₃ (i j : Fin n) : C n i j * C n j i ≠ 3 := by
    simp only [C, of_apply]; split_ifs <;> norm_num
  rw [supportInvariants_of_single_double_path (C n) p q hpq hdeg hneg hprod₂ hprod₃]
  have hq : supportDegree (C n) q = 2 := by
    rw [supportDegree_C, supportDegree_A]
    dsimp [q]
    split_ifs <;> omega
  have hp : supportDegree (C n) p = 1 := by
    rw [supportDegree_C, supportDegree_A]
    dsimp [p]
    split_ifs <;> omega
  simp only [hq, hp, ite_true, show (2 : ℕ) ≠ 1 by omega, ite_false]

/-- The D rows of the invariant table, including the three short arms of D₄
(`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_D (n : ℕ) (hn : 4 ≤ n) :
    supportInvariants (D n) = ![n, 0, 0, 1, 0, 0, if n = 4 then 3 else 2] := by
  have hentry (i j : Fin n) : D n i j ≠ -2 := by
    by_cases hij : i = j
    · subst j; simp only [D_diag]; norm_num
    · rcases isSimplyLaced_D n hij with h | h <;> rw [h] <;> norm_num
  have hprod (i j : Fin n) : D n i j * D n j i ≠ 2 ∧ D n i j * D n j i ≠ 3 := by
    rw [(D_isSymm n).apply i j]
    by_cases hij : i = j
    · subst j; simp only [D_diag]; norm_num
    · rcases isSimplyLaced_D n hij with h | h <;> rw [h] <;> norm_num
  have hbranch : (∑ i : Fin n, if supportDegree (D n) i = 3 then 1 else 0) = (1 : ℕ) := by
    simp only [supportDegree_D_eq_three n hn, sum_ite_fin_val_eq]
    rw [ite_eq_left (by omega : n - 3 < n)]
  let b : Fin n := ⟨n - 3, by omega⟩
  have hb (i : Fin n) : supportDegree (D n) i = 3 ↔ i = b := by
    rw [supportDegree_D_eq_three n hn]
    exact (Fin.ext_iff (a := i) (b := b)).symm
  have hleaf (i : Fin n) : (supportDegree (D n) i = 1 ∧
      ∃ j, D n i j ≠ 0 ∧ supportDegree (D n) j = 3) ↔
      i.val = n - 2 ∨ i.val = n - 1 ∨ (n = 4 ∧ i.val = 0) := by
    have hi := i.isLt
    have hex : (∃ j, D n i j ≠ 0 ∧ supportDegree (D n) j = 3) ↔ D n i b ≠ 0 := by
      constructor
      · rintro ⟨j, hj, hd⟩
        have he := (hb j).mp hd
        subst j
        exact hj
      · intro h
        exact ⟨b, h, (hb b).mpr rfl⟩
    by_cases hib : i = b
    · subst i
      simp only [(hb b).mpr rfl, show (3 : ℕ) ≠ 1 by decide, false_and, false_iff]
      dsimp only [b]
      omega
    · have hsupport := (and_iff_right (Ne.symm hib)).symm.trans (D_support_iff n hn i b)
      rw [hex, supportDegree_D n hn, hsupport]
      dsimp only [b]
      split_ifs <;> omega
  have hshort : (∑ i : Fin n, if supportDegree (D n) i = 1 ∧
      (∃ j, D n i j ≠ 0 ∧ supportDegree (D n) j = 3) then 1 else 0) =
      (if n = 4 then 3 else 2 : ℕ) := by
    have he (i : Fin n) : (if supportDegree (D n) i = 1 ∧
        (∃ j, D n i j ≠ 0 ∧ supportDegree (D n) j = 3) then (1 : ℕ) else 0) =
        (if i.val = n - 2 then 1 else 0) + (if i.val = n - 1 then 1 else 0) +
        (if n = 4 then (if i.val = 0 then 1 else 0) else 0) := by
      simp only [hleaf]
      split_ifs <;> first | (simp_all; done) | (simp_all; omega)
    simp only [he, Finset.sum_add_distrib, Finset.sum_ite_irrel, sum_ite_fin_val_eq,
      Finset.sum_const_zero]
    split_ifs <;> omega
  simp only [supportInvariants, hentry, hprod, hbranch, false_and,
    ite_false, Finset.sum_const_zero, Fintype.card_fin]
  refine congrArg (fun x : ℕ ↦ (![n, 0, 0, 1, 0, 0, x] : Fin 7 → ℕ)) ?_
  convert hshort

/-- The E₆ row of the invariant table (`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_E₆ : supportInvariants (E 6) = ![6, 0, 0, 1, 0, 0, 1] := by
  decide +kernel

/-- The E₇ row of the invariant table (`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_E₇ : supportInvariants (E 7) = ![7, 0, 0, 1, 0, 0, 1] := by
  decide +kernel

/-- The E₈ row of the invariant table (`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_E₈ : supportInvariants (E 8) = ![8, 0, 0, 1, 0, 0, 1] := by
  decide +kernel

/-- The F₄ row of the invariant table (`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_F₄ : supportInvariants F₄ = ![4, 0, 2, 0, 0, 0, 0] := by
  decide +kernel

/-- The G₂ row of the invariant table (`lem:rem-invariants`, Remark 3.11). -/
theorem supportInvariants_G₂ : supportInvariants G₂ = ![2, 2, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- The table in `lem:rem-invariants`, Remark 3.11, indexed by the permitted types. -/
def modelInvariants {n : ℕ} : FiniteType n → Fin 7 → ℕ
  | .a n _ => ![n, 0, 0, 0, 0, 0, 0]
  | .b n _ => ![n, 0, 2, 0, 1, if n = 2 then 1 else 0, 0]
  | .c n _ => ![n, 0, 2, 0, 0, 1, 0]
  | .d n _ => ![n, 0, 0, 1, 0, 0, if n = 4 then 3 else 2]
  | .e₆ => ![6, 0, 0, 1, 0, 0, 1]
  | .e₇ => ![7, 0, 0, 1, 0, 0, 1]
  | .e₈ => ![8, 0, 0, 1, 0, 0, 1]
  | .f₄ => ![4, 0, 2, 0, 0, 0, 0]
  | .g₂ => ![2, 2, 0, 0, 0, 0, 0]

/-- All rows of the named-model invariant table (`lem:rem-invariants`, Remark 3.11). -/
theorem model_supportInvariants {n : ℕ} (t : FiniteType n) :
    supportInvariants (modelEntries t) = modelInvariants t := by
  cases t with
  | a n _ => exact supportInvariants_A n
  | b n hn => exact supportInvariants_B n hn
  | c n hn => exact supportInvariants_C n hn
  | d n hn => exact supportInvariants_D n hn
  | e₆ => exact supportInvariants_E₆
  | e₇ => exact supportInvariants_E₇
  | e₈ => exact supportInvariants_E₈
  | f₄ => exact supportInvariants_F₄
  | g₂ => exact supportInvariants_G₂

/-- The invariant table distinguishes all permitted choices at a fixed rank
(the uniqueness step of Theorem A, Remark 3.11). -/
theorem FiniteType.eq_of_modelInvariants_eq {n : ℕ} (s t : FiniteType n)
    (h : modelInvariants s = modelInvariants t) : s = t := by
  have h₁ := congr_fun h 1
  have h₂ := congr_fun h 2
  have h₃ := congr_fun h 3
  have h₄ := congr_fun h 4
  have h₅ := congr_fun h 5
  have h₆ := congr_fun h 6
  clear h
  cases s <;> cases t <;> first | rfl |
    (dsimp [modelInvariants] at h₁ h₂ h₃ h₄ h₅ h₆
     (try split_ifs at h₆) <;> omega)

/-- Two permitted named matrices equal after simultaneous reindexing have the same
type and rank. The labelling itself need not be unique (Theorem A, Remark 3.11). -/
theorem IsFiniteTypeModel.type_eq_of_reindex_eq {m n : ℕ} (s : FiniteType m) (t : FiniteType n)
    (e : Fin n ≃ Fin m) (h : (modelEntries s).submatrix e e = modelEntries t) :
    (⟨m, s⟩ : (n : ℕ) × FiniteType n) = ⟨n, t⟩ := by
  have hmn : n = m := by simpa using Fintype.card_congr e
  subst n
  have hinv := congrArg supportInvariants h
  rw [supportInvariants_reindex, model_supportInvariants, model_supportInvariants] at hinv
  have ht := s.eq_of_modelInvariants_eq t hinv
  subst t
  rfl

end CartanMatrix
