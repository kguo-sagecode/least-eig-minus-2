/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Agreement
import LineGraphs.Hadamard.FixedRow

/-!
# Counting fourth rows

Blueprint Lemma `lem:6-fourth` for [CGSS], Section 6. Parseval in the fixed-row basis gives
the divisibility statement without using the erroneous row-sum identity in the paper.
-/

open scoped BigOperators RealInnerProductSpace

namespace Matrix

/-- The exceptional fourth rows in blueprint Lemma `lem:6-fourth`. -/
def fourthRows {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i k l : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ i ≠ j ∧ j ≠ k ∧ j ≠ l ∧
    (8 * (H.fourRowAgreeCount i j k l : ℤ)) ≠ n

namespace IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)

include hH

/-- Parseval in step `s6fparseval` of blueprint Lemma `lem:6-fourth`. -/
theorem sum_sq_inner_hadamardPairs (i k l : Fin n) :
    (∑ j, ⟪H.hadamardRowProduct i j, H.hadamardRowProduct k l⟫ ^ 2) = (n : ℝ) ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Fin.pos i))
  have he := congrArg (fun v ↦ ⟪v, H.hadamardRowProduct k l⟫)
    (hH.eq_sum_inner_hadamardRowProduct i (H.hadamardRowProduct k l))
  simp only [real_inner_smul_left, sum_inner, hH.inner_hadamardPairs_self] at he
  simp_rw [real_inner_comm (H.hadamardRowProduct k l), ← pow_two] at he
  field_simp at he
  simpa only [real_inner_comm] using he.symm

/-- Steps `s6fkl` and `s6fother`: each summand is zero or `x²`, with precisely the
exceptional fourth rows contributing `x²`. -/
theorem FourRowAgreement.inner_sq_eq_indicator {x : ℕ} (ha : hH.FourRowAgreement x)
    (i j k l : Fin n) (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    ⟪H.hadamardRowProduct i j, H.hadamardRowProduct k l⟫ ^ 2 =
      if j ∈ H.fourthRows i k l then (x : ℝ) ^ 2 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [hH.hadamardRowProduct_self, real_inner_comm, hH.inner_hadamardPairs_one k l hkl]
    simp [fourthRows]
  by_cases hjk : j = k
  · subst j
    rw [hadamardRowProduct_comm H i k,
      hH.inner_hadamardRowProduct_of_ne k i l hil]
    simp [fourthRows]
  by_cases hjl : j = l
  · subst j
    rw [hadamardRowProduct_comm H i l, hadamardRowProduct_comm H k l,
      hH.inner_hadamardRowProduct_of_ne l i k hik]
    simp [fourthRows]
  rw [hH.inner_hadamardPairs_of_disjoint i j k l hij hik hil hjk hjl hkl]
  simp only [fourthRows, Finset.mem_filter, Finset.mem_univ, true_and]
  have hh := ha i j k l hij hik hil hjk hjl hkl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  split_ifs with he
  · rcases hh with hh | hh | hh
    · exact (he.2.2.2 hh).elim
    · have hh' : 8 * (H.fourRowAgreeCount i j k l : ℝ) = (n : ℝ) - x := by
        exact_mod_cast hh
      rw [hh']; ring
    · have hh' : 8 * (H.fourRowAgreeCount i j k l : ℝ) = (n : ℝ) + x := by
        exact_mod_cast hh
      rw [hh']; ring
  · have he' : 8 * (H.fourRowAgreeCount i j k l : ℝ) = n := by
      have heq := not_not.mp (fun hg ↦ he ⟨hij, hjk, hjl, hg⟩)
      exact_mod_cast heq
    rw [he']; ring

/-- Blueprint Lemma `lem:6-fourth`: if `m` counts exceptional fourth rows, `m x² = n²`.
The hypotheses retain the blueprint's `n ≥ 3` and `x > 0`. -/
theorem FourRowAgreement.card_fourthRows {x : ℕ} (ha : hH.FourRowAgreement x)
    (_hn : 3 ≤ n) (_hx : 0 < x) (i k l : Fin n) (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    (H.fourthRows i k l).card * x ^ 2 = n ^ 2 := by
  have hs := hH.sum_sq_inner_hadamardPairs i k l
  simp_rw [ha.inner_sq_eq_indicator hH i _ k l hik hil hkl] at hs
  have he : (∑ j : Fin n, if j ∈ H.fourthRows i k l then (x : ℝ) ^ 2 else 0) =
      ((H.fourthRows i k l).card : ℝ) * (x : ℝ) ^ 2 := by
    rw [← Finset.sum_filter]
    simp
  rw [he] at hs
  exact_mod_cast hs

/-- The divisibility claim after Hypothesis 6.1 of [CGSS] (blueprint `lem:6-fourth`):
`x ∣ n`, obtained from `x² ∣ n²`. The hypothesis `3 ≤ n` supplies three distinct rows;
for orders one and two the four-row condition is vacuous and divisibility can fail
(e.g. `n = 2`, `x = 3`). For `n ≥ 3`, the fourth-row count forces `x > 0`. -/
theorem FourRowAgreement.dvd_card {x : ℕ} (ha : hH.FourRowAgreement x)
    (hn : 3 ≤ n) (hx : 0 < x) : x ∣ n := by
  have hn' : 2 < Fintype.card (Fin n) := by simpa using (show 2 < n by omega)
  obtain ⟨i, k, l, hik, hil, hkl⟩ := Fintype.two_lt_card_iff.mp hn'
  have he := ha.card_fourthRows hH hn hx i k l hik hil hkl
  exact (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    ⟨(H.fourthRows i k l).card, by simpa [mul_comm] using he.symm⟩

/-- The fourth-row count after Hypothesis 6.1 of [CGSS], the last clause of blueprint
`lem:6-fourth`: `d² = m` for `d = n/x`. Natural-number division is exact here,
because the proof first establishes `x ∣ n`. -/
theorem FourRowAgreement.div_sq_eq_card_fourthRows {x : ℕ} (ha : hH.FourRowAgreement x)
    (hx : 0 < x) (i k l : Fin n) (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    (n / x) ^ 2 = (H.fourthRows i k l).card := by
  have hn : 3 ≤ n := by
    have ht := Fintype.two_lt_card_iff.mpr ⟨i, k, l, hik, hil, hkl⟩
    simpa using (show 3 ≤ Fintype.card (Fin n) from ht)
  have he := ha.card_fourthRows hH hn hx i k l hik hil hkl
  have hd : x ∣ n := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    ⟨(H.fourthRows i k l).card, by simpa [mul_comm] using he.symm⟩
  have hm := Nat.div_mul_cancel hd
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hx 2)
  rw [← mul_pow, hm, he]

end IsHadamard
end Matrix
