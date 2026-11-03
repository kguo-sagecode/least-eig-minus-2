/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Lines

/-!
# The degree of the Hadamard line system

Blueprint Lemma `lem:6-lines`, part 5, Section 6 of [CGSS].
-/

open scoped BigOperators RealInnerProductSpace

namespace Matrix.IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
include hH

omit hH in
/-- Symmetry of `C_H`, used in step `s6ldiag` of blueprint Lemma `lem:6-lines`. -/
theorem hadamardSignedAdj_symm (_hH : H.IsHadamard) (x : ℕ) (p q : HadamardPair n) :
    H.hadamardSignedAdj x p q = H.hadamardSignedAdj x q p := by
  simp only [hadamardSignedAdj, smul_apply, sub_apply, hadamardPairs_gram_apply,
    smul_eq_mul, one_apply]
  rw [real_inner_comm]
  congr 3
  simp only [eq_comm]

/-- The diagonal of the quadratic identity, steps `s6lsq` and `s6ldiag`. -/
theorem sum_sq_hadamardSignedAdj (hn : 16 ∣ n) (hn16 : 16 ≤ n) (p : HadamardPair n) :
    (∑ q, H.hadamardSignedAdj (n / 2) p q ^ 2) = 2 * ((n : ℝ) - 2) := by
  have hq := hH.lineSystem_quadratic hn hn16
  rw [add_mul, mul_sub, mul_sub, mul_smul_comm, mul_one, smul_mul_assoc, one_mul,
    smul_mul_assoc, mul_smul_comm, one_mul, smul_smul] at hq
  have he := congrArg (fun M : Matrix (HadamardPair n) (HadamardPair n) ℝ ↦ M p p) hq
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, hH.hadamardSignedAdj_diag,
    mul_zero, sub_zero, zero_sub, one_apply_eq, mul_one, zero_apply] at he
  have hs : ((H.hadamardSignedAdj (n / 2)) * H.hadamardSignedAdj (n / 2)) p p =
      ∑ q, H.hadamardSignedAdj (n / 2) p q ^ 2 := by
    simp only [mul_apply]
    apply Finset.sum_congr rfl
    intro q _
    rw [hH.hadamardSignedAdj_symm (n / 2) q p, pow_two]
  rw [hs] at he
  linarith

/-- Blueprint Lemma `lem:6-lines`, part 5: each line has exactly `2n - 4` nonorthogonal
neighbors. This is a count of distinct pairs, with the diagonal explicitly excluded. -/
theorem card_adj_lineSystem (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths)
    (p : HadamardPair n) :
    (Finset.univ.filter fun q : HadamardPair n ↦ q ≠ p ∧
      ⟪H.hadamardRoot p, H.hadamardRoot q⟫ ≠ 0).card = 2 * n - 4 := by
  classical
  have hx : 0 < n / 2 := by omega
  have hs := hH.sum_sq_hadamardSignedAdj hn hn16 p
  have ht (q : HadamardPair n) : H.hadamardSignedAdj (n / 2) p q ^ 2 =
      if q ≠ p ∧ ⟪H.hadamardRoot p, H.hadamardRoot q⟫ ≠ 0 then (1 : ℝ) else 0 := by
    by_cases hpq : p = q
    · subst q
      simp [hH.hadamardSignedAdj_diag]
    · rw [hH.inner_hadamardRoot_eq_signedAdj hn hn16 p q hpq]
      have hh := (hH.fourRowAgreement_half hn ha).hadamardSignedAdj_mem hH hx p q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with hh | hh | hh <;> simp [hh, Ne.symm hpq]
  simp_rw [ht] at hs
  rw [Finset.sum_boole] at hs
  have hcast : ((2 * n - 4 : ℕ) : ℝ) = 2 * ((n : ℝ) - 2) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hcast] at hs
  exact_mod_cast hs

end Matrix.IsHadamard
