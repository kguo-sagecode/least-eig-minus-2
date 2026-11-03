/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Matrix

/-!
# Entries and the quadratic identity

Blueprint Lemmas `lem:6-CHentries` and `lem:6-quadratic`, Section 6 of [CGSS].
-/

open scoped BigOperators RealInnerProductSpace

namespace Matrix

/-- Row products are independent of the order of the two rows (`def:6-pairs`). -/
theorem hadamardRowProduct_comm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    H.hadamardRowProduct i j = H.hadamardRowProduct j i := by
  ext c
  exact mul_comm _ _

/-- The entries of `PPᵀ` are the inner products in blueprint Lemma `lem:6-gram`. -/
theorem hadamardPairs_gram_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (p q : HadamardPair n) :
    (H.hadamardPairs * H.hadamardPairsᵀ) p q =
      ⟪H.hadamardRowProduct p.1.1 p.1.2, H.hadamardRowProduct q.1.1 q.1.2⟫ := by
  simp [mul_apply, hadamardPairs, hadamardRowProduct, PiLp.inner_apply,
    RCLike.inner_apply, mul_comm]

namespace IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)

/-- Blueprint Lemma `lem:6-CHentries`, steps `s6Cmeet` and `s6Cdisj`, before division by `x`. -/
theorem FourRowAgreement.inner_hadamardPairs_mem {x : ℕ} (ha : hH.FourRowAgreement x)
    (p q : HadamardPair n) (hpq : p ≠ q) :
    ⟪H.hadamardRowProduct p.1.1 p.1.2, H.hadamardRowProduct q.1.1 q.1.2⟫ ∈
      ({0, -(x : ℝ), (x : ℝ)} : Set ℝ) := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  rcases q with ⟨⟨k, l⟩, hkl⟩
  dsimp at hpq ⊢
  by_cases hik : i = k
  · subst k
    have hjl : j ≠ l := by rintro rfl; exact hpq rfl
    rw [hH.inner_hadamardRowProduct_of_ne i j l hjl]
    simp
  by_cases hil : i = l
  · subst l
    rw [hadamardRowProduct_comm H k i,
      hH.inner_hadamardRowProduct_of_ne i j k (ne_of_gt (hkl.trans hij))]
    simp
  by_cases hjk : j = k
  · subst k
    rw [hadamardRowProduct_comm H i j,
      hH.inner_hadamardRowProduct_of_ne j i l (ne_of_lt (hij.trans hkl))]
    simp
  by_cases hjl : j = l
  · subst l
    rw [hadamardRowProduct_comm H i j, hadamardRowProduct_comm H k j,
      hH.inner_hadamardRowProduct_of_ne j i k hik]
    simp
  rw [hH.inner_hadamardPairs_of_disjoint i j k l hij.ne hik hil hjk hjl hkl.ne]
  have hh := ha i j k l hij.ne hik hil hjk hjl hkl.ne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh ⊢
  rcases hh with hh | hh | hh
  · left
    have hh' : 8 * (H.fourRowAgreeCount i j k l : ℝ) = n := by exact_mod_cast hh
    linarith
  · right; left
    have hh' : 8 * (H.fourRowAgreeCount i j k l : ℝ) = (n : ℝ) - x := by
      exact_mod_cast hh
    linarith
  · right; right
    have hh' : 8 * (H.fourRowAgreeCount i j k l : ℝ) = (n : ℝ) + x := by
      exact_mod_cast hh
    linarith

include hH

/-- Blueprint Definition `def:6-CH`: the diagonal of `C_H` is zero (`s6Cdiag`). -/
theorem hadamardSignedAdj_diag (x : ℕ) (p : HadamardPair n) :
    H.hadamardSignedAdj x p p = 0 := by
  simp only [hadamardSignedAdj, smul_apply, sub_apply, hadamardPairs_gram_apply,
    hH.inner_hadamardPairs_self, one_apply_eq, smul_eq_mul, mul_one, sub_self, mul_zero]

/-- Blueprint Lemma `lem:6-CHentries`: every entry of `C_H` is `0`, `1`, or `-1`. -/
theorem FourRowAgreement.hadamardSignedAdj_mem {x : ℕ} (ha : hH.FourRowAgreement x)
    (hx : 0 < x) (p q : HadamardPair n) :
    H.hadamardSignedAdj x p q ∈ ({0, 1, -1} : Set ℝ) := by
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  by_cases hpq : p = q
  · subst q
    simp [hH.hadamardSignedAdj_diag]
  have hh := ha.inner_hadamardPairs_mem hH p q hpq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  simp only [hadamardSignedAdj, smul_apply, sub_apply, one_apply_ne hpq, mul_zero,
    smul_eq_mul, sub_zero, hadamardPairs_gram_apply]
  rcases hh with hh | hh | hh <;> simp [hh, hx']

omit hH in
/-- Reconstructing the Gram matrix, step `s6qsub` of blueprint Lemma `lem:6-quadratic`. -/
theorem hadamardSignedAdj_gram (_hH : H.IsHadamard) (x : ℕ) (hx : 0 < x) :
    (x : ℝ) • H.hadamardSignedAdj x + (n : ℝ) • 1 =
      H.hadamardPairs * H.hadamardPairsᵀ := by
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  simp [hadamardSignedAdj, smul_smul, hx']

/-- Blueprint Lemma `lem:6-quadratic`, first equation. No Hypothesis 6.1 is used. -/
theorem hadamardSignedAdj_quadratic_scaled (x : ℕ) (hx : 0 < x) :
    ((x : ℝ) • H.hadamardSignedAdj x + (n : ℝ) • 1) *
      ((x : ℝ) • H.hadamardSignedAdj x - ((n : ℝ) * (n - 2) / 2) • 1) = 0 := by
  have he : (x : ℝ) • H.hadamardSignedAdj x - ((n : ℝ) * (n - 2) / 2) • 1 =
      H.hadamardPairs * H.hadamardPairsᵀ - ((n : ℝ) ^ 2 / 2) • 1 := by
    rw [← hH.hadamardSignedAdj_gram x hx]
    have hr : (n : ℝ) * (n - 2) / 2 = (n : ℝ) ^ 2 / 2 - n := by ring
    rw [hr, sub_smul]
    abel
  rw [hH.hadamardSignedAdj_gram x hx, he, mul_sub, mul_smul_comm, mul_one,
    ← pow_two, hH.hadamardPairs_gram_sq, sub_self]

/-- Blueprint Lemma `lem:6-quadratic`: with `d = n/x`, `(C_H+dI)(C_H-d(n-2)I/2)=0`.
Here `d` is real (the canonical image of the rational `n/x`); integrality is proved later. -/
theorem hadamardSignedAdj_quadratic (x : ℕ) (hx : 0 < x) :
    (H.hadamardSignedAdj x + ((n : ℝ) / x) • 1) *
      (H.hadamardSignedAdj x - (((n : ℝ) / x) * (n - 2) / 2) • 1) = 0 := by
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  have h := hH.hadamardSignedAdj_quadratic_scaled x hx
  have he : (x : ℝ) ^ 2 •
      ((H.hadamardSignedAdj x + ((n : ℝ) / x) • 1) *
        (H.hadamardSignedAdj x - (((n : ℝ) / x) * (n - 2) / 2) • 1)) = 0 := by
    rw [pow_two, ← smul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul]
    simpa [smul_add, smul_sub, smul_smul, hx', mul_div_cancel₀,
      mul_div_assoc, ← mul_assoc] using h
  exact (smul_eq_zero.mp he).resolve_left (pow_ne_zero _ hx')

end IsHadamard
end Matrix
