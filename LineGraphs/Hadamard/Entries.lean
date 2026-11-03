/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Agreement

/-!
# Zero entries of the Hadamard signed adjacency

The meeting-pair and disjoint-pair clauses of blueprint Lemma `lem:6-CHentries`.
-/

open scoped RealInnerProductSpace

namespace Matrix.IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
include hH

/-- Blueprint Lemma `lem:6-CHentries`, step `s6Cmeet`: distinct meeting pairs are orthogonal. -/
theorem inner_hadamardPairs_of_meet (p q : HadamardPair n) (hpq : p ≠ q)
    (hmeet : p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨ p.1.2 = q.1.2) :
    ⟪H.hadamardRowProduct p.1.1 p.1.2, H.hadamardRowProduct q.1.1 q.1.2⟫ = 0 := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  rcases q with ⟨⟨k, l⟩, hkl⟩
  dsimp at hmeet hpq ⊢
  rcases hmeet with h | h | h | h
  · subst k
    exact hH.inner_hadamardRowProduct_of_ne i j l
      (by rintro rfl; exact hpq rfl)
  · subst l
    rw [hadamardRowProduct_comm H k i]
    exact hH.inner_hadamardRowProduct_of_ne i j k (ne_of_gt (hkl.trans hij))
  · subst k
    rw [hadamardRowProduct_comm H i j]
    exact hH.inner_hadamardRowProduct_of_ne j i l (ne_of_lt (hij.trans hkl))
  · subst l
    rw [hadamardRowProduct_comm H i j, hadamardRowProduct_comm H k j]
    exact hH.inner_hadamardRowProduct_of_ne j i k
      (by rintro rfl; exact hpq rfl)

/-- Blueprint Lemma `lem:6-CHentries`: the signed adjacency vanishes on distinct meeting pairs.
This clause holds without Hypothesis 6.1 and even when `x = 0`. -/
theorem hadamardSignedAdj_of_meet (x : ℕ) (p q : HadamardPair n) (hpq : p ≠ q)
    (hmeet : p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨ p.1.2 = q.1.2) :
    H.hadamardSignedAdj x p q = 0 := by
  simp only [hadamardSignedAdj, smul_apply, sub_apply, one_apply_ne hpq, smul_eq_mul,
    mul_zero, sub_zero, hadamardPairs_gram_apply, hH.inner_hadamardPairs_of_meet p q hpq hmeet]

/-- Blueprint Lemma `lem:6-CHentries`, step `s6Cdisj`: on disjoint pairs, a zero entry is
equivalent to `8 agr = n`. Hypothesis 6.1 is unnecessary for this equivalence. -/
theorem hadamardSignedAdj_eq_zero_iff_of_disjoint {x : ℕ} (hx : 0 < x)
    (p q : HadamardPair n)
    (hik : p.1.1 ≠ q.1.1) (hil : p.1.1 ≠ q.1.2)
    (hjk : p.1.2 ≠ q.1.1) (hjl : p.1.2 ≠ q.1.2) :
    H.hadamardSignedAdj x p q = 0 ↔
      (8 * (H.fourRowAgreeCount p.1.1 p.1.2 q.1.1 q.1.2 : ℤ)) = n := by
  have hpq : p ≠ q := fun he ↦ hik (congrArg (fun r : HadamardPair n ↦ r.1.1) he)
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [hadamardSignedAdj, smul_apply, sub_apply, one_apply_ne hpq, smul_eq_mul,
    mul_zero, sub_zero, hadamardPairs_gram_apply,
    hH.inner_hadamardPairs_of_disjoint _ _ _ _ p.2.ne hik hil hjk hjl q.2.ne,
    mul_eq_zero, inv_eq_zero, hx', false_or, sub_eq_zero]
  exact_mod_cast (Iff.rfl : (8 * (H.fourRowAgreeCount p.1.1 p.1.2 q.1.1 q.1.2 : ℤ)) = n ↔ _)

end Matrix.IsHadamard
