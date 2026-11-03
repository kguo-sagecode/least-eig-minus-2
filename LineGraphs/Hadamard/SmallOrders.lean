/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Agreement
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The small-order obstruction

Blueprint Lemma `lem:6-small`, repairing Gap 10 in Theorem 6.2 of [CGSS].
-/

open scoped BigOperators RealInnerProductSpace

namespace Matrix

/-- The exact agreement condition of Theorem 6.2 of [CGSS], without division or rounding. -/
def AgreeSixteenths {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i j k l : Fin n, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    16 * H.fourRowAgreeCount i j k l ∈ ({n, 2 * n, 3 * n} : Set ℕ)

namespace IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
include hH

/-- Blueprint Lemma `lem:6-small`: `16 ∣ n` and `16 ≤ n`, with exactly the hypothesis
`16 * agr ∈ {n, 2n, 3n}`. The proof follows `s6sfour` through `s6sbound`. -/
theorem sixteen_dvd_of_agree_sixteenths (hn : 2 < n) (ha : H.AgreeSixteenths) :
    16 ∣ n ∧ 16 ≤ n := by
  have h4 : 4 ∣ n := by simpa using hH.four_dvd_card (by simpa using hn)
  have hn4 : 4 ≤ n := Nat.le_of_dvd (by omega) h4
  have h16 : 16 ∣ n := by
    by_contra h16
    have hzero : hH.FourRowAgreement 0 := by
      intro i j k l hij hik hil hjk hjl hkl
      have hh := ha i j k l hij hik hil hjk hjl hkl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      have he : 16 * H.fourRowAgreeCount i j k l = 2 * n := by
        rcases hh with hh | hh | hh
        · exact (h16 ⟨_, hh.symm⟩).elim
        · exact hh
        · have hd : 16 ∣ 3 * n := ⟨_, hh.symm⟩
          exact (h16 ((by decide : Nat.Coprime 16 3).dvd_of_dvd_mul_left hd)).elim
      have he' : 8 * H.fourRowAgreeCount i j k l = n := by omega
      simp only [Nat.cast_zero, sub_zero, add_zero, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl (by exact_mod_cast he')
    have horth : Pairwise (fun p q : HadamardPair n ↦
        ⟪H.hadamardRowProduct p.1.1 p.1.2, H.hadamardRowProduct q.1.1 q.1.2⟫ = 0) := by
      intro p q hpq
      simpa using hzero.inner_hadamardPairs_mem hH p q hpq
    have hnz (p : HadamardPair n) : H.hadamardRowProduct p.1.1 p.1.2 ≠ 0 := by
      intro hp
      have hs := hH.inner_hadamardPairs_self p.1.1 p.1.2
      rw [hp, inner_zero_left] at hs
      have : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      linarith
    have hli := linearIndependent_of_ne_zero_of_inner_eq_zero hnz horth
    have hb := hli.fintype_card_le_finrank
    simp only [card_hadamardPair, finrank_euclideanSpace_fin, Nat.choose_two_right] at hb
    have hmul : n * (n - 1) < 2 * (n + 1) := by omega
    have hsub : n - 1 + 1 = n := by omega
    nlinarith
  exact ⟨h16, Nat.le_of_dvd (by omega) h16⟩

/-- Blueprint Lemma `lem:6-lines`, part 1: the sixteenths condition is Hypothesis 6.1
with the integer parameter `x = n/2`. -/
theorem fourRowAgreement_half (hn : 16 ∣ n) (ha : H.AgreeSixteenths) :
    hH.FourRowAgreement (n / 2) := by
  have heven : 2 ∣ n := dvd_trans (by decide : 2 ∣ 16) hn
  have hhalf := Nat.div_mul_cancel heven
  intro i j k l hij hik hil hjk hjl hkl
  have hh := ha i j k l hij hik hil hjk hjl hkl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh ⊢
  rcases hh with hh | hh | hh
  · right; left
    have he : 8 * H.fourRowAgreeCount i j k l + n / 2 = n := by omega
    have he' : 8 * (H.fourRowAgreeCount i j k l : ℤ) + (n / 2 : ℕ) = n := by
      exact_mod_cast he
    omega
  · left
    have he : 8 * H.fourRowAgreeCount i j k l = n := by omega
    exact_mod_cast he
  · right; right
    have he : 8 * H.fourRowAgreeCount i j k l = n + n / 2 := by omega
    exact_mod_cast he

end IsHadamard
end Matrix
