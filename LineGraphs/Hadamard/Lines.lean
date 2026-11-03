/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Roots

/-!
# The line system of a Hadamard matrix

Blueprint Lemma `lem:6-lines`, the construction preceding the classification argument in
Theorem 6.2 of [CGSS]. No classification theorem is used here.
-/

open scoped BigOperators RealInnerProductSpace

namespace Matrix.IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)

/-- Blueprint Lemma `lem:6-lines`, part 3, step `s6lls`: the line system with roots `±√(2/n)p`.
The hypotheses retain exactly `16 ∣ n`, `16 ≤ n`, and the sixteenths agreement condition. -/
noncomputable def lineSystem (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths) :
    LineSystem (EuclideanSpace ℝ (Fin n)) where
  Φ := Set.range (LineSystem.signedVec H.hadamardRoot)
  finite := Set.finite_range _
  inner_self := by
    rintro _ ⟨⟨p, b⟩, rfl⟩
    cases b <;> simp only [LineSystem.signedVec, Bool.false_eq_true, ite_false, ite_true,
      inner_neg_left, inner_neg_right, neg_neg] <;>
      exact hH.inner_hadamardRoot_self (by omega) p
  neg_mem := by
    rintro _ ⟨⟨p, b⟩, rfl⟩
    refine ⟨(p, !b), ?_⟩
    cases b <;> simp [LineSystem.signedVec]
  inner_mem := by
    rintro _ ⟨⟨p, b⟩, rfl⟩ _ ⟨⟨q, c⟩, rfl⟩
    by_cases hpq : p = q
    · subst q
      cases b <;> cases c <;>
        simp only [LineSystem.signedVec, Bool.false_eq_true, ite_false, ite_true,
          inner_neg_left, inner_neg_right, neg_neg,
          hH.inner_hadamardRoot_self (by omega)] <;> norm_num
    · have hh := hH.inner_hadamardRoot_mem hn hn16 ha p q hpq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with hh | hh | hh <;> cases b <;> cases c <;>
        simp [LineSystem.signedVec, hh]

include hH

/-- No roots from distinct pairs agree up to sign, step `s6ldistinct`. -/
theorem signed_hadamardRoot_injective (hn : 16 ∣ n) (hn16 : 16 ≤ n)
    (ha : H.AgreeSixteenths) : Function.Injective (LineSystem.signedVec H.hadamardRoot) := by
  rintro ⟨p, b⟩ ⟨q, c⟩ he
  have hs := hH.inner_hadamardRoot_self (by omega) p
  have hi := congrArg (fun v ↦ ⟪H.hadamardRoot p, v⟫) he
  have hpq : p = q := by
    by_contra hpq
    have hh := hH.inner_hadamardRoot_mem hn hn16 ha p q hpq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    cases b <;> cases c <;>
      simp only [LineSystem.signedVec, Bool.false_eq_true, ite_false, ite_true,
        inner_neg_right, hs] at hi <;> rcases hh with hh | hh | hh <;> linarith
  subst q
  cases b <;> cases c <;>
    simp only [LineSystem.signedVec, Bool.false_eq_true, ite_false, ite_true,
      inner_neg_right, hs] at hi <;> first | rfl | linarith

/-- The signing of blueprint Lemma `lem:6-lines`, step `s6lsigning`. -/
noncomputable def lineSystemSigning (hn : 16 ∣ n) (hn16 : 16 ≤ n)
    (ha : H.AgreeSixteenths) : (hH.lineSystem hn hn16 ha).Signing (HadamardPair n) where
  toFun := H.hadamardRoot
  bijOn := ⟨fun p _ ↦ ⟨p, rfl⟩,
    (hH.signed_hadamardRoot_injective hn hn16 ha).injOn,
    fun _ ⟨p, hp⟩ ↦ ⟨p, Set.mem_univ p, hp⟩⟩

/-- Blueprint Lemma `lem:6-lines`, part 3: the number of lines is `n(n-1)/2`. -/
theorem numLines_lineSystem (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths) :
    (hH.lineSystem hn hn16 ha).numLines = n * (n - 1) / 2 := by
  rw [LineSystem.numLines]
  change (Set.range (LineSystem.signedVec H.hadamardRoot)).ncard / 2 = _
  rw [Set.ncard_range_of_injective (hH.signed_hadamardRoot_injective hn hn16 ha)]
  simp [Nat.card_eq_fintype_card, card_hadamardPair, Nat.choose_two_right]

/-- Blueprint Lemma `lem:6-lines`, part 3: the signed adjacency of this signing is `C_H`. -/
theorem lineSystem_signedAdj (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths) :
    LineSystem.signedAdj (hH.lineSystemSigning hn hn16 ha) = H.hadamardSignedAdj (n / 2) := by
  ext p q
  by_cases hpq : p = q
  · subst q
    rw [LineSystem.signedAdj_apply_self, hH.hadamardSignedAdj_diag]
  · simp only [LineSystem.signedAdj, sub_apply, gram_apply, smul_apply,
      one_apply_ne hpq, smul_eq_mul, mul_zero, sub_zero]
    exact hH.inner_hadamardRoot_eq_signedAdj hn hn16 p q hpq

/-- Blueprint Lemma `lem:6-lines`, part 4: the quadratic equation with `d = 2`. -/
theorem lineSystem_quadratic (hn : 16 ∣ n) (hn16 : 16 ≤ n) :
    (H.hadamardSignedAdj (n / 2) + (2 : ℝ) • 1) *
      (H.hadamardSignedAdj (n / 2) - ((n : ℝ) - 2) • 1) = 0 := by
  have hq := hH.hadamardSignedAdj_quadratic (n / 2) (by omega)
  rw [hH.div_half_eq_two hn hn16] at hq
  have hc : (2 : ℝ) * (n - 2) / 2 = (n : ℝ) - 2 := by ring
  rwa [hc] at hq

/-- Blueprint Lemma `lem:6-lines`, part 6, for both signs of every root. -/
theorem lineSystem_inner_one (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ (hH.lineSystem hn hn16 ha).Φ) :
    ⟪v, WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ))⟫ = 0 := by
  obtain ⟨⟨p, b⟩, rfl⟩ := hv
  cases b <;> simp [LineSystem.signedVec, hH.inner_hadamardRoot_one]

/-- Blueprint Lemma `lem:6-lines`, part 6: both signs have coordinates `±√(2/n)`. -/
theorem lineSystem_apply_mem (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ (hH.lineSystem hn hn16 ha).Φ) (c : Fin n) :
    v c = Real.sqrt (2 / (n : ℝ)) ∨ v c = -Real.sqrt (2 / (n : ℝ)) := by
  obtain ⟨⟨p, b⟩, rfl⟩ := hv
  have hp := hH.hadamardRoot_apply_mem p c
  cases b <;> rcases hp with hp | hp <;> simp [LineSystem.signedVec, hp]

/-- Blueprint Lemma `lem:6-lines`, part 6: the normalized lines through a row are orthogonal. -/
theorem hadamardRoots_orthogonal_of_mem (i j k : Fin n) (hjk : j ≠ k) :
    ⟪Real.sqrt (2 / (n : ℝ)) • H.hadamardRowProduct i j,
      Real.sqrt (2 / (n : ℝ)) • H.hadamardRowProduct i k⟫ = 0 := by
  rw [real_inner_smul_left, real_inner_smul_right,
    hH.inner_hadamardRowProduct_of_ne i j k hjk, mul_zero, mul_zero]

end Matrix.IsHadamard
