/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Models

/-! Parametric integer certificates for the A and D families.
A squared-norm-two integer vector has exactly two nonzero coordinates, each a sign.
This gives star-closure without a pair sweep, in every dimension, including the empty cases. -/

open Finset

namespace LineSystem

/-- Norm two characterizes the integer roots of Dₙ, including in small dimensions. -/
theorem exists_dnRoot_of_inner_self {n : ℕ} (w : Fin n → ℤ)
    (hw : integerInner w w = 2) : ∃ a : Dn.Index n, dnRoot a = w := by
  have hsq (i : Fin n) : w i * w i ≤ 2 := by
    calc
      w i * w i ≤ ∑ j, w j * w j :=
        Finset.single_le_sum (fun j _ ↦ mul_self_nonneg (w j)) (Finset.mem_univ i)
      _ = 2 := hw
  have hb (i : Fin n) : w i = -1 ∨ w i = 0 ∨ w i = 1 := by
    have h := hsq i
    have hl : -1 ≤ w i := by nlinarith
    have hu : w i ≤ 1 := by nlinarith
    omega
  have he (i : Fin n) : w i * w i = if w i ≠ 0 then 1 else 0 := by
    rcases hb i with h | h | h <;> simp [h]
  have hcard : (Finset.univ.filter (fun i ↦ w i ≠ 0)).card = 2 := by
    have h : (∑ i, if w i ≠ 0 then (1 : ℤ) else 0) = 2 := by
      simpa only [integerInner, dotProduct, he] using hw
    rw [Finset.sum_boole] at h
    exact_mod_cast h
  obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp hcard
  have hm (k : Fin n) : w k ≠ 0 ↔ k = i ∨ k = j := by
    have h : k ∈ Finset.univ.filter (fun i ↦ w i ≠ 0) ↔ k ∈ ({i, j} : Finset (Fin n)) := by
      rw [hs]
    simpa using h
  have hi : w i ≠ 0 := (hm i).mpr (Or.inl rfl)
  have hj : w j ≠ 0 := (hm j).mpr (Or.inr rfl)
  have hsign (k : Fin n) (hk : w k ≠ 0) : rootSign (decide (w k = -1)) = w k := by
    rcases hb k with h | h | h
    · simp [h, rootSign]
    · exact False.elim (hk h)
    · simp [h, rootSign]
  obtain ⟨a, ha⟩ := exists_dnRoot_eq_pairVector i j hij
    (decide (w i = -1)) (decide (w j = -1))
  refine ⟨a, ?_⟩
  rw [ha, hsign i hi, hsign j hj]
  ext k
  by_cases hki : k = i
  · subst k
    simp [pairVector, hij]
  · by_cases hkj : k = j
    · subst k
      simp [pairVector, hij.symm]
    · have hz : w k = 0 := by by_contra h; exact (hm k).mp h |>.elim hki hkj
      simp [pairVector, hki, hkj, hz]

/-- The A roots are exactly the norm-two integer vectors with coordinate sum zero. -/
theorem exists_anRoot_of_inner_self_of_sum {n : ℕ} (w : Fin (n + 1) → ℤ)
    (hw : integerInner w w = 2) (hs : ∑ i, w i = 0) :
    ∃ a : An.Index n, anRoot a = w := by
  obtain ⟨⟨⟨⟨i, j⟩, hij⟩, a, b⟩, rfl⟩ := exists_dnRoot_of_inner_self w hw
  have hsum : rootSign a + rootSign b = 0 := by
    simpa [dnRoot, pairVector, Finset.sum_add_distrib] using hs
  cases a <;> cases b
  · norm_num [rootSign] at hsum
  · exact ⟨⟨(i, j), ne_of_lt hij⟩, rfl⟩
  · refine ⟨⟨(j, i), ne_of_gt hij⟩, ?_⟩
    exact add_comm _ _
  · norm_num [rootSign] at hsum

/-- The squared norm of a sum, expressed entirely over the integers. -/
theorem integerInner_add_self {n : ℕ} (v w : Fin n → ℤ) :
    integerInner (v + w) (v + w) =
      integerInner v v + 2 * integerInner v w + integerInner w w := by
  change (v + w) ⬝ᵥ (v + w) = _
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm w v]
  ring

-- Theorem 3.5 / computation C4
/-- C4: Dₙ is star-closed in every dimension, by the integer norm-two criterion. -/
theorem isStarClosed_Dn (n : ℕ) : (Dn n).IsStarClosed := by
  apply (Dn.integerModel n).isStarClosed_of
  intro a b hab
  change integerInner (dnRoot a) (dnRoot b) = -1 at hab
  change ∃ d : Dn.Index n, dnRoot d = dnRoot a + dnRoot b
  apply exists_dnRoot_of_inner_self
  rw [integerInner_add_self, integerInner_dnRoot_self, integerInner_dnRoot_self, hab]
  norm_num

-- Theorem 3.5 / computation C4
/-- C4: Aₙ is star-closed in every dimension, retaining the coordinate-sum condition. -/
theorem isStarClosed_An (n : ℕ) : (An n).IsStarClosed := by
  apply (An.integerModel n).isStarClosed_of
  intro a b hab
  change integerInner (anRoot a) (anRoot b) = -1 at hab
  change ∃ d : An.Index n, anRoot d = anRoot a + anRoot b
  apply exists_anRoot_of_inner_self_of_sum
  · rw [integerInner_add_self, integerInner_anRoot_self, integerInner_anRoot_self, hab]
    norm_num
  · simp [anRoot, pairVector, Finset.sum_add_distrib]

end LineSystem
