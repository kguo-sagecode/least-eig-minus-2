/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Theorem312.Completion

/-!
# Seeds from a colouring for Theorem 3.12 of [CGSS]

`lem:312-seeds` of the blueprint: give the false and true fibres squared norms
2 and 4, respectively, and check the four ordered pairs of colours.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The square-factorization leaves of `t312seedsPairs`, Theorem 3.12 of [CGSS]. -/
private theorem int_and_even_of_sq {p q : ℝ}
    (hshort : q = 2 → p ^ 2 = 0 ∨ p ^ 2 = 1 ∨ p ^ 2 = 4 ∨ p = 2)
    (hlong : q = 4 → p ^ 2 = 0 ∨ p ^ 2 = 4 ∨ p = 4)
    (hq : q = 2 ∨ q = 4) :
    (∃ z : ℤ, p = z) ∧ (q = 4 → ∃ z : ℤ, p = 2 * z) := by
  have hsmall {a : ℝ} (ha : p ^ 2 = a ^ 2) : p = a ∨ p = -a :=
    sq_eq_sq_iff_eq_or_eq_neg.mp ha
  rcases hq with hq | hq
  · refine ⟨?_, by intro h; linarith⟩
    rcases hshort hq with h | h | h | h
    · exact ⟨0, by simpa only [Int.cast_zero] using sq_eq_zero_iff.mp h⟩
    · rcases hsmall (a := 1) (by simpa using h) with h | h
      · exact ⟨1, by simpa using h⟩
      · exact ⟨-1, by simpa using h⟩
    · rcases hsmall (a := 2) (by nlinarith only [h]) with h | h
      · exact ⟨2, by simpa using h⟩
      · exact ⟨-2, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  · have he : ∃ z : ℤ, p = 2 * z := by
      rcases hlong hq with h | h | h
      · exact ⟨0, by simpa only [Int.cast_zero, mul_zero] using sq_eq_zero_iff.mp h⟩
      · rcases hsmall (a := 2) (by nlinarith only [h]) with h | h
        · exact ⟨1, by simpa using h⟩
        · exact ⟨-1, by norm_num; exact h⟩
      · exact ⟨2, by norm_num; exact h⟩
    obtain ⟨z, hz⟩ := he
    exact ⟨⟨2 * z, by simpa only [Int.cast_mul, Int.cast_ofNat] using hz⟩,
      fun _ ↦ ⟨z, hz⟩⟩

-- Theorem 3.12
/-- `lem:312-seeds`, Theorem 3.12 of [CGSS]. A compatible colouring gives
finite integral seeds with precisely the prescribed lines and span, and with
even pairings for every seed of squared norm 4. -/
theorem exists_integral_seeds_of_hasBipartition [FiniteDimensional ℝ V]
    {S : Set (Submodule ℝ V)} (hline : ∀ ℓ ∈ S, Module.finrank ℝ ℓ = 1)
    (hS : HasBipartition S) :
    ∃ T : Set V, T.Finite ∧ rootLines T = S ∧
      span ℝ T = span ℝ {x | ∃ ℓ ∈ S, x ∈ ℓ} ∧
      (∀ t ∈ T, ⟪t, t⟫ = 2 ∨ ⟪t, t⟫ = 4) ∧
      (∀ t ∈ T, ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = z) ∧
      (∀ t ∈ T, ⟪t, t⟫ = 4 → ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = 2 * z) := by
  classical
  have : Finite S := (finite_of_hasAllowedAngles hline hS.hasAllowedAngles).to_subtype
  obtain ⟨b, hb⟩ := hS
  have hex (ℓ : S) : ∃ t ∈ ℓ.1, ⟪t, t⟫ = if b ℓ then 4 else 2 := by
    obtain ⟨r, hr, hr0⟩ := exists_ne_zero_mem_line (hline ℓ.1 ℓ.2)
    apply exists_mem_line_sqNorm_eq hr hr0
    cases b ℓ <;> norm_num
  choose t ht hq using hex
  have hn (ℓ : S) : ⟪t ℓ, t ℓ⟫ = 2 ∨ ⟪t ℓ, t ℓ⟫ = 4 := by
    rw [hq]
    cases b ℓ <;> simp
  have ht0 (ℓ : S) : t ℓ ≠ 0 := by
    intro h
    have := hn ℓ
    simp [h] at this
  have hℓspan (ℓ : S) : ℓ.1 = span ℝ {t ℓ} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (hline ℓ.1 ℓ.2) (ht ℓ) (ht0 ℓ)
  have hp (ℓ m : S) : (∃ z : ℤ, ⟪t ℓ, t m⟫ = z) ∧
      (⟪t ℓ, t ℓ⟫ = 4 → ∃ z : ℤ, ⟪t ℓ, t m⟫ = 2 * z) := by
    apply int_and_even_of_sq (q := ⟪t ℓ, t ℓ⟫) ?_ ?_ (hn ℓ)
    · intro hshort
      by_cases he : ℓ = m
      · subst m
        exact Or.inr (Or.inr (Or.inr hshort))
      · have hbl : b ℓ = false := by
          cases h : b ℓ <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
          linarith [hq ℓ]
        cases hbm : b m
        · have hc := (hb ℓ m he).1 (by rw [hbl, hbm])
          rcases hc with hc | hc
          · left
            have := hc (t ℓ) (ht ℓ) (t m) (ht m)
            nlinarith only [this]
          · right; left
            have := hc (t ℓ) (ht ℓ) (t m) (ht m)
            rw [hshort, hq m, hbm] at this
            simp only [Bool.false_eq_true, ↓reduceIte] at this
            nlinarith only [this]
        · have hc := (hb ℓ m he).2 (by rw [hbl, hbm]; decide)
          rcases hc with hc | hc
          · left
            have := hc (t ℓ) (ht ℓ) (t m) (ht m)
            nlinarith only [this]
          · right; right; left
            have := hc (t ℓ) (ht ℓ) (t m) (ht m)
            rw [hshort, hq m, hbm] at this
            simp only [↓reduceIte] at this
            nlinarith only [this]
    · intro hlong
      by_cases he : ℓ = m
      · subst m
        exact Or.inr (Or.inr hlong)
      · have hbl : b ℓ = true := by
          cases h : b ℓ <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
          linarith [hq ℓ]
        cases hbm : b m
        · have hc := (hb ℓ m he).2 (by rw [hbl, hbm]; decide)
          rcases hc with hc | hc
          · left
            have := hc (t ℓ) (ht ℓ) (t m) (ht m)
            nlinarith only [this]
          · right; left
            have := hc (t ℓ) (ht ℓ) (t m) (ht m)
            rw [hlong, hq m, hbm] at this
            simp only [Bool.false_eq_true, ↓reduceIte] at this
            nlinarith only [this]
        · have hc := (hb ℓ m he).1 (by rw [hbl, hbm])
          rcases hc with hc | hc
          · left
            have := hc (t ℓ) (ht ℓ) (t m) (ht m)
            nlinarith only [this]
          · right; left
            have := hc (t ℓ) (ht ℓ) (t m) (ht m)
            rw [hlong, hq m, hbm] at this
            simp only [↓reduceIte] at this
            nlinarith only [this]
  refine ⟨Set.range t, Set.finite_range t, ?_, ?_, ?_, ?_, ?_⟩
  · ext ℓ
    constructor
    · rintro ⟨x, ⟨m, rfl⟩, rfl⟩
      rw [← hℓspan m]
      exact m.property
    · intro hℓ
      exact ⟨t ⟨ℓ, hℓ⟩, ⟨⟨ℓ, hℓ⟩, rfl⟩, hℓspan ⟨ℓ, hℓ⟩⟩
  · apply le_antisymm
    · apply span_le.mpr
      rintro x ⟨ℓ, rfl⟩
      exact subset_span ⟨ℓ.1, ℓ.2, ht ℓ⟩
    · apply span_le.mpr
      rintro x ⟨ℓ, hℓ, hx⟩
      have hle : ℓ ≤ span ℝ (Set.range t) := by
        rw [show ℓ = span ℝ {t ⟨ℓ, hℓ⟩} from hℓspan ⟨ℓ, hℓ⟩]
        apply span_mono
        exact Set.singleton_subset_iff.mpr ⟨⟨ℓ, hℓ⟩, rfl⟩
      exact hle hx
  · rintro x ⟨ℓ, rfl⟩
    exact hn ℓ
  · rintro x ⟨ℓ, rfl⟩ y ⟨m, rfl⟩
    exact (hp ℓ m).1
  · rintro x ⟨ℓ, rfl⟩ hlong y ⟨m, rfl⟩
    exact (hp ℓ m).2 hlong

end LineSystem
