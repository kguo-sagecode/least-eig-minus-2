/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.RootLatticeBasis
import LineGraphs.LineSystem.ClassicalModels
import Mathlib.Data.ZMod.Basic

/-! # The integral sum-of-squares obstruction for E₆

Lemma `lem:E6Zm` (Lemma 2.5) of [Exc]. We use the support argument of the note
modulo two: orthogonal norm-two integral vectors with intersecting supports have
the same reduction modulo two. Three neighbours of the branch node then give a
contradiction with an end root.
-/

open Module Submodule Computations
open scoped RealInnerProductSpace

namespace LineSystem

-- Lemma 2.5 [Exc]
/-- The support step in Lemma `lem:E6Zm` (Lemma 2.5) of [Exc]: two orthogonal
`D` roots sharing a coordinate agree modulo two. -/
theorem dnRoot_cast_zmod_two_eq_of_orthogonal {n : ℕ} (p q : DnIndex n)
    (horth : integerInner (dnRoot p) (dnRoot q) = 0)
    (hshare : ∃ k, dnRoot p k ≠ 0 ∧ dnRoot q k ≠ 0) :
    ∀ k, (dnRoot p k : ZMod 2) = (dnRoot q k : ZMod 2) := by
  obtain ⟨⟨⟨i, j⟩, hij⟩, a, b⟩ := p
  obtain ⟨⟨⟨k, l⟩, hkl⟩, c, d⟩ := q
  dsimp at hij hkl
  let q : DnIndex n := (⟨(k, l), hkl⟩, c, d)
  have hdot : rootSign a * dnRoot q i + rootSign b * dnRoot q j = 0 := by
    simpa only [dnRoot, integerInner_pairVector] using horth
  have he : dnRoot q i ≠ 0 ↔ dnRoot q j ≠ 0 := by
    constructor
    · intro hi hj
      rw [hj, mul_zero, add_zero] at hdot
      exact hi ((mul_eq_zero.mp hdot).resolve_left (rootSign_ne_zero a))
    · intro hj hi
      rw [hi, mul_zero, zero_add] at hdot
      exact hj ((mul_eq_zero.mp hdot).resolve_left (rootSign_ne_zero b))
  have hi : dnRoot q i ≠ 0 := by
    obtain ⟨t, ht, hq⟩ := hshare
    rcases (dnRoot_ne_zero_iff _ t).mp ht with rfl | rfl
    · exact hq
    · exact he.mpr hq
  have hj := he.mp hi
  have hi' := (dnRoot_ne_zero_iff q i).mp hi
  have hj' := (dnRoot_ne_zero_iff q j).mp hj
  dsimp [q] at hi' hj'
  have hik : i = k := by rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj' <;> omega
  have hjl : j = l := by rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj' <;> omega
  subst k
  subst l
  intro t
  simp only [dnRoot, pairVector, Pi.add_apply, Pi.single_apply]
  cases a <;> cases b <;> cases c <;> cases d <;>
    split_ifs <;> norm_num [rootSign] <;> decide

-- Lemma 2.5 [Exc]
/-- The parity step in Lemma `lem:E6Zm` (Lemma 2.5) of [Exc]: equal reductions
of vectors give equal reductions of their inner products. -/
theorem integerInner_cast_zmod_two_eq {n : ℕ} {u v : Fin n → ℤ}
    (h : ∀ k, (u k : ZMod 2) = (v k : ZMod 2)) (w : Fin n → ℤ) :
    (integerInner u w : ZMod 2) = (integerInner v w : ZMod 2) := by
  simp only [integerInner, dotProduct, Int.cast_sum, Int.cast_mul]
  exact Finset.sum_congr rfl (fun k _ ↦ congrArg (fun z ↦ z * (w k : ZMod 2)) (h k))

-- Lemma 2.5 [Exc]
/-- Lemma `lem:E6Zm` (Lemma 2.5) of [Exc]: the Gram matrix of the simple roots
of `E₆` has no integral sum-of-squares representation, in any dimension. This is
Mordell's classical obstruction to expressing the quadratic form of `E₆` as a sum
of squares of integral linear forms (L. J. Mordell, Ann. of Math. 38 (1937), 751–757). -/
theorem E₆.not_exists_integral_gram_simpleRoot (m : ℕ) :
    ¬ ∃ y : Fin 6 → Fin m → ℤ, ∀ i j,
      (integerInner (y i) (y j) : ℝ) = (Matrix.gram ℝ E₆.simpleRoot) i j := by
  rintro ⟨y, hy⟩
  have hg (i j : Fin 6) : integerInner (y i) (y j) = entry C21.e6Gram i j := by
    apply Int.cast_injective (α := ℝ)
    simpa only [E₆.gram_simpleRoot, toMatrix] using hy i j
  have hn (i : Fin 6) : integerInner (y i) (y i) = 2 := by
    rw [hg]
    exact (by decide +kernel : ∀ i : Fin 6, entry C21.e6Gram i i = 2) i
  choose p hp using fun i ↦ exists_dnRoot_of_inner_self (y i) (hn i)
  have hs (i : Fin 6) (hi : i = 0 ∨ i = 1 ∨ i = 3) :
      dnRoot (p i) (p 2).1.val.1 ≠ 0 ∨ dnRoot (p i) (p 2).1.val.2 ≠ 0 := by
    have hh : integerInner (dnRoot (p 2)) (dnRoot (p i)) = -1 := by
      rw [hp, hp, hg]
      rcases hi with rfl | rfl | rfl <;> decide
    rw [dnRoot, integerInner_pairVector] at hh
    by_contra hz
    simp only [not_or, not_not] at hz
    rw [hz.1, hz.2, mul_zero, mul_zero, zero_add] at hh
    norm_num at hh
  have horth (i j : Fin 6) (hij : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨
      (i = 1 ∧ j = 3)) : integerInner (dnRoot (p i)) (dnRoot (p j)) = 0 := by
    rw [hp, hp, hg]
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hne01 : ¬ ∀ k, (dnRoot (p 0) k : ZMod 2) = (dnRoot (p 1) k : ZMod 2) := by
    intro he
    have hh := integerInner_cast_zmod_two_eq he (dnRoot (p 5))
    rw [hp, hp, hp, hg, hg] at hh
    norm_num [entry, C21.e6Gram] at hh
  have hne03 : ¬ ∀ k, (dnRoot (p 0) k : ZMod 2) = (dnRoot (p 3) k : ZMod 2) := by
    intro he
    have hh := integerInner_cast_zmod_two_eq he (dnRoot (p 4))
    rw [hp, hp, hp, hg, hg] at hh
    norm_num [entry, C21.e6Gram] at hh
  have hne13 : ¬ ∀ k, (dnRoot (p 1) k : ZMod 2) = (dnRoot (p 3) k : ZMod 2) := by
    intro he
    have hh := integerInner_cast_zmod_two_eq he (dnRoot (p 5))
    rw [hp, hp, hp, hg, hg] at hh
    norm_num [entry, C21.e6Gram] at hh
  have h01 := hne01 ∘ dnRoot_cast_zmod_two_eq_of_orthogonal (p 0) (p 1)
    (horth 0 1 (Or.inl ⟨rfl, rfl⟩))
  have h03 := hne03 ∘ dnRoot_cast_zmod_two_eq_of_orthogonal (p 0) (p 3)
    (horth 0 3 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have h13 := hne13 ∘ dnRoot_cast_zmod_two_eq_of_orthogonal (p 1) (p 3)
    (horth 1 3 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  rcases hs 0 (Or.inl rfl) with h0 | h0 <;>
    rcases hs 1 (Or.inr (Or.inl rfl)) with h1 | h1 <;>
    rcases hs 3 (Or.inr (Or.inr rfl)) with h3 | h3
  all_goals first
    | exact h01 ⟨_, h0, h1⟩
    | exact h03 ⟨_, h0, h3⟩
    | exact h13 ⟨_, h1, h3⟩

-- Lemma 2.5 [Exc]
/-- Lemma `lem:E6Zm` (Lemma 2.5) of [Exc]: the `E₆` root lattice has no
inner-product-preserving integral linear map into `ℤᵐ`. Equivalently, its quadratic
form is not a sum of squares of integral linear forms, as proved by L. J. Mordell,
Ann. of Math. 38 (1937), 751–757. -/
theorem E₆.not_exists_lattice_isometry_int (m : ℕ) :
    ¬ ∃ f : span ℤ E₆.Φ →ₗ[ℤ] (Fin m → ℤ), ∀ u v,
      (integerInner (f u) (f v) : ℝ) =
        ⟪(u : EuclideanSpace ℝ (Fin 8)), (v : EuclideanSpace ℝ (Fin 8))⟫ := by
  rintro ⟨f, hf⟩
  apply E₆.not_exists_integral_gram_simpleRoot m
  refine ⟨fun i ↦ f ⟨E₆.simpleRoot i, subset_span (E₆.simpleRoot_mem i)⟩, ?_⟩
  intro i j
  exact hf _ _

end LineSystem
