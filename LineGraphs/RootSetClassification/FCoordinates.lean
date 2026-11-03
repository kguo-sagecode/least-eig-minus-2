/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.ExceptionalCoordinates
import LineGraphs.RootSetClassification.Classical

/-!
# Coordinates and reflections for F₄

Steps `rFbasic` and `rFreflection` of `lem:F` in the blueprint for Remark 3.11
of [CGSS]. The finite integer checks below enumerate exactly the three coordinate
patterns, and the reflection in the positive half vector. Arbitrary half-vector
reflections follow by conjugating with a diagonal sign isometry.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

/-- The three signed patterns in `eq:F-roots` of Remark 3.11. -/
abbrev F₄Index := LineSystem.DnIndex 4 ⊕ ((Fin 4 × Bool) ⊕ (Fin 4 → Bool))

/-- Twice the coordinates in `eq:F-roots` of Remark 3.11. -/
def fRootEntries : F₄Index → Fin 4 → ℤ
  | .inl a => fun i ↦ 2 * LineSystem.dnRoot a i
  | .inr (.inl a) => Pi.single a.1 (2 * LineSystem.rootSign a.2)
  | .inr (.inr s) => fun i ↦ LineSystem.rootSign (s i)

/-- The finite parametrization in step `rFfinite` of Remark 3.11. -/
theorem F₄_eq_range : F₄ = Set.range (fun a ↦ LineSystem.integerVector (1 / 2)
    (fRootEntries a)) := by
  classical
  ext x
  constructor
  · rintro ((⟨a, rfl⟩ | ⟨i, rfl | rfl⟩) | hx)
    · refine ⟨.inl a, ?_⟩
      ext i
      simp [fRootEntries, LineSystem.integerVector]
    · refine ⟨.inr (.inl (i, false)), ?_⟩
      ext k
      by_cases hk : k = i <;>
        simp [fRootEntries, LineSystem.integerVector, LineSystem.rootSign, unit,
          Pi.single_apply, hk]
    · refine ⟨.inr (.inl (i, true)), ?_⟩
      ext k
      by_cases hk : k = i <;>
        simp [fRootEntries, LineSystem.integerVector, LineSystem.rootSign, unit,
          Pi.single_apply, hk]
    · refine ⟨.inr (.inr (fun i ↦ decide (x i = -(1 / 2)))), ?_⟩
      ext i
      rcases hx i with hi | hi <;>
        norm_num [fRootEntries, LineSystem.integerVector, LineSystem.rootSign, hi]
  · rintro ⟨a, rfl⟩
    rcases a with a | (⟨i, b⟩ | s)
    · left; left
      refine ⟨a, ?_⟩
      ext i
      simp [fRootEntries, LineSystem.integerVector]
    · left; right
      refine ⟨i, ?_⟩
      cases b
      · left; ext k
        by_cases hk : k = i <;>
          simp [fRootEntries, LineSystem.integerVector, LineSystem.rootSign, unit,
            Pi.single_apply, hk]
      · right; ext k
        by_cases hk : k = i <;>
          simp [fRootEntries, LineSystem.integerVector, LineSystem.rootSign, unit,
            Pi.single_apply, hk]
    · right
      intro i
      cases hs : s i <;>
        norm_num [fRootEntries, LineSystem.integerVector, LineSystem.rootSign, hs]

/-- Step `rFfinite` of Remark 3.11: the F₄ coordinate set is finite. -/
theorem F₄_finite : F₄.Finite := by
  rw [F₄_eq_range]
  exact Set.finite_range _

/-- Step `rFlength`: a half-coordinate F₄ root has squared length one. -/
theorem inner_self_of_mem_halfRoots_four {x : EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ halfRoots 4) : ⟪x, x⟫ = 1 := by
  rw [PiLp.inner_apply]
  have he (i : Fin 4) : ⟪x i, x i⟫ = (1 / 4 : ℝ) := by
    rcases hx i with h | h <;> norm_num [h]
  simp only [he]
  norm_num

/-- Step `rFlength`: the two-coordinate pattern has squared length two, the others one. -/
theorem F₄_inner_self {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ F₄) :
    ⟪x, x⟫ = 1 ∨ ⟪x, x⟫ = 2 := by
  rcases hx with (hx | hx) | hx
  · exact Or.inr ((LineSystem.Dn 4).inner_self x hx)
  · exact Or.inl (by simpa using inner_self_of_mem_axisRoots hx)
  · exact Or.inl (inner_self_of_mem_halfRoots_four hx)

/-- Step `rFfinite`: zero is absent from the coordinate list. -/
theorem F₄_zero_notMem : (0 : EuclideanSpace ℝ (Fin 4)) ∉ F₄ := by
  intro h
  have he := F₄_inner_self h
  simp at he

/-- The support separation used in step `rFreduced` of Remark 3.11. -/
theorem exists_zero_coordinate_of_mem_F₄_integer {x : EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ Dn 4 ∪ axisRoots 4 1) : ∃ i, x i = 0 := by
  rcases hx with ⟨a, rfl⟩ | ⟨i, rfl | rfl⟩
  · have h : ∀ a : LineSystem.DnIndex 4, ∃ i, LineSystem.dnRoot a i = 0 := by
      decide +kernel
    obtain ⟨i, hi⟩ := h a
    exact ⟨i, by simp [LineSystem.integerVector, hi]⟩
  · have h : ∀ i : Fin 4, ∃ j, j ≠ i := by decide +kernel
    obtain ⟨j, hj⟩ := h i
    exact ⟨j, by simp [unit, hj]⟩
  · have h : ∀ i : Fin 4, ∃ j, j ≠ i := by decide +kernel
    obtain ⟨j, hj⟩ := h i
    exact ⟨j, by simp [unit, hj]⟩

/-- Step `rFreduced`: support separation and equal lengths give reducedness. -/
theorem F₄_reduced {r : EuclideanSpace ℝ (Fin 4)} (hr : r ∈ F₄)
    (t : ℝ) (ht : t • r ∈ F₄) : t = 1 ∨ t = -1 := by
  have hnz : t ≠ 0 := by
    intro h
    subst t
    exact F₄_zero_notMem (by simpa using ht)
  rcases hr with hr | hr <;> rcases ht with ht | ht
  · exact reduced_axisRoots_union_Dn (by norm_num : (1 : ℝ) ≠ 0)
      hr.symm t ht.symm
  · obtain ⟨i, hi⟩ := exists_zero_coordinate_of_mem_F₄_integer hr
    rcases ht i with h | h <;> simp [hi] at h
  · obtain ⟨i, hi⟩ := exists_zero_coordinate_of_mem_F₄_integer ht
    rcases hr i with h | h <;> simp [h, hnz] at hi
  · have he := inner_self_of_mem_halfRoots_four ht
    rw [real_inner_smul_left, real_inner_smul_right, inner_self_of_mem_halfRoots_four hr] at he
    have hp : (t - 1) * (t + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

/-- Step `rFspan`: the signed axes span the ambient four-dimensional space. -/
theorem span_F₄_eq_top : span ℝ F₄ = ⊤ := by
  apply top_unique
  rw [← span_axisRoots_union_Dn (n := 4) (by norm_num : (1 : ℝ) ≠ 0)]
  apply span_mono
  intro x hx
  exact Or.inl hx.symm

/-- Step `rFsignmap`: signed permutations preserve all three F₄ patterns. -/
theorem signedPermutation_mem_F₄ (e : Equiv.Perm (Fin 4)) (s : Fin 4 → Bool)
    {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ F₄) : signedPermutation e s x ∈ F₄ := by
  rcases hx with (hx | hx) | hx
  · exact Or.inl (Or.inl (signedPermutation_mem_Dn e s hx))
  · exact Or.inl (Or.inr (signedPermutation_mem_axisRoots e s 1 hx))
  · exact Or.inr (signedPermutation_mem_halfRoots e s hx)

/-- The isometry assertion used to conjugate in step `rFhalfref` of Remark 3.11. -/
theorem signedPermutation_inner {n : ℕ} (e : Equiv.Perm (Fin n)) (s : Fin n → Bool)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪signedPermutation e s x, signedPermutation e s y⟫ = ⟪x, y⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  calc
    _ = ∑ i, ⟪x (e.symm i), y (e.symm i)⟫ := by
      apply Finset.sum_congr rfl
      intro i _
      cases hs : s (e.symm i) <;> simp [signedPermutation, LineSystem.rootSign, hs]
    _ = _ := e.symm.sum_comp (fun i ↦ ⟪x i, y i⟫)

/-- The reflection conjugation used in step `rFhalfref` of Remark 3.11. -/
theorem reflect_signedPermutation {n : ℕ} (e : Equiv.Perm (Fin n)) (s : Fin n → Bool)
    (r x : EuclideanSpace ℝ (Fin n)) :
    reflect (signedPermutation e s r) (signedPermutation e s x) =
      signedPermutation e s (reflect r x) := by
  simp only [reflect, signedPermutation_inner, map_sub, map_smul]

/-- The diagonal sign map in step `rFsignmap` is an involution. -/
theorem signedPermutation_sign_involutive {n : ℕ} (s : Fin n → Bool)
    (x : EuclideanSpace ℝ (Fin n)) :
    signedPermutation (Equiv.refl _) s (signedPermutation (Equiv.refl _) s x) = x := by
  ext i
  cases hs : s i <;> simp [signedPermutation, LineSystem.rootSign, hs]

/-- The positive half-coordinate root used in step `rFvformula` of Remark 3.11. -/
noncomputable def fHalf : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 (fun _ ↦ 1 / 2)

/-- Step `rFvformula`: reflection in the positive half vector subtracts the coordinate sum. -/
theorem reflect_fHalf (x : EuclideanSpace ℝ (Fin 4)) :
    reflect fHalf x = x - (∑ i, x i) • fHalf := by
  have hn : ⟪fHalf, fHalf⟫ = (1 : ℝ) :=
    inner_self_of_mem_halfRoots_four (fun _ ↦ Or.inl rfl)
  have hi : ⟪fHalf, x⟫ = (∑ i, x i) / 2 := by
    simp only [PiLp.inner_apply, fHalf, RCLike.inner_apply,
      conj_trivial, div_eq_mul_inv, one_mul]
    rw [Finset.sum_mul]
  rw [reflect, hn, hi]
  congr 2
  ring

/-- Steps `rFvaxis`--`rFvhalf4`: the eight pattern cases for the positive half reflection,
in doubled integer coordinates. The quotient records the coordinate sum. -/
theorem fHalf_reflection_entries (a : F₄Index) :
    (∑ i, fRootEntries a i) = 2 * ((∑ i, fRootEntries a i) / 2) ∧
    ∃ b : F₄Index, ∀ i,
      fRootEntries b i = fRootEntries a i - (∑ j, fRootEntries a j) / 2 := by
  have h : ∀ a : F₄Index,
      (∑ i, fRootEntries a i) = 2 * ((∑ i, fRootEntries a i) / 2) ∧
      ∃ b : F₄Index, ∀ i,
        fRootEntries b i = fRootEntries a i - (∑ j, fRootEntries a j) / 2 := by
    decide +kernel
  exact h a

/-- Step `rFvclosed`: reflection in the positive half vector preserves the entire list. -/
theorem reflect_fHalf_mem_F₄ {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ F₄) :
    reflect fHalf x ∈ F₄ := by
  rw [F₄_eq_range] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨hs, b, hb⟩ := fHalf_reflection_entries a
  have hsum : (∑ i, LineSystem.integerVector (1 / 2) (fRootEntries a) i) =
      (((∑ i, fRootEntries a i) / 2 : ℤ) : ℝ) := by
    have hsr : (∑ i, (fRootEntries a i : ℝ)) =
        2 * (((∑ i, fRootEntries a i) / 2 : ℤ) : ℝ) := by exact_mod_cast hs
    change (∑ i, (1 / 2 : ℝ) * (fRootEntries a i : ℝ)) = _
    rw [← Finset.mul_sum, hsr]
    ring
  refine ⟨b, ?_⟩
  rw [reflect_fHalf, hsum]
  ext i
  simp only [LineSystem.integerVector, hb, Int.cast_sub,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, fHalf]
  ring

/-- Step `rFhalfref`: a sign conjugate of the positive half reflection preserves F₄. -/
theorem reflect_half_mem_F₄ {r x : EuclideanSpace ℝ (Fin 4)}
    (hr : r ∈ halfRoots 4) (hx : x ∈ F₄) : reflect r x ∈ F₄ := by
  classical
  let s : Fin 4 → Bool := fun i ↦ decide (r i = -(1 / 2))
  have he : signedPermutation (Equiv.refl _) s fHalf = r := by
    ext i
    rcases hr i with hi | hi <;>
      norm_num [signedPermutation, s, fHalf, LineSystem.rootSign, hi]
  have hc := reflect_signedPermutation (Equiv.refl _) s fHalf
    (signedPermutation (Equiv.refl _) s x)
  rw [he, signedPermutation_sign_involutive] at hc
  rw [hc]
  exact signedPermutation_mem_F₄ _ _
    (reflect_fHalf_mem_F₄ (signedPermutation_mem_F₄ _ _ hx))

/-- Step `rFreflection`: the three kinds of roots all reflect the list into itself. -/
theorem F₄_reflection_mem {r x : EuclideanSpace ℝ (Fin 4)}
    (hr : r ∈ F₄) (hx : x ∈ F₄) : reflect r x ∈ F₄ := by
  rcases hr with (hr | ⟨i, rfl | rfl⟩) | hr
  · obtain ⟨e, s, he⟩ := exists_signedPermutation_reflect_of_mem_Dn hr
    rw [he]
    exact signedPermutation_mem_F₄ e s hx
  · rw [reflect_smul_unit_eq_signedPermutation i (by norm_num : (1 : ℝ) ≠ 0)]
    exact signedPermutation_mem_F₄ _ _ hx
  · rw [reflect_neg,
      reflect_smul_unit_eq_signedPermutation i (by norm_num : (1 : ℝ) ≠ 0)]
    exact signedPermutation_mem_F₄ _ _ hx
  · exact reflect_half_mem_F₄ hr hx

end RootSetModel
