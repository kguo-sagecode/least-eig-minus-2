/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.FCoordinates

/-!
# The G₂ coordinate patterns and reflections

Steps `rGbasic`--`rGinteger` of `lem:G` in the blueprint for Remark 3.11 of
[CGSS]. Short reflections interchange coordinates; a long reflection is a
coordinate interchange followed by negation on the zero-sum plane.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

/-- The ambient coordinate list `eq:G-roots` of Remark 3.11. -/
noncomputable def gRoots : Set (EuclideanSpace ℝ (Fin 3)) :=
  (LineSystem.An 2).Φ ∪ {x | ∃ i, x = g₂LongRoot i ∨ x = -g₂LongRoot i}

/-- The zero-sum equation used throughout `lem:G` of Remark 3.11. -/
theorem mem_g₂Space (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ g₂Space ↔ x 0 + x 1 + x 2 = 0 := by
  change (∑ i, x i) = 0 ↔ _
  simp [Fin.sum_univ_succ, add_assoc]

/-- The long-root coordinate pattern of step `rGlong` in Remark 3.11. -/
theorem g₂LongRoot_apply (i j : Fin 3) : g₂LongRoot i j = if j = i then 2 else -1 := by
  by_cases h : j = i <;> norm_num [g₂LongRoot, unit, h]

/-- The integer coordinates of the long pattern in step `rGlong` of Remark 3.11. -/
theorem g₂LongRoot_eq_integerVector (i : Fin 3) : g₂LongRoot i =
    LineSystem.integerVector 1 (fun j ↦ if j = i then 2 else -1) := by
  ext j
  rw [g₂LongRoot_apply]
  by_cases h : j = i <;> simp [LineSystem.integerVector, h]

/-- Step `rGlong`: the squared norm of each long root is six. -/
theorem g₂LongRoot_inner_self (i : Fin 3) : ⟪g₂LongRoot i, g₂LongRoot i⟫ = 6 := by
  have he : ∀ i : Fin 3, LineSystem.integerInner
      (fun j ↦ if j = i then 2 else -1) (fun j ↦ if j = i then 2 else -1) = 6 := by
    decide +kernel
  rw [g₂LongRoot_eq_integerVector, LineSystem.inner_integerVector, he]
  norm_num

/-- The short and long index sets in step `rGbasic` of Remark 3.11. -/
abbrev G₂Index := LineSystem.AnIndex 2 ⊕ (Fin 3 × Bool)

/-- The integer roots in `eq:G-roots` of Remark 3.11. -/
def gRootEntries : G₂Index → Fin 3 → ℤ
  | .inl a => LineSystem.anRoot a
  | .inr a => fun i ↦ LineSystem.rootSign a.2 * (if i = a.1 then 2 else -1)

/-- The finite coordinate parametrization in step `rGbasic` of Remark 3.11. -/
theorem gRoots_eq_range : gRoots = Set.range (fun a ↦ LineSystem.integerVector 1
    (gRootEntries a)) := by
  ext x
  constructor
  · rintro (⟨a, rfl⟩ | ⟨i, rfl | rfl⟩)
    · exact ⟨.inl a, rfl⟩
    · refine ⟨.inr (i, false), ?_⟩
      ext j
      simp [gRootEntries, LineSystem.integerVector, g₂LongRoot_apply, LineSystem.rootSign]
    · refine ⟨.inr (i, true), ?_⟩
      ext j
      by_cases h : j = i <;>
        simp [gRootEntries, LineSystem.integerVector, g₂LongRoot_apply, LineSystem.rootSign, h]
  · rintro ⟨a, rfl⟩
    rcases a with a | ⟨i, b⟩
    · exact Or.inl ⟨a, rfl⟩
    · right
      refine ⟨i, ?_⟩
      cases b
      · left; ext j
        simp [gRootEntries, LineSystem.integerVector, g₂LongRoot_apply, LineSystem.rootSign]
      · right; ext j
        by_cases h : j = i <;>
          simp [gRootEntries, LineSystem.integerVector, g₂LongRoot_apply, LineSystem.rootSign, h]

/-- Step `rGbasic`: every listed root lies in the zero-sum plane. -/
theorem gRootEntries_sum : ∀ a : G₂Index, ∑ i, gRootEntries a i = 0 := by
  decide +kernel

/-- The roots of `eq:G-roots`, as vectors of the zero-sum plane. -/
noncomputable def gRoot (a : G₂Index) : g₂Space :=
  ⟨LineSystem.integerVector 1 (gRootEntries a), by
    change (∑ i, (LineSystem.integerVector 1 (gRootEntries a)) i) = 0
    simp [LineSystem.integerVector, ← Int.cast_sum, gRootEntries_sum]⟩

/-- The finite parametrization in the correct ambient space, in step `rGbasic`. -/
theorem G₂_eq_range : G₂ = Set.range gRoot := by
  ext x
  change (x : EuclideanSpace ℝ (Fin 3)) ∈ gRoots ↔ _
  rw [gRoots_eq_range]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

/-- Steps `rGshort`, `rGlong`: the two possible squared lengths are two and six. -/
theorem gRoots_inner_self {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ gRoots) :
    ⟪x, x⟫ = 2 ∨ ⟪x, x⟫ = 6 := by
  rcases hx with hx | ⟨i, rfl | rfl⟩
  · exact Or.inl ((LineSystem.An 2).inner_self x hx)
  · exact Or.inr (g₂LongRoot_inner_self i)
  · exact Or.inr (by rw [inner_neg_neg, g₂LongRoot_inner_self])

/-- Step `rGreduced`: the short roots have a zero coordinate. -/
theorem exists_zero_coordinate_of_mem_G₂_short {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (LineSystem.An 2).Φ) : ∃ i, x i = 0 := by
  obtain ⟨a, rfl⟩ := hx
  have h : ∀ a : LineSystem.AnIndex 2, ∃ i, LineSystem.anRoot a i = 0 := by
    decide +kernel
  obtain ⟨i, hi⟩ := h a
  exact ⟨i, by simp [LineSystem.integerVector, hi]⟩

/-- Step `rGreduced`: support sizes distinguish the lengths, and equal lengths are reduced. -/
theorem gRoots_reduced {r : EuclideanSpace ℝ (Fin 3)} (hr : r ∈ gRoots)
    (t : ℝ) (ht : t • r ∈ gRoots) : t = 1 ∨ t = -1 := by
  have solve {q : ℝ} (hq : q ≠ 0) (h₁ : ⟪r, r⟫ = q) (h₂ : ⟪t • r, t • r⟫ = q) :
      t = 1 ∨ t = -1 := by
    rw [real_inner_smul_left, real_inner_smul_right, h₁] at h₂
    have hp : (t - 1) * (t + 1) = 0 := by
      have : t * t = 1 := by apply mul_right_cancel₀ hq; nlinarith
      nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hlong (x : EuclideanSpace ℝ (Fin 3)) (hx : ∃ j, x = g₂LongRoot j ∨
      x = -g₂LongRoot j) : ∀ i, x i ≠ 0 := by
    obtain ⟨j, rfl | rfl⟩ := hx <;> intro i <;>
      simp only [PiLp.neg_apply, g₂LongRoot_apply] <;>
      split_ifs <;> norm_num
  rcases hr with hr | hr <;> rcases ht with ht | ht
  · exact solve (by norm_num : (2 : ℝ) ≠ 0)
      ((LineSystem.An 2).inner_self r hr) ((LineSystem.An 2).inner_self _ ht)
  · obtain ⟨i, hi⟩ := exists_zero_coordinate_of_mem_G₂_short hr
    exact False.elim (hlong _ ht i (by simp [hi]))
  · have ht0 : t ≠ 0 := by
      intro h
      have hn := (LineSystem.An 2).inner_self _ ht
      simp [h] at hn
    obtain ⟨i, hi⟩ := exists_zero_coordinate_of_mem_G₂_short ht
    exact False.elim ((mul_ne_zero ht0 (hlong _ hr i)) hi)
  · have hn (x : EuclideanSpace ℝ (Fin 3)) (hx : ∃ j, x = g₂LongRoot j ∨
        x = -g₂LongRoot j) : ⟪x, x⟫ = 6 := by
      obtain ⟨j, rfl | rfl⟩ := hx <;> simp only [inner_neg_neg, g₂LongRoot_inner_self]
    exact solve (by norm_num : (6 : ℝ) ≠ 0) (hn _ hr) (hn _ ht)

/-- Steps `rGshortref`, `rGlongref`: unsigned permutations take long roots to long roots. -/
theorem signedPermutation_g₂LongRoot (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    signedPermutation e (fun _ ↦ false) (g₂LongRoot i) = g₂LongRoot (e i) := by
  ext j
  simp [signedPermutation, g₂LongRoot_apply, LineSystem.rootSign, e.symm_apply_eq]

/-- The permutation invariance used in steps `rGshortref` and `rGlongref`. -/
theorem signedPermutation_mem_gRoots (e : Equiv.Perm (Fin 3))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ gRoots) :
    signedPermutation e (fun _ ↦ false) x ∈ gRoots := by
  rcases hx with hx | ⟨i, rfl | rfl⟩
  · exact Or.inl (signedPermutation_mem_An e hx)
  · exact Or.inr ⟨e i, Or.inl (signedPermutation_g₂LongRoot e i)⟩
  · exact Or.inr ⟨e i, Or.inr (by rw [map_neg, signedPermutation_g₂LongRoot])⟩

/-- The global-sign invariance used in step `rGbetaref`. -/
theorem neg_mem_gRoots {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ gRoots) :
    -x ∈ gRoots := by
  rcases hx with hx | ⟨i, rfl | rfl⟩
  · exact Or.inl ((LineSystem.An 2).neg_mem x hx)
  · exact Or.inr ⟨i, Or.inr rfl⟩
  · exact Or.inr ⟨i, Or.inl (neg_neg _)⟩

/-- Step `rGinner`: a long root pairs with a zero-sum vector by three times one coordinate. -/
theorem inner_g₂LongRoot (i : Fin 3) (x : g₂Space) : ⟪g₂LongRoot i, x.val⟫ = 3 * x.val i := by
  have hx : ∑ j, x.val j = 0 := x.property
  rw [g₂LongRoot, inner_sub_left, real_inner_smul_left, sum_inner]
  simp only [unit, EuclideanSpace.inner_single_left, map_one, one_mul, hx, sub_zero]

/-- Step `rGlongformula`: the first long reflection is minus a coordinate interchange. -/
theorem reflect_g₂LongRoot_zero (x : g₂Space) :
    reflect (g₂LongRoot 0) x.val =
      -signedPermutation (Equiv.swap (1 : Fin 3) 2) (fun _ ↦ false) x.val := by
  have hx := (mem_g₂Space x).mp x.property
  rw [reflect, inner_g₂LongRoot, g₂LongRoot_inner_self]
  ext i
  change x.val i - (2 * (3 * x.val 0) / 6) * g₂LongRoot 0 i =
    -((LineSystem.rootSign false : ℝ) *
      x.val ((Equiv.swap (1 : Fin 3) 2).symm i))
  rw [Equiv.symm_swap]
  have hswap : ∀ i : Fin 3, Equiv.swap (1 : Fin 3) 2 i = ![0, 2, 1] i := by
    decide +kernel
  rw [hswap]
  simp only [LineSystem.rootSign, Bool.false_eq_true, ite_false, Int.cast_one, one_mul]
  have hentry : (fun j : Fin 3 ↦ if j = 0 then (2 : ℤ) else -1) = ![2, -1, -1] := by
    decide +kernel
  rw [g₂LongRoot_eq_integerVector, hentry]
  fin_cases i <;> norm_num [LineSystem.integerVector] <;> try linarith
  change x.val 2 + 2 * (3 * x.val 0) / 6 = -x.val 1
  linarith

/-- The involutive coordinate interchanges used in step `rGlongref`. -/
theorem signedPermutation_swap_involutive {n : ℕ} (i j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    signedPermutation (Equiv.swap i j) (fun _ ↦ false)
      (signedPermutation (Equiv.swap i j) (fun _ ↦ false) x) = x := by
  ext k
  simp [signedPermutation, LineSystem.rootSign]

/-- Steps `rGbetaref`, `rGlongref`: conjugate the first long reflection by a permutation. -/
theorem reflect_g₂LongRoot_mem (i : Fin 3) (x : g₂Space) (hx : x.val ∈ gRoots) :
    reflect (g₂LongRoot i) x.val ∈ gRoots := by
  let e := Equiv.swap (0 : Fin 3) i
  let y : g₂Space := ⟨signedPermutation e (fun _ ↦ false) x.val, by
    change LineSystem.coordinateSum 3 _ = 0
    rw [coordinateSum_signedPermutation]
    exact x.property⟩
  have hy : y.val ∈ gRoots := signedPermutation_mem_gRoots e hx
  have he : signedPermutation e (fun _ ↦ false) (g₂LongRoot 0) = g₂LongRoot i := by
    rw [signedPermutation_g₂LongRoot]
    simp [e]
  have hc := reflect_signedPermutation e (fun _ ↦ false) (g₂LongRoot 0) y.val
  rw [he] at hc
  have hxy : signedPermutation e (fun _ ↦ false) y.val = x.val :=
    signedPermutation_swap_involutive 0 i x.val
  rw [hxy, reflect_g₂LongRoot_zero] at hc
  rw [hc]
  exact signedPermutation_mem_gRoots e
    (neg_mem_gRoots (signedPermutation_mem_gRoots _ hy))

/-- Step `rGreflection`: the short and long reflection formulas preserve the coordinate list. -/
theorem gRoots_reflection_mem {r : EuclideanSpace ℝ (Fin 3)} (hr : r ∈ gRoots)
    (x : g₂Space) (hx : x.val ∈ gRoots) : reflect r x.val ∈ gRoots := by
  rcases hr with hr | ⟨i, rfl | rfl⟩
  · obtain ⟨⟨⟨i, j⟩, hij⟩, rfl⟩ := hr
    have he : LineSystem.integerVector 1 (LineSystem.anRoot ⟨(i, j), hij⟩) =
        unit i - unit j := by
      ext k
      simp [LineSystem.integerVector, LineSystem.anRoot, LineSystem.pairVector,
        unit, Pi.single_apply]
      split_ifs <;> norm_num
    change reflect (LineSystem.integerVector 1 (LineSystem.anRoot ⟨(i, j), hij⟩)) x.val ∈ _
    rw [he, reflect_sub_unit_eq_signedPermutation i j hij]
    exact signedPermutation_mem_gRoots _ hx
  · exact reflect_g₂LongRoot_mem i x hx
  · rw [reflect_neg]
    exact reflect_g₂LongRoot_mem i x hx

/-- Steps `rGshortpair`--`rGlongpair`: the pairings are integers. -/
theorem gRoots_crystallographic {r : EuclideanSpace ℝ (Fin 3)} (hr : r ∈ gRoots)
    (x : g₂Space) (hx : x.val ∈ gRoots) :
    ∃ z : ℤ, (z : ℝ) = 2 * ⟪r, x.val⟫ / ⟪r, r⟫ := by
  obtain ⟨a, ha⟩ := gRoots_eq_range ▸ hx
  rcases hr with hr | ⟨i, rfl | rfl⟩
  · rw [(LineSystem.An 2).inner_self r hr]
    obtain ⟨b, rfl⟩ := hr
    refine ⟨LineSystem.integerInner (LineSystem.anRoot b) (gRootEntries a), ?_⟩
    rw [← ha, LineSystem.inner_integerVector]
    ring
  · refine ⟨gRootEntries a i, ?_⟩
    rw [g₂LongRoot_inner_self, inner_g₂LongRoot, ← ha]
    simp [LineSystem.integerVector]
    ring
  · refine ⟨-gRootEntries a i, ?_⟩
    rw [inner_neg_neg, g₂LongRoot_inner_self, inner_neg_left, inner_g₂LongRoot, ← ha]
    simp [LineSystem.integerVector]
    ring

end RootSetModel
