/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.ModelUniqueness

/-!
# The one-length and two-length models

The length assertion of blueprint Theorem B and step `rBonevsTwo` in Remark 3.11 of
[CGSS]. The length spectrum follows from the complete length-count table.
-/

open scoped RealInnerProductSpace

namespace IsRootSet

/-- The squared lengths occurring in a root set, used in Theorems B and C of Remark 3.11. -/
def squaredLengths {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Φ : Set V) : Set ℝ := (fun r ↦ ⟪r, r⟫) '' Φ

end IsRootSet

namespace RootSetModel

/-- The one-length types in blueprint Theorem B and `rangADE` of Remark 3.11. -/
def IsSimplyLaced {n : ℕ} : CartanMatrix.FiniteType n → Prop
  | .a _ _ | .d _ _ | .e₆ | .e₇ | .e₈ => True
  | _ => False

/-- The greatest squared length in the table of `lem:counts`, Remark 3.11. -/
def maxLengthSq {n : ℕ} : CartanMatrix.FiniteType n → ℝ
  | .c _ _ => 4
  | .g₂ => 6
  | _ => 2

/-- The positive entries of the length-count table are precisely its two endpoints
(coincident for the one-length models), in `rBonevsTwo` of Remark 3.11. -/
theorem lengthCount_pos_iff {n : ℕ} (t : CartanMatrix.FiniteType n) (q : ℝ) :
    0 < lengthCount t q ↔ q = minLengthSq t ∨ q = maxLengthSq t := by
  have hn := t.rank_pos
  cases t <;> dsimp [lengthCount, rootCount, minLengthSq, maxLengthSq] <;>
    split_ifs <;> simp_all <;> omega

/-- The complete squared-length spectrum in Theorem B of the blueprint for Remark 3.11 of [CGSS]. -/
theorem squaredLengths_eq {n : ℕ} (t : CartanMatrix.FiniteType n) :
    IsRootSet.squaredLengths (roots t) = {minLengthSq t, maxLengthSq t} := by
  ext q
  have he : q ∈ IsRootSet.squaredLengths (roots t) ↔
      {r ∈ roots t | ⟪r, r⟫ = q}.Nonempty := by
    simp only [IsRootSet.squaredLengths, Set.mem_image, Set.nonempty_def, Set.mem_ofPred_eq]
  rw [he, ← Set.ncard_pos ((isRootSet t).finite.sep _), length_counts, lengthCount_pos_iff]
  rfl

/-- Blueprint Theorem B's one-length types are exactly A, D, and E (`rBonevsTwo`). -/
theorem maxLengthSq_eq_min_iff {n : ℕ} (t : CartanMatrix.FiniteType n) :
    maxLengthSq t = minLengthSq t ↔ IsSimplyLaced t := by
  cases t <;> norm_num [maxLengthSq, minLengthSq, IsSimplyLaced]

/-- Theorem B of the blueprint for Remark 3.11 of [CGSS] (`thm:B`, with the length assertion of
`lem:counts`):
the two-length types are exactly B, C, F and G. -/
theorem two_lengths_iff {n : ℕ} (t : CartanMatrix.FiniteType n) :
    (IsRootSet.squaredLengths (roots t)).ncard = 2 ↔ ¬ IsSimplyLaced t := by
  rw [squaredLengths_eq]
  cases t <;> norm_num [minLengthSq, maxLengthSq, IsSimplyLaced]

/-- The one-length assertion of `lem:counts`, Remark 3.11: exactly A, D and E have one length. -/
theorem one_length_iff {n : ℕ} (t : CartanMatrix.FiniteType n) :
    (IsRootSet.squaredLengths (roots t)).ncard = 1 ↔ IsSimplyLaced t := by
  rw [squaredLengths_eq]
  cases t <;> norm_num [minLengthSq, maxLengthSq, IsSimplyLaced]

/-- The ratio of greatest to least squared length in `lem:counts`, Remark 3.11. -/
def lengthRatio {n : ℕ} : CartanMatrix.FiniteType n → ℝ
  | .b _ _ | .c _ _ | .f₄ => 2
  | .g₂ => 3
  | _ => 1

/-- The length-ratio assertion of `lem:counts`, Remark 3.11: ratio 2 in B, C and F,
ratio 3 in G, and ratio 1 in every other model. -/
theorem maxLengthSq_eq_lengthRatio_mul {n : ℕ} (t : CartanMatrix.FiniteType n) :
    maxLengthSq t = lengthRatio t * minLengthSq t := by
  cases t <;> norm_num [maxLengthSq, lengthRatio, minLengthSq]

end RootSetModel
