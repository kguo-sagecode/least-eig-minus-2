/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Affine

/-!
# Positive eigenvectors of affine obstructions

The explicit vectors of `lem:affine` in the Remark 3.11 blueprint.
-/

namespace WeightedGraph

open Matrix

/-- The endpoint-weighted path vector is 1 at its ends and √2 in its interior. -/
noncomputable def endPathEigenvector (m : ℕ) (i : Fin m) : ℝ :=
  if i.val = 0 ∨ i.val + 1 = m then 1 else Real.sqrt 2

/-- The displayed positive vector solves every endpoint-weighted path, including `m=3`. -/
theorem endPath_eigenvector (m : ℕ) (hm : 3 ≤ m) :
    (∀ i, 0 < endPathEigenvector m i) ∧
    (endPath m).weights *ᵥ endPathEigenvector m = (2 : ℝ) • endPathEigenvector m := by
  constructor
  · intro i
    unfold endPathEigenvector
    split_ifs <;> positivity
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
    funext i
    by_cases hi : i.val = 0
    · have hieq : i = 0 := Fin.ext hi
      subst i
      rw [endPath, path_mulVec_first (n + 1)]
      norm_num [endPathEigenvector, Real.sq_sqrt, ← pow_two]
    · by_cases hi' : i.val + 1 = n + 3
      · have hieq : i = Fin.last (n + 2) := Fin.ext (by simp; omega)
        subst i
        rw [endPath, path_mulVec_last (n + 1)]
        have hn1 : n + 1 ≠ 0 := by omega
        have hn2 : ¬ n + 1 + 1 = n + 3 := by omega
        norm_num [endPathEigenvector, hn1, hn2, Real.sq_sqrt, ← pow_two]
      · have hleft : i.val - 1 + 1 = i.val := by omega
        have hile : i.val + 1 < n + 3 := by omega
        rw [endPath, path_mulVec_interior _ _ _ _ i (by omega) hile]
        simp only [Pi.smul_apply, smul_eq_mul, endPathEigenvector]
        have hprev : ¬ i.val - 1 + 1 = n + 3 := by omega
        have hnext : ¬ i.val + 1 = 0 := by omega
        have hi2 : ¬ i.val - 1 + 2 = n + 3 := by omega
        simp only [hi, hi', hprev, hnext, hi2, or_false, false_or, ite_false]
        split_ifs <;> ring

private theorem sum_armVertex (a b c : ℕ)
    (f : SimpleGraph.ArmVertex ![a, b, c] → ℝ) :
    ∑ i, f i = f none + ((∑ i : Fin a, f (some ⟨0, i⟩)) +
      (∑ i : Fin b, f (some ⟨1, i⟩)) + ∑ i : Fin c, f (some ⟨2, i⟩)) := by
  rw [Fintype.sum_option, Fintype.sum_sigma, Fin.sum_univ_three]
  rfl

/-- The affine E arm vector, with prescribed central value and zero-based arm position. -/
noncomputable def armEigenvector (a : Fin 3 → ℕ) (h : ℝ) : SimpleGraph.ArmVertex a → ℝ
  | none => h
  | some ⟨r, t⟩ => h * ((a r : ℝ) - t.val) / ((a r : ℝ) + 1)

/-- The affine E₆ vector has centre 3 and arm values 2, 1. -/
theorem smithE₆_eigenvector :
    (∀ i, 0 < armEigenvector ![2, 2, 2] 3 i) ∧
    (unit SimpleGraph.smithE₆).weights *ᵥ armEigenvector ![2, 2, 2] 3 =
      (2 : ℝ) • armEigenvector ![2, 2, 2] 3 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [armEigenvector]
  · funext i
    simp only [mulVec, dotProduct, sum_armVertex]
    fin_cases i <;>
      norm_num [unit, SimpleGraph.smithE₆, SimpleGraph.adjMatrix, SimpleGraph.armTree,
        Fin.sum_univ_succ, armEigenvector] <;>
      dsimp <;> norm_num [Fin.ext_iff]

/-- The affine E₇ vector has centre 4 and the arm arithmetic progressions. -/
theorem smithE₇_eigenvector :
    (∀ i, 0 < armEigenvector ![1, 3, 3] 4 i) ∧
    (unit SimpleGraph.smithE₇).weights *ᵥ armEigenvector ![1, 3, 3] 4 =
      (2 : ℝ) • armEigenvector ![1, 3, 3] 4 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [armEigenvector]
  · funext i
    simp only [mulVec, dotProduct, sum_armVertex]
    fin_cases i <;>
      norm_num [unit, SimpleGraph.smithE₇, SimpleGraph.adjMatrix, SimpleGraph.armTree,
        Fin.sum_univ_succ, armEigenvector] <;>
      dsimp <;> norm_num [Fin.ext_iff]

/-- The affine E₈ vector has centre 6 and the arm arithmetic progressions. -/
theorem smithE₈_eigenvector :
    (∀ i, 0 < armEigenvector ![1, 2, 5] 6 i) ∧
    (unit SimpleGraph.smithE₈).weights *ᵥ armEigenvector ![1, 2, 5] 6 =
      (2 : ℝ) • armEigenvector ![1, 2, 5] 6 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [armEigenvector]
  · funext i
    simp only [mulVec, dotProduct, sum_armVertex]
    fin_cases i <;>
      norm_num [unit, SimpleGraph.smithE₈, SimpleGraph.adjMatrix, SimpleGraph.armTree,
        Fin.sum_univ_succ, armEigenvector] <;>
      dsimp <;> norm_num [Fin.ext_iff]

/-- The middle-weighted affine path has positive 2-eigenvector `(1,2,3,2√2,√2)`. -/
theorem middlePath_eigenvector :
    (∀ i : Fin 5, 0 < (![1, 2, 3, 2 * Real.sqrt 2, Real.sqrt 2] : Fin 5 → ℝ) i) ∧
    middlePath.weights *ᵥ ![1, 2, 3, 2 * Real.sqrt 2, Real.sqrt 2] =
      (2 : ℝ) • ![1, 2, 3, 2 * Real.sqrt 2, Real.sqrt 2] := by
  constructor
  · intro i
    fin_cases i <;> norm_num
  · ext i
    fin_cases i <;>
      norm_num [middlePath, path, mulVec, dotProduct, Fin.sum_univ_succ, ← pow_two] <;>
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The triple-weighted affine path has positive 2-eigenvector `(√3,2,1)`. -/
theorem triplePath_eigenvector :
    (∀ i : Fin 3, 0 < (![Real.sqrt 3, 2, 1] : Fin 3 → ℝ) i) ∧
    triplePath.weights *ᵥ ![Real.sqrt 3, 2, 1] =
      (2 : ℝ) • ![Real.sqrt 3, 2, 1] := by
  constructor
  · intro i
    fin_cases i <;> norm_num
  · ext i
    fin_cases i <;>
      norm_num [triplePath, path, mulVec, dotProduct, Fin.sum_univ_succ, ← pow_two]
    ring

end WeightedGraph
