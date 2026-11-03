/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.LabelledGraphs

/-!
# Weighted path row formulas

Uniform row formulas, including endpoints, for the unbounded affine obstruction families.
-/

namespace WeightedGraph

open Matrix

/-- The first row of a weighted path on at least two vertices. -/
theorem path_mulVec_first (n : ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : Fin (n + 2) → ℝ) :
    ((path (n + 2) w hw).weights *ᵥ x) 0 = w 0 * x 1 := by
  change (∑ j, (path (n + 2) w hw).weights 0 j * x j) = _
  rw [Finset.sum_eq_single (1 : Fin (n + 2))]
  · simp [path]
  · intro j _ hj
    have hjv : j.val ≠ 1 := fun h => hj (Fin.ext h)
    simp [path, Ne.symm hjv]
  · simp

/-- The last row of a weighted path on at least two vertices. -/
theorem path_mulVec_last (n : ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : Fin (n + 2) → ℝ) :
    ((path (n + 2) w hw).weights *ᵥ x) (Fin.last (n + 1)) =
      w n * x ⟨n, by omega⟩ := by
  let j₀ : Fin (n + 2) := ⟨n, by omega⟩
  change (∑ j, (path (n + 2) w hw).weights (Fin.last (n + 1)) j * x j) = _
  rw [Finset.sum_eq_single j₀]
  · have hne : ¬ n + 1 + 1 = n := by omega
    simp [path, j₀, hne]
  · intro j _ hj
    have hjv : j.val ≠ n := fun h => hj (Fin.ext h)
    have hnext : ¬ n + 1 + 1 = j.val := by omega
    simp [path, hnext, hjv]
  · simp

/-- An interior row of a weighted path is the sum of the two neighbouring contributions. -/
theorem path_mulVec_interior (n : ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : Fin n → ℝ) (i : Fin n) (hi : 0 < i.val) (hi' : i.val + 1 < n) :
    ((path n w hw).weights *ᵥ x) i =
      w (i.val - 1) * x ⟨i.val - 1, by omega⟩ +
      w i.val * x ⟨i.val + 1, hi'⟩ := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let q : Fin n := ⟨i.val + 1, hi'⟩
  have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; dsimp [p, q] at this; omega
  change (∑ j, (path n w hw).weights i j * x j) = _
  calc
    _ = (path n w hw).weights i p * x p + (path n w hw).weights i q * x q := by
      apply Fintype.sum_eq_add p q hpq
      rintro j ⟨hjp, hjq⟩
      have hjp' : j.val ≠ i.val - 1 := fun h => hjp (Fin.ext h)
      have hjq' : j.val ≠ i.val + 1 := fun h => hjq (Fin.ext h)
      have hprev : ¬ j.val + 1 = i.val := by omega
      simp [path, Ne.symm hjq', hprev]
    _ = _ := by
      have hp : i.val - 1 + 1 = i.val := by omega
      have hp' : ¬ i.val + 1 = i.val - 1 := by omega
      simp [path, p, q, hp, hp']

/-- A constant vector on a unit path has one contribution from each available neighbour. -/
theorem path_mulVec_const (n : ℕ) (c : ℝ) (i : Fin (n + 1)) :
    ((path (n + 1) (fun _ => 1) (by intro _; norm_num)).weights *ᵥ (fun _ => c)) i =
      (if i.val = 0 then 0 else c) + (if i.val = n then 0 else c) := by
  cases n with
  | zero => fin_cases i; simp [path, mulVec, dotProduct]
  | succ n =>
    by_cases hi : i.val = 0
    · have hieq : i = 0 := Fin.ext hi
      subst i
      rw [path_mulVec_first]
      simp
    · by_cases hi' : i.val = n + 1
      · have hieq : i = Fin.last (n + 1) := Fin.ext hi'
        subst i
        rw [path_mulVec_last]
        simp
      · rw [path_mulVec_interior _ _ _ _ i (by omega) (by omega)]
        simp [hi, hi']

end WeightedGraph
