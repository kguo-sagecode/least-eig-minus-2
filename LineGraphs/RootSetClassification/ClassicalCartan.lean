/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.ClassicalBases
import Mathlib.LinearAlgebra.Matrix.Cartan

/-!
# Cartan matrices of the classical root bases

Step `rclcartan` of `lem:classical` in the blueprint for Remark 3.11 of [CGSS].
The pairing convention is `2 * ⟪α i, α j⟫ / ⟪α j, α j⟫`: the second root
supplies the denominator. Matrix entries are compared after casting integers to reals.
-/

open scoped RealInnerProductSpace

namespace RootSetModel

/-- Coordinate orthonormality used in step `rcldiffgram` of Remark 3.11. -/
theorem inner_unit {n : ℕ} (i j : Fin n) :
    ⟪unit i, unit j⟫ = if i = j then (1 : ℝ) else 0 := by
  simp [unit, EuclideanSpace.inner_single_left]

/-- Step `rcldiffgram`: the Gram matrix of consecutive differences is A. -/
theorem inner_consecutive_differences (n : ℕ) (i j : Fin n) :
    ⟪unit i.castSucc - unit i.succ, unit j.castSucc - unit j.succ⟫ =
      (CartanMatrix.A n i j : ℝ) := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  simp only [inner_unit, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
    CartanMatrix.A, Matrix.of_apply, Int.cast_ite, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
  split_ifs <;> norm_num <;> omega

/-- Step `rcldiffgram`: each consecutive difference has squared length two. -/
theorem inner_consecutive_difference_self (n : ℕ) (i : Fin n) :
    ⟪unit i.castSucc - unit i.succ, unit i.castSucc - unit i.succ⟫ = (2 : ℝ) := by
  rw [inner_consecutive_differences]
  simp [CartanMatrix.A]

/-- The A case of `rclcartan` in Remark 3.11, in the specified zero-sum space. -/
theorem An.cartanMatrix (n : ℕ) (i j : Fin n) :
    IsRootSet.cartanPairing (An.simpleRoot n) i j = (CartanMatrix.A n i j : ℝ) := by
  change 2 * ⟪unit i.castSucc - unit i.succ, unit j.castSucc - unit j.succ⟫ /
    ⟪unit j.castSucc - unit j.succ, unit j.castSucc - unit j.succ⟫ = _
  rw [inner_consecutive_difference_self, inner_consecutive_differences]
  ring

/-- Steps `rclBgram`, `rclCgram`: pairing a difference with the final axis. -/
theorem inner_difference_last (n : ℕ) (i : Fin n) (c : ℝ) :
    ⟪unit i.castSucc - unit i.succ, c • unit (Fin.last n)⟫ =
      if i.val + 1 = n then -c else 0 := by
  rw [real_inner_smul_right, inner_sub_left, inner_unit, inner_unit]
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
  have hi := i.isLt
  split_ifs <;> simp_all

/-- The final squared length in steps `rclBgram`, `rclCgram`. -/
theorem inner_smul_unit_self {n : ℕ} (i : Fin n) (c : ℝ) :
    ⟪c • unit i, c • unit i⟫ = c ^ 2 := by
  rw [real_inner_smul_left, real_inner_smul_right, inner_unit]
  simp [pow_two]

/-- The B case of `rclcartan` in Remark 3.11, including the orientation of the final edge. -/
theorem Bn.cartanMatrix (n : ℕ) (i j : Fin (n + 1)) :
    IsRootSet.cartanPairing (Bn.simpleRoot n) i j = (CartanMatrix.B (n + 1) i j : ℝ) := by
  unfold IsRootSet.cartanPairing
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp only [Bn.simpleRoot, axisSimpleRoots, Fin.lastCases_last, inner_smul_unit_self]
    norm_num
  · simp only [Bn.simpleRoot, axisSimpleRoots, Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [real_inner_comm, inner_difference_last, inner_consecutive_difference_self]
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_last,
      Fin.val_castSucc, Nat.add_sub_cancel, Int.cast_ite, Int.cast_ofNat, Int.cast_neg,
      Int.cast_zero]
    have hj := j.isLt
    split_ifs <;> norm_num <;> omega
  · simp only [Bn.simpleRoot, axisSimpleRoots, Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [inner_difference_last, inner_smul_unit_self]
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_last,
      Fin.val_castSucc, Nat.add_sub_cancel, Int.cast_ite, Int.cast_ofNat, Int.cast_neg,
      Int.cast_zero]
    have hi := i.isLt
    split_ifs <;> norm_num <;> omega
  · simp only [Bn.simpleRoot, axisSimpleRoots, Fin.lastCases_castSucc]
    rw [inner_consecutive_difference_self, inner_consecutive_differences]
    simp only [CartanMatrix.A, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,
      Fin.val_castSucc, Nat.add_sub_cancel, Int.cast_ite, Int.cast_ofNat, Int.cast_neg,
      Int.cast_zero]
    have hi := i.isLt
    have hj := j.isLt
    split_ifs <;> norm_num <;> omega

/-- The C case of `rclcartan` in Remark 3.11, with the opposite final-edge orientation. -/
theorem Cn.cartanMatrix (n : ℕ) (i j : Fin (n + 1)) :
    IsRootSet.cartanPairing (Cn.simpleRoot n) i j = (CartanMatrix.C (n + 1) i j : ℝ) := by
  unfold IsRootSet.cartanPairing
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp only [Cn.simpleRoot, axisSimpleRoots, Fin.lastCases_last, inner_smul_unit_self]
    norm_num
  · simp only [Cn.simpleRoot, axisSimpleRoots, Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [real_inner_comm, inner_difference_last, inner_consecutive_difference_self]
    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_last,
      Fin.val_castSucc, Nat.add_sub_cancel, Int.cast_ite, Int.cast_ofNat, Int.cast_neg,
      Int.cast_zero]
    have hj := j.isLt
    split_ifs <;> norm_num <;> omega
  · simp only [Cn.simpleRoot, axisSimpleRoots, Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [inner_difference_last, inner_smul_unit_self]
    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_last,
      Fin.val_castSucc, Nat.add_sub_cancel, Int.cast_ite, Int.cast_ofNat, Int.cast_neg,
      Int.cast_zero]
    have hi := i.isLt
    split_ifs <;> norm_num <;> omega
  · simp only [Cn.simpleRoot, axisSimpleRoots, Fin.lastCases_castSucc]
    rw [inner_consecutive_difference_self, inner_consecutive_differences]
    simp only [CartanMatrix.A, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff,
      Fin.val_castSucc, Nat.add_sub_cancel, Int.cast_ite, Int.cast_ofNat, Int.cast_neg,
      Int.cast_zero]
    have hi := i.isLt
    have hj := j.isLt
    split_ifs <;> norm_num <;> omega

/-- Step `rclDgram`: the last D root pairs only with the branching root. -/
theorem inner_difference_fork (n : ℕ) (i : Fin (n + 1)) :
    ⟪unit i.castSucc - unit i.succ,
      unit (Fin.last n).castSucc + unit (Fin.last (n + 1))⟫ =
        if i.val + 1 = n then (-1 : ℝ) else 0 := by
  rw [inner_sub_left, inner_add_right, inner_add_right]
  simp only [inner_unit, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
  have hi := i.isLt
  split_ifs <;> norm_num <;> omega

/-- Step `rclDgram`: the final D simple root has squared length two. -/
theorem inner_fork_self (n : ℕ) :
    ⟪unit (Fin.last n).castSucc + unit (Fin.last (n + 1)),
      unit (Fin.last n).castSucc + unit (Fin.last (n + 1))⟫ = (2 : ℝ) := by
  rw [inner_add_left, inner_add_right, inner_add_right]
  simp only [inner_unit, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]
  norm_num

/-- The D case of `rclcartan` in Remark 3.11, with exactly Mathlib's fork labelling. -/
theorem Dn.cartanMatrix (n : ℕ) (i j : Fin (n + 2)) :
    IsRootSet.cartanPairing (Dn.simpleRoot n) i j = (CartanMatrix.D (n + 2) i j : ℝ) := by
  unfold IsRootSet.cartanPairing
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp only [Dn.simpleRoot, Fin.lastCases_last, inner_fork_self]
    simp
  · simp only [Dn.simpleRoot, Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [real_inner_comm, inner_difference_fork, inner_consecutive_difference_self]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_last,
      Fin.val_castSucc, Int.cast_ite, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
    have hj := j.isLt
    split_ifs <;> norm_num <;> (try simp_all only [or_true, and_true]) <;> omega
  · simp only [Dn.simpleRoot, Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [inner_difference_fork, inner_fork_self]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_last,
      Fin.val_castSucc, Int.cast_ite, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
    have hi := i.isLt
    split_ifs <;> norm_num <;> (try simp_all only [or_true, and_true]) <;> omega
  · simp only [Dn.simpleRoot, Fin.lastCases_castSucc]
    rw [inner_consecutive_difference_self, inner_consecutive_differences]
    simp only [CartanMatrix.A, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,
      Fin.val_castSucc, Int.cast_ite, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
    have hi := i.isLt
    have hj := j.isLt
    split_ifs <;> norm_num <;> omega

-- Remark 3.11, lem:classical
/-- All four matrix identifications in `lem:classical` of Remark 3.11 of [CGSS].
The equality is with the integer Mathlib entries cast to the real root-pairing field. -/
theorem classical_cartanMatrix :
    (∀ n i j, IsRootSet.cartanPairing (An.simpleRoot n) i j = (CartanMatrix.A n i j : ℝ)) ∧
    (∀ n i j, IsRootSet.cartanPairing (Bn.simpleRoot n) i j =
      (CartanMatrix.B (n + 1) i j : ℝ)) ∧
    (∀ n i j, IsRootSet.cartanPairing (Cn.simpleRoot n) i j =
      (CartanMatrix.C (n + 1) i j : ℝ)) ∧
    (∀ n i j, IsRootSet.cartanPairing (Dn.simpleRoot n) i j =
      (CartanMatrix.D (n + 2) i j : ℝ)) :=
  ⟨An.cartanMatrix, Bn.cartanMatrix, Cn.cartanMatrix, Dn.cartanMatrix⟩

end RootSetModel
