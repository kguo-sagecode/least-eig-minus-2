/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.Checkers
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# C19: Hall–Connor matrix certificates

The matrices in `hc:def:certificates` and computations in `hc:comp:C19` of the Hall–Connor
blueprint, used in Remark 5.12 and Example 5.13 of [CGSS]. The integer data are transcribed
from `cgss/certificates/data/c19.json`; every identity below is checked by the Lean kernel.
-/

open scoped Matrix

namespace Computations.C19

/-- The matrix `clawMatrix` of `hc:def:certificates` (C19; [CGSS], Remark 5.12). -/
def clawMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  toMatrix 4
    [[10, 3, 3, 3],
     [3, 10, -4, -4],
     [3, -4, 10, -4],
     [3, -4, -4, 10]]

/-- The matrix `fiveBlockMatrix` of `hc:def:certificates` (C19; [CGSS], Remark 5.12). -/
def fiveBlockMatrix : Matrix (Fin 5) (Fin 5) ℤ :=
  toMatrix 5
    [[10, 3, 3, 3, -4],
     [3, 10, 3, -4, 3],
     [3, 3, 10, -4, 3],
     [3, -4, -4, 10, 3],
     [-4, 3, 3, 3, 10]]

/-- The matrix `Q1` of `hc:def:certificates` (C19; [CGSS], Remark 5.12). -/
def Q1 : Matrix (Fin 7) (Fin 7) ℤ :=
  toMatrix 7
    [[10, 3, 3, 3, -4, -4, -4],
     [3, 10, 3, -4, 3, 3, 3],
     [3, 3, 10, -4, 3, 3, 3],
     [3, -4, -4, 10, -4, -4, -4],
     [-4, 3, 3, -4, 10, 3, 3],
     [-4, 3, 3, -4, 3, 10, 3],
     [-4, 3, 3, -4, 3, 3, 10]]

/-- The matrix `Q2` of `hc:def:certificates` (C19; [CGSS], Remark 5.12). -/
def Q2 : Matrix (Fin 7) (Fin 7) ℤ :=
  toMatrix 7
    [[10, 3, 3, 3, 3, -4, -4],
     [3, 10, 3, -4, -4, 3, 3],
     [3, 3, 10, -4, -4, 3, 3],
     [3, -4, -4, 10, 3, -4, -4],
     [3, -4, -4, 3, 10, -4, -4],
     [-4, 3, 3, -4, -4, 10, 3],
     [-4, 3, 3, -4, -4, 3, 10]]

/-- The matrix `K1` of `hc:def:certificates` (C19; [CGSS], Remark 5.12). -/
def K1 : Matrix (Fin 7) (Fin 7) ℤ :=
  toMatrix 7
    [[20, -12, -12, -6, 8, 8, 8],
     [-12, 9, 7, 4, -5, -5, -5],
     [-12, 7, 9, 4, -5, -5, -5],
     [-6, 4, 4, 4, -2, -2, -2],
     [8, -5, -5, -2, 5, 3, 3],
     [8, -5, -5, -2, 3, 5, 3],
     [8, -5, -5, -2, 3, 3, 5]]

/-- The matrix `K2` of `hc:def:certificates` (C19; [CGSS], Remark 5.12). -/
def K2 : Matrix (Fin 7) (Fin 7) ℤ :=
  toMatrix 7
    [[17, -11, -11, -7, -7, 6, 6],
     [-11, 9, 7, 5, 5, -4, -4],
     [-11, 7, 9, 5, 5, -4, -4],
     [-7, 5, 5, 5, 3, -2, -2],
     [-7, 5, 5, 3, 5, -2, -2],
     [6, -4, -4, -2, -2, 4, 2],
     [6, -4, -4, -2, -2, 2, 4]]

/-- The claw value `hcCertClaw` in C19 ([CGSS], Remark 5.12). -/
theorem claw_quadratic :
    (![-1, 1, 1, 1] : Fin 4 → ℤ) ⬝ᵥ (clawMatrix *ᵥ ![-1, 1, 1, 1]) = -2 := by
  decide +kernel

/-- The five-block value `hcCertFive` in C19 ([CGSS], Remark 5.12). -/
theorem five_block_quadratic :
    (![-1, 1, 1, 1, -1] : Fin 5 → ℤ) ⬝ᵥ
      (fiveBlockMatrix *ᵥ ![-1, 1, 1, 1, -1]) = -4 := by
  decide +kernel

/-- The left inverse `hcCertOne` in C19 ([CGSS], Remark 5.12). -/
theorem left_inverse_Q1 : K1 * Q1 = (14 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by
  unfold K1 Q1
  rw [← toMatrix_mul]
  calc
    _ = toMatrix (R := ℤ) 7 (scalarMatrix 7 14) := by rfl
    _ = _ := by simpa only [Int.cast_id] using toMatrix_scalar (R := ℤ) 7 14

/-- The nonzero determinant of `Q1`, `hc:lem:inverse` (C19; [CGSS], Remark 5.12). -/
theorem det_Q1_ne_zero : (Q1.map (Int.castRingHom ℚ)).det ≠ 0 := by
  have hdet : Q1.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det left_inverse_Q1
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, hz] at h
    norm_num at h
  change (Matrix.map _ (fun x : ℤ ↦ (x : ℚ))).det ≠ 0
  rw [← Int.cast_det]
  exact_mod_cast hdet

/-- The left inverse `hcCertTwo` in C19 ([CGSS], Remark 5.12). -/
theorem left_inverse_Q2 : K2 * Q2 = (14 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by
  unfold K2 Q2
  rw [← toMatrix_mul]
  calc
    _ = toMatrix (R := ℤ) 7 (scalarMatrix 7 14) := by rfl
    _ = _ := by simpa only [Int.cast_id] using toMatrix_scalar (R := ℤ) 7 14

/-- The nonzero determinant of `Q2`, `hc:lem:inverse` (C19; [CGSS], Remark 5.12). -/
theorem det_Q2_ne_zero : (Q2.map (Int.castRingHom ℚ)).det ≠ 0 := by
  have hdet : Q2.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det left_inverse_Q2
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, hz] at h
    norm_num at h
  change (Matrix.map _ (fun x : ℤ ↦ (x : ℚ))).det ≠ 0
  rw [← Int.cast_det]
  exact_mod_cast hdet

end Computations.C19
