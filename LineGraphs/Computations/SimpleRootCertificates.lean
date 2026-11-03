/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ModelCertificates
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Certificates for simple-root bases

Integral coordinates of one sign certify simplicity. A scaled triangular factorization
computes Gram determinants without expanding a determinant over permutations.
-/

namespace Computations

/-- Check a scaled integer LDL factorization of a Gram matrix. -/
def checkScaledLDL (n : ℕ) (scale : ℤ) (G L : IntMatrix) (D : IntVector) : Bool :=
  checkShape n G && checkShape n L && D.length == n &&
    (List.finRange n).all fun (i : Fin n) => (List.finRange n).all fun (j : Fin n) =>
      scale * entry G i j == ((List.finRange n).map fun (k : Fin n) =>
        entry L i k * D[k.val]?.getD 0 * entry L j k).sum

theorem checkScaledLDL_sound {n : ℕ} {scale : ℤ} {G L : IntMatrix} {D : IntVector}
    (h : checkScaledLDL n scale G L D = true) :
    scale • toMatrix (R := ℤ) n G = toMatrix n L *
      Matrix.diagonal (fun i : Fin n => D[i.val]?.getD 0) * (toMatrix n L).transpose := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  have hi := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 i (List.mem_finRange i)
  have hij := List.all_eq_true.mp hi j (List.mem_finRange j)
  simpa only [beq_iff_eq, ← List.ofFn_eq_map, List.sum_ofFn, Matrix.smul_apply, smul_eq_mul,
    Matrix.transpose_apply, toMatrix, Int.cast_id] using hij

/-- Check root expansions and the common sign of their integral coefficients. -/
def checkRootCoordinates (n d k : ℕ) (roots basis coefficients : IntMatrix) : Bool :=
  (List.finRange n).all fun (a : Fin n) =>
    ((List.finRange k).all (fun (i : Fin k) => decide (0 ≤ entry coefficients a i)) ||
      (List.finRange k).all (fun (i : Fin k) => decide (entry coefficients a i ≤ 0))) &&
    (List.finRange d).all fun (j : Fin d) =>
      entry roots a j == ((List.finRange k).map
        (fun (i : Fin k) => entry coefficients a i * entry basis i j)).sum

theorem checkRootCoordinates_sound {n d k : ℕ} {roots basis coefficients : IntMatrix}
    (h : checkRootCoordinates n d k roots basis coefficients = true) (a : Fin n) :
    ((∀ i : Fin k, 0 ≤ entry coefficients a i) ∨
      (∀ i : Fin k, entry coefficients a i ≤ 0)) ∧
    ∀ j : Fin d, entry roots a j = ∑ i : Fin k, entry coefficients a i * entry basis i j := by
  obtain ⟨hs, hv⟩ := Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp h a (List.mem_finRange a))
  constructor
  · rcases Bool.or_eq_true_iff.mp hs with hs | hs
    · left; intro i
      simpa using List.all_eq_true.mp hs i (List.mem_finRange i)
    · right; intro i
      simpa using List.all_eq_true.mp hs i (List.mem_finRange i)
  · intro j
    have hj := List.all_eq_true.mp hv j (List.mem_finRange j)
    simpa only [beq_iff_eq, ← List.ofFn_eq_map, List.sum_ofFn] using hj

/-- Determinants of real interpretations are casts of the integer determinants. -/
theorem det_toMatrix_real (n : ℕ) (A : IntMatrix) :
    (toMatrix (R := ℝ) n A).det = ((toMatrix (R := ℤ) n A).det : ℝ) :=
  ((Int.castRingHom ℝ).map_det (toMatrix (R := ℤ) n A)).symm

end Computations

namespace LineSystem

/-- Integer linear combinations commute with normalization and passage to real coordinates. -/
theorem integerVector_sum {k d : ℕ} (c : ℝ) (z : Fin k → ℤ) (v : Fin k → Fin d → ℤ) :
    integerVector c (fun j => ∑ i, z i * v i j) =
      ∑ i, (z i : ℝ) • integerVector c (v i) := by
  ext j
  simp [integerVector, Int.cast_sum, Int.cast_mul, Finset.mul_sum, mul_left_comm]

end LineSystem
