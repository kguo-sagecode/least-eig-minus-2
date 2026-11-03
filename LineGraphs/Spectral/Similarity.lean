/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Basic

/-!
# Similarity from an explicit scaled inverse

The certificate identities avoid symbolic determinant computation.
-/

namespace Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- An invertible intertwiner identifies characteristic polynomials. -/
theorem charpoly_eq_of_invertible_intertwiner {A B Q : Matrix ι ι K}
    (hQ : Q.det ≠ 0) (h : Q * A = B * Q) : A.charpoly = B.charpoly := by
  have hQA : Q⁻¹ * (Q * A) = A := by
    rw [← mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ), one_mul]
  rw [← hQA, charpoly_mul_comm, h, mul_assoc,
    mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hQ), mul_one]

/-- A nonzero scalar times an explicit inverse suffices for similarity. -/
theorem charpoly_eq_of_scaled_inverse_intertwiner {A B Q R : Matrix ι ι K} {d : K}
    (hd : d ≠ 0) (h : Q * A = B * Q) (hQR : Q * R = d • 1)
    (hRQ : R * Q = d • 1) : A.charpoly = B.charpoly := by
  have hleft : (d⁻¹ • R) * Q = 1 := by simp [hRQ, smul_smul, hd]
  have hright : Q * (d⁻¹ • R) = 1 := by simp [hQR, smul_smul, hd]
  calc
    A.charpoly = ((d⁻¹ • R) * (Q * A)).charpoly := by rw [← mul_assoc, hleft, one_mul]
    _ = ((Q * A) * (d⁻¹ • R)).charpoly := charpoly_mul_comm _ _
    _ = B.charpoly := by rw [h, mul_assoc, hright, mul_one]

end Matrix
