/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.TraceRank

/-!
# The projection in the parameter lemma

The matrix algebra behind steps `s414srgidem`--`s414srgrkQ` of Lemma
`lem:414-srg`, Remark 4.14 of [CGSS]. Adding the all-ones projection back to
the centred projection gives a projection with the same range as `Q`.
-/

open Matrix

namespace Matrix

/-- The projection calculation for Lemma `lem:414-srg`, Remark 4.14 of [CGSS].
Here `J` is the all-ones matrix, `b` the row sum of `Q`, and `d = a - c + 4`.
The hypotheses also cover the calculation abstractly, without symmetry. -/
theorem mul_rank_sub_one_eq_of_quadratic {V : Type*} [Fintype V]
    (Q J : Matrix V V ℝ) (b c d n : ℝ) (hb : b ≠ 0) (hd : d ≠ 0)
    (hQ : Q * Q = d • Q + c • J)
    (hQJ : Q * J = b • J) (hJQ : J * Q = b • J)
    (hJJ : J * J = n • J) (hcn : c * n = b * (b - d))
    (htrQ : Q.trace = 2 * n) (htrJ : J.trace = n) :
    d * ((Q.rank : ℝ) - 1) = 2 * n - b := by
  classical
  let P := d⁻¹ • Q - (c / (d * b)) • J
  have hcoef : c / (d * b) * b = d⁻¹ * c := by field_simp
  have hcoefJ : d⁻¹ * b - c / (d * b) * n = 1 := by
    apply (mul_right_cancel₀ (mul_ne_zero hd hb))
    field_simp
    nlinarith [hcn]
  have hPQ : P * Q = Q := by
    dsimp [P]
    simp only [sub_mul, smul_mul, hQ, hJQ, smul_add, smul_smul,
      inv_mul_cancel₀ hd, one_smul, hcoef]
    module
  have hPJ : P * J = J := by
    dsimp [P]
    rw [sub_mul, smul_mul, smul_mul, hQJ, hJJ, smul_smul, smul_smul,
      ← sub_smul, hcoefJ, one_smul]
  have hPP : P * P = P := by
    conv_lhs => rhs; unfold P
    rw [mul_sub, mul_smul_comm, mul_smul_comm, hPQ, hPJ]
  have hfactor : Q * (d⁻¹ • 1 - (c / (d * b * b)) • J) = P := by
    rw [mul_sub, mul_smul_comm, mul_one, mul_smul_comm, hQJ, smul_smul]
    dsimp [P]
    congr 2
    field_simp
  have hrank : P.rank = Q.rank := le_antisymm
    (hfactor ▸ rank_mul_le_left Q _)
    (hPQ ▸ rank_mul_le_left P Q)
  have htrace := trace_eq_rank_of_idempotent hPP
  rw [hrank] at htrace
  dsimp [P] at htrace
  rw [trace_sub, trace_smul, trace_smul, htrQ, htrJ] at htrace
  simp only [smul_eq_mul] at htrace
  rw [← htrace]
  field_simp
  nlinarith [hcn]

end Matrix
