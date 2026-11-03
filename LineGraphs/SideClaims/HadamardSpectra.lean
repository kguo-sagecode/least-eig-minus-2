/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Matrix
import LineGraphs.Spectral.AllOnes

/-!
# The spectra of `PᵀP` and `PPᵀ`

[CGSS], J. Algebra 43 (1976), Section 6, p. 326. Let `H` be a Hadamard matrix of order `n` and
let `P` be the `C(n,2) × n` matrix of the Hadamard products of pairs of rows of `H`
(`Matrix.hadamardPairs H`, rows indexed by the pairs `i < j`). Then
`PᵀP = ½n²I − ½nJ` (`Matrix.IsHadamard.transpose_hadamardPairs_mul`, in
`LineGraphs/Hadamard/Matrix.lean`). This matrix has the eigenvalues `0` (simple) and `½n²`, of
multiplicity `n − 1`; hence `PPᵀ`, of order `½n(n − 1)` (`Matrix.card_hadamardPair`), has the
eigenvalues `0` and `½n²`, of multiplicities `½(n − 1)(n − 2)` and `n − 1`.

The spectra are stated in the three forms of the spectral toolkit (`LineGraphs/Spectral/`):
the characteristic polynomial, the root multiset `Matrix.spectrumMultiset`, and the
multiplicities `Matrix.eigenvalueMultiplicity`, which are the dimensions of the eigenspaces
(`Matrix.IsHermitian.eigenvalueMultiplicity_eq_finrank`).

The only hypothesis on the order is `0 < n`: for `n = 0` the matrix `PᵀP` is empty and does not
have the eigenvalue `0`. The statements cover the orders `1` and `2` too; for `n = 1` the
eigenvalue `½n²` has multiplicity `n − 1 = 0`, and `PPᵀ` is empty.

## Main statements

* `Matrix.IsHadamard.charpoly_transpose_hadamardPairs_mul`: `χ(PᵀP) = X (X − ½n²)^(n−1)`.
* `Matrix.IsHadamard.charpoly_hadamardPairs_mul_transpose`:
  `χ(PPᵀ) = X^(½(n−1)(n−2)) (X − ½n²)^(n−1)`.
* `Matrix.IsHadamard.spectrumMultiset_transpose_hadamardPairs_mul`,
  `Matrix.IsHadamard.spectrumMultiset_hadamardPairs_mul_transpose`: the spectra as multisets.
* `Matrix.IsHadamard.eigenvalueMultiplicity_transpose_hadamardPairs_mul_zero` and its
  companions: the four multiplicities, and the dimensions of the four eigenspaces.
-/

open Polynomial Module

namespace Matrix

/-- The root multiset of `X^a (X − c)^b`. -/
private theorem roots_X_pow_mul_X_sub_C_pow (a b : ℕ) (c : ℝ) :
    (X ^ a * (X - C c) ^ b : ℝ[X]).roots =
      Multiset.replicate a 0 + Multiset.replicate b c := by
  rw [roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (X_sub_C_ne_zero c))),
    roots_X_pow, roots_pow, roots_X_sub_C, Multiset.nsmul_singleton, Multiset.nsmul_singleton]

namespace IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
include hH

/-- [CGSS], Section 6, p. 326: `PᵀP = ½n²I − ½nJ` has the eigenvalues `0` (simple) and
`½n²`, of multiplicity `n − 1`; as a characteristic polynomial. The order must be positive. -/
theorem charpoly_transpose_hadamardPairs_mul (hn : 0 < n) :
    (H.hadamardPairsᵀ * H.hadamardPairs).charpoly =
      X * (X - C ((n : ℝ) ^ 2 / 2)) ^ (n - 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [hH.transpose_hadamardPairs_mul, sub_eq_add_neg, ← neg_smul,
    charpoly_smul_one_add_smul_allOnes, Fintype.card_fin]
  have h0 : (n : ℝ) ^ 2 / 2 + -((n : ℝ) / 2) * n = 0 := by ring
  rw [h0, C_0, sub_zero]

/-- [CGSS], Section 6, p. 326: `PPᵀ` has the eigenvalues `0` and `½n²`, of
multiplicities `½(n − 1)(n − 2)` and `n − 1`; as a characteristic polynomial. It follows from
`charpoly_transpose_hadamardPairs_mul` by Mathlib's `Matrix.charpoly_mul_comm'`, since
`C(n,2) + 1 = n + ½(n − 1)(n − 2)`. The order must be positive. -/
theorem charpoly_hadamardPairs_mul_transpose (hn : 0 < n) :
    (H.hadamardPairs * H.hadamardPairsᵀ).charpoly =
      X ^ ((n - 1) * (n - 2) / 2) * (X - C ((n : ℝ) ^ 2 / 2)) ^ (n - 1) := by
  have h := charpoly_mul_comm' H.hadamardPairs H.hadamardPairsᵀ
  rw [hH.charpoly_transpose_hadamardPairs_mul hn, card_hadamardPair, Fintype.card_fin] at h
  have hk : n.choose 2 + 1 = n + (n - 1) * (n - 2) / 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_two_right,
      show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega]
    omega
  apply mul_left_cancel₀ (pow_ne_zero n (X_ne_zero : (X : ℝ[X]) ≠ 0))
  rw [h, ← mul_assoc, ← pow_succ, hk, pow_add, mul_assoc]

/-- [CGSS], Section 6, p. 326: the spectrum of `PᵀP`, with multiplicities. -/
theorem spectrumMultiset_transpose_hadamardPairs_mul (hn : 0 < n) :
    (H.hadamardPairsᵀ * H.hadamardPairs).spectrumMultiset =
      {0} + Multiset.replicate (n - 1) ((n : ℝ) ^ 2 / 2) := by
  have h := roots_X_pow_mul_X_sub_C_pow 1 (n - 1) ((n : ℝ) ^ 2 / 2)
  rw [pow_one, Multiset.replicate_one] at h
  rw [spectrumMultiset, hH.charpoly_transpose_hadamardPairs_mul hn, h]

/-- [CGSS], Section 6, p. 326: the spectrum of `PPᵀ`, with multiplicities. -/
theorem spectrumMultiset_hadamardPairs_mul_transpose (hn : 0 < n) :
    (H.hadamardPairs * H.hadamardPairsᵀ).spectrumMultiset =
      Multiset.replicate ((n - 1) * (n - 2) / 2) 0 +
        Multiset.replicate (n - 1) ((n : ℝ) ^ 2 / 2) := by
  rw [spectrumMultiset, hH.charpoly_hadamardPairs_mul_transpose hn, roots_X_pow_mul_X_sub_C_pow]

omit hH in
/-- The eigenvalue `½n²` is not zero. -/
private theorem half_sq_ne_zero (hn : 0 < n) : (n : ℝ) ^ 2 / 2 ≠ 0 := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/-- [CGSS], Section 6, p. 326: the eigenvalue `0` of `PᵀP` is simple. -/
theorem eigenvalueMultiplicity_transpose_hadamardPairs_mul_zero (hn : 0 < n) :
    (H.hadamardPairsᵀ * H.hadamardPairs).eigenvalueMultiplicity 0 = 1 := by
  change (H.hadamardPairsᵀ * H.hadamardPairs).spectrumMultiset.count 0 = 1
  rw [hH.spectrumMultiset_transpose_hadamardPairs_mul hn, Multiset.count_add,
    Multiset.count_singleton_self, Multiset.count_replicate,
    ite_eq_right (half_sq_ne_zero hn), add_zero]

/-- [CGSS], Section 6, p. 326: the eigenvalue `½n²` of `PᵀP` has multiplicity `n − 1`. -/
theorem eigenvalueMultiplicity_transpose_hadamardPairs_mul_half_sq (hn : 0 < n) :
    (H.hadamardPairsᵀ * H.hadamardPairs).eigenvalueMultiplicity ((n : ℝ) ^ 2 / 2) = n - 1 := by
  change (H.hadamardPairsᵀ * H.hadamardPairs).spectrumMultiset.count ((n : ℝ) ^ 2 / 2) = n - 1
  rw [hH.spectrumMultiset_transpose_hadamardPairs_mul hn, Multiset.count_add,
    Multiset.count_singleton, ite_eq_right (half_sq_ne_zero hn),
    Multiset.count_replicate_self, zero_add]

/-- [CGSS], Section 6, p. 326: the eigenvalue `0` of `PPᵀ` has multiplicity
`½(n − 1)(n − 2)`. -/
theorem eigenvalueMultiplicity_hadamardPairs_mul_transpose_zero (hn : 0 < n) :
    (H.hadamardPairs * H.hadamardPairsᵀ).eigenvalueMultiplicity 0 =
      (n - 1) * (n - 2) / 2 := by
  change (H.hadamardPairs * H.hadamardPairsᵀ).spectrumMultiset.count 0 = _
  rw [hH.spectrumMultiset_hadamardPairs_mul_transpose hn, Multiset.count_add,
    Multiset.count_replicate_self, Multiset.count_replicate,
    ite_eq_right (half_sq_ne_zero hn), add_zero]

/-- [CGSS], Section 6, p. 326: the eigenvalue `½n²` of `PPᵀ` has multiplicity `n − 1`. -/
theorem eigenvalueMultiplicity_hadamardPairs_mul_transpose_half_sq (hn : 0 < n) :
    (H.hadamardPairs * H.hadamardPairsᵀ).eigenvalueMultiplicity ((n : ℝ) ^ 2 / 2) = n - 1 := by
  change (H.hadamardPairs * H.hadamardPairsᵀ).spectrumMultiset.count ((n : ℝ) ^ 2 / 2) = n - 1
  rw [hH.spectrumMultiset_hadamardPairs_mul_transpose hn, Multiset.count_add,
    Multiset.count_replicate, ite_eq_right (half_sq_ne_zero hn).symm,
    Multiset.count_replicate_self, zero_add]

omit hH in
/-- `PᵀP` is symmetric. -/
private theorem isHermitian_transpose_hadamardPairs_mul :
    (H.hadamardPairsᵀ * H.hadamardPairs).IsHermitian := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    isHermitian_conjTranspose_mul_self H.hadamardPairs

omit hH in
/-- `PPᵀ` is symmetric. -/
private theorem isHermitian_hadamardPairs_mul_transpose :
    (H.hadamardPairs * H.hadamardPairsᵀ).IsHermitian := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    isHermitian_mul_conjTranspose_self H.hadamardPairs

/-- [CGSS], Section 6, p. 326: the kernel of `PᵀP` has dimension `1`. -/
theorem finrank_eigenspace_transpose_hadamardPairs_mul_zero (hn : 0 < n) :
    finrank ℝ (Module.End.eigenspace (toLin' (H.hadamardPairsᵀ * H.hadamardPairs)) 0) = 1 := by
  rw [← isHermitian_transpose_hadamardPairs_mul.eigenvalueMultiplicity_eq_finrank,
    hH.eigenvalueMultiplicity_transpose_hadamardPairs_mul_zero hn]

/-- [CGSS], Section 6, p. 326: the `½n²`-eigenspace of `PᵀP` has dimension `n − 1`. -/
theorem finrank_eigenspace_transpose_hadamardPairs_mul_half_sq (hn : 0 < n) :
    finrank ℝ (Module.End.eigenspace (toLin' (H.hadamardPairsᵀ * H.hadamardPairs))
      ((n : ℝ) ^ 2 / 2)) = n - 1 := by
  rw [← isHermitian_transpose_hadamardPairs_mul.eigenvalueMultiplicity_eq_finrank,
    hH.eigenvalueMultiplicity_transpose_hadamardPairs_mul_half_sq hn]

/-- [CGSS], Section 6, p. 326: the kernel of `PPᵀ` has dimension `½(n − 1)(n − 2)`. -/
theorem finrank_eigenspace_hadamardPairs_mul_transpose_zero (hn : 0 < n) :
    finrank ℝ (Module.End.eigenspace (toLin' (H.hadamardPairs * H.hadamardPairsᵀ)) 0) =
      (n - 1) * (n - 2) / 2 := by
  rw [← isHermitian_hadamardPairs_mul_transpose.eigenvalueMultiplicity_eq_finrank,
    hH.eigenvalueMultiplicity_hadamardPairs_mul_transpose_zero hn]

/-- [CGSS], Section 6, p. 326: the `½n²`-eigenspace of `PPᵀ` has dimension `n − 1`. -/
theorem finrank_eigenspace_hadamardPairs_mul_transpose_half_sq (hn : 0 < n) :
    finrank ℝ (Module.End.eigenspace (toLin' (H.hadamardPairs * H.hadamardPairsᵀ))
      ((n : ℝ) ^ 2 / 2)) = n - 1 := by
  rw [← isHermitian_hadamardPairs_mul_transpose.eigenvalueMultiplicity_eq_finrank,
    hH.eigenvalueMultiplicity_hadamardPairs_mul_transpose_half_sq hn]

end IsHadamard
end Matrix
