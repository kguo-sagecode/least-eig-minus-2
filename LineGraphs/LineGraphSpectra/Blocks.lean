/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.GramProducts
import LineGraphs.Spectral.Polynomial

/-!
# Quadratic spectral mapping for bipartite blocks

The algebraic part of toolkit Theorem 6.6 used in the blueprint's `lem:rootgraph`
and `lem:tworoot` for [CGSS, Lemma 5.6].
-/

open Polynomial

namespace Matrix

variable {P Q V : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Fintype V] [DecidableEq V]

/-- Reindexing preserves the spectral multiset, as used in the blueprint's
block decomposition for [CGSS, Lemma 5.6]. -/
theorem spectrumMultiset_submatrix_equiv (A : Matrix V V ℝ) (e : P ≃ V) :
    (A.submatrix e e).spectrumMultiset = A.spectrumMultiset := by
  exact congrArg Polynomial.roots (charpoly_reindex e.symm A)

/-- The spectrum of a block diagonal matrix is the sum of its block spectra,
used in blueprint step `s5rgquad` for [CGSS, Lemma 5.6]. -/
theorem spectrumMultiset_fromBlocks_zero (A : Matrix P P ℝ) (D : Matrix Q Q ℝ) :
    (fromBlocks A 0 0 D).spectrumMultiset = A.spectrumMultiset + D.spectrumMultiset := by
  simp only [spectrumMultiset, charpoly_fromBlocks_zero₁₂]
  exact roots_mul (mul_ne_zero (charpoly_monic A).ne_zero (charpoly_monic D).ne_zero)

/-- Toolkit Theorem 6.6, the quadratic identity used in the blueprint's
`lem:rootgraph`, assertion 6, for [CGSS, Lemma 5.6]. -/
theorem fromBlocks_scalar_quadratic (B : Matrix P Q ℝ) (s t : ℝ) :
    let C := fromBlocks (s • 1) B Bᵀ (t • 1)
    (C - s • 1) * (C - t • 1) = fromBlocks (B * Bᵀ) 0 0 (Bᵀ * B) := by
  dsimp only
  simp only [sub_eq_add_neg, ← fromBlocks_one, fromBlocks_smul, fromBlocks_neg,
    fromBlocks_add, smul_zero, neg_zero, add_zero, add_neg_cancel]
  rw [fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  congr 1
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  abel

/-- Blueprint step `s5rgquad` for [CGSS, Lemma 5.6]: the quadratic image of
the block spectrum is the sum of the two Gram spectra. -/
theorem spectrumMultiset_map_quadratic_fromBlocks (B : Matrix P Q ℝ) (s t : ℝ) :
    (fromBlocks (s • 1) B Bᵀ (t • 1)).spectrumMultiset.map
        (fun μ ↦ (μ - s) * (μ - t)) =
      (B * Bᵀ).spectrumMultiset + (Bᵀ * B).spectrumMultiset := by
  let C := fromBlocks (s • 1) B Bᵀ (t • 1)
  have hC : C.IsHermitian := by
    apply isHermitian_iff_isSymm.mpr
    ext (u | u) (v | v) <;> simp [C, transpose_apply, Matrix.one_apply, eq_comm]
  have heval : aeval C ((X - Polynomial.C s) * (X - Polynomial.C t)) =
      fromBlocks (B * Bᵀ) 0 0 (Bᵀ * B) := by
    simpa only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
      using fromBlocks_scalar_quadratic B s t
  have hs := hC.spectrumMultiset_aeval ((X - Polynomial.C s) * (X - Polynomial.C t))
  rw [heval, spectrumMultiset_fromBlocks_zero] at hs
  simpa only [eval_mul, eval_sub, eval_X, eval_C] using hs.symm

end Matrix
