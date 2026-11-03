/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.GraphCertificates
import LineGraphs.Spectral.Similarity

/-!
# Integer similarity certificates

An integer intertwiner and its scaled inverse certify real characteristic polynomials.
-/

namespace Computations

/-- Check shapes, a nonzero denominator, intertwining, and both inverse identities. -/
def checkSimilarity (n : ℕ) (A B Q R : IntMatrix) (d : ℤ) : Bool :=
  checkShape n A && checkShape n B && checkShape n Q && checkShape n R &&
  decide (d ≠ 0) && (matrixMul n Q A == matrixMul n B Q) &&
  (matrixMul n Q R == scalarMatrix n d) && (matrixMul n R Q == scalarMatrix n d)

/-- Soundness over the reals uses only casts of exact integer identities. -/
theorem checkSimilarity_sound {n : ℕ} {A B Q R : IntMatrix} {d : ℤ}
    (h : checkSimilarity n A B Q R d = true) :
    (toMatrix (R := ℝ) n A).charpoly = (toMatrix (R := ℝ) n B).charpoly := by
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hd⟩, hQA⟩, hQR⟩, hRQ⟩ := by
    simpa only [checkSimilarity, Bool.and_eq_true_iff, decide_eq_true_eq,
      beq_iff_eq] using h
  apply Matrix.charpoly_eq_of_scaled_inverse_intertwiner (d := (d : ℝ))
    (Q := toMatrix n Q) (R := toMatrix n R) (by exact_mod_cast hd)
  · simpa using congrArg (toMatrix (R := ℝ) n) hQA
  · simpa using congrArg (toMatrix (R := ℝ) n) hQR
  · simpa using congrArg (toMatrix (R := ℝ) n) hRQ

/-- Similarity certificates for adjacency matrices prove graph cospectrality. -/
theorem cospectral_graphOfMatrix_of_checkSimilarity {n : ℕ} {A B Q R : IntMatrix} {d : ℤ}
    (hA : checkAdjacency n A = true) (hB : checkAdjacency n B = true)
    (h : checkSimilarity n A B Q R d = true) :
    (graphOfMatrix hA).Cospectral (graphOfMatrix hB) := by
  simpa only [SimpleGraph.Cospectral, adjMatrix_graphOfMatrix] using checkSimilarity_sound h

end Computations

/-- Compatibility name from the spectral toolkit. -/
alias Matrix.similarityCertificate_sound := Computations.checkSimilarity_sound
