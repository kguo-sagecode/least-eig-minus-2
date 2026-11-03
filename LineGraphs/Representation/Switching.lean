/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Switching

/-!
# Integer certificates for Seidel switching

The transfer used in C9 for the switching assertions of Example 4.8 of [CGSS].
-/

namespace SimpleGraph

/-- C9, Example 4.8 of [CGSS]: a signed integer Seidel identity is a
certificate of the switching equivalence of the actual graphs. -/
theorem isSwitchingEquivalent_of_integer_certificate {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : V ≃ W) (d : V → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1)
    (he : ∀ i j,
      ((if i = j then 0 else 1) - 2 * (if G.Adj i j then 1 else 0) : ℤ) =
        d i * d j * ((if e i = e j then 0 else 1) -
          2 * (if H.Adj (e i) (e j) then 1 else 0))) :
    G.IsSwitchingEquivalent H := by
  refine ⟨e, fun i ↦ (d i : ℝ), ?_, ?_⟩
  · intro i
    rcases hd i with h | h <;> simp [h]
  · intro i j
    have h := congrArg (fun z : ℤ ↦ (z : ℝ)) (he i j)
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_ite,
      Int.cast_zero, Int.cast_one] at h
    by_cases hij : i = j
    · subst j
      simp [seidelMatrix, Matrix.of_apply, Matrix.sub_apply,
        Matrix.smul_apply, adjMatrix_apply]
    · simpa [seidelMatrix, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, adjMatrix_apply, e.injective.eq_iff, hij] using h

end SimpleGraph
