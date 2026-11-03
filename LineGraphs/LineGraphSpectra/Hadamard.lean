/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.SmallDesigns
import LineGraphs.Computations.C12

/-!
# The Hadamard obstruction

Corollary 5.9 of [CGSS], steps `s559Y`–`s559H`. Computation C12 supplies the
bordering construction; the quadratic identity is derived here from the graph spectrum.
-/

open scoped BigOperators Matrix
open Matrix Polynomial

namespace Matrix

/-- The matrix-existence condition in `cor:5.9`, Corollary 5.9 of [CGSS]. -/
def HasSymmetricHadamardWithConstantDiagonal (n : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I) (H : Matrix I I ℝ),
    Fintype.card I = n ∧ H.IsSymm ∧ H.IsHadamard ∧ ∃ d : ℝ, ∀ i, H i i = d

end Matrix

namespace SimpleGraph

/-- Steps `s559Y`–`s559H`, Corollary 5.9 of [CGSS]: derive the quadratic adjacency
identity by the Hoffman polynomial and apply C12's symmetric Hadamard border. -/
theorem hasSymmetricHadamardWithConstantDiagonal_of_spectrum
    {W : Type} [Fintype W] [DecidableEq W] (Y : SimpleGraph W) [DecidableRel Y.Adj]
    (t : ℕ) (hc : Y.Connected) (hr : Y.IsRegularOfDegree (2 * t ^ 2))
    (hn : Fintype.card W + 1 = 4 * t ^ 2)
    (hs : ∀ μ ∈ Y.spectrumMultiset, μ ≠ ((2 * t ^ 2 : ℕ) : ℝ) → μ ^ 2 = (t : ℝ) ^ 2) :
    Matrix.HasSymmetricHadamardWithConstantDiagonal (4 * t ^ 2) := by
  classical
  have : Nonempty W := hc.nonempty
  have hnR : (Fintype.card W : ℝ) + 1 = 4 * (t : ℝ) ^ 2 := by exact_mod_cast hn
  have hn0 : (Fintype.card W : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let p : ℝ[X] := X ^ 2 - C ((t : ℝ) ^ 2)
  have hp := hr.aeval_eq_smul_allOnes_of_connected hc p (by
    intro μ hμ hne
    simp [p, hs μ hμ hne])
  have hv : p.eval ((2 * t ^ 2 : ℕ) : ℝ) / Fintype.card W = (t : ℝ) ^ 2 := by
    apply (div_eq_iff hn0).mpr
    simp only [p, eval_sub, eval_pow, eval_X, eval_C, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_pow]
    nlinarith
  rw [hv] at hp
  have hq : Y.adjMatrix ℝ * Y.adjMatrix ℝ =
      (t : ℝ) ^ 2 • (1 + of (fun _ _ ↦ (1 : ℝ))) := by
    have hh : (Y.adjMatrix ℝ) ^ 2 - (t : ℝ) ^ 2 • 1 =
        (t : ℝ) ^ 2 • of (fun _ _ ↦ (1 : ℝ)) := by
      dsimp only [p] at hp
      rw [map_sub, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at hp
      exact hp
    rw [smul_add, ← pow_two]
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  let e := (Fintype.equivFin W).symm
  let A := (Y.adjMatrix ℝ).submatrix e e
  have hAr (i : Fin (Fintype.card W)) : ∑ j, A i j = 2 * (t : ℝ) ^ 2 := by
    change ∑ j, Y.adjMatrix ℝ (e i) (e j) = _
    rw [e.sum_comp]
    have hh := Y.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hr (a := 1) (v := e i)
    simpa [Matrix.mulVec, dotProduct] using hh
  have hAq : A * A = (t : ℝ) ^ 2 • (1 + of (fun _ _ ↦ (1 : ℝ))) := by
    dsimp only [A]
    rw [Matrix.submatrix_mul_equiv, hq]
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff, mul_add]
  obtain ⟨hHsym, hHhad, hHdiag, hHcard⟩ := Computations.C12.hadamard_border A t hnR
    (by simp [A, Matrix.IsSymm, Matrix.transpose_submatrix])
    (fun i j ↦ by
      change (if Y.Adj (e i) (e j) then (1 : ℝ) else 0) = 0 ∨ _
      by_cases hij : Y.Adj (e i) (e j) <;> simp [A, SimpleGraph.adjMatrix, hij])
    (fun i ↦ by simp [A]) hAr hAq
  exact ⟨Option (Fin (Fintype.card W)), inferInstance, inferInstance,
    Computations.C12.border (Computations.C12.core A), by exact_mod_cast hHcard,
    hHsym, hHhad, -1, hHdiag⟩

end SimpleGraph
