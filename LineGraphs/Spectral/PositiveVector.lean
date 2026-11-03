/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Positive vectors bound the largest eigenvalue

A maximum coordinate ratio proves the bound directly, without a connectivity assumption.
-/

namespace Matrix

open WithLp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
/-- A positive supervector bounds every real eigenvalue of a nonnegative matrix. -/
theorem eigenvalue_le_of_pos_supervector {A : Matrix ι ι ℝ} {x y : ι → ℝ} {b θ : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ i, 0 < x i)
    (hAx : ∀ i, (A *ᵥ x) i ≤ b * x i) (hy : y ≠ 0) (hAy : A *ᵥ y = θ • y) : θ ≤ b := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => |y i| / x i)
  let r := |y i| / x i
  have hmax (j : ι) : |y j| / x j ≤ r :=
    (Finset.le_sup' (fun i => |y i| / x i) (Finset.mem_univ j)).trans_eq hi
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  have hr : 0 < r := lt_of_lt_of_le (div_pos (abs_pos.mpr hj) (hx j)) (hmax j)
  have hri : r * x i = |y i| := div_mul_cancel₀ _ (ne_of_gt (hx i))
  have hyi : 0 < |y i| := hri ▸ mul_pos hr (hx i)
  have hbound (j : ι) : |y j| ≤ r * x j := (div_le_iff₀ (hx j)).mp (hmax j)
  have hle : θ * |y i| ≤ b * |y i| := calc
    θ * |y i| ≤ |θ| * |y i| :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
    _ = |(A *ᵥ y) i| := by rw [hAy, Pi.smul_apply, smul_eq_mul, abs_mul]
    _ ≤ ∑ j, |A i j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, A i j * |y j| := by simp_rw [abs_mul, abs_of_nonneg (hA i _)]
    _ ≤ ∑ j, A i j * (r * x j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbound j) (hA i j)
    _ = r * (A *ᵥ x) i := by
      simp only [mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ r * (b * x i) := mul_le_mul_of_nonneg_left (hAx i) hr.le
    _ = b * |y i| := by rw [← hri]; ring
  exact (mul_le_mul_iff_left₀ hyi).mp hle

/-- The spectral toolkit's positive-supervector bound for symmetric nonnegative matrices. -/
theorem IsHermitian.largestEigenvalue_le_of_pos_supervector {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hpos : ∀ i j, 0 ≤ A i j) {x : ι → ℝ} {b : ℝ}
    (hx : ∀ i, 0 < x i) (hAx : ∀ i, (A *ᵥ x) i ≤ b * x i) :
    hA.largestEigenvalue ≤ b := by
  let i := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
    (⟨0, Fintype.card_pos⟩ : Fin (Fintype.card ι))
  have h := eigenvalue_le_of_pos_supervector hpos hx hAx
    ((ofLp_eq_zero 2).ne.mpr (hA.eigenvectorBasis.orthonormal.ne_zero i))
    (hA.mulVec_eigenvectorBasis i)
  simpa only [IsHermitian.eigenvalues, i, Equiv.symm_apply_apply,
    IsHermitian.largestEigenvalue] using h

/-- A strictly positive eigenvector identifies the largest eigenvalue, even when disconnected. -/
theorem IsHermitian.largestEigenvalue_eq_of_pos_eigenvector {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hpos : ∀ i j, 0 ≤ A i j) {x : ι → ℝ} {b : ℝ}
    (hx : ∀ i, 0 < x i) (hAx : A *ᵥ x = b • x) : hA.largestEigenvalue = b := by
  apply le_antisymm (hA.largestEigenvalue_le_of_pos_supervector hpos hx
    (fun i => (congrFun hAx i).le))
  have hn : x ≠ 0 := by
    intro h
    have := hx (Classical.arbitrary ι)
    simp [h] at this
  have hb : b ∈ spectrum ℝ A := by
    rw [← spectrum_toLin']
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      (show Module.End.HasEigenvector A.toLin' b x from
        ⟨Module.End.mem_eigenspace_iff.mpr hAx, hn⟩)).mem_spectrum
  obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hb
  exact hA.eigenvalues₀_antitone (Fin.zero_le _)

end Matrix
