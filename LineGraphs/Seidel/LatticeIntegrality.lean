/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Integrality
import LineGraphs.Computations.C21

/-! # The two integrality exclusions in Remark 4.14

Steps `s414mint` and `s414mexcl` of `rem:414-proof`.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

/-- The five allowed products are integers, as used in step `s414mbasis` of Remark 4.14. -/
theorem inner_mem_int {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : LineSystem E) {y z : E} (hy : y ∈ S.Φ) (hz : z ∈ S.Φ) :
    ⟪y, z⟫ ∈ Set.range (Int.cast : ℤ → ℝ) := by
  have h := S.inner_mem y hy z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h <;> rw [h]
  · exact ⟨-2, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨2, by norm_num⟩

end LineSystem

namespace SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

/-- Step `s414mint` of Remark 4.14: transport the apex to a model's simple-root basis
and apply `lem:414-dual`. -/
theorem IsRepresentation.det_gram_mul_apex_mem_int (hx : X.IsRepresentation x) {k : ℕ}
    (hr : X.IsRegularOfDegree k) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {S : LineSystem F} (e : hx.latticeRoots.Iso S) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (span ℝ S.Φ)) (hb : ∀ i, (b i : F) ∈ S.Φ) :
    (Matrix.gram ℝ b).det * (Fintype.card V / ((k : ℝ) + 2)) ∈
      Set.range (Int.cast : ℤ → ℝ) := by
  let w : span ℝ hx.latticeRoots.Φ :=
    ⟨hx.apex k, by rw [hx.span_latticeRoots]; exact hx.apex_mem_span k⟩
  have h := InnerProductSpace.det_gram_mul_inner_self_mem_int b (e.spanIsometry w)
    (fun i j ↦ S.inner_mem_int (hb i) (hb j)) (fun i ↦ ?_)
  · have hn : ⟪e.spanIsometry w, e.spanIsometry w⟫ =
        Fintype.card V / ((k : ℝ) + 2) := by
      rw [e.spanIsometry.inner_map_map]
      exact hx.inner_apex_self hr
    rwa [hn] at h
  have hi : (e.spanIsometry.symm (b i) : E) ∈ hx.latticeRoots.Φ :=
    (e.spanIsometry_mem_iff _).mp (by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hb i)
  have he : ⟪e.spanIsometry w, b i⟫ = ⟪hx.apex k, (e.spanIsometry.symm (b i) : E)⟫ := by
    calc
      _ = ⟪e.spanIsometry w, e.spanIsometry (e.spanIsometry.symm (b i))⟫ := by
        rw [e.spanIsometry.apply_symm_apply]
      _ = _ := e.spanIsometry.inner_map_map w _
  rw [he]
  exact hx.inner_apex_mem_int hr hi.1

/-- C21's determinant 3 gives the `E₆` integrality condition in step `s414mint`. -/
theorem IsRepresentation.three_mul_apex_mem_int_of_E₆ (hx : X.IsRepresentation x) {k : ℕ}
    (hr : X.IsRegularOfDegree k) (e : hx.latticeRoots.Iso LineSystem.E₆) :
    3 * (Fintype.card V / ((k : ℝ) + 2)) ∈ Set.range (Int.cast : ℤ → ℝ) := by
  have h := hx.det_gram_mul_apex_mem_int hr e LineSystem.E₆.simpleBasis
    (fun i ↦ by simpa only [LineSystem.E₆.simpleBasis_apply] using LineSystem.E₆.simpleRoot_mem i)
  have hg : Matrix.gram ℝ LineSystem.E₆.simpleBasis = Matrix.gram ℝ LineSystem.E₆.simpleRoot := by
    ext i j
    change ⟪(LineSystem.E₆.simpleBasis i : EuclideanSpace ℝ (Fin 8)),
      (LineSystem.E₆.simpleBasis j : EuclideanSpace ℝ (Fin 8))⟫ = _
    simp only [LineSystem.E₆.simpleBasis_apply, Matrix.gram_apply]
  rwa [hg, LineSystem.E₆.det_gram_simpleRoot] at h

/-- C21's determinant 2 gives the `E₇` integrality condition in step `s414mint`. -/
theorem IsRepresentation.two_mul_apex_mem_int_of_E₇ (hx : X.IsRepresentation x) {k : ℕ}
    (hr : X.IsRegularOfDegree k) (e : hx.latticeRoots.Iso LineSystem.E₇) :
    2 * (Fintype.card V / ((k : ℝ) + 2)) ∈ Set.range (Int.cast : ℤ → ℝ) := by
  have h := hx.det_gram_mul_apex_mem_int hr e LineSystem.E₇.simpleBasis
    (fun i ↦ by simpa only [LineSystem.E₇.simpleBasis_apply] using LineSystem.E₇.simpleRoot_mem i)
  have hg : Matrix.gram ℝ LineSystem.E₇.simpleBasis = Matrix.gram ℝ LineSystem.E₇.simpleRoot := by
    ext i j
    change ⟪(LineSystem.E₇.simpleBasis i : EuclideanSpace ℝ (Fin 8)),
      (LineSystem.E₇.simpleBasis j : EuclideanSpace ℝ (Fin 8))⟫ = _
    simp only [LineSystem.E₇.simpleBasis_apply, Matrix.gram_apply]
  rwa [hg, LineSystem.E₇.det_gram_simpleRoot] at h

end SimpleGraph
