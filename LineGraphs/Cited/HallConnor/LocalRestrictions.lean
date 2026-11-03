/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.Connor
import LineGraphs.Computations.C19

/-!
# The claw and five-block restrictions

The local restrictions `hc:lem:claw` and `hc:lem:five` of the Hall–Connor blueprint,
used in Remark 5.12 and Example 5.13 of [CGSS]. Distinct labels are bundled as embeddings.
-/

open scoped Matrix

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable (D : Design P B 15 5 21 7 2)

/-- No four distinct labels induce a claw, `hc:lem:claw`
([CGSS], Remark 5.12 and Example 5.13). Index zero is the centre. -/
theorem Z_clawFree (e : Fin 4 ↪ B)
    (h01 : D.Z.Adj (e 0) (e 1)) (h02 : D.Z.Adj (e 0) (e 2))
    (h03 : D.Z.Adj (e 0) (e 3))
    (h12 : ¬ D.Z.Adj (e 1) (e 2)) (h13 : ¬ D.Z.Adj (e 1) (e 3))
    (h23 : ¬ D.Z.Adj (e 2) (e 3)) : False := by
  have h10 := h01.symm
  have h20 := h02.symm
  have h30 := h03.symm
  have h21 : ¬ D.Z.Adj (e 2) (e 1) := fun h ↦ h12 h.symm
  have h31 : ¬ D.Z.Adj (e 3) (e 1) := fun h ↦ h13 h.symm
  have h32 : ¬ D.Z.Adj (e 3) (e 2) := fun h ↦ h23 h.symm
  have hmatrix : D.C.submatrix e e =
      Computations.C19.clawMatrix.map (Int.castRingHom ℚ) := by
    ext i j
    simp only [Matrix.submatrix_apply, D.C_apply, e.injective.eq_iff]
    fin_cases i <;> fin_cases j <;>
      norm_num [Computations.C19.clawMatrix, Computations.toMatrix, Computations.entry,
        h01, h02, h03, h10, h20, h30, h12, h13, h23, h21, h31, h32] <;> assumption
  have hn := D.C_submatrix_quadratic_nonneg e ![-1, 1, 1, 1]
  rw [hmatrix] at hn
  norm_num [Computations.C19.clawMatrix, Computations.toMatrix, Computations.entry,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hn

/-- The five-block restriction, `hc:lem:five` (Hall–Connor Lemma 4.5 at `k = 5`;
[CGSS], Remark 5.12). Indices `0,1,2` form the triangle, with `Y = e 3` and `W = e 4`. -/
theorem not_adj_of_five_block_pattern (e : Fin 5 ↪ B)
    (h01 : D.Z.Adj (e 0) (e 1)) (h02 : D.Z.Adj (e 0) (e 2))
    (h12 : D.Z.Adj (e 1) (e 2)) (h30 : D.Z.Adj (e 3) (e 0))
    (h31 : ¬ D.Z.Adj (e 3) (e 1)) (h32 : ¬ D.Z.Adj (e 3) (e 2))
    (h41 : D.Z.Adj (e 4) (e 1)) (h42 : D.Z.Adj (e 4) (e 2))
    (h40 : ¬ D.Z.Adj (e 4) (e 0)) : ¬ D.Z.Adj (e 3) (e 4) := by
  intro h34
  have h10 := h01.symm
  have h20 := h02.symm
  have h21 := h12.symm
  have h03 := h30.symm
  have h14 := h41.symm
  have h24 := h42.symm
  have h43 := h34.symm
  have h13 : ¬ D.Z.Adj (e 1) (e 3) := fun h ↦ h31 h.symm
  have h23 : ¬ D.Z.Adj (e 2) (e 3) := fun h ↦ h32 h.symm
  have h04 : ¬ D.Z.Adj (e 0) (e 4) := fun h ↦ h40 h.symm
  have hmatrix : D.C.submatrix e e =
      Computations.C19.fiveBlockMatrix.map (Int.castRingHom ℚ) := by
    ext i j
    simp only [Matrix.submatrix_apply, D.C_apply, e.injective.eq_iff]
    fin_cases i <;> fin_cases j <;>
      norm_num [Computations.C19.fiveBlockMatrix, Computations.toMatrix, Computations.entry,
        h01, h02, h12, h30, h31, h32, h41, h42, h40, h34,
        h10, h20, h21, h03, h14, h24, h43, h13, h23, h04] <;> assumption
  have hn := D.C_submatrix_quadratic_nonneg e ![-1, 1, 1, 1, -1]
  rw [hmatrix] at hn
  norm_num [Computations.C19.fiveBlockMatrix, Computations.toMatrix, Computations.entry,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hn

end Design
