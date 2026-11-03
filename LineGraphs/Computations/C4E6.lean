/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4E6Data
import LineGraphs.Computations.StarCertificates
import LineGraphs.Computations.E8

/-!
# C4 E₆ marked-star verification

Computation C4 for E₆: connectivity and the specified ordered star. -/

open Computations C4
open scoped RealInnerProductSpace

namespace LineSystem

/-- The sorted finite presentation used for this model's certificates. -/
@[reducible] noncomputable def E₆.tableModel : IntegerModel E₆ :=
  E₆.integerModel.ofTable E₆.rootList 72
    (by decide +kernel) (by decide +kernel) E₆.mem_rootList

/-- C4: the spanning tree in the Sage certificate proves indecomposability. -/
theorem isIndecomposable_E₆ : E₆.IsIndecomposable := by
  apply E₆.tableModel.isIndecomposable_of_parent (71 : Fin 72)
    (fun i => ⟨e6Parents[i.val]?.getD 0 % 72, Nat.mod_lt _ (by decide)⟩)
    (fun i => e6Depths[i.val]?.getD 0)
  · change ∀ i : Fin 72, i ≠ 71 →
      e6Depths[e6Parents[i.val]?.getD 0 % 72]?.getD 0 < e6Depths[i.val]?.getD 0
    decide +kernel
  · change ∀ i : Fin 72, i ≠ 71 →
      integerInner (E₆.tableModel.v i)
        (E₆.tableModel.v ⟨e6Parents[i.val]?.getD 0 % 72, Nat.mod_lt _ (by decide)⟩) ≠ 0
    decide +kernel

/-- The ordered star `(e₀+e₁, -e₀+e₂, -e₁-e₂)` in the normalized model. -/
noncomputable def E₆.hyp24 : Hyp24 (EuclideanSpace ℝ (Fin 8)) :=
  E₆.tableModel.hyp24 isIndecomposable_E₆ isStarClosed_E₆
    (71 : Fin 72) (6 : Fin 72) (by decide +kernel)

/-- Identification of the first marked root in standard coordinates. -/
theorem E₆.hyp24_a : E₆.hyp24.a =
    EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 1 := by
  change integerVector (1 / 2) (E₆.tableModel.v (71 : Fin 72)) = _
  have hv : E₆.tableModel.v (71 : Fin 72) = ![2, 2, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

/-- Identification of the second marked root in standard coordinates. -/
theorem E₆.hyp24_b : E₆.hyp24.b =
    -EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 2 1 := by
  change integerVector (1 / 2) (E₆.tableModel.v (6 : Fin 72)) = _
  have hv : E₆.tableModel.v (6 : Fin 72) = ![-2, 0, 2, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

/-- Identification of the third marked root in standard coordinates. -/
theorem E₆.hyp24_c : E₆.hyp24.c =
    -EuclideanSpace.single 1 (1 : ℝ) - EuclideanSpace.single 2 1 := by
  rw [Hyp24.c, E₆.hyp24_a, E₆.hyp24_b]
  module

/-- Indices of the Γa roots, in the Sage certificate order. -/
def E₆.gammaLabel (i : Fin 9) : Fin 72 :=
  ⟨e6Gamma[i.val]?.getD 0 % 72, Nat.mod_lt _ (by decide)⟩

/-- The labels enumerate exactly the actual set `E₆.hyp24.Γa`. -/
noncomputable def E₆.gammaEquiv : Fin 9 ≃ E₆.hyp24.Γa :=
  E₆.tableModel.subsetEquiv _ E₆.hyp24.Γa_subset_Φ E₆.gammaLabel
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      unfold E₆.hyp24
      rw [E₆.tableModel.mem_Γa_iff]
      exact (by decide +kernel : ∀ i : Fin 72,
        integerInner (E₆.tableModel.v i) (E₆.tableModel.v (71 : Fin 72)) = 0 ∧
        integerInner (E₆.tableModel.v i) (E₆.tableModel.v (6 : Fin 72)) = 4 ↔
          ∃ j, E₆.gammaLabel j = i) i)

/-- Indices of the Δ roots, in the Sage certificate order. -/
def E₆.deltaLabel (i : Fin 12) : Fin 72 :=
  ⟨e6Delta[i.val]?.getD 0 % 72, Nat.mod_lt _ (by decide)⟩

/-- The labels enumerate exactly the actual set `E₆.hyp24.Δ`. -/
noncomputable def E₆.deltaEquiv : Fin 12 ≃ E₆.hyp24.Δ :=
  E₆.tableModel.subsetEquiv _ E₆.hyp24.Δ_subset_Φ E₆.deltaLabel
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      unfold E₆.hyp24
      rw [E₆.tableModel.mem_Δ_iff]
      exact (by decide +kernel : ∀ i : Fin 72,
        integerInner (E₆.tableModel.v i) (E₆.tableModel.v (71 : Fin 72)) = 0 ∧
        integerInner (E₆.tableModel.v i) (E₆.tableModel.v (6 : Fin 72)) = 0 ↔
          ∃ j, E₆.deltaLabel j = i) i)

/-- C4: the graph on Γa has the Sage adjacency table. -/
noncomputable def E₆.orthGraphIso :
    graphOfMatrix (by decide +kernel : checkAdjacency 9 e6Adjacency = true) ≃g
      E₆.hyp24.orthGraph :=
  graphOfMatrixIso _ _ E₆.gammaEquiv fun i j => by
    change (⟪integerVector E₆.tableModel.c
      (E₆.tableModel.v (E₆.gammaLabel i)),
      integerVector E₆.tableModel.c (E₆.tableModel.v (E₆.gammaLabel j))⟫ = 0) ↔ _
    rw [E₆.tableModel.inner_eq_zero_iff]
    exact (by decide +kernel : ∀ i j : Fin 9,
      integerInner (E₆.tableModel.v (E₆.gammaLabel i))
        (E₆.tableModel.v (E₆.gammaLabel j)) = 0 ↔ entry e6Adjacency i j = 1) i j

/-- C4: the orthogonality graph on the specified Γa is strongly regular. -/
theorem E₆.orthGraph_isSRGWith : E₆.hyp24.orthGraph.IsSRGWith 9 4 1 2 :=
  E₆.orthGraphIso.isSRGWith (checkSRG_sound _ (by decide +kernel))

/-- C4: the number of vertices in the specified Γa. -/
theorem E₆.card_Γa : E₆.hyp24.Γa.ncard = 9 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr E₆.gammaEquiv, Nat.card_eq_fintype_card]
  exact Fintype.card_fin 9

/-- C4: the number of roots in the specified Δ, with both signs. -/
theorem E₆.card_Δ : E₆.hyp24.Δ.ncard = 12 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr E₆.deltaEquiv, Nat.card_eq_fintype_card]
  exact Fintype.card_fin 12

/-- C4: Δ contains both signs, so it carries 6 lines. -/
theorem E₆.card_Δ_div_two : E₆.hyp24.Δ.ncard / 2 = 6 := by
  rw [E₆.card_Δ]

end LineSystem
