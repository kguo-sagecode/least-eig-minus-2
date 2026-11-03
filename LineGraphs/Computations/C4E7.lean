/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4E7Data
import LineGraphs.Computations.StarCertificates
import LineGraphs.Computations.E8

/-!
# C4 E₇ marked-star verification

Computation C4 for E₇: connectivity and the specified ordered star. -/

open Computations C4
open scoped RealInnerProductSpace

namespace LineSystem

/-- The sorted finite presentation used for this model's certificates. -/
@[reducible] noncomputable def E₇.tableModel : IntegerModel E₇ :=
  E₇.integerModel.ofTable E₇.rootList 126
    (by decide +kernel) (by decide +kernel) E₇.mem_rootList

/-- C4: the spanning tree in the Sage certificate proves indecomposability. -/
theorem isIndecomposable_E₇ : E₇.IsIndecomposable := by
  apply E₇.tableModel.isIndecomposable_of_parent (125 : Fin 126)
    (fun i => ⟨e7Parents[i.val]?.getD 0 % 126, Nat.mod_lt _ (by decide)⟩)
    (fun i => e7Depths[i.val]?.getD 0)
  · change ∀ i : Fin 126, i ≠ 125 →
      e7Depths[e7Parents[i.val]?.getD 0 % 126]?.getD 0 < e7Depths[i.val]?.getD 0
    decide +kernel
  · change ∀ i : Fin 126, i ≠ 125 →
      integerInner (E₇.tableModel.v i)
        (E₇.tableModel.v ⟨e7Parents[i.val]?.getD 0 % 126, Nat.mod_lt _ (by decide)⟩) ≠ 0
    decide +kernel

/-- The ordered star `(e₀+e₁, -e₀+e₂, -e₁-e₂)` in the normalized model. -/
noncomputable def E₇.hyp24 : Hyp24 (EuclideanSpace ℝ (Fin 8)) :=
  E₇.tableModel.hyp24 isIndecomposable_E₇ isStarClosed_E₇
    (125 : Fin 126) (8 : Fin 126) (by decide +kernel)

/-- Identification of the first marked root in standard coordinates. -/
theorem E₇.hyp24_a : E₇.hyp24.a =
    EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 1 := by
  change integerVector (1 / 2) (E₇.tableModel.v (125 : Fin 126)) = _
  have hv : E₇.tableModel.v (125 : Fin 126) = ![2, 2, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

/-- Identification of the second marked root in standard coordinates. -/
theorem E₇.hyp24_b : E₇.hyp24.b =
    -EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 2 1 := by
  change integerVector (1 / 2) (E₇.tableModel.v (8 : Fin 126)) = _
  have hv : E₇.tableModel.v (8 : Fin 126) = ![-2, 0, 2, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

/-- Identification of the third marked root in standard coordinates. -/
theorem E₇.hyp24_c : E₇.hyp24.c =
    -EuclideanSpace.single 1 (1 : ℝ) - EuclideanSpace.single 2 1 := by
  rw [Hyp24.c, E₇.hyp24_a, E₇.hyp24_b]
  module

/-- Indices of the Γa roots, in the Sage certificate order. -/
def E₇.gammaLabel (i : Fin 15) : Fin 126 :=
  ⟨e7Gamma[i.val]?.getD 0 % 126, Nat.mod_lt _ (by decide)⟩

/-- The labels enumerate exactly the actual set `E₇.hyp24.Γa`. -/
noncomputable def E₇.gammaEquiv : Fin 15 ≃ E₇.hyp24.Γa :=
  E₇.tableModel.subsetEquiv _ E₇.hyp24.Γa_subset_Φ E₇.gammaLabel
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      unfold E₇.hyp24
      rw [E₇.tableModel.mem_Γa_iff]
      exact (by decide +kernel : ∀ i : Fin 126,
        integerInner (E₇.tableModel.v i) (E₇.tableModel.v (125 : Fin 126)) = 0 ∧
        integerInner (E₇.tableModel.v i) (E₇.tableModel.v (8 : Fin 126)) = 4 ↔
          ∃ j, E₇.gammaLabel j = i) i)

/-- Indices of the Δ roots, in the Sage certificate order. -/
def E₇.deltaLabel (i : Fin 30) : Fin 126 :=
  ⟨e7Delta[i.val]?.getD 0 % 126, Nat.mod_lt _ (by decide)⟩

/-- The labels enumerate exactly the actual set `E₇.hyp24.Δ`. -/
noncomputable def E₇.deltaEquiv : Fin 30 ≃ E₇.hyp24.Δ :=
  E₇.tableModel.subsetEquiv _ E₇.hyp24.Δ_subset_Φ E₇.deltaLabel
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      unfold E₇.hyp24
      rw [E₇.tableModel.mem_Δ_iff]
      exact (by decide +kernel : ∀ i : Fin 126,
        integerInner (E₇.tableModel.v i) (E₇.tableModel.v (125 : Fin 126)) = 0 ∧
        integerInner (E₇.tableModel.v i) (E₇.tableModel.v (8 : Fin 126)) = 0 ↔
          ∃ j, E₇.deltaLabel j = i) i)

/-- C4: the graph on Γa has the Sage adjacency table. -/
noncomputable def E₇.orthGraphIso :
    graphOfMatrix (by decide +kernel : checkAdjacency 15 e7Adjacency = true) ≃g
      E₇.hyp24.orthGraph :=
  graphOfMatrixIso _ _ E₇.gammaEquiv fun i j => by
    change (⟪integerVector E₇.tableModel.c
      (E₇.tableModel.v (E₇.gammaLabel i)),
      integerVector E₇.tableModel.c (E₇.tableModel.v (E₇.gammaLabel j))⟫ = 0) ↔ _
    rw [E₇.tableModel.inner_eq_zero_iff]
    exact (by decide +kernel : ∀ i j : Fin 15,
      integerInner (E₇.tableModel.v (E₇.gammaLabel i))
        (E₇.tableModel.v (E₇.gammaLabel j)) = 0 ↔ entry e7Adjacency i j = 1) i j

/-- C4: the orthogonality graph on the specified Γa is strongly regular. -/
theorem E₇.orthGraph_isSRGWith : E₇.hyp24.orthGraph.IsSRGWith 15 6 1 3 :=
  E₇.orthGraphIso.isSRGWith (checkSRG_sound _ (by decide +kernel))

/-- C4: the number of vertices in the specified Γa. -/
theorem E₇.card_Γa : E₇.hyp24.Γa.ncard = 15 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr E₇.gammaEquiv, Nat.card_eq_fintype_card]
  exact Fintype.card_fin 15

/-- C4: the number of roots in the specified Δ, with both signs. -/
theorem E₇.card_Δ : E₇.hyp24.Δ.ncard = 30 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr E₇.deltaEquiv, Nat.card_eq_fintype_card]
  exact Fintype.card_fin 30

/-- C4: Δ contains both signs, so it carries 15 lines. -/
theorem E₇.card_Δ_div_two : E₇.hyp24.Δ.ncard / 2 = 15 := by
  rw [E₇.card_Δ]

end LineSystem
