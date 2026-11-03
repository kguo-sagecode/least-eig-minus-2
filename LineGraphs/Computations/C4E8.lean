/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4E8Data
import LineGraphs.Computations.StarCertificates
import LineGraphs.Computations.E8

/-!
# C4 E₈ marked-star verification

Computation C4 for E₈: connectivity and the specified ordered star. -/

open Computations C4
open scoped RealInnerProductSpace

namespace LineSystem

/-- The sorted finite presentation used for this model's certificates. -/
@[reducible] noncomputable def E₈.tableModel : IntegerModel E₈ :=
  E₈viaD₈.integerModel.ofTable E₈viaD₈.rootList 240
    (by decide +kernel) (by decide +kernel) E₈viaD₈.mem_rootList

/-- C4: the spanning tree in the Sage certificate proves indecomposability. -/
theorem isIndecomposable_E₈ : E₈.IsIndecomposable := by
  apply E₈.tableModel.isIndecomposable_of_parent (239 : Fin 240)
    (fun i => ⟨e8Parents[i.val]?.getD 0 % 240, Nat.mod_lt _ (by decide)⟩)
    (fun i => e8Depths[i.val]?.getD 0)
  · change ∀ i : Fin 240, i ≠ 239 →
      e8Depths[e8Parents[i.val]?.getD 0 % 240]?.getD 0 < e8Depths[i.val]?.getD 0
    decide +kernel
  · change ∀ i : Fin 240, i ≠ 239 →
      integerInner (E₈.tableModel.v i)
        (E₈.tableModel.v ⟨e8Parents[i.val]?.getD 0 % 240, Nat.mod_lt _ (by decide)⟩) ≠ 0
    decide +kernel

/-- The ordered star `(e₀+e₁, -e₀+e₂, -e₁-e₂)` in the normalized model. -/
noncomputable def E₈.hyp24 : Hyp24 (EuclideanSpace ℝ (Fin 8)) :=
  E₈.tableModel.hyp24 isIndecomposable_E₈ isStarClosed_E₈
    (239 : Fin 240) (12 : Fin 240) (by decide +kernel)

/-- Identification of the first marked root in standard coordinates. -/
theorem E₈.hyp24_a : E₈.hyp24.a =
    EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 1 := by
  change integerVector (1 / 2) (E₈.tableModel.v (239 : Fin 240)) = _
  have hv : E₈.tableModel.v (239 : Fin 240) = ![2, 2, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

/-- Identification of the second marked root in standard coordinates. -/
theorem E₈.hyp24_b : E₈.hyp24.b =
    -EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 2 1 := by
  change integerVector (1 / 2) (E₈.tableModel.v (12 : Fin 240)) = _
  have hv : E₈.tableModel.v (12 : Fin 240) = ![-2, 0, 2, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

/-- Identification of the third marked root in standard coordinates. -/
theorem E₈.hyp24_c : E₈.hyp24.c =
    -EuclideanSpace.single 1 (1 : ℝ) - EuclideanSpace.single 2 1 := by
  rw [Hyp24.c, E₈.hyp24_a, E₈.hyp24_b]
  module

/-- Indices of the Γa roots, in the Sage certificate order. -/
def E₈.gammaLabel (i : Fin 27) : Fin 240 :=
  ⟨e8Gamma[i.val]?.getD 0 % 240, Nat.mod_lt _ (by decide)⟩

/-- The labels enumerate exactly the actual set `E₈.hyp24.Γa`. -/
noncomputable def E₈.gammaEquiv : Fin 27 ≃ E₈.hyp24.Γa :=
  E₈.tableModel.subsetEquiv _ E₈.hyp24.Γa_subset_Φ E₈.gammaLabel
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      unfold E₈.hyp24
      rw [E₈.tableModel.mem_Γa_iff]
      exact (by decide +kernel : ∀ i : Fin 240,
        integerInner (E₈.tableModel.v i) (E₈.tableModel.v (239 : Fin 240)) = 0 ∧
        integerInner (E₈.tableModel.v i) (E₈.tableModel.v (12 : Fin 240)) = 4 ↔
          ∃ j, E₈.gammaLabel j = i) i)

/-- Indices of the Δ roots, in the Sage certificate order. -/
def E₈.deltaLabel (i : Fin 72) : Fin 240 :=
  ⟨e8Delta[i.val]?.getD 0 % 240, Nat.mod_lt _ (by decide)⟩

/-- The labels enumerate exactly the actual set `E₈.hyp24.Δ`. -/
noncomputable def E₈.deltaEquiv : Fin 72 ≃ E₈.hyp24.Δ :=
  E₈.tableModel.subsetEquiv _ E₈.hyp24.Δ_subset_Φ E₈.deltaLabel
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      unfold E₈.hyp24
      rw [E₈.tableModel.mem_Δ_iff]
      exact (by decide +kernel : ∀ i : Fin 240,
        integerInner (E₈.tableModel.v i) (E₈.tableModel.v (239 : Fin 240)) = 0 ∧
        integerInner (E₈.tableModel.v i) (E₈.tableModel.v (12 : Fin 240)) = 0 ↔
          ∃ j, E₈.deltaLabel j = i) i)

/-- C4: the graph on Γa has the Sage adjacency table. -/
noncomputable def E₈.orthGraphIso :
    graphOfMatrix (by decide +kernel : checkAdjacency 27 e8Adjacency = true) ≃g
      E₈.hyp24.orthGraph :=
  graphOfMatrixIso _ _ E₈.gammaEquiv fun i j => by
    change (⟪integerVector E₈.tableModel.c
      (E₈.tableModel.v (E₈.gammaLabel i)),
      integerVector E₈.tableModel.c (E₈.tableModel.v (E₈.gammaLabel j))⟫ = 0) ↔ _
    rw [E₈.tableModel.inner_eq_zero_iff]
    exact (by decide +kernel : ∀ i j : Fin 27,
      integerInner (E₈.tableModel.v (E₈.gammaLabel i))
        (E₈.tableModel.v (E₈.gammaLabel j)) = 0 ↔ entry e8Adjacency i j = 1) i j

/-- C4: the orthogonality graph on the specified Γa is strongly regular. -/
theorem E₈.orthGraph_isSRGWith : E₈.hyp24.orthGraph.IsSRGWith 27 10 1 5 :=
  E₈.orthGraphIso.isSRGWith (checkSRG_sound _ (by decide +kernel))

/-- C4: the number of vertices in the specified Γa. -/
theorem E₈.card_Γa : E₈.hyp24.Γa.ncard = 27 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr E₈.gammaEquiv, Nat.card_eq_fintype_card]
  exact Fintype.card_fin 27

/-- C4: the number of roots in the specified Δ, with both signs. -/
theorem E₈.card_Δ : E₈.hyp24.Δ.ncard = 72 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr E₈.deltaEquiv, Nat.card_eq_fintype_card]
  exact Fintype.card_fin 72

/-- C4: Δ contains both signs, so it carries 36 lines. -/
theorem E₈.card_Δ_div_two : E₈.hyp24.Δ.ncard / 2 = 36 := by
  rw [E₈.card_Δ]

end LineSystem
