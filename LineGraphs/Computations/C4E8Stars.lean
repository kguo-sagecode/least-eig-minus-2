/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4E8
import LineGraphs.Computations.C4StarData
import LineGraphs.Computations.StarOrbits

/-!
# C4 for every ordered star of E₈

The reflections in the roots of E₈ act transitively on its ordered stars, by two checked
reflection trees (`Computations.C4.e8RootParents` and `e8StarParents`). Hence the rows of
computation C4 proved for the fixed star `E₈.hyp24` hold for every term `H : Hyp24` with
`H.S = E₈`: the orthogonality graph is strongly regular with parameters (27, 10, 1, 5),
`|Γa| = 27` and `|Δ| = 72`. The star `(e₁ - e₂, e₂ - e₃)` of the blueprint's C4 table is
`E₈.hyp24Simple`, at `Fin 8` indices 0, 1, 2.
-/

open Computations C4
open scoped RealInnerProductSpace

namespace LineSystem

/-- The tree over all roots of E₈, from the root `e₁ + e₂` (index 239). -/
theorem E₈.root_tree_checked : ∀ i : Fin 240, i ≠ (239 : Fin 240) →
    listNat e8RootDepths (listFin 240 e8RootParents i) < listNat e8RootDepths i ∧
    E₈.tableModel.q • E₈.tableModel.v i =
      E₈.tableModel.q • E₈.tableModel.v (listFin 240 e8RootParents i) -
      integerInner (E₈.tableModel.v (listFin 240 e8RootReflections i))
          (E₈.tableModel.v (listFin 240 e8RootParents i)) •
        E₈.tableModel.v (listFin 240 e8RootReflections i) := by
  decide +kernel

/-- The tree over the roots at product `-1` with `e₁ + e₂`, from `-e₁ + e₃` (index 12); each
reflecting root is orthogonal to `e₁ + e₂`. -/
theorem E₈.star_tree_checked : ∀ i : Fin 240,
    integerInner (E₈.tableModel.v i) (E₈.tableModel.v (239 : Fin 240)) = -E₈.tableModel.q →
    i ≠ (12 : Fin 240) →
    integerInner (E₈.tableModel.v (listFin 240 e8StarParents i)) (E₈.tableModel.v (239 : Fin 240)) =
      -E₈.tableModel.q ∧
    listNat e8StarDepths (listFin 240 e8StarParents i) < listNat e8StarDepths i ∧
    integerInner (E₈.tableModel.v (listFin 240 e8StarReflections i))
      (E₈.tableModel.v (239 : Fin 240)) = 0 ∧
    E₈.tableModel.q • E₈.tableModel.v i =
      E₈.tableModel.q • E₈.tableModel.v (listFin 240 e8StarParents i) -
      integerInner (E₈.tableModel.v (listFin 240 e8StarReflections i))
          (E₈.tableModel.v (listFin 240 e8StarParents i)) •
        E₈.tableModel.v (listFin 240 e8StarReflections i) := by
  decide +kernel

-- Computation C4
/-- C4: the isometries preserving E₈ act transitively on its ordered stars. -/
theorem E₈.exists_isometry_star {a b : EuclideanSpace ℝ (Fin 8)} (ha : a ∈ E₈.Φ)
    (hb : b ∈ E₈.Φ) (hab : ⟪a, b⟫ = -1) :
    ∃ g ∈ E₈.isometryGroup, g E₈.hyp24.a = a ∧ g E₈.hyp24.b = b :=
  E₈.tableModel.exists_isometry_of_star (239 : Fin 240) (12 : Fin 240)
    (fun i => by
      obtain ⟨g, hg, -, h⟩ := E₈.tableModel.exists_isometry_of_tree isStarClosed_E₈ 0
        (fun _ => True) (239 : Fin 240) (listFin 240 e8RootParents) (listFin 240 e8RootReflections)
        (listNat e8RootDepths)
        (fun i _ hi => ⟨trivial, (E₈.root_tree_checked i hi).1, inner_zero_right _,
          (E₈.root_tree_checked i hi).2⟩) i trivial
      exact ⟨g, hg, h⟩)
    (fun j hj => E₈.tableModel.exists_isometry_of_tree isStarClosed_E₈ _
      (fun i => integerInner (E₈.tableModel.v i) (E₈.tableModel.v (239 : Fin 240)) =
        -E₈.tableModel.q) (12 : Fin 240)
      (listFin 240 e8StarParents) (listFin 240 e8StarReflections) (listNat e8StarDepths)
      (fun i hi hne => by
        obtain ⟨h₁, h₂, h₃, h₄⟩ := E₈.star_tree_checked i hi hne
        exact ⟨h₁, h₂, (E₈.tableModel.inner_eq_zero_iff _ _).mpr h₃, h₄⟩) j hj)
    ha hb hab

namespace Hyp24

variable (H : Hyp24 (EuclideanSpace ℝ (Fin 8)))

/-- C4 for every ordered star of E₈: an isometry preserving `Φ` carries the fixed star
`E₈.hyp24` to the star of `H`. -/
theorem exists_isometry_of_S_eq_E₈ (hS : H.S = E₈) :
    ∃ g : EuclideanSpace ℝ (Fin 8) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 8),
      (∀ x, g x ∈ H.S.Φ ↔ x ∈ E₈.hyp24.S.Φ) ∧ g E₈.hyp24.a = H.a ∧ g E₈.hyp24.b = H.b :=
  exists_isometry_of_S_eq E₈.hyp24 H rfl hS (fun _ _ => E₈.exists_isometry_star)

-- Computation C4
/-- C4 for every ordered star of E₈: its orthogonality graph is that of `E₈.hyp24`. -/
theorem nonempty_orthGraph_iso_of_S_eq_E₈ (hS : H.S = E₈) :
    Nonempty (E₈.hyp24.orthGraph ≃g H.orthGraph) := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_E₈ hS
  exact ⟨orthGraphIsoOfIsometry _ _ g hΦ ha hb⟩

-- Computation C4
/-- C4 for every ordered star of E₈: the orthogonality graph is strongly regular with
parameters (27, 10, 1, 5). -/
theorem orthGraph_isSRGWith_of_S_eq_E₈ (hS : H.S = E₈) :
    H.orthGraph.IsSRGWith 27 10 1 5 := by
  obtain ⟨e⟩ := H.nonempty_orthGraph_iso_of_S_eq_E₈ hS
  exact e.isSRGWith E₈.orthGraph_isSRGWith

-- Computation C4
/-- C4 for every ordered star of E₈: `|Γa| = 27`. -/
theorem card_Γa_of_S_eq_E₈ (hS : H.S = E₈) : H.Γa.ncard = 27 := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_E₈ hS
  rw [ncard_Γa_eq_of_isometry _ _ g hΦ ha hb, E₈.card_Γa]

-- Computation C4
/-- C4 for every ordered star of E₈: `|Δ| = 72`, that is, 36 lines. -/
theorem card_Δ_of_S_eq_E₈ (hS : H.S = E₈) : H.Δ.ncard = 72 := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_E₈ hS
  rw [ncard_Δ_eq_of_isometry _ _ g hΦ ha hb, E₈.card_Δ]

end Hyp24

/-- The ordered star `(e₁ - e₂, e₂ - e₃)` of the blueprint's C4 table: in `Fin 8`,
`a = e₀ - e₁` and `b = e₁ - e₂` (indices 226 and 150 of the root table). -/
noncomputable def E₈.hyp24Simple : Hyp24 (EuclideanSpace ℝ (Fin 8)) :=
  E₈.tableModel.hyp24 isIndecomposable_E₈ isStarClosed_E₈
    (226 : Fin 240) (150 : Fin 240) (by decide +kernel)

theorem E₈.hyp24Simple_a : E₈.hyp24Simple.a =
    EuclideanSpace.single 0 (1 : ℝ) - EuclideanSpace.single 1 1 := by
  change integerVector (1 / 2) (E₈.tableModel.v (226 : Fin 240)) = _
  have hv : E₈.tableModel.v (226 : Fin 240) = ![2, -2, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

theorem E₈.hyp24Simple_b : E₈.hyp24Simple.b =
    EuclideanSpace.single 1 (1 : ℝ) - EuclideanSpace.single 2 1 := by
  change integerVector (1 / 2) (E₈.tableModel.v (150 : Fin 240)) = _
  have hv : E₈.tableModel.v (150 : Fin 240) = ![0, 2, -2, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

end LineSystem
