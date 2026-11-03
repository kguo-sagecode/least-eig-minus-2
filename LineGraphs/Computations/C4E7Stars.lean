/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4E7
import LineGraphs.Computations.C4StarData
import LineGraphs.Computations.StarOrbits

/-!
# C4 for every ordered star of E₇

The reflections in the roots of E₇ act transitively on its ordered stars, by two checked
reflection trees (`Computations.C4.e7RootParents` and `e7StarParents`). Hence the rows of
computation C4 proved for the fixed star `E₇.hyp24` hold for every term `H : Hyp24` with
`H.S = E₇`: the orthogonality graph is strongly regular with parameters (15, 6, 1, 3),
`|Γa| = 15` and `|Δ| = 30`. The star `(e₁ - e₂, e₂ - e₃)` of the blueprint's C4 table is
`E₇.hyp24Simple`, at `Fin 8` indices 0, 1, 2.
-/

open Computations C4
open scoped RealInnerProductSpace

namespace LineSystem

/-- The tree over all roots of E₇, from the root `e₁ + e₂` (index 125). -/
theorem E₇.root_tree_checked : ∀ i : Fin 126, i ≠ (125 : Fin 126) →
    listNat e7RootDepths (listFin 126 e7RootParents i) < listNat e7RootDepths i ∧
    E₇.tableModel.q • E₇.tableModel.v i =
      E₇.tableModel.q • E₇.tableModel.v (listFin 126 e7RootParents i) -
      integerInner (E₇.tableModel.v (listFin 126 e7RootReflections i))
          (E₇.tableModel.v (listFin 126 e7RootParents i)) •
        E₇.tableModel.v (listFin 126 e7RootReflections i) := by
  decide +kernel

/-- The tree over the roots at product `-1` with `e₁ + e₂`, from `-e₁ + e₃` (index 8); each
reflecting root is orthogonal to `e₁ + e₂`. -/
theorem E₇.star_tree_checked : ∀ i : Fin 126,
    integerInner (E₇.tableModel.v i) (E₇.tableModel.v (125 : Fin 126)) = -E₇.tableModel.q →
    i ≠ (8 : Fin 126) →
    integerInner (E₇.tableModel.v (listFin 126 e7StarParents i)) (E₇.tableModel.v (125 : Fin 126)) =
      -E₇.tableModel.q ∧
    listNat e7StarDepths (listFin 126 e7StarParents i) < listNat e7StarDepths i ∧
    integerInner (E₇.tableModel.v (listFin 126 e7StarReflections i))
      (E₇.tableModel.v (125 : Fin 126)) = 0 ∧
    E₇.tableModel.q • E₇.tableModel.v i =
      E₇.tableModel.q • E₇.tableModel.v (listFin 126 e7StarParents i) -
      integerInner (E₇.tableModel.v (listFin 126 e7StarReflections i))
          (E₇.tableModel.v (listFin 126 e7StarParents i)) •
        E₇.tableModel.v (listFin 126 e7StarReflections i) := by
  decide +kernel

-- Computation C4
/-- C4: the isometries preserving E₇ act transitively on its ordered stars. -/
theorem E₇.exists_isometry_star {a b : EuclideanSpace ℝ (Fin 8)} (ha : a ∈ E₇.Φ)
    (hb : b ∈ E₇.Φ) (hab : ⟪a, b⟫ = -1) :
    ∃ g ∈ E₇.isometryGroup, g E₇.hyp24.a = a ∧ g E₇.hyp24.b = b :=
  E₇.tableModel.exists_isometry_of_star (125 : Fin 126) (8 : Fin 126)
    (fun i => by
      obtain ⟨g, hg, -, h⟩ := E₇.tableModel.exists_isometry_of_tree isStarClosed_E₇ 0
        (fun _ => True) (125 : Fin 126) (listFin 126 e7RootParents) (listFin 126 e7RootReflections)
        (listNat e7RootDepths)
        (fun i _ hi => ⟨trivial, (E₇.root_tree_checked i hi).1, inner_zero_right _,
          (E₇.root_tree_checked i hi).2⟩) i trivial
      exact ⟨g, hg, h⟩)
    (fun j hj => E₇.tableModel.exists_isometry_of_tree isStarClosed_E₇ _
      (fun i => integerInner (E₇.tableModel.v i) (E₇.tableModel.v (125 : Fin 126)) =
        -E₇.tableModel.q) (8 : Fin 126)
      (listFin 126 e7StarParents) (listFin 126 e7StarReflections) (listNat e7StarDepths)
      (fun i hi hne => by
        obtain ⟨h₁, h₂, h₃, h₄⟩ := E₇.star_tree_checked i hi hne
        exact ⟨h₁, h₂, (E₇.tableModel.inner_eq_zero_iff _ _).mpr h₃, h₄⟩) j hj)
    ha hb hab

namespace Hyp24

variable (H : Hyp24 (EuclideanSpace ℝ (Fin 8)))

/-- C4 for every ordered star of E₇: an isometry preserving `Φ` carries the fixed star
`E₇.hyp24` to the star of `H`. -/
theorem exists_isometry_of_S_eq_E₇ (hS : H.S = E₇) :
    ∃ g : EuclideanSpace ℝ (Fin 8) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 8),
      (∀ x, g x ∈ H.S.Φ ↔ x ∈ E₇.hyp24.S.Φ) ∧ g E₇.hyp24.a = H.a ∧ g E₇.hyp24.b = H.b :=
  exists_isometry_of_S_eq E₇.hyp24 H rfl hS (fun _ _ => E₇.exists_isometry_star)

-- Computation C4
/-- C4 for every ordered star of E₇: its orthogonality graph is that of `E₇.hyp24`. -/
theorem nonempty_orthGraph_iso_of_S_eq_E₇ (hS : H.S = E₇) :
    Nonempty (E₇.hyp24.orthGraph ≃g H.orthGraph) := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_E₇ hS
  exact ⟨orthGraphIsoOfIsometry _ _ g hΦ ha hb⟩

-- Computation C4
/-- C4 for every ordered star of E₇: the orthogonality graph is strongly regular with
parameters (15, 6, 1, 3). -/
theorem orthGraph_isSRGWith_of_S_eq_E₇ (hS : H.S = E₇) :
    H.orthGraph.IsSRGWith 15 6 1 3 := by
  obtain ⟨e⟩ := H.nonempty_orthGraph_iso_of_S_eq_E₇ hS
  exact e.isSRGWith E₇.orthGraph_isSRGWith

-- Computation C4
/-- C4 for every ordered star of E₇: `|Γa| = 15`. -/
theorem card_Γa_of_S_eq_E₇ (hS : H.S = E₇) : H.Γa.ncard = 15 := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_E₇ hS
  rw [ncard_Γa_eq_of_isometry _ _ g hΦ ha hb, E₇.card_Γa]

-- Computation C4
/-- C4 for every ordered star of E₇: `|Δ| = 30`, that is, 15 lines. -/
theorem card_Δ_of_S_eq_E₇ (hS : H.S = E₇) : H.Δ.ncard = 30 := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_E₇ hS
  rw [ncard_Δ_eq_of_isometry _ _ g hΦ ha hb, E₇.card_Δ]

end Hyp24

/-- The ordered star `(e₁ - e₂, e₂ - e₃)` of the blueprint's C4 table: in `Fin 8`,
`a = e₀ - e₁` and `b = e₁ - e₂` (indices 116 and 76 of the root table). -/
noncomputable def E₇.hyp24Simple : Hyp24 (EuclideanSpace ℝ (Fin 8)) :=
  E₇.tableModel.hyp24 isIndecomposable_E₇ isStarClosed_E₇
    (116 : Fin 126) (76 : Fin 126) (by decide +kernel)

theorem E₇.hyp24Simple_a : E₇.hyp24Simple.a =
    EuclideanSpace.single 0 (1 : ℝ) - EuclideanSpace.single 1 1 := by
  change integerVector (1 / 2) (E₇.tableModel.v (116 : Fin 126)) = _
  have hv : E₇.tableModel.v (116 : Fin 126) = ![2, -2, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

theorem E₇.hyp24Simple_b : E₇.hyp24Simple.b =
    EuclideanSpace.single 1 (1 : ℝ) - EuclideanSpace.single 2 1 := by
  change integerVector (1 / 2) (E₇.tableModel.v (76 : Fin 126)) = _
  have hv : E₇.tableModel.v (76 : Fin 126) = ![0, 2, -2, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

end LineSystem
