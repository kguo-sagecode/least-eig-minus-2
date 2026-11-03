/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4E6
import LineGraphs.Computations.C4StarData
import LineGraphs.Computations.StarOrbits

/-!
# C4 for every ordered star of E₆

The reflections in the roots of E₆ act transitively on its ordered stars, by two checked
reflection trees (`Computations.C4.e6RootParents` and `e6StarParents`). Hence the rows of
computation C4 proved for the fixed star `E₆.hyp24` hold for every term `H : Hyp24` with
`H.S = E₆`: the orthogonality graph is strongly regular with parameters (9, 4, 1, 2),
`|Γa| = 9` and `|Δ| = 12`. The star `(e₁ - e₂, e₂ - e₃)` of the blueprint's C4 table is
`E₆.hyp24Simple`, at `Fin 8` indices 0, 1, 2.
-/

open Computations C4
open scoped RealInnerProductSpace

namespace LineSystem

/-- The tree over all roots of E₆, from the root `e₁ + e₂` (index 71). -/
theorem E₆.root_tree_checked : ∀ i : Fin 72, i ≠ (71 : Fin 72) →
    listNat e6RootDepths (listFin 72 e6RootParents i) < listNat e6RootDepths i ∧
    E₆.tableModel.q • E₆.tableModel.v i =
      E₆.tableModel.q • E₆.tableModel.v (listFin 72 e6RootParents i) -
      integerInner (E₆.tableModel.v (listFin 72 e6RootReflections i))
          (E₆.tableModel.v (listFin 72 e6RootParents i)) •
        E₆.tableModel.v (listFin 72 e6RootReflections i) := by
  decide +kernel

/-- The tree over the roots at product `-1` with `e₁ + e₂`, from `-e₁ + e₃` (index 6); each
reflecting root is orthogonal to `e₁ + e₂`. -/
theorem E₆.star_tree_checked : ∀ i : Fin 72,
    integerInner (E₆.tableModel.v i) (E₆.tableModel.v (71 : Fin 72)) = -E₆.tableModel.q →
    i ≠ (6 : Fin 72) →
    integerInner (E₆.tableModel.v (listFin 72 e6StarParents i)) (E₆.tableModel.v (71 : Fin 72)) =
      -E₆.tableModel.q ∧
    listNat e6StarDepths (listFin 72 e6StarParents i) < listNat e6StarDepths i ∧
    integerInner (E₆.tableModel.v (listFin 72 e6StarReflections i))
      (E₆.tableModel.v (71 : Fin 72)) = 0 ∧
    E₆.tableModel.q • E₆.tableModel.v i =
      E₆.tableModel.q • E₆.tableModel.v (listFin 72 e6StarParents i) -
      integerInner (E₆.tableModel.v (listFin 72 e6StarReflections i))
          (E₆.tableModel.v (listFin 72 e6StarParents i)) •
        E₆.tableModel.v (listFin 72 e6StarReflections i) := by
  decide +kernel

-- Computation C4
/-- C4: the isometries preserving E₆ act transitively on its ordered stars. -/
theorem E₆.exists_isometry_star {a b : EuclideanSpace ℝ (Fin 8)} (ha : a ∈ E₆.Φ)
    (hb : b ∈ E₆.Φ) (hab : ⟪a, b⟫ = -1) :
    ∃ g ∈ E₆.isometryGroup, g E₆.hyp24.a = a ∧ g E₆.hyp24.b = b :=
  E₆.tableModel.exists_isometry_of_star (71 : Fin 72) (6 : Fin 72)
    (fun i => by
      obtain ⟨g, hg, -, h⟩ := E₆.tableModel.exists_isometry_of_tree isStarClosed_E₆ 0
        (fun _ => True) (71 : Fin 72) (listFin 72 e6RootParents) (listFin 72 e6RootReflections)
        (listNat e6RootDepths)
        (fun i _ hi => ⟨trivial, (E₆.root_tree_checked i hi).1, inner_zero_right _,
          (E₆.root_tree_checked i hi).2⟩) i trivial
      exact ⟨g, hg, h⟩)
    (fun j hj => E₆.tableModel.exists_isometry_of_tree isStarClosed_E₆ _
      (fun i => integerInner (E₆.tableModel.v i) (E₆.tableModel.v (71 : Fin 72)) =
        -E₆.tableModel.q) (6 : Fin 72)
      (listFin 72 e6StarParents) (listFin 72 e6StarReflections) (listNat e6StarDepths)
      (fun i hi hne => by
        obtain ⟨h₁, h₂, h₃, h₄⟩ := E₆.star_tree_checked i hi hne
        exact ⟨h₁, h₂, (E₆.tableModel.inner_eq_zero_iff _ _).mpr h₃, h₄⟩) j hj)
    ha hb hab

namespace Hyp24

variable (H : Hyp24 (EuclideanSpace ℝ (Fin 8)))

/-- C4 for every ordered star of E₆: an isometry preserving `Φ` carries the fixed star
`E₆.hyp24` to the star of `H`. -/
theorem exists_isometry_of_S_eq_E₆ (hS : H.S = E₆) :
    ∃ g : EuclideanSpace ℝ (Fin 8) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 8),
      (∀ x, g x ∈ H.S.Φ ↔ x ∈ E₆.hyp24.S.Φ) ∧ g E₆.hyp24.a = H.a ∧ g E₆.hyp24.b = H.b :=
  exists_isometry_of_S_eq E₆.hyp24 H rfl hS (fun _ _ => E₆.exists_isometry_star)

-- Computation C4
/-- C4 for every ordered star of E₆: its orthogonality graph is that of `E₆.hyp24`. -/
theorem nonempty_orthGraph_iso_of_S_eq_E₆ (hS : H.S = E₆) :
    Nonempty (E₆.hyp24.orthGraph ≃g H.orthGraph) := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_E₆ hS
  exact ⟨orthGraphIsoOfIsometry _ _ g hΦ ha hb⟩

-- Computation C4
/-- C4 for every ordered star of E₆: the orthogonality graph is strongly regular with
parameters (9, 4, 1, 2). -/
theorem orthGraph_isSRGWith_of_S_eq_E₆ (hS : H.S = E₆) :
    H.orthGraph.IsSRGWith 9 4 1 2 := by
  obtain ⟨e⟩ := H.nonempty_orthGraph_iso_of_S_eq_E₆ hS
  exact e.isSRGWith E₆.orthGraph_isSRGWith

-- Computation C4
/-- C4 for every ordered star of E₆: `|Γa| = 9`. -/
theorem card_Γa_of_S_eq_E₆ (hS : H.S = E₆) : H.Γa.ncard = 9 := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_E₆ hS
  rw [ncard_Γa_eq_of_isometry _ _ g hΦ ha hb, E₆.card_Γa]

-- Computation C4
/-- C4 for every ordered star of E₆: `|Δ| = 12`, that is, 6 lines. -/
theorem card_Δ_of_S_eq_E₆ (hS : H.S = E₆) : H.Δ.ncard = 12 := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_E₆ hS
  rw [ncard_Δ_eq_of_isometry _ _ g hΦ ha hb, E₆.card_Δ]

end Hyp24

/-- The ordered star `(e₁ - e₂, e₂ - e₃)` of the blueprint's C4 table: in `Fin 8`,
`a = e₀ - e₁` and `b = e₁ - e₂` (indices 64 and 42 of the root table). -/
noncomputable def E₆.hyp24Simple : Hyp24 (EuclideanSpace ℝ (Fin 8)) :=
  E₆.tableModel.hyp24 isIndecomposable_E₆ isStarClosed_E₆
    (64 : Fin 72) (42 : Fin 72) (by decide +kernel)

theorem E₆.hyp24Simple_a : E₆.hyp24Simple.a =
    EuclideanSpace.single 0 (1 : ℝ) - EuclideanSpace.single 1 1 := by
  change integerVector (1 / 2) (E₆.tableModel.v (64 : Fin 72)) = _
  have hv : E₆.tableModel.v (64 : Fin 72) = ![2, -2, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

theorem E₆.hyp24Simple_b : E₆.hyp24Simple.b =
    EuclideanSpace.single 1 (1 : ℝ) - EuclideanSpace.single 2 1 := by
  change integerVector (1 / 2) (E₆.tableModel.v (42 : Fin 72)) = _
  have hv : E₆.tableModel.v (42 : Fin 72) = ![0, 2, -2, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

end LineSystem
