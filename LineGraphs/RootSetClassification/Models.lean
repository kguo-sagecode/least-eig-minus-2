/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.ESystems
import LineGraphs.RootSetClassification.FSystem
import LineGraphs.RootSetClassification.GSystem
import LineGraphs.RootSetClassification.ConnectedBase
import LineGraphs.Cartan.Converse

/-!
# The canonical coordinate models are indecomposable

`lem:models-irreducible` in the blueprint for Remark 3.11 of [CGSS]. The family
is indexed by the canonical finite types of blueprint Theorem A. Its spaces, root sets,
and bases are exactly the coordinate constructions already checked separately.
-/

open scoped RealInnerProductSpace
open Submodule
open CartanMatrix

namespace RootSetModel

/-- The specified ambient space for each model in `eq:list` of Remark 3.11. -/
def Space {n : ℕ} : FiniteType n → Type
  | .a n _ => span ℝ (LineSystem.An n).Φ
  | .b n _ | .c n _ | .d n _ => EuclideanSpace ℝ (Fin n)
  | .e₆ => e₆Space
  | .e₇ => e₇Space
  | .e₈ => EuclideanSpace ℝ (Fin 8)
  | .f₄ => EuclideanSpace ℝ (Fin 4)
  | .g₂ => g₂Space

/-- The Euclidean normed group of the specified space in `def:rem-classical` and
`def:rem-exceptional`, Remark 3.11. -/
noncomputable instance spaceNormedAddCommGroup {n : ℕ} (t : FiniteType n) :
    NormedAddCommGroup (Space t) := by
  cases t <;> dsimp [Space] <;> infer_instance

/-- The Euclidean inner product of the specified space in `def:rem-classical` and
`def:rem-exceptional`, Remark 3.11. -/
noncomputable instance spaceInnerProductSpace {n : ℕ} (t : FiniteType n) :
    InnerProductSpace ℝ (Space t) := by
  cases t with
  | a n _ => exact (span ℝ (LineSystem.An n).Φ).innerProductSpace
  | b n _ | c n _ | d n _ => exact PiLp.innerProductSpace (fun _ : Fin n ↦ ℝ)
  | e₆ => exact e₆Space.innerProductSpace
  | e₇ => exact e₇Space.innerProductSpace
  | e₈ => exact PiLp.innerProductSpace (fun _ : Fin 8 ↦ ℝ)
  | f₄ => exact PiLp.innerProductSpace (fun _ : Fin 4 ↦ ℝ)
  | g₂ => exact g₂Space.innerProductSpace

/-- The canonical root sets in `eq:list` of Remark 3.11, with their specified coordinates. -/
noncomputable def roots {n : ℕ} (t : FiniteType n) : Set (Space t) := by
  cases t with
  | a n _ => exact An n
  | b n _ => exact Bn n
  | c n _ => exact Cn n
  | d n _ => exact Dn n
  | e₆ => exact E₆
  | e₇ => exact E₇
  | e₈ => exact E₈
  | f₄ => exact F₄
  | g₂ => exact G₂

/-- The combined model root-set assertions of `lem:classical`, `lem:E`, `lem:F`, `lem:G`. -/
theorem isRootSet {n : ℕ} (t : FiniteType n) : IsRootSet (roots t) := by
  cases t with
  | a n _ => exact An_isRootSet n
  | b n _ => exact Bn_isRootSet n
  | c n _ => exact Cn_isRootSet n
  | d n hn => exact Dn_isRootSet (n := n) (by omega)
  | e₆ => exact E₆_isRootSet
  | e₇ => exact E₇_isRootSet
  | e₈ => exact E₈_isRootSet
  | f₄ => exact F₄_isRootSet
  | g₂ => exact G₂_isRootSet

/-- The prescribed simple roots of the canonical models in Remark 3.11. -/
noncomputable def simpleRoot {n : ℕ} (t : FiniteType n) : Fin n → Space t := by
  cases t with
  | a n _ => exact An.simpleRoot n
  | b n hn =>
    cases n with
    | zero => omega
    | succ n => exact Bn.simpleRoot n
  | c n hn =>
    cases n with
    | zero => omega
    | succ n => exact Cn.simpleRoot n
  | d n hn =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ n => exact Dn.simpleRoot n
  | e₆ => exact E₆.simpleRoot
  | e₇ => exact E₇.simpleRoot
  | e₈ => exact E₈.simpleRoot
  | f₄ => exact F₄.simpleRoot
  | g₂ => exact G₂.simpleRoot

/-- The bases used in steps `rmiA`--`rmiG` of Remark 3.11. -/
theorem base {n : ℕ} (t : FiniteType n) : (isRootSet t).IsBase (simpleRoot t) := by
  cases t with
  | a n _ => exact An.base n
  | b n hn =>
    cases n with
    | zero => omega
    | succ n => exact Bn.base n
  | c n hn =>
    cases n with
    | zero => omega
    | succ n => exact Cn.base n
  | d n hn =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ n => exact Dn.base n
  | e₆ => exact E₆.base
  | e₇ => exact E₇.base
  | e₈ => exact E₈.base
  | f₄ => exact F₄_base
  | g₂ => exact G₂_base

/-- The Cartan identifications used in steps `rmiA`--`rmiG` of Remark 3.11. -/
theorem cartanMatrix {n : ℕ} (t : FiniteType n) (i j : Fin n) :
    IsRootSet.cartanPairing (simpleRoot t) i j = (modelEntries t i j : ℝ) := by
  cases t with
  | a n _ => exact An.cartanMatrix n i j
  | b n hn =>
    cases n with
    | zero => omega
    | succ n => exact Bn.cartanMatrix n i j
  | c n hn =>
    cases n with
    | zero => omega
    | succ n => exact Cn.cartanMatrix n i j
  | d n hn =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ n => exact Dn.cartanMatrix n i j
  | e₆ => exact E₆.cartanMatrix i j
  | e₇ => exact E₇.cartanMatrix i j
  | e₈ => exact E₈.cartanMatrix i j
  | f₄ => exact F₄_cartanMatrix i j
  | g₂ => exact G₂_cartanMatrix i j

/-- The rank of every coordinate model agrees with its index in `eq:list` of Remark 3.11. -/
theorem finrank_space {n : ℕ} (t : FiniteType n) : Module.finrank ℝ (Space t) = n := by
  simpa using Module.finrank_eq_card_basis (base t).toBasis

/-- Steps `rmiA`--`rmiG`: the Cartan support is exactly base nonorthogonality. -/
theorem nonorthogonalityGraph_eq_support {n : ℕ} (t : FiniteType n) :
    IsRootSet.nonorthogonalityGraph (simpleRoot t) =
      (modelEntries t).supportGraph (model_zero_comm t) := by
  ext i j
  change (i ≠ j ∧ ⟪simpleRoot t i, simpleRoot t j⟫ ≠ 0) ↔
    (i ≠ j ∧ modelEntries t i j ≠ 0)
  have hn : ⟪simpleRoot t j, simpleRoot t j⟫ ≠ 0 :=
    ne_of_gt (real_inner_self_pos.mpr ((isRootSet t).ne_zero ((base t).mem j)))
  have he := cartanMatrix t i j
  have hm : modelEntries t i j = 0 ↔ ⟪simpleRoot t i, simpleRoot t j⟫ = 0 := by
    rw [← Int.cast_eq_zero (α := ℝ), ← he]
    simp only [IsRootSet.cartanPairing, div_eq_zero_iff, mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or, hn, or_false]
  exact and_congr_right fun _ ↦ not_congr hm.symm

-- Remark 3.11, lem:models-irreducible
/-- Every coordinate model in the canonical list is indecomposable
(`lem:models-irreducible` of Remark 3.11 of [CGSS]). -/
theorem isIndecomposable {n : ℕ} (t : FiniteType n) : (isRootSet t).IsIndecomposable := by
  apply IsRootSet.isIndecomposable_of_connected_base _ (base t)
  rw [nonorthogonalityGraph_eq_support]
  let : Nonempty (Fin n) := ⟨⟨0, t.rank_pos⟩⟩
  exact (Matrix.isIndecomposable_iff_connected_support _ (model_zero_comm t)).mp
    (modelEntries_isFiniteTypeModel t).isIndecomposable

end RootSetModel
