/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.FixedLengths
import LineGraphs.RootSetClassification.LineOccurrence
import LineGraphs.RootSetClassification.ModelMatrices

/-!
# Theorem C of the blueprint for Remark 3.11 of [CGSS]

`thm:C` of the blueprint for Remark 3.11 of [CGSS], the line statement of the remark.
Its parts are proved in `Angles`, `FixedLengths`, `ClassicalLines`, `LineOccurrence`,
`ModelMatrices` and `ThreeLines`; this file adds the F₄ and G₂ line counts
(step `rCcounts`) and assembles the statement.

Every line matrix is `C = 2G - 2I` for unit vectors `u i` on the lines, one on each line,
given as `IsRootSet.signedAdj u` with root representatives `r` and `ℝ ∙ u i = ℝ ∙ r i`.
The angle between two distinct lines is `IsRootSet.lineAngle`, and `IsRootSet.lineAngles Φ`
is the set of the angles between distinct lines of `Φ`.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

open IsRootSet

/-- Step `rCcounts` of blueprint Theorem C for F₄: 24 lines in dimension 4. -/
theorem F₄_line_counts :
    (rootLines F₄).ncard = 24 ∧ Module.finrank ℝ (span ℝ F₄) = 4 := by
  refine ⟨?_, ?_⟩
  · rw [F₄_isRootSet.ncard_rootLines, IsRootSet.numLines, F₄_ncard]
  · rw [F₄_isRootSet.span_eq_top, finrank_top]
    simp

/-- Step `rCcounts` of blueprint Theorem C for G₂: 6 lines in dimension 2. -/
theorem G₂_line_counts : (rootLines G₂).ncard = 6 ∧ Module.finrank ℝ (span ℝ G₂) = 2 := by
  refine ⟨?_, ?_⟩
  · rw [G₂_isRootSet.ncard_rootLines, IsRootSet.numLines, G₂_ncard]
  · rw [G₂_isRootSet.span_eq_top, finrank_top]
    exact finrank_space .g₂

end RootSetModel

namespace IsRootSet

open RootSetModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ : Set V}

open scoped Classical in
-- Remark 3.11, thm:C
/-- Theorem C of the blueprint for Remark 3.11 of [CGSS], the line statement of the remark, for a
root set
`Φ` and the models of `def:rem-classical` and `def:rem-exceptional`:

* (`rCgeneral`) nonperpendicular, nonproportional roots of `Φ` have one of the three
  length-ratio and angle alternatives of `lem:angles`, and the roots of each length form a
  root set in their own span, the orthogonal direct sum of its components, each similar to
  exactly one model, which has type A, D or E;
* (`rCclassicalsame`, `rCcounts`, `rCallowed`, `rCoccurrence`, `rCeqBC`) for `n ≥ 2` the
  Bₙ and Cₙ models have the same `n²` lines in dimension `n`, with the same angles
  90, 60, 45 degrees, where 60 degrees does not occur for `n = 2` and all three occur for
  `n ≥ 3`, and `(C + 2I)(C - 2(n - 1)I) = 0`;
* (`rCcounts`, `rCallowed`, `rCoccurrence`, `rCeqF`) F₄ has 24 lines in dimension 4, at
  exactly the angles 90, 60, 45 degrees, and `(C + 2I)(C - 10I) = 0`;
* (`rCcounts`, `rCallowed`, `rCoccurrence`, `rCeqG`) G₂ has 6 lines in dimension 2, at
  exactly the angles 90, 60, 30 degrees, and `(C + 2I)(C - 4I) = 0`;
* (`rCexample`) three unit vectors of `ℝ³` lie on distinct lines pairwise at 45 degrees,
  and no three roots of `Φ` are pairwise at 45 degrees.

The matrix clauses use index types in `Type` so projections need no universe annotation.
The separate `signedAdj_quadratic_Bn`, `_Cn`, `_F₄` and `_G₂` theorems are universe polymorphic. -/
theorem remark_lines (hΦ : IsRootSet Φ) :
    (∀ r ∈ Φ, ∀ s ∈ Φ, ⟪r, s⟫ ≠ 0 → s ∉ ℝ ∙ r →
      (max ‖r‖ ‖s‖ / min ‖r‖ ‖s‖ = 1 ∧ lineAngle r s = Real.pi / 3) ∨
      (max ‖r‖ ‖s‖ / min ‖r‖ ‖s‖ = Real.sqrt 2 ∧ lineAngle r s = Real.pi / 4) ∨
      (max ‖r‖ ‖s‖ / min ‖r‖ ‖s‖ = Real.sqrt 3 ∧ lineAngle r s = Real.pi / 6)) ∧
    (∀ a : ℝ, IsRootSet (fixedLengthInSpan Φ a) ∧
      (∀ C : (rootGraph (fixedLengthInSpan Φ a)).ConnectedComponent,
        ∃! T : (n : ℕ) × CartanMatrix.FiniteType n, IsSimplyLaced T.2 ∧
          IsSimilarToModel ((Subtype.val : componentSpan C → span ℝ (fixedLength Φ a)) ⁻¹'
            componentRoots C) T) ∧
      OrthogonalFamily ℝ
        (fun C : (rootGraph (fixedLengthInSpan Φ a)).ConnectedComponent ↦ componentSpan C)
        (fun C ↦ (componentSpan C).subtypeₗᵢ) ∧
      DirectSum.IsInternal
        (fun C : (rootGraph (fixedLengthInSpan Φ a)).ConnectedComponent ↦ componentSpan C)) ∧
    (∀ n : ℕ, 2 ≤ n →
      rootLines (Bn n) = rootLines (Cn n) ∧ (rootLines (Bn n)).ncard = n ^ 2 ∧
      Module.finrank ℝ (span ℝ (Bn n)) = n ∧
      lineAngles (Bn n) = lineAngles (Cn n) ∧
      lineAngles (Bn n) ⊆ {Real.pi / 2, Real.pi / 3, Real.pi / 4} ∧
      (n = 2 → lineAngles (Bn n) = {Real.pi / 2, Real.pi / 4}) ∧
      (3 ≤ n → lineAngles (Bn n) = {Real.pi / 2, Real.pi / 3, Real.pi / 4}) ∧
      (∀ {I : Type} [Fintype I] [DecidableEq I] {r u : I → EuclideanSpace ℝ (Fin n)},
        (RootRepresentatives (Bn n) r ∨ RootRepresentatives (Cn n) r) →
        (∀ i, ‖u i‖ = 1) → (∀ i, ℝ ∙ u i = ℝ ∙ r i) →
        (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - (2 * ((n : ℝ) - 1)) • 1) = 0)) ∧
    ((rootLines F₄).ncard = 24 ∧ Module.finrank ℝ (span ℝ F₄) = 4 ∧
      lineAngles F₄ = {Real.pi / 2, Real.pi / 3, Real.pi / 4} ∧
      (∀ {I : Type} [Fintype I] [DecidableEq I] {r u : I → EuclideanSpace ℝ (Fin 4)},
        RootRepresentatives F₄ r → (∀ i, ‖u i‖ = 1) → (∀ i, ℝ ∙ u i = ℝ ∙ r i) →
        (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - (10 : ℝ) • 1) = 0)) ∧
    ((rootLines G₂).ncard = 6 ∧ Module.finrank ℝ (span ℝ G₂) = 2 ∧
      lineAngles G₂ = {Real.pi / 2, Real.pi / 3, Real.pi / 6} ∧
      (∀ {I : Type} [Fintype I] [DecidableEq I] {r u : I → g₂Space},
        RootRepresentatives G₂ r → (∀ i, ‖u i‖ = 1) → (∀ i, ℝ ∙ u i = ℝ ∙ r i) →
        (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - (4 : ℝ) • 1) = 0)) ∧
    ((∀ i, ‖fortyFiveTriple i‖ = 1) ∧
      (∀ i j, i ≠ j → fortyFiveTriple j ∉ ℝ ∙ fortyFiveTriple i ∧
        lineAngle (fortyFiveTriple i) (fortyFiveTriple j) = Real.pi / 4) ∧
      ∀ r ∈ Φ, ∀ s ∈ Φ, ∀ t ∈ Φ, ¬ (4 * ⟪r, s⟫ ^ 2 = 2 * ⟪r, r⟫ * ⟪s, s⟫ ∧
        4 * ⟪r, t⟫ ^ 2 = 2 * ⟪r, r⟫ * ⟪t, t⟫ ∧ 4 * ⟪s, t⟫ ^ 2 = 2 * ⟪s, s⟫ * ⟪t, t⟫)) := by
  refine ⟨fun r hr s hs ho hl ↦ hΦ.angle_length_cases hr hs ho hl, fun a ↦ ?_,
    fun n hn ↦ ?_, ⟨F₄_line_counts.1, F₄_line_counts.2, lineAngles_F₄,
      fun hr hu hl ↦ signedAdj_quadratic_F₄ hr hu hl⟩,
    ⟨G₂_line_counts.1, G₂_line_counts.2, lineAngles_G₂,
      fun hr hu hl ↦ signedAdj_quadratic_G₂ hr hu hl⟩,
    fortyFiveTriple_properties.1, fortyFiveTriple_properties.2,
    fun r hr s hs t ht h ↦ hΦ.not_contains_three_equiangular_lines hr hs ht h.1 h.2.1 h.2.2⟩
  · have hΨ := hΦ.fixedLength_isRootSet a
    exact ⟨hΨ, hΦ.fixedLength_components_simplyLaced a, hΨ.orthogonal_components.2⟩
  · obtain ⟨hB, -, hd⟩ := Bn_Cn_line_counts n
    refine ⟨Bn_Cn_same_lines n, hB, hd, lineAngles_Bn_eq_Cn n, lineAngles_Bn_subset n,
      fun h ↦ h ▸ lineAngles_B₂, lineAngles_Bn, fun hr hu hl ↦ ?_⟩
    rcases hr with hr | hr
    · exact signedAdj_quadratic_Bn hn hr hu hl
    · exact signedAdj_quadratic_Cn hn hr hu hl

end IsRootSet
