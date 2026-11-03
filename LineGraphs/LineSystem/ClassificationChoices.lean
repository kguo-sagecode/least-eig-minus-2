/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.ClassificationMaximal

/-!
# The independence of the perpendicular choices

Lemma (independence of the perpendicular choices), `lem:sec3-choices` of
`blueprint/sec3-rootsystems.tex`, for Definition 3.3 of [CGSS] (errata, Gap 5): the cuts of
`E₈` perpendicular to any root, or to any star, are isomorphic to `E₇`, or `E₆`. The ordered
stars are moved by the isometries of C4 (`E₈.exists_isometry_star`). The statements for the
other two `E₈` models and for `T₇`, `T₆` are in `LineSystem/ClassificationChoicesModels.lean`.
-/

open Submodule Module
open scoped RealInnerProductSpace

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A linear isometry carrying the roots of `S` exactly onto those of `T` is an isomorphism
(`lem:sec3-transport`), for `lem:sec3-choices` of Section 3 of [CGSS]. -/
def Iso.ofLinearIsometryEquiv (S T : LineSystem V) (g : V ≃ₗᵢ[ℝ] V)
    (hg : ∀ x, g x ∈ T.Φ ↔ x ∈ S.Φ) : S.Iso T where
  toEquiv :=
    { toFun := fun r ↦ ⟨g r, (hg r).mpr r.property⟩
      invFun := fun r ↦ ⟨g.symm r, (hg _).mp (by rw [g.apply_symm_apply]; exact r.property)⟩
      left_inv := fun r ↦ Subtype.ext (g.symm_apply_apply r)
      right_inv := fun r ↦ Subtype.ext (g.apply_symm_apply r) }
  inner_map r s := g.inner_map_map r s

/-- Step `s3choicecuts` of `lem:sec3-choices` (Section 3 of [CGSS]): an isometry of `S`
carries the cut perpendicular to `v` onto the cut perpendicular to `g v`. -/
theorem nonempty_iso_orthogonalTo_of_mem_isometryGroup (S : LineSystem V) {g : V ≃ₗᵢ[ℝ] V}
    (hg : g ∈ S.isometryGroup) (v : V) :
    Nonempty ((S.orthogonalTo v).Iso (S.orthogonalTo (g v))) := by
  refine ⟨Iso.ofLinearIsometryEquiv _ _ g fun x ↦ ?_⟩
  change g x ∈ S.Φ ∧ ⟪g x, g v⟫ = 0 ↔ x ∈ S.Φ ∧ ⟪x, v⟫ = 0
  rw [g.inner_map_map]
  exact and_congr_left' (hg x)

-- Lemma "independence of the perpendicular choices"
/-- Step `s3choicepair` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5): an
isometry of `E₈` carries any ordered star `(r, s)` to the star `(e₇ - e₈, e₆ - e₇)` of
Definition 3.3. It composes two isometries of C4, `E₈.exists_isometry_star`. -/
theorem E₈.exists_isometry_of_ordered_star {r s : EuclideanSpace ℝ (Fin 8)} (hr : r ∈ E₈.Φ)
    (hs : s ∈ E₈.Φ) (hrs : ⟪r, s⟫ = -1) :
    ∃ g ∈ E₈.isometryGroup, g r = e₇Normal ∧ g s = e₆Normal := by
  obtain ⟨g₁, hg₁, h₁a, h₁b⟩ := E₈.exists_isometry_star hr hs hrs
  obtain ⟨g₂, hg₂, h₂a, h₂b⟩ :=
    E₈.exists_isometry_star e₇Normal_mem_E₈ e₆Normal_mem_E₈ inner_e₇Normal_e₆Normal
  refine ⟨g₁.symm.trans g₂, fun x ↦ ?_, ?_, ?_⟩
  · change g₂ (g₁.symm x) ∈ E₈.Φ ↔ x ∈ E₈.Φ
    rw [hg₂, ← hg₁ (g₁.symm x), g₁.apply_symm_apply]
  · rw [LinearIsometryEquiv.trans_apply, ← h₁a, g₁.symm_apply_apply, h₂a]
  · rw [LinearIsometryEquiv.trans_apply, ← h₁b, g₁.symm_apply_apply, h₂b]

/-- Step `s3choiceroot` of `lem:sec3-choices` (Section 3 of [CGSS]): every root of `E₈` has a
partner of inner product `-1`, by the indecomposability of C4 and the 120 lines of C2. -/
theorem E₈.exists_inner_eq_neg_one {r : EuclideanSpace ℝ (Fin 8)} (hr : r ∈ E₈.Φ) :
    ∃ s ∈ E₈.Φ, ⟪r, s⟫ = -1 := by
  by_contra! h
  have ho : ∀ s ∈ E₈.Φ, s ∉ ({r, -r} : Set (EuclideanSpace ℝ (Fin 8))) → ⟪r, s⟫ = 0 := by
    intro s hs hsp
    have hne : r ≠ s := fun he ↦ hsp (Or.inl he.symm)
    have hneg : r ≠ -s := fun he ↦ hsp (Or.inr
      (Set.mem_singleton_iff.mpr (by simpa using congrArg Neg.neg he.symm)))
    rcases E₈.inner_eq_neg_one_or_zero_or_one hr hs hne hneg with h' | h' | h'
    · exact (h s hs h').elim
    · exact h'
    · exact (h (-s) (E₈.neg_mem s hs) (by rw [inner_neg_right, h'])).elim
  have hp : ({r, -r} : Set (EuclideanSpace ℝ (Fin 8))) ⊆ E₈.Φ := by
    rintro x (rfl | hx)
    · exact hr
    · exact Set.mem_singleton_iff.mp hx ▸ E₈.neg_mem r hr
  have hcover : ({r, -r} : Set (EuclideanSpace ℝ (Fin 8))) ∪ (E₈.Φ \ {r, -r}) = E₈.Φ := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    exact ⟨fun h ↦ h.elim (hp ·) And.left, fun hx ↦ by tauto⟩
  have horth : ∀ p ∈ ({r, -r} : Set (EuclideanSpace ℝ (Fin 8))), ∀ q ∈ E₈.Φ \ {r, -r},
      ⟪p, q⟫ = 0 := by
    rintro p (rfl | hp) q hq
    · exact ho q hq.1 hq.2
    · rw [Set.mem_singleton_iff] at hp
      rw [hp, inner_neg_left, ho q hq.1 hq.2, neg_zero]
  rcases isIndecomposable_E₈ _ _ hcover horth with hempty | hempty
  · have : r ∈ (∅ : Set (EuclideanSpace ℝ (Fin 8))) := hempty ▸ Set.mem_insert r {-r}
    exact this.elim
  · rw [hempty, Set.union_empty] at hcover
    have hc := ncard_Φ_E₈
    rw [← hcover] at hc
    have := Set.ncard_insert_le r ({-r} : Set (EuclideanSpace ℝ (Fin 8)))
    rw [Set.ncard_singleton] at this
    omega

-- Lemma "independence of the perpendicular choices"
/-- Step `s3choiceSeven` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5): the cut of
`E₈` perpendicular to any root is isomorphic to `E₇`. -/
theorem E₈.nonempty_iso_E₇_orthogonalTo {r : EuclideanSpace ℝ (Fin 8)} (hr : r ∈ E₈.Φ) :
    Nonempty ((E₈.orthogonalTo r).Iso E₇) := by
  obtain ⟨s, hs, hrs⟩ := E₈.exists_inner_eq_neg_one hr
  obtain ⟨g, hg, hgr, -⟩ := E₈.exists_isometry_of_ordered_star hr hs hrs
  obtain ⟨e⟩ := E₈.nonempty_iso_orthogonalTo_of_mem_isometryGroup hg r
  rw [hgr] at e
  exact ⟨e⟩

-- Lemma "independence of the perpendicular choices"
/-- Step `s3choiceSix` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5): the cut of
`E₈` perpendicular to any star `r, s, -r-s` is isomorphic to `E₆`; orthogonality to `-r-s`
follows from orthogonality to `r` and `s`. -/
theorem E₈.nonempty_iso_E₆_orthogonalTo {r s : EuclideanSpace ℝ (Fin 8)} (hr : r ∈ E₈.Φ)
    (hs : s ∈ E₈.Φ) (hrs : ⟪r, s⟫ = -1) :
    Nonempty (((E₈.orthogonalTo r).orthogonalTo s).Iso E₆) := by
  obtain ⟨g, hg, hgr, hgs⟩ := E₈.exists_isometry_of_ordered_star hr hs hrs
  refine ⟨Iso.ofLinearIsometryEquiv _ _ g fun x ↦ ?_⟩
  change (g x ∈ E₈.Φ ∧ ⟪g x, e₇Normal⟫ = 0) ∧ ⟪g x, e₆Normal⟫ = 0 ↔
    (x ∈ E₈.Φ ∧ ⟪x, r⟫ = 0) ∧ ⟪x, s⟫ = 0
  rw [← hgr, ← hgs, g.inner_map_map, g.inner_map_map, hg x]

end LineSystem
