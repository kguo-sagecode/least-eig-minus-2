/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.ClassificationMaximal
import LineGraphs.Computations.C4E6Stars
import LineGraphs.Computations.C4E7Stars
import LineGraphs.Computations.C4E8Stars
import LineGraphs.Computations.C20Apex

/-! # Moving a root to the apex

Lemma `lem:414-transitive` of Remark 4.14 of [CGSS].
-/

open scoped RealInnerProductSpace

namespace LineSystem

/-- Step `s414trr` of `lem:414-transitive`: indecomposability and more than one line
put every root in an ordered star. -/
theorem IsIndecomposable.exists_inner_eq_neg_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {S : LineSystem E} (hS : S.IsIndecomposable)
    (hcard : 2 < S.Φ.ncard) {r : E} (hr : r ∈ S.Φ) : ∃ s ∈ S.Φ, ⟪r, s⟫ = -1 := by
  by_contra! h
  have ho : ∀ s ∈ S.Φ, s ∉ ({r, -r} : Set E) → ⟪r, s⟫ = 0 := by
    intro s hs hsp
    have hne : r ≠ s := fun he ↦ hsp (Or.inl he.symm)
    have hneg : r ≠ -s := fun he ↦ hsp (Or.inr
      (Set.mem_singleton_iff.mpr (by simpa using congrArg Neg.neg he.symm)))
    rcases S.inner_eq_neg_one_or_zero_or_one hr hs hne hneg with h' | h' | h'
    · exact (h s hs h').elim
    · exact h'
    · exact (h (-s) (S.neg_mem s hs) (by rw [inner_neg_right, h'])).elim
  have hp : ({r, -r} : Set E) ⊆ S.Φ := by
    rintro x (rfl | hx)
    · exact hr
    · exact Set.mem_singleton_iff.mp hx ▸ S.neg_mem r hr
  have hcover : ({r, -r} : Set E) ∪ (S.Φ \ {r, -r}) = S.Φ := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    exact ⟨fun h ↦ h.elim (hp ·) And.left, fun hx ↦ by tauto⟩
  have horth : ∀ p ∈ ({r, -r} : Set E), ∀ q ∈ S.Φ \ {r, -r}, ⟪p, q⟫ = 0 := by
    rintro p (rfl | hp) q hq
    · exact ho q hq.1 hq.2
    · rw [Set.mem_singleton_iff] at hp
      rw [hp, inner_neg_left, ho q hq.1 hq.2, neg_zero]
  rcases hS _ _ hcover horth with hempty | hempty
  · have : r ∈ (∅ : Set E) := hempty ▸ Set.mem_insert r {-r}
    exact this.elim
  · rw [hempty, Set.union_empty] at hcover
    rw [← hcover] at hcard
    have := Set.ncard_insert_le r ({-r} : Set E)
    rw [Set.ncard_singleton] at this
    omega

/-- The composition of the two ordered-star isometries in `lem:414-transitive`. -/
theorem exists_isometry_apply_eq_of_star_transitivity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : LineSystem E) (a₀ : E)
    (ht : ∀ a ∈ S.Φ, ∀ b ∈ S.Φ, ⟪a, b⟫ = -1 →
      ∃ g ∈ S.isometryGroup, g a₀ = a)
    (hi : S.IsIndecomposable) (hc : 2 < S.Φ.ncard) {r c : E}
    (hr : r ∈ S.Φ) (hc' : c ∈ S.Φ) :
    ∃ g ∈ S.isometryGroup, g r = c := by
  obtain ⟨s, hs, hrs⟩ := hi.exists_inner_eq_neg_one hc hr
  obtain ⟨t, ht', hct⟩ := hi.exists_inner_eq_neg_one hc hc'
  obtain ⟨g₁, hg₁, h₁⟩ := ht r hr s hs hrs
  obtain ⟨g₂, hg₂, h₂⟩ := ht c hc' t ht' hct
  refine ⟨g₁.symm.trans g₂, fun x ↦ ?_, ?_⟩
  · change g₂ (g₁.symm x) ∈ S.Φ ↔ x ∈ S.Φ
    rw [hg₂, ← hg₁ (g₁.symm x), g₁.apply_symm_apply]
  · rw [LinearIsometryEquiv.trans_apply, ← h₁, g₁.symm_apply_apply, h₂]

-- Lemma (transitivity on roots), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-transitive` for `E₆`, Remark 4.14: an isometry takes any root to `c`. -/
theorem E₆.exists_isometry_apply_eq_c {r : EuclideanSpace ℝ (Fin 8)} (hr : r ∈ E₆.Φ) :
    ∃ g ∈ E₆.isometryGroup, g r = E₈.c := by
  apply exists_isometry_apply_eq_of_star_transitivity E₆ E₆.hyp24.a
    (fun a ha b hb hab ↦ ?_) isIndecomposable_E₆ (by rw [ncard_Φ_E₆]; norm_num) hr E₆.c_mem
  obtain ⟨g, hg, ha, _⟩ := E₆.exists_isometry_star ha hb hab
  exact ⟨g, hg, ha⟩

-- Lemma (transitivity on roots), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-transitive` for `E₇`, Remark 4.14: an isometry takes any root to `c`. -/
theorem E₇.exists_isometry_apply_eq_c {r : EuclideanSpace ℝ (Fin 8)} (hr : r ∈ E₇.Φ) :
    ∃ g ∈ E₇.isometryGroup, g r = E₈.c := by
  apply exists_isometry_apply_eq_of_star_transitivity E₇ E₇.hyp24.a
    (fun a ha b hb hab ↦ ?_) isIndecomposable_E₇ (by rw [ncard_Φ_E₇]; norm_num) hr E₇.c_mem
  obtain ⟨g, hg, ha, _⟩ := E₇.exists_isometry_star ha hb hab
  exact ⟨g, hg, ha⟩

-- Lemma (transitivity on roots), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-transitive` for `E₈`, Remark 4.14: an isometry takes any root to `c`. -/
theorem E₈.exists_isometry_apply_eq_c {r : EuclideanSpace ℝ (Fin 8)} (hr : r ∈ E₈.Φ) :
    ∃ g ∈ E₈.isometryGroup, g r = E₈.c := by
  apply exists_isometry_apply_eq_of_star_transitivity E₈ E₈.hyp24.a
    (fun a ha b hb hab ↦ ?_) isIndecomposable_E₈ (by rw [ncard_Φ_E₈]; norm_num) hr E₈.c_mem
  obtain ⟨g, hg, ha, _⟩ := E₈.exists_isometry_star ha hb hab
  exact ⟨g, hg, ha⟩

end LineSystem
