/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Classification
import LineGraphs.LineSystem.SpanExtension
import LineGraphs.Computations.C5

/-!
# Theorem 3.6 of [CGSS]: the maximal line systems

`blueprint/sec3-rootsystems.tex`, `thm:3.6`. A nonempty indecomposable line system is maximal
within its span exactly when it is isomorphic to `Aℓ` (`ℓ ≥ 1`, `ℓ ≠ 7, 8`), `Dℓ` (`ℓ ≥ 4`,
`ℓ ≠ 8`), `E₆`, `E₇` or `E₈`. The excluded types are not maximal by C5 and
`lem:sec3-proper-inclusion` (`An.not_isMaximal_seven`, `An.not_isMaximal_eight`,
`Dn.not_isMaximal_eight`). A retained model that were not maximal would have a proper
extension of the same rank in its span (`lem:sec3-extension`, `exists_maximal_extension_span`),
which Theorem 3.5 identifies with a listed model; line counts and the obstructions of C5 exclude
every candidate.
-/

open Submodule Module

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The number of roots of `E₆` (C2, `comp:C2`), for step `s336E` of Theorem 3.6 of [CGSS]. -/
theorem ncard_Φ_E₆ : E₆.Φ.ncard = 72 := by
  rw [E₆.integerModel.ncard_Φ]
  exact card_E₆Index

/-- The root count of `Dℓ`, `4 · (ℓ choose 2) = 2ℓ(ℓ - 1)`, for step `s336DA` of Theorem 3.6
of [CGSS]. -/
theorem choose_two_mul_four (n : ℕ) : (n + 1).choose 2 * 4 = 2 * ((n + 1) * n) := by
  have h := Nat.add_one_mul_choose_eq n 1
  rw [Nat.choose_one_right] at h
  linarith

namespace RootType

/-- Every model has a root, since its rank is positive (C4, used in step `s336extension` of
Theorem 3.6 of [CGSS]). -/
theorem Φ_nonempty_model (t : RootType) : t.model.Φ.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  have h' := t.finrank_span_model
  rw [h, span_empty, finrank_bot] at h'
  exact (t.rank_pos.ne h')

/-- The root counts of the models (C2, `comp:C2`), for Theorem 3.6 of [CGSS]. -/
theorem ncard_model_A (ℓ : ℕ) (h : 1 ≤ ℓ) : (A ℓ h).model.Φ.ncard = ℓ * (ℓ + 1) :=
  ncard_Φ_An ℓ

/-- The root counts of the models (C2, `comp:C2`), for Theorem 3.6 of [CGSS]. -/
theorem ncard_model_D (ℓ : ℕ) (h : 4 ≤ ℓ) : (D ℓ h).model.Φ.ncard = ℓ.choose 2 * 4 :=
  ncard_Φ_Dn ℓ

/-- The root counts of the models (C2, `comp:C2`), for Theorem 3.6 of [CGSS]. -/
theorem ncard_model_E₆ : E₆.model.Φ.ncard = 72 := ncard_Φ_E₆

/-- The root counts of the models (C2, `comp:C2`), for Theorem 3.6 of [CGSS]. -/
theorem ncard_model_E₇ : E₇.model.Φ.ncard = 126 := ncard_Φ_E₇

/-- The root counts of the models (C2, `comp:C2`), for Theorem 3.6 of [CGSS]. -/
theorem ncard_model_E₈ : E₈.model.Φ.ncard = 240 := ncard_Φ_E₈

-- Theorem 3.6, step s336target
/-- Steps `s336extension` and `s336target` of `thm:3.6` (Theorem 3.6 of [CGSS]): a model that is
not maximal within its span has an isometric inclusion in a listed model of the same rank with
strictly more roots. The extension is `exists_maximal_extension_span` (`lem:sec3-extension`),
and Theorem 3.5 (`exists_iso_rootType`) identifies it (step `s336targetiso`). -/
theorem exists_inclusion_of_not_isMaximal (s : RootType) (hs : ¬ s.model.IsMaximal) :
    ∃ t : RootType, Nonempty (IsometricInclusion s.model t.model) ∧ t.rank = s.rank ∧
      s.model.Φ.ncard < t.model.Φ.ncard := by
  obtain ⟨T, hsub, _, hspan, _, hTI, hTSC⟩ :=
    s.model.exists_maximal_extension_span s.Φ_nonempty_model s.isIndecomposable_model hs
  obtain ⟨t, ⟨e⟩⟩ := T.exists_iso_rootType (s.Φ_nonempty_model.mono hsub.subset) hTI hTSC
  refine ⟨t, ⟨(IsometricInclusion.ofSubset hsub.subset).trans e.toIsometricInclusion⟩, ?_, ?_⟩
  · rw [← t.finrank_span_model, ← e.finrank_span_eq, hspan, s.finrank_span_model]
  · rw [← e.ncard_eq]
    exact Set.ncard_lt_ncard hsub T.finite

end RootType

-- Theorem 3.6, step s336A
/-- Step `s336A` of `thm:3.6` (Theorem 3.6 of [CGSS]): `Aℓ`, `ℓ ≠ 7, 8`, is maximal within its
span. The target of step `s336target` has rank `ℓ`: `Aℓ` has the same count, and C5 excludes
`Aℓ ⊂ Dℓ` (step `s336AD`) and `A₆ ⊂ E₆` (step `s336AE`). -/
theorem isMaximal_An {ℓ : ℕ} (h1 : 1 ≤ ℓ) (h7 : ℓ ≠ 7) (h8 : ℓ ≠ 8) : (An ℓ).IsMaximal := by
  by_contra hs
  obtain ⟨t, ⟨G⟩, hr, hc⟩ := RootType.exists_inclusion_of_not_isMaximal (.A ℓ h1) hs
  cases t with
  | A ℓ' _ =>
    simp only [RootType.rank] at hr
    subst hr
    exact lt_irrefl _ hc
  | D ℓ' h =>
    simp only [RootType.rank] at hr
    subst hr
    exact (not_embeds_An_Dn h).false G
  | E₆ =>
    simp only [RootType.rank] at hr
    subst hr
    exact not_embeds_An_E₆.false G
  | E₇ => simp only [RootType.rank] at hr; omega
  | E₈ => simp only [RootType.rank] at hr; omega

-- Theorem 3.6, step s336D
/-- Step `s336D` of `thm:3.6` (Theorem 3.6 of [CGSS]): `Dℓ`, `ℓ ≥ 4`, `ℓ ≠ 8`, is maximal
within its span. `Aℓ` and `Dℓ` have at most as many roots (step `s336DA`), and C5 excludes
`D₆ ⊂ E₆` and `D₇ ⊂ E₇` (step `s336DE`). -/
theorem isMaximal_Dn {ℓ : ℕ} (h4 : 4 ≤ ℓ) (h8 : ℓ ≠ 8) : (Dn ℓ).IsMaximal := by
  by_contra hs
  obtain ⟨t, ⟨G⟩, hr, hc⟩ := RootType.exists_inclusion_of_not_isMaximal (.D ℓ h4) hs
  cases t with
  | A ℓ' _ =>
    simp only [RootType.rank] at hr
    subst hr
    rw [RootType.ncard_model_A, RootType.ncard_model_D] at hc
    obtain ⟨n, rfl⟩ : ∃ n, ℓ' = n + 1 := ⟨ℓ' - 1, by omega⟩
    rw [choose_two_mul_four] at hc
    nlinarith
  | D ℓ' h =>
    simp only [RootType.rank] at hr
    subst hr
    exact lt_irrefl _ hc
  | E₆ =>
    simp only [RootType.rank] at hr
    subst hr
    exact not_embeds_Dn_E₆.false G
  | E₇ =>
    simp only [RootType.rank] at hr
    subst hr
    exact not_embeds_Dn_E₇.false G
  | E₈ => simp only [RootType.rank] at hr; omega

-- Theorem 3.6, step s336E
/-- Step `s336E` of `thm:3.6` (Theorem 3.6 of [CGSS]): `E₆` is maximal within its span; at
rank 6 the root counts are `42`, `60`, `72`. -/
theorem isMaximal_E₆ : E₆.IsMaximal := by
  by_contra hs
  obtain ⟨t, _, hr, hc⟩ := RootType.exists_inclusion_of_not_isMaximal .E₆ hs
  cases t <;> simp only [RootType.rank] at hr <;> subst_vars <;>
    simp only [RootType.ncard_model_A, RootType.ncard_model_D, RootType.ncard_model_E₆,
      RootType.ncard_model_E₇, RootType.ncard_model_E₈] at hc <;>
    first | omega | (revert hc; decide)

-- Theorem 3.6, step s336E
/-- Step `s336E` of `thm:3.6` (Theorem 3.6 of [CGSS]): `E₇` is maximal within its span; at
rank 7 the root counts are `56`, `84`, `126`. -/
theorem isMaximal_E₇ : E₇.IsMaximal := by
  by_contra hs
  obtain ⟨t, _, hr, hc⟩ := RootType.exists_inclusion_of_not_isMaximal .E₇ hs
  cases t <;> simp only [RootType.rank] at hr <;> subst_vars <;>
    simp only [RootType.ncard_model_A, RootType.ncard_model_D, RootType.ncard_model_E₆,
      RootType.ncard_model_E₇, RootType.ncard_model_E₈] at hc <;>
    first | omega | (revert hc; decide)

-- Theorem 3.6, step s336E
/-- Step `s336E` of `thm:3.6` (Theorem 3.6 of [CGSS]): `E₈` is maximal within its span; at
rank 8 the root counts are `72`, `112`, `240`. -/
theorem isMaximal_E₈ : E₈.IsMaximal := by
  by_contra hs
  obtain ⟨t, _, hr, hc⟩ := RootType.exists_inclusion_of_not_isMaximal .E₈ hs
  cases t <;> simp only [RootType.rank] at hr <;> subst_vars <;>
    simp only [RootType.ncard_model_A, RootType.ncard_model_D, RootType.ncard_model_E₆,
      RootType.ncard_model_E₇, RootType.ncard_model_E₈] at hc <;>
    first | omega | (revert hc; decide)

-- Theorem 3.6
/-- Theorem 3.6 of [CGSS] (`thm:3.6`): a nonempty indecomposable line system is maximal within
its span (Definition 2.2; errata, Implicit hypothesis 7) if and only if it is isomorphic to
`Aℓ` (`ℓ ≥ 1`, `ℓ ≠ 7, 8`), `Dℓ` (`ℓ ≥ 4`, `ℓ ≠ 8`), `E₆`, `E₇` or `E₈`. Step `s336forward`:
Lemma 2.3, Theorem 3.5 and step `s336excluded` (C5); step `s336reverse`: steps
`s336modelsmaximal` (`isMaximal_An`, ..., `isMaximal_E₈`) and `lem:sec3-transport`. The space
need not be finite-dimensional. -/
theorem classification_of_isMaximal (S : LineSystem V) (hne : S.Φ.Nonempty)
    (hI : S.IsIndecomposable) :
    S.IsMaximal ↔
      (∃ ℓ, 1 ≤ ℓ ∧ ℓ ≠ 7 ∧ ℓ ≠ 8 ∧ Nonempty (S.Iso (An ℓ))) ∨
      (∃ ℓ, 4 ≤ ℓ ∧ ℓ ≠ 8 ∧ Nonempty (S.Iso (Dn ℓ))) ∨
      Nonempty (S.Iso E₆) ∨ Nonempty (S.Iso E₇) ∨ Nonempty (S.Iso E₈) := by
  constructor
  · intro hmax
    obtain ⟨t, ⟨e⟩⟩ := S.exists_iso_rootType hne hI hmax.isStarClosed
    have hM : t.model.IsMaximal := e.symm.isMaximal hmax
    cases t with
    | A ℓ h =>
      refine Or.inl ⟨ℓ, h, ?_, ?_, ⟨e⟩⟩
      · rintro rfl
        exact An.not_isMaximal_seven hM
      · rintro rfl
        exact An.not_isMaximal_eight hM
    | D ℓ h =>
      refine Or.inr (Or.inl ⟨ℓ, h, ?_, ⟨e⟩⟩)
      rintro rfl
      exact Dn.not_isMaximal_eight hM
    | E₆ => exact Or.inr (Or.inr (Or.inl ⟨e⟩))
    | E₇ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    | E₈ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))
  · rintro (⟨ℓ, h1, h7, h8, ⟨e⟩⟩ | ⟨ℓ, h4, h8, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩)
    · exact e.isMaximal (isMaximal_An h1 h7 h8)
    · exact e.isMaximal (isMaximal_Dn h4 h8)
    · exact e.isMaximal isMaximal_E₆
    · exact e.isMaximal isMaximal_E₇
    · exact e.isMaximal isMaximal_E₈

/-- Theorem 3.6 of [CGSS] in the form used by Section 4 (`lem:4-rootType`): a nonempty maximal
indecomposable line system is isomorphic to the model of some `RootType`. -/
theorem IsMaximal.exists_iso_rootType {S : LineSystem V} (hmax : S.IsMaximal)
    (hne : S.Φ.Nonempty) (hI : S.IsIndecomposable) :
    ∃ t : RootType, Nonempty (S.Iso t.model) := by
  rcases (S.classification_of_isMaximal hne hI).mp hmax with
    ⟨ℓ, h1, -, -, e⟩ | ⟨ℓ, h4, -, e⟩ | e | e | e
  · exact ⟨.A ℓ h1, e⟩
  · exact ⟨.D ℓ h4, e⟩
  · exact ⟨.E₆, e⟩
  · exact ⟨.E₇, e⟩
  · exact ⟨.E₈, e⟩

end LineSystem
