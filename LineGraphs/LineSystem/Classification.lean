/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.ClassificationModels
import LineGraphs.LineSystem.ClassicalModels
import LineGraphs.Computations.C4Classical

/-!
# Theorem 3.5 of [CGSS]: the classification

`blueprint/sec3-rootsystems.tex`, `thm:3.5`. A nonempty line system is indecomposable and
star-closed exactly when it is isomorphic to the model of exactly one `RootType`. The forward
direction restricts `S` to its span (`lem:sec3-restrict`) and applies the unconditional
Theorem 2.13, `five_possibilities'`, whose isomorphisms go directly to the listed models; the
reverse direction is C4 with `lem:sec3-transport`; uniqueness compares ranks and line counts
(Lemma 3.4).

The ambient space need not be finite-dimensional: the span of the finite root set is, and
Theorem 2.13 is applied there.
-/

open Submodule Module

namespace LineSystem

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The composite of two isomorphisms of line systems (`lem:sec3-transport`, used in steps
`s335atmost` and `s336targetmap` of Theorems 3.5 and 3.6 of [CGSS]). -/
def Iso.trans {S : LineSystem U} {T : LineSystem V} {R : LineSystem W} (e : S.Iso T)
    (f : T.Iso R) : S.Iso R where
  toEquiv := e.toEquiv.trans f.toEquiv
  inner_map x y := (f.inner_map (e.toEquiv x) (e.toEquiv y)).trans (e.inner_map x y)

/-- Isomorphic systems have root sets of the same size (`lem:sec3-transport`, step
`s3trlines`, for Theorem 3.6 of [CGSS]). -/
theorem Iso.ncard_eq {S : LineSystem U} {T : LineSystem V} (e : S.Iso T) :
    S.Φ.ncard = T.Φ.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr e.toEquiv]

namespace RootType

/-- Steps `s335rank` to `s335exceptionalcounts` of `thm:3.5` (Theorem 3.5 of [CGSS]):
the rank and the number of lines determine the type. -/
theorem eq_of_rank_eq_of_numLines_eq {t t' : RootType} (hr : t.rank = t'.rank)
    (hn : t.numLines = t'.numLines) : t = t' := by
  have hAD : ∀ ℓ, 4 ≤ ℓ → ℓ * (ℓ + 1) / 2 ≠ ℓ * (ℓ - 1) := by
    intro ℓ hℓ he
    have h2 : ℓ * (ℓ + 1) < ℓ * (ℓ - 1) * 2 := by
      rw [mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mpr h2
    omega
  cases t <;> cases t' <;> simp only [rank, numLines] at hr hn <;> subst_vars <;>
    first
    | rfl
    | (exfalso; exact hAD _ ‹_› hn)
    | (exfalso; exact hAD _ ‹_› hn.symm)
    | (exfalso; revert hn; decide)

/-- Step `s335unique` of `thm:3.5` (Theorem 3.5 of [CGSS]): different listed types are not
isomorphic, since an isomorphism preserves rank and line count (`lem:sec3-transport`). -/
theorem eq_of_iso {t t' : RootType} (e : t.model.Iso t'.model) : t = t' :=
  eq_of_rank_eq_of_numLines_eq
    ((t.finrank_span_model.symm.trans e.finrank_span_eq).trans t'.finrank_span_model)
    ((t.numLines_model.symm.trans e.numLines_eq).trans t'.numLines_model)

/-- C4 (`comp:C4`), its first assertion, used in step `s335reverse` of Theorem 3.5 of [CGSS]:
every model is indecomposable. -/
theorem isIndecomposable_model (t : RootType) : t.model.IsIndecomposable := by
  cases t with
  | A ℓ h => exact isIndecomposable_An h
  | D ℓ h => exact isIndecomposable_Dn h
  | E₆ => exact isIndecomposable_E₆
  | E₇ => exact isIndecomposable_E₇
  | E₈ => exact isIndecomposable_E₈

/-- C4 (`comp:C4`), its first assertion, used in step `s335reverse` of Theorem 3.5 of [CGSS]:
every model is star-closed. -/
theorem isStarClosed_model (t : RootType) : t.model.IsStarClosed := by
  cases t with
  | A ℓ _ => exact isStarClosed_An ℓ
  | D ℓ _ => exact isStarClosed_Dn ℓ
  | E₆ => exact isStarClosed_E₆
  | E₇ => exact isStarClosed_E₇
  | E₈ => exact isStarClosed_E₈

end RootType

/-- Step `s335forward` of `thm:3.5` (Theorem 3.5 of [CGSS]): a nonempty indecomposable
star-closed system is isomorphic to a listed model. Steps `s335restrict` and
`s335possibilities`: Theorem 2.13 applies to `S.restrictSpan` (`lem:sec3-restrict`), and its
five cases name the model; the isomorphism is composed with `Iso.restrictSpan`. -/
theorem exists_iso_rootType (S : LineSystem V) (hne : S.Φ.Nonempty)
    (hI : S.IsIndecomposable) (hSC : S.IsStarClosed) :
    ∃ t : RootType, Nonempty (S.Iso t.model) := by
  have : FiniteDimensional ℝ (span ℝ S.Φ) := FiniteDimensional.span_of_finite ℝ S.finite
  let R := S.restrictSpan
  have e₀ : S.Iso R := (Iso.restrictSpan S).symm
  have hRne : R.Φ.Nonempty := (e₀.nonempty_iff).mp hne
  have hRI : R.IsIndecomposable := e₀.isIndecomposable_iff.mp hI
  have hRSC : R.IsStarClosed := e₀.isStarClosed_iff.mp hSC
  rcases R.five_possibilities' hRne hRI hRSC S.restrictSpan_span_eq_top with
    ⟨⟨q⟩, _, hA⟩ | ⟨h4, ⟨q⟩, _⟩ | ⟨_, ⟨q⟩, _⟩ | ⟨_, ⟨q⟩, _⟩ | ⟨_, ⟨q⟩, _⟩
  · have h1 : 1 ≤ finrank ℝ (span ℝ S.Φ) := by
      rcases hA with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    exact ⟨.A _ h1, ⟨e₀.trans q⟩⟩
  · exact ⟨.D _ h4, ⟨e₀.trans q⟩⟩
  · exact ⟨.E₈, ⟨e₀.trans q⟩⟩
  · exact ⟨.E₇, ⟨e₀.trans q⟩⟩
  · exact ⟨.E₆, ⟨e₀.trans q⟩⟩

-- Theorem 3.5
/-- Theorem 3.5 of [CGSS] (`thm:3.5`): a nonempty line system is indecomposable and star-closed
if and only if it is isomorphic to exactly one of `Aℓ` (`ℓ ≥ 1`), `Dℓ` (`ℓ ≥ 4`), `E₆`, `E₇`,
`E₈`, listed as `RootType`. Steps `s335forward` (`exists_iso_rootType`), `s335reverse` (C4
and `lem:sec3-transport`) and `s335atmost` (`RootType.eq_of_iso`). Each isomorphism is induced
by the surjective linear isometry of spans `Iso.spanIsometry` (`lem:sec3-transport`); the
three `E₈` models give the same type by C3 (`E₈viaA₈.isoE₈`, `E₈viaSteiner.isoE₈`). The space
need not be finite-dimensional, since the span of the finite root set is. -/
theorem classification (S : LineSystem V) (hne : S.Φ.Nonempty) :
    S.IsIndecomposable ∧ S.IsStarClosed ↔ ∃! t : RootType, Nonempty (S.Iso t.model) := by
  constructor
  · rintro ⟨hI, hSC⟩
    obtain ⟨t, ht⟩ := S.exists_iso_rootType hne hI hSC
    refine ⟨t, ht, fun t' ⟨e'⟩ ↦ ?_⟩
    obtain ⟨e⟩ := ht
    exact RootType.eq_of_iso (e'.symm.trans e)
  · rintro ⟨t, ⟨e⟩, _⟩
    exact ⟨e.isIndecomposable_iff.mpr t.isIndecomposable_model,
      e.isStarClosed_iff.mpr t.isStarClosed_model⟩

end LineSystem
