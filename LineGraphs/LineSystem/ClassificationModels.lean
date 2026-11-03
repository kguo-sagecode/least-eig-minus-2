/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.FivePossibilities
import LineGraphs.LineSystem.RootType
import LineGraphs.Computations.C4

/-!
# The model inputs to the classification

The inputs `input:sec3-models` to Theorem 2.13 of [CGSS] follow from the coordinate
models, their spans, and C4. This discharges Gap 4 without using either classification.
-/

open Submodule Module

namespace LineSystem

/-- The one-line case in `input:sec3-models`, for Theorem 2.13 of [CGSS]. -/
theorem An.exists_eq_pair_one : ∃ r ∈ (An 1).Φ, (An 1).Φ = {r, -r} := by
  obtain ⟨r, hr⟩ := An.Φ_nonempty (n := 1) (by omega)
  refine ⟨r, hr, ?_⟩
  have hcard : (An 1).Φ.ncard = 2 := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr (An.integerModel 1).equiv,
      Nat.card_eq_fintype_card]
    exact card_AnIndex 1
  symm
  apply Set.eq_of_subset_of_ncard_le
  · exact Set.insert_subset hr (Set.singleton_subset_iff.mpr ((An 1).neg_mem r hr))
  · rw [hcard, Set.ncard_pair ((An 1).ne_neg_of_mem hr)]
  · exact (An 1).finite

/-- `input:sec3-models` of the blueprint: the independent Section 3 inputs to
Theorem 2.13 of [CGSS], discharging errata Gap 4. -/
theorem modelInputs : ModelInputs where
  an_one := An.exists_eq_pair_one
  an_rank n _ := finrank_span_An n
  an_lines n _ := numLines_An n
  an_star n hn := ⟨An.hyp24 hn, rfl, ⟨(An.orthGraphIso hn).symm⟩⟩
  dn_rank _ hn := finrank_span_Dn (by omega)
  dn_lines n _ := numLines_Dn n
  dn_star n hn := ⟨Dn.hyp24 hn, rfl, ⟨(Dn.orthGraphIso hn).symm⟩⟩
  e₈ := ⟨E₈.hyp24, rfl, finrank_span_E₈, numLines_E₈,
    E₈.orthGraph_isSRGWith, E₈.card_Δ_div_two⟩
  e₇ := ⟨E₇.hyp24, rfl, finrank_span_E₇, numLines_E₇,
    E₇.orthGraph_isSRGWith, E₇.card_Δ_div_two⟩
  e₆ := ⟨E₆.hyp24, rfl, finrank_span_E₆, numLines_E₆,
    E₆.orthGraph_isSRGWith, E₆.card_Δ_div_two⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

local notation "ℓ" => finrank ℝ V

-- Theorem 2.13
/-- Theorem 2.13 of [CGSS] (`thm:2.13`), with all Section 3 inputs discharged.
The exceptional `Δ` entries count lines, as required by errata Error 6. -/
theorem five_possibilities' (S : LineSystem V) (hNE : S.Φ.Nonempty)
    (hI : S.IsIndecomposable) (hSC : S.IsStarClosed) (hspan : span ℝ S.Φ = ⊤) :
    (Nonempty (S.Iso (An ℓ)) ∧ S.numLines = ℓ * (ℓ + 1) / 2 ∧
      ((ℓ = 1 ∧ S.numLines = 1) ∨
        (2 ≤ ℓ ∧ ∃ H : Hyp24 V, H.S = S ∧
          Nonempty (H.orthGraph ≃g (⊥ : SimpleGraph (Fin (ℓ - 2))))))) ∨
    (4 ≤ ℓ ∧ Nonempty (S.Iso (Dn ℓ)) ∧ S.numLines = ℓ * (ℓ - 1) ∧
      ∃ H : Hyp24 V, H.S = S ∧
        Nonempty (H.orthGraph ≃g SimpleGraph.friendship (ℓ - 3))) ∨
    (ℓ = 8 ∧ Nonempty (S.Iso E₈) ∧ S.numLines = 120 ∧
      ∃ H : Hyp24 V, H.S = S ∧ H.Γa.ncard = 27 ∧ H.Δ.ncard / 2 = 36) ∨
    (ℓ = 7 ∧ Nonempty (S.Iso E₇) ∧ S.numLines = 63 ∧
      ∃ H : Hyp24 V, H.S = S ∧ H.Γa.ncard = 15 ∧ H.Δ.ncard / 2 = 15) ∨
    (ℓ = 6 ∧ Nonempty (S.Iso E₆) ∧ S.numLines = 36 ∧
      ∃ H : Hyp24 V, H.S = S ∧ H.Γa.ncard = 9 ∧ H.Δ.ncard / 2 = 6) :=
  S.five_possibilities modelInputs hNE hI hSC hspan

-- Theorem 2.13
/-- Theorem 2.13 of [CGSS] for an arbitrary star of Hypothesis 2.4. All graph and
cardinality data refer to the supplied star, with no replacement by a specially chosen one.
The one-line case has no star and is covered separately by `five_possibilities'`. -/
theorem five_possibilities_forall_hyp24 (H : Hyp24 V) (hspan : span ℝ H.S.Φ = ⊤) :
    (2 ≤ ℓ ∧ Nonempty (H.S.Iso (An ℓ)) ∧ H.S.numLines = ℓ * (ℓ + 1) / 2 ∧
      Nonempty (H.orthGraph ≃g (⊥ : SimpleGraph (Fin (ℓ - 2))))) ∨
    (4 ≤ ℓ ∧ Nonempty (H.S.Iso (Dn ℓ)) ∧ H.S.numLines = ℓ * (ℓ - 1) ∧
      Nonempty (H.orthGraph ≃g SimpleGraph.friendship (ℓ - 3))) ∨
    (ℓ = 8 ∧ Nonempty (H.S.Iso E₈) ∧ H.S.numLines = 120 ∧
      H.Γa.ncard = 27 ∧ H.Δ.ncard / 2 = 36) ∨
    (ℓ = 7 ∧ Nonempty (H.S.Iso E₇) ∧ H.S.numLines = 63 ∧
      H.Γa.ncard = 15 ∧ H.Δ.ncard / 2 = 15) ∨
    (ℓ = 6 ∧ Nonempty (H.S.Iso E₆) ∧ H.S.numLines = 36 ∧
      H.Γa.ncard = 9 ∧ H.Δ.ncard / 2 = 6) := by
  classical
  -- 213match: the alternatives from Lemma 2.12 are exhaustive.
  rcases H.orthGraph_cases with hX | ⟨m, hm, hX⟩ | hX | hX | hX
  · -- 213A, 213spaniso, 213dimension, 213lines and 213classical.
    obtain ⟨q⟩ := H.nonempty_iso_An_of_orthGraph_eq_bot modelInputs hX
    have hd : ℓ = H.Γa.ncard + 2 :=
      (q.finrank_eq_span_of_span_eq_top hspan).trans (modelInputs.an_rank _ (by omega))
    refine Or.inl ⟨by omega, ?_, ?_, ?_⟩
    · exact Eq.mp (congrArg (fun n ↦ Nonempty (H.S.Iso (An n))) hd.symm) ⟨q⟩
    · rw [hd]
      exact q.numLines_eq.trans (modelInputs.an_lines _ (by omega))
    · let b : H.Γa ≃ Fin (ℓ - 2) := Fintype.equivOfCardEq
        (by simp only [Fintype.card_fin, Set.fintypeCard_eq_ncard, hd]; omega)
      exact ⟨{ b with map_rel_iff' := by intro x y; simp only [hX, SimpleGraph.bot_adj] }⟩
  · -- 213Dsize, 213D and 213classical; `m ≥ 1` gives `ℓ ≥ 4`.
    obtain ⟨q⟩ := H.nonempty_iso_Dn_of_iso_friendship modelInputs hm hX
    have hd : ℓ = m + 3 :=
      (q.finrank_eq_span_of_span_eq_top hspan).trans (modelInputs.dn_rank _ (by omega))
    refine Or.inr (Or.inl ⟨by omega, ?_, ?_, ?_⟩)
    · exact Eq.mp (congrArg (fun n ↦ Nonempty (H.S.Iso (Dn n))) hd.symm) ⟨q⟩
    · rw [hd]
      exact q.numLines_eq.trans (modelInputs.dn_lines _ (by omega))
    · have hidx : m = ℓ - 3 := by omega
      exact Eq.mp
        (congrArg (fun n ↦ Nonempty (H.orthGraph ≃g SimpleGraph.friendship n)) hidx) hX
  · -- 213Echoose, 213E, 213transfer and 213exceptional for `E₆`.
    obtain ⟨M, hM, hr, hl, hY, hΔ⟩ := modelInputs.e₆
    obtain ⟨hd, q, hn, hΓ, hΔ'⟩ := H.exceptional_data_of_isSRGWith M hM hr hl
      hX hY (by norm_num) (by norm_num) hΔ hspan
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hd, q, hn, hΓ, hΔ'⟩)))
  · -- The same steps for `E₇`.
    obtain ⟨M, hM, hr, hl, hY, hΔ⟩ := modelInputs.e₇
    obtain ⟨hd, q, hn, hΓ, hΔ'⟩ := H.exceptional_data_of_isSRGWith M hM hr hl
      hX hY (by norm_num) (by norm_num) hΔ hspan
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd, q, hn, hΓ, hΔ'⟩)))
  · -- The same steps for `E₈`; the list is in the paper's order.
    obtain ⟨M, hM, hr, hl, hY, hΔ⟩ := modelInputs.e₈
    obtain ⟨hd, q, hn, hΓ, hΔ'⟩ := H.exceptional_data_of_isSRGWith M hM hr hl
      hX hY (by norm_num) (by norm_num) hΔ hspan
    exact Or.inr (Or.inr (Or.inl ⟨hd, q, hn, hΓ, hΔ'⟩))

end LineSystem
