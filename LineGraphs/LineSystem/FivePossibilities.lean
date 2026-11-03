/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Section2Models

/-! # The five possibilities in [CGSS, Theorem 2.13]

`ModelInputs` records exactly the deferred model data. The proof matches the graph
of a chosen star and transports the numerical data along the reconstructed root isomorphism.
`Iso.exists_ambient_isometry_of_same_model` supplies uniqueness by orthogonal transformations.
-/

open Submodule Module

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

local notation "ℓ" => finrank ℝ V

-- Theorem 2.13
/-- Theorem 2.13 of [CGSS] (`thm:2.13`), with the Section 3 inputs explicit (Gap 4).
A nonempty, indecomposable, star-closed spanning system is isomorphic to one of
the five model families with the displayed rank, line count, and chosen-star data.
Nonemptiness and the separate one-line case implement errata Implicit hypothesis 4.
The signed set `Δ` is divided by two to count lines (Error 6). The isomorphisms to the
named models give uniqueness via `Iso.exists_ambient_isometry_of_same_model`. -/
theorem five_possibilities (S : LineSystem V) (D : ModelInputs)
    (hNE : S.Φ.Nonempty) (hI : S.IsIndecomposable) (hSC : S.IsStarClosed)
    (hspan : span ℝ S.Φ = ⊤) :
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
      ∃ H : Hyp24 V, H.S = S ∧ H.Γa.ncard = 9 ∧ H.Δ.ncard / 2 = 6) := by
  classical
  -- 213numbers and 213samemodel: each branch identifies its named model and transfers
  -- its rank and line count; the ambient-isometry theorem then gives uniqueness.
  rcases hI.eq_pair_or_exists_hyp24 hNE hSC with ⟨r, hr, hΦ⟩ | ⟨H, hHS⟩
  · -- 213one, 213rankone, 213onemap.
    obtain ⟨s, hs, hA⟩ := D.an_one
    have hp := S.finrank_span_numLines_of_eq_pair hr hΦ
    have hd : ℓ = 1 :=
      (LinearIsometryEquiv.ofTop V _ hspan).toLinearEquiv.finrank_eq.symm.trans hp.1
    have q := Iso.ofPairs S (An 1) hr hs hΦ hA
    refine Or.inl ⟨?_, ?_, Or.inl ⟨hd, hp.2⟩⟩
    · exact Eq.mp (congrArg (fun n ↦ Nonempty (S.Iso (An n))) hd.symm) ⟨q⟩
    · norm_num [hd, hp.2]
  · subst S
    -- 213match: the alternatives from Lemma 2.12 are exhaustive.
    rcases H.orthGraph_cases with hX | ⟨m, hm, hX⟩ | hX | hX | hX
    · -- 213A, 213spaniso, 213dimension, 213lines and 213classical.
      obtain ⟨q⟩ := H.nonempty_iso_An_of_orthGraph_eq_bot D hX
      have hd : ℓ = H.Γa.ncard + 2 :=
        (q.finrank_eq_span_of_span_eq_top hspan).trans (D.an_rank _ (by omega))
      refine Or.inl ⟨?_, ?_, Or.inr ⟨by omega, H, rfl, ?_⟩⟩
      · exact Eq.mp (congrArg (fun n ↦ Nonempty (H.S.Iso (An n))) hd.symm) ⟨q⟩
      · rw [hd]
        exact q.numLines_eq.trans (D.an_lines _ (by omega))
      · let b : H.Γa ≃ Fin (ℓ - 2) := Fintype.equivOfCardEq
          (by simp only [Fintype.card_fin, Set.fintypeCard_eq_ncard, hd]; omega)
        exact ⟨{ b with map_rel_iff' := by intro x y; simp only [hX, SimpleGraph.bot_adj] }⟩
    · -- 213Dsize, 213D and 213classical; `m ≥ 1` gives `ℓ ≥ 4`.
      obtain ⟨q⟩ := H.nonempty_iso_Dn_of_iso_friendship D hm hX
      have hd : ℓ = m + 3 :=
        (q.finrank_eq_span_of_span_eq_top hspan).trans (D.dn_rank _ (by omega))
      refine Or.inr (Or.inl ⟨by omega, ?_, ?_, H, rfl, ?_⟩)
      · exact Eq.mp (congrArg (fun n ↦ Nonempty (H.S.Iso (Dn n))) hd.symm) ⟨q⟩
      · rw [hd]
        exact q.numLines_eq.trans (D.dn_lines _ (by omega))
      · have hidx : m = ℓ - 3 := by omega
        exact Eq.mp
          (congrArg (fun n ↦ Nonempty (H.orthGraph ≃g SimpleGraph.friendship n)) hidx) hX
    · -- 213Echoose, 213E, 213transfer and 213exceptional for `E₆`.
      obtain ⟨M, hM, hr, hl, hY, hΔ⟩ := D.e₆
      obtain ⟨hd, q, hn, hΓ, hΔ'⟩ := H.exceptional_data_of_isSRGWith M hM hr hl
        hX hY (by norm_num) (by norm_num) hΔ hspan
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hd, q, hn, H, rfl, hΓ, hΔ'⟩)))
    · -- The same steps for `E₇`.
      obtain ⟨M, hM, hr, hl, hY, hΔ⟩ := D.e₇
      obtain ⟨hd, q, hn, hΓ, hΔ'⟩ := H.exceptional_data_of_isSRGWith M hM hr hl
        hX hY (by norm_num) (by norm_num) hΔ hspan
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd, q, hn, H, rfl, hΓ, hΔ'⟩)))
    · -- The same steps for `E₈`; the list is in the paper's order.
      obtain ⟨M, hM, hr, hl, hY, hΔ⟩ := D.e₈
      obtain ⟨hd, q, hn, hΓ, hΔ'⟩ := H.exceptional_data_of_isSRGWith M hM hr hl
        hX hY (by norm_num) (by norm_num) hΔ hspan
      exact Or.inr (Or.inr (Or.inl ⟨hd, q, hn, H, rfl, hΓ, hΔ'⟩))

/-- Step 213overlap of `thm:2.13` ([CGSS, Theorem 2.13]): the zero-triangle
friendship graph is a singleton, giving `A₃`, dimension three, and six lines.
Thus it is already in the first family, where both classical line-count formulas agree. -/
theorem Hyp24.six_lines_of_iso_friendship_zero (H : Hyp24 V) (D : ModelInputs)
    (hspan : span ℝ H.S.Φ = ⊤)
    (hX : Nonempty (H.orthGraph ≃g SimpleGraph.friendship 0)) :
    ℓ = 3 ∧ H.S.numLines = 6 ∧ Nonempty (H.S.Iso (An 3)) := by
  classical
  obtain ⟨e⟩ := hX
  have hcard : H.Γa.ncard = 1 := by
    have h := Fintype.card_congr e.toEquiv
    simpa only [Set.fintypeCard_eq_ncard, Fintype.card_option, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool, zero_mul, zero_add] using h
  have hbot : H.orthGraph = ⊥ := by
    ext x y
    exact iff_of_false (fun h ↦ (e.map_rel_iff.mpr h).ne (Subsingleton.elim _ _)) (by simp)
  obtain ⟨q⟩ := H.nonempty_iso_An_of_orthGraph_eq_bot D hbot
  have q' : H.S.Iso (An 3) := by
    have hidx : H.Γa.ncard + 2 = 3 := by omega
    exact Eq.mp (congrArg (fun n ↦ H.S.Iso (An n)) hidx) q
  refine ⟨(q'.finrank_eq_span_of_span_eq_top hspan).trans (D.an_rank 3 (by norm_num)),
    ?_, ⟨q'⟩⟩
  have h := q'.numLines_eq.trans (D.an_lines 3 (by norm_num))
  norm_num at h
  exact h

end LineSystem
