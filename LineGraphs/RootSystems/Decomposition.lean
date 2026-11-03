/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.LineSystem
import LineGraphs.LineSystem.Classification

/-!
# Orthogonal sums of the A/D/E models

Theorem 3.10 of [CGSS], (ii) ↔ (iii), using `LineSystem.classification`
(Theorem 3.5, blueprint `thm:3.5`). Split a decomposable finite root set into two
orthogonal nonempty parts, whose cardinalities decrease, and classify the resulting
indecomposable parts. The empty system is the empty orthogonal sum.

There are no Lamport steps for Theorem 3.10 in the current blueprint. The argument here
expands the reference to Section 2 and Theorem 3.5 in the corrected paper's proof.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The orthogonal sum in Theorem 3.10(iii) of [CGSS]: a finite family of root sets,
each isometric to an A/D/E model, covers the roots, and distinct parts are orthogonal.
The isomorphisms induce linear isometries of spans by `lem:sec3-transport`. -/
def IsOrthogonalSumOfModels (S : LineSystem V) : Prop :=
  ∃ C : Finset (LineSystem V),
    (∀ T ∈ C, ∃ t : RootType, Nonempty (T.Iso t.model)) ∧
    (∀ r, r ∈ S.Φ ↔ ∃ T ∈ C, r ∈ T.Φ) ∧
    (∀ T ∈ C, ∀ U ∈ C, T ≠ U → ∀ r ∈ T.Φ, ∀ s ∈ U.Φ, ⟪r, s⟫ = 0)

/-- A part of an orthogonal partition is closed under negation, for the decomposition
in Theorem 3.10 of [CGSS]. -/
def ofOrthogonalPartition (S : LineSystem V) (A B : Set V) (hab : A ∪ B = S.Φ)
    (horth : ∀ a ∈ A, ∀ b ∈ B, ⟪a, b⟫ = 0) : LineSystem V where
  Φ := A
  finite := S.finite.subset (fun _ h ↦ hab ▸ Or.inl h)
  inner_self r hr := S.inner_self r (hab ▸ Or.inl hr)
  neg_mem r hr := by
    have hrΦ : r ∈ S.Φ := hab ▸ Or.inl hr
    have hneg : -r ∈ A ∪ B := hab ▸ S.neg_mem r hrΦ
    rcases hneg with hneg | hneg
    · exact hneg
    · have hz := horth r hr (-r) hneg
      rw [inner_neg_right, S.inner_self r hrΦ] at hz
      norm_num at hz
  inner_mem r hr s hs := S.inner_mem r (hab ▸ Or.inl hr) s (hab ▸ Or.inl hs)

/-- Orthogonal parts inherit star closure, for Theorem 3.10 of [CGSS]. -/
theorem IsStarClosed.ofOrthogonalPartition {S : LineSystem V} (hS : S.IsStarClosed)
    (A B : Set V) (hab : A ∪ B = S.Φ) (horth : ∀ a ∈ A, ∀ b ∈ B, ⟪a, b⟫ = 0) :
    (S.ofOrthogonalPartition A B hab horth).IsStarClosed := by
  intro r hr s hs hrs
  have hrΦ : r ∈ S.Φ := hab ▸ Or.inl hr
  have hsΦ : s ∈ S.Φ := hab ▸ Or.inl hs
  have hadd : r + s ∈ A ∪ B := hab ▸ hS r hrΦ s hsΦ hrs
  rcases hadd with hadd | hadd
  · exact hadd
  · have hz := horth r hr (r + s) hadd
    rw [inner_add_right, S.inner_self r hrΦ, hrs] at hz
    norm_num at hz

/-- A proper orthogonal part has fewer roots, for the finite decomposition in
Theorem 3.10 of [CGSS]. -/
theorem ncard_lt_of_orthogonal_partition (S : LineSystem V) (A B : Set V)
    (hab : A ∪ B = S.Φ) (horth : ∀ a ∈ A, ∀ b ∈ B, ⟪a, b⟫ = 0)
    (hne : B.Nonempty) : A.ncard < S.Φ.ncard := by
  apply Set.ncard_lt_ncard _ S.finite
  refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ h ↦ hab ▸ Or.inl h, ?_⟩
  intro he
  obtain ⟨b, hb⟩ := hne
  have hbΦ : b ∈ S.Φ := hab ▸ Or.inr hb
  have hz := horth b (he ▸ hbΦ) b hb
  rw [S.inner_self b hbΦ] at hz
  norm_num at hz

/-- Theorem 3.10 of [CGSS], (ii) → (iii): finite orthogonal splitting followed by
Theorem 3.5 (`thm:3.5`, step `s335forward`) classifies every component. -/
theorem IsStarClosed.isOrthogonalSumOfModels {S : LineSystem V} (hS : S.IsStarClosed) :
    S.IsOrthogonalSumOfModels := by
  classical
  induction hn : S.Φ.ncard using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hne : S.Φ.Nonempty
    · by_cases hI : S.IsIndecomposable
      · refine ⟨{S}, ?_, ?_, ?_⟩
        · intro T hT
          simpa only [Finset.mem_singleton.mp hT] using S.exists_iso_rootType hne hI hS
        · intro r
          simp
        · intro T hT U hU hTU
          exact False.elim (hTU ((Finset.mem_singleton.mp hT).trans
            (Finset.mem_singleton.mp hU).symm))
      · simp only [IsIndecomposable, not_forall, not_or] at hI
        obtain ⟨A, B, hab, horth, hA, hB⟩ := hI
        have hba : B ∪ A = S.Φ := (Set.union_comm B A).trans hab
        have horth' : ∀ b ∈ B, ∀ a ∈ A, ⟪b, a⟫ = 0 := by
          intro b hb a ha
          rw [real_inner_comm]
          exact horth a ha b hb
        let T := S.ofOrthogonalPartition A B hab horth
        let U := S.ofOrthogonalPartition B A hba horth'
        have hT : T.Φ.ncard < n := by
          rw [← hn]
          exact S.ncard_lt_of_orthogonal_partition A B hab horth
            (Set.nonempty_iff_ne_empty.mpr hB)
        have hU : U.Φ.ncard < n := by
          rw [← hn]
          exact S.ncard_lt_of_orthogonal_partition B A hba horth'
            (Set.nonempty_iff_ne_empty.mpr hA)
        obtain ⟨C, hC, hc, hoC⟩ := ih _ hT
          (hS.ofOrthogonalPartition A B hab horth) rfl
        obtain ⟨D, hD, hd, hoD⟩ := ih _ hU
          (hS.ofOrthogonalPartition B A hba horth') rfl
        refine ⟨C ∪ D, ?_, ?_, ?_⟩
        · intro R hR
          rcases Finset.mem_union.mp hR with hR | hR
          · exact hC R hR
          · exact hD R hR
        · intro r
          constructor
          · intro hr
            have hr' : r ∈ A ∪ B := hab ▸ hr
            rcases hr' with hr' | hr'
            · obtain ⟨R, hR, hrR⟩ := (hc r).mp hr'
              exact ⟨R, Finset.mem_union_left D hR, hrR⟩
            · obtain ⟨R, hR, hrR⟩ := (hd r).mp hr'
              exact ⟨R, Finset.mem_union_right C hR, hrR⟩
          · rintro ⟨R, hR, hrR⟩
            rcases Finset.mem_union.mp hR with hR | hR
            · exact hab ▸ Or.inl ((hc r).mpr ⟨R, hR, hrR⟩)
            · exact hab ▸ Or.inr ((hd r).mpr ⟨R, hR, hrR⟩)
        · intro R hR R' hR' hRR r hr s hs
          rcases Finset.mem_union.mp hR with hR | hR <;>
            rcases Finset.mem_union.mp hR' with hR' | hR'
          · exact hoC R hR R' hR' hRR r hr s hs
          · exact horth r ((hc r).mpr ⟨R, hR, hr⟩) s ((hd s).mpr ⟨R', hR', hs⟩)
          · exact horth' r ((hd r).mpr ⟨R, hR, hr⟩) s ((hc s).mpr ⟨R', hR', hs⟩)
          · exact hoD R hR R' hR' hRR r hr s hs
    · refine ⟨∅, by simp, ?_, by simp⟩
      intro r
      simp only [Finset.notMem_empty, false_and, exists_false, iff_false]
      exact fun hr ↦ hne ⟨r, hr⟩

/-- Theorem 3.10 of [CGSS], (iii) → (ii): a star cannot meet two orthogonal parts,
and each model is star-closed by C4 (`s335reverse` of `thm:3.5`). -/
theorem IsOrthogonalSumOfModels.isStarClosed {S : LineSystem V}
    (hS : S.IsOrthogonalSumOfModels) : S.IsStarClosed := by
  obtain ⟨C, hC, hc, ho⟩ := hS
  intro r hr s hs hrs
  obtain ⟨T, hT, hrT⟩ := (hc r).mp hr
  obtain ⟨U, hU, hsU⟩ := (hc s).mp hs
  have hTU : T = U := by
    by_contra hn
    have := ho T hT U hU hn r hrT s hsU
    linarith
  subst U
  obtain ⟨t, ⟨e⟩⟩ := hC T hT
  have hTC : T.IsStarClosed := e.isStarClosed_iff.mpr t.isStarClosed_model
  exact (hc (r + s)).mpr ⟨T, hT, hTC r hrT s hsU hrs⟩

/-- Orthogonality extends from roots to their spans in the decomposition of
Theorem 3.10 of [CGSS]. -/
theorem orthogonalFamily_span (C : Finset (LineSystem V))
    (ho : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → ∀ r ∈ T.Φ, ∀ s ∈ U.Φ, ⟪r, s⟫ = 0) :
    OrthogonalFamily ℝ (fun T : C ↦ span ℝ T.val.Φ)
      (fun T ↦ (span ℝ T.val.Φ).subtypeₗᵢ) := by
  intro T U hTU r s
  have hne : T.val ≠ U.val := fun h ↦ hTU (Subtype.ext h)
  have hl : span ℝ T.val.Φ ≤ LinearMap.ker (innerₗ V (s : V)) := by
    apply span_le.mpr
    intro a ha
    have hr : span ℝ U.val.Φ ≤ LinearMap.ker (innerₗ V a) := by
      apply span_le.mpr
      intro b hb
      exact ho T T.property U U.property hne a ha b hb
    change ⟪(s : V), a⟫ = 0
    rw [real_inner_comm]
    exact hr s.property
  change ⟪(r : V), (s : V)⟫ = 0
  rw [real_inner_comm]
  exact hl r.property

/-- Covering the roots makes the component spans cover the whole span in
Theorem 3.10 of [CGSS]. -/
theorem iSup_span_eq_of_root_cover (S : LineSystem V) (C : Finset (LineSystem V))
    (hc : ∀ r, r ∈ S.Φ ↔ ∃ T ∈ C, r ∈ T.Φ) :
    (⨆ T : C, span ℝ T.val.Φ) = span ℝ S.Φ := by
  apply le_antisymm
  · apply iSup_le
    intro T
    exact span_mono (fun r hr ↦ (hc r).mpr ⟨T, T.property, hr⟩)
  · apply span_le.mpr
    intro r hr
    obtain ⟨T, hT, hrT⟩ := (hc r).mp hr
    exact le_iSup (fun U : C ↦ span ℝ U.val.Φ) ⟨T, hT⟩ (subset_span hrT)

open scoped Classical in
/-- The sum in Theorem 3.10(iii) of [CGSS] is an internal direct sum in Mathlib's
sense, with an orthogonal family of component spans. -/
theorem IsOrthogonalSumOfModels.exists_isInternal {S : LineSystem V}
    (hS : S.IsOrthogonalSumOfModels) (hspan : span ℝ S.Φ = ⊤) :
    ∃ C : Finset (LineSystem V),
      (∀ T ∈ C, ∃ t : RootType, Nonempty (T.Iso t.model)) ∧
      (∀ r, r ∈ S.Φ ↔ ∃ T ∈ C, r ∈ T.Φ) ∧
      OrthogonalFamily ℝ (fun T : C ↦ span ℝ T.val.Φ)
        (fun T ↦ (span ℝ T.val.Φ).subtypeₗᵢ) ∧
      DirectSum.IsInternal (fun T : C ↦ span ℝ T.val.Φ) := by
  obtain ⟨C, hC, hc, ho⟩ := hS
  have horth := orthogonalFamily_span C ho
  refine ⟨C, hC, hc, horth, ?_⟩
  apply (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
  exact ⟨horth.independent, (S.iSup_span_eq_of_root_cover C hc).trans hspan⟩

end LineSystem
