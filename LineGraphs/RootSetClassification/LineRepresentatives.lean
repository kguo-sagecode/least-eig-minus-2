/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.LineCounts
import LineGraphs.RootSetClassification.Projectors

/-!
# Representatives of root lines

The two roots on each line give the reindexing used in `lem:tight-frame`
of Remark 3.11 of [CGSS]. Representatives here are roots; arbitrary unit
representatives are compared with their normalized projectors in `LineFrame`.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Φ : Set V} {I : Type*}

/-- The actual set of root lines in Theorem C of the blueprint for Remark 3.11 of [CGSS]. -/
def rootLines (Φ : Set V) : Set (Submodule ℝ V) := (fun r ↦ ℝ ∙ r) '' Φ

/-- One root from each line, allowing either sign (`rfrsign`). -/
structure RootRepresentatives (Φ : Set V) (r : I → V) : Prop where
  mem : ∀ i, r i ∈ Φ
  covers : ∀ s ∈ Φ, ∃ i, s = r i ∨ s = -r i
  unique : ∀ i j, r i = r j ∨ r i = -r j → i = j

variable (hΦ : IsRootSet Φ) {r : I → V} (hr : RootRepresentatives Φ r)

include hΦ

/-- The two signs of a nonzero root are distinct (`rctlines`). -/
theorem root_ne_neg {s : V} (hs : s ∈ Φ) : s ≠ -s := by
  intro he
  have hz : (2 : ℝ) • s = 0 := by
    simpa only [two_smul] using (add_eq_zero_iff_eq_neg.mpr he)
  exact hΦ.ne_zero hs ((smul_eq_zero.mp hz).resolve_left (by norm_num))

include hr

/-- The oriented root chosen by an index and a sign (`rfrpermute`). -/
def RootRepresentatives.signedRoot (p : I × Bool) : Φ :=
  ⟨if p.2 then -r p.1 else r p.1, by
    split
    · exact hΦ.neg_mem (hr.mem p.1)
    · exact hr.mem p.1⟩

/-- Two signs per line give a bijection onto the full root set (`rctlines`). -/
theorem RootRepresentatives.signedRoot_bijective :
    Function.Bijective (hr.signedRoot hΦ) := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ he
    have hv := congrArg Subtype.val he
    have hij : i = j := by
      apply hr.unique i j
      cases a <;> cases b <;> simp only [signedRoot, Bool.false_eq_true, ↓reduceIte] at hv
      · exact Or.inl hv
      · exact Or.inr hv
      · exact Or.inr (by simpa using congrArg Neg.neg hv)
      · exact Or.inl (neg_injective hv)
    subst j
    congr 1
    cases a <;> cases b
    · rfl
    · exact False.elim (hΦ.root_ne_neg (hr.mem i) hv)
    · exact False.elim (hΦ.root_ne_neg (hr.mem i) hv.symm)
    · rfl
  · intro s
    obtain ⟨i, hi | hi⟩ := hr.covers s s.property
    · exact ⟨(i, false), Subtype.ext hi.symm⟩
    · exact ⟨(i, true), Subtype.ext hi.symm⟩

/-- The sign-pair equivalence used to halve the full root frame (`rfrvalue`). -/
noncomputable def RootRepresentatives.signEquiv : (I × Bool) ≃ Φ :=
  Equiv.ofBijective (hr.signedRoot hΦ) (hr.signedRoot_bijective hΦ)

/-- The number of oriented roots is twice the number of representatives (`rctlines`). -/
theorem RootRepresentatives.card [Fintype I] [Fintype Φ] :
    Fintype.card Φ = 2 * Fintype.card I := by
  simpa only [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using
    (Fintype.card_congr (hr.signEquiv hΦ)).symm

/-- Every representative index is an actual root line (`rCcounts`). -/
noncomputable def RootRepresentatives.lineEquiv : I ≃ rootLines Φ :=
  Equiv.ofBijective (fun i ↦ ⟨ℝ ∙ r i, r i, hr.mem i, rfl⟩) (by
    constructor
    · intro i j he
      apply hr.unique i j
      have he' : ℝ ∙ r i = ℝ ∙ r j := congrArg Subtype.val he
      have hm : r i ∈ ℝ ∙ r j := by
        rw [← he']
        exact mem_span_singleton_self _
      have h := hΦ.roots_on_line (hr.mem j)
      have : r i ∈ ({r j, -r j} : Set V) := h ▸ ⟨hr.mem i, hm⟩
      exact this
    · rintro ⟨L, s, hs, rfl⟩
      obtain ⟨i, hi | hi⟩ := hr.covers s hs
      · exact ⟨i, Subtype.ext (congrArg (fun s ↦ ℝ ∙ s) hi.symm)⟩
      · refine ⟨i, Subtype.ext ?_⟩
        change ℝ ∙ r i = ℝ ∙ s
        rw [hi, ← neg_one_smul ℝ (r i)]
        exact (span_singleton_smul_eq (by norm_num : IsUnit (-1 : ℝ)) (r i)).symm)

/-- The representative count agrees with the half-root convention (`rctlines`). -/
theorem RootRepresentatives.numLines [Fintype I] :
    hΦ.numLines = Fintype.card I := by
  let := hΦ.finite_root_index
  let := Fintype.ofFinite Φ
  rw [IsRootSet.numLines, Set.ncard_eq_toFinset_card', Set.toFinset_card, hr.card hΦ]
  omega

/-- Normalized representatives span the ambient space (`rCsurjective`). -/
theorem RootRepresentatives.span_normalized :
    span ℝ (Set.range (fun i ↦ normalizedRoot (r i))) = ⊤ := by
  apply top_unique
  rw [← hΦ.span_eq_top]
  apply span_le.mpr
  intro s hs
  obtain ⟨i, hi | hi⟩ := hr.covers s hs
  all_goals
    have hn : r i ∈ span ℝ (Set.range (fun i ↦ normalizedRoot (r i))) := by
      have he : r i = ‖r i‖ • normalizedRoot (r i) := by
        simp [normalizedRoot, smul_smul, hΦ.ne_zero (hr.mem i)]
      rw [he]
      exact smul_mem _ _ (subset_span ⟨i, rfl⟩)
  · rw [hi]; exact hn
  · rw [hi]; exact Submodule.neg_mem _ hn

omit hΦ hr

/-- A chosen root on each actual line in Theorem C of the blueprint for Remark 3.11 of [CGSS]. -/
noncomputable def lineRoot (L : rootLines Φ) : V := Classical.choose L.property

/-- The chosen root lies in the root set (`rfrpermute`). -/
theorem lineRoot_mem (L : rootLines Φ) : lineRoot L ∈ Φ :=
  (Classical.choose_spec L.property).1

/-- The chosen root spans the prescribed line (`rfrpermute`). -/
theorem span_lineRoot (L : rootLines Φ) : ℝ ∙ lineRoot L = (L : Submodule ℝ V) :=
  (Classical.choose_spec L.property).2

/-- The actual line set admits root representatives (`lem:tight-frame`). -/
theorem lineRoot_representatives (hΦ : IsRootSet Φ) :
    RootRepresentatives Φ (lineRoot (Φ := Φ)) := by
  refine ⟨lineRoot_mem, ?_, ?_⟩
  · intro s hs
    let L : rootLines Φ := ⟨ℝ ∙ s, s, hs, rfl⟩
    refine ⟨L, ?_⟩
    have hm : s ∈ ℝ ∙ lineRoot L := by
      rw [span_lineRoot]
      exact mem_span_singleton_self s
    have he := hΦ.roots_on_line (lineRoot_mem L)
    change s ∈ ({lineRoot L, -lineRoot L} : Set V)
    rw [← he]
    exact ⟨hs, hm⟩
  · intro L K he
    apply Subtype.ext
    rw [← span_lineRoot L, ← span_lineRoot K]
    rcases he with he | he
    · rw [he]
    · rw [he, ← neg_one_smul ℝ (lineRoot K)]
      exact span_singleton_smul_eq (by norm_num : IsUnit (-1 : ℝ)) _

/-- There are finitely many actual root lines (`rCcounts`). -/
theorem finite_rootLines (hΦ : IsRootSet Φ) : (rootLines Φ).Finite :=
  hΦ.finite.image _

/-- The actual line set has the asserted half-root cardinality (`rctlines`). -/
theorem ncard_rootLines (hΦ : IsRootSet Φ) : (rootLines Φ).ncard = hΦ.numLines := by
  let := (hΦ.finite_rootLines).fintype
  rw [← Set.fintypeCard_eq_ncard]
  exact ((hΦ.lineRoot_representatives).numLines hΦ).symm

-- Remark 3.11
/-- Remark 3.11 of [CGSS]: root representatives exist, indexed by the number of lines,
so the matrix identities quantified over such representatives have witnesses. -/
theorem exists_rootRepresentatives (hΦ : IsRootSet Φ) :
    ∃ r : Fin hΦ.numLines → V, RootRepresentatives Φ r := by
  classical
  let := hΦ.finite_rootLines.fintype
  have hc : Fintype.card (rootLines Φ) = hΦ.numLines :=
    (hΦ.lineRoot_representatives.numLines hΦ).symm
  let e : Fin hΦ.numLines ≃ rootLines Φ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun i => lineRoot (e i), ⟨fun i => lineRoot_mem (e i), ?_, ?_⟩⟩
  · intro s hs
    obtain ⟨i, hi⟩ := hΦ.lineRoot_representatives.covers s hs
    exact ⟨e.symm i, by simpa using hi⟩
  · intro i j h
    exact e.injective (hΦ.lineRoot_representatives.unique _ _ h)

end IsRootSet
