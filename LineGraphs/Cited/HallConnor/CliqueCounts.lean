/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.SixCliques

/-!
# Counting the global six-cliques

The results `hc:cor:unique`, `hc:cor:two`, `hc:lem:seven`, and `hc:lem:clique-meet` of the
Hall–Connor blueprint ([CGSS], Remark 5.12 and Example 5.13).
-/

open scoped BigOperators

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable (D : Design P B 15 5 21 7 2)

/-- The unique six-clique through an edge, `hc:cor:unique` ([CGSS], Remark 5.12). -/
theorem exists_unique_sixClique_of_adj {X Y : B} (hXY : D.Z.Adj X Y) :
    ∃! S : Finset B, S ∈ D.sixCliques ∧ X ∈ S ∧ Y ∈ S := by
  obtain ⟨S, hS, T, hT, hXS, hYS, hmeet, hcover, hunique⟩ :=
    D.exists_sixClique_neighborhood_split hXY
  exact ⟨S, ⟨hS, hXS, hYS⟩, fun K hK ↦ hunique K hK.1 hK.2.1 hK.2.2⟩

/-- Two six-cliques through the same edge agree, `hc:cor:unique` ([CGSS], Remark 5.12). -/
theorem sixClique_eq_of_adj {X Y : B} (hXY : D.Z.Adj X Y)
    {S T : Finset B} (hS : S ∈ D.sixCliques) (hT : T ∈ D.sixCliques)
    (hXS : X ∈ S) (hYS : Y ∈ S) (hXT : X ∈ T) (hYT : Y ∈ T) : S = T :=
  (D.exists_unique_sixClique_of_adj hXY).unique ⟨hS, hXS, hYS⟩ ⟨hT, hXT, hYT⟩

/-- Exactly two six-cliques contain a block, `hc:cor:two` ([CGSS], Remark 5.12). -/
theorem card_sixCliques_through_block (X : B) :
    (D.sixCliques.filter (fun S ↦ X ∈ S)).card = 2 := by
  have hn : (D.Z.neighborFinset X).Nonempty := Finset.card_pos.mp (by
    rw [D.card_neighbors]; decide)
  obtain ⟨Y, hY⟩ := hn
  have hXY := (D.Z.mem_neighborFinset X Y).mp hY
  obtain ⟨S, hS, T, hT, hXS, hYS, hmeet, hcover, hunique⟩ :=
    D.exists_sixClique_neighborhood_split hXY
  have hXT : X ∈ T := by
    have h : X ∈ S ∩ T := by rw [hmeet]; simp
    exact (Finset.mem_inter.mp h).2
  have hST : S ≠ T := by
    intro he
    have hcard := (D.mem_sixCliques S).mp hS |>.card_eq
    rw [← he, Finset.inter_self] at hmeet
    rw [hmeet] at hcard
    simp at hcard
  have hf : D.sixCliques.filter (fun K ↦ X ∈ K) = {S, T} := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hK, hXK⟩
      have hk := (D.mem_sixCliques K).mp hK
      have hpos : 0 < (K.erase X).card := by
        rw [Finset.card_erase_of_mem hXK, hk.card_eq]; decide
      obtain ⟨W, hW⟩ := Finset.card_pos.mp hpos
      obtain ⟨hWX, hWK⟩ := Finset.mem_erase.mp hW
      have hXW := hk.isClique hXK hWK hWX.symm
      have hWU : W ∈ S ∪ T := by
        rw [hcover]
        exact Finset.mem_insert_of_mem ((D.Z.mem_neighborFinset X W).mpr hXW)
      rcases Finset.mem_union.mp hWU with hWS | hWT
      · exact Or.inl (D.sixClique_eq_of_adj hXW hK hS hXK hWK hXS hWS)
      · exact Or.inr (D.sixClique_eq_of_adj hXW hK hT hXK hWK hXT hWT)
    · rintro (rfl | rfl)
      · exact ⟨hS, hXS⟩
      · exact ⟨hT, hXT⟩
  rw [hf]
  simp [hST]

/-- There are seven six-cliques, `hc:lem:seven` ([CGSS], Remark 5.12). -/
theorem card_sixCliques : D.sixCliques.card = 7 := by
  have h := Finset.card_mul_eq_card_mul (fun X (S : Finset B) ↦ X ∈ S)
    (s := Finset.univ) (t := D.sixCliques) (m := 2) (n := 6)
    (fun X _ ↦ D.card_sixCliques_through_block X)
    (fun S hS ↦ by
      simpa [Finset.bipartiteBelow] using ((D.mem_sixCliques S).mp hS).card_eq)
  rw [Finset.card_univ, D.card_blocks] at h
  omega

/-- Distinct six-cliques share at most one block, the first step of
`hc:lem:clique-meet` ([CGSS], Remark 5.12). -/
theorem sixClique_inter_card_le_one {S T : Finset B}
    (hS : S ∈ D.sixCliques) (hT : T ∈ D.sixCliques) (hST : S ≠ T) :
    (S ∩ T).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro X hX Y hY
  by_contra hXY
  obtain ⟨hXS, hXT⟩ := Finset.mem_inter.mp hX
  obtain ⟨hYS, hYT⟩ := Finset.mem_inter.mp hY
  have hadj := ((D.mem_sixCliques S).mp hS).isClique hXS hYS hXY
  exact hST (D.sixClique_eq_of_adj hadj hS hT hXS hYS hXT hYT)

/-- A fixed six-clique has six intersections with the other six-cliques,
counted with multiplicity (`hc:lem:clique-meet`; [CGSS], Remark 5.12). -/
theorem sum_sixClique_inter_card {S : Finset B} (hS : S ∈ D.sixCliques) :
    (∑ T ∈ D.sixCliques.erase S, (S ∩ T).card) = 6 := by
  have hcount (X : B) (hXS : X ∈ S) :
      ((D.sixCliques.erase S).filter (fun T ↦ X ∈ T)).card = 1 := by
    rw [Finset.filter_erase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hS, hXS⟩),
      D.card_sixCliques_through_block]
  have hswap := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun X (T : Finset B) ↦ X ∈ T) (s := S) (t := D.sixCliques.erase S)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hswap
  have hleft : (∑ X ∈ S,
      ((D.sixCliques.erase S).filter (fun T ↦ X ∈ T)).card) = 6 := by
    calc
      _ = ∑ _ ∈ S, 1 := Finset.sum_congr rfl hcount
      _ = 6 := by simpa using ((D.mem_sixCliques S).mp hS).card_eq
  rw [hleft] at hswap
  convert hswap.symm using 1
  apply Finset.sum_congr rfl
  intro T _
  congr 1

/-- Any two distinct six-cliques meet in one block, `hc:lem:clique-meet`
([CGSS], Remark 5.12). -/
theorem sixClique_inter_card {S T : Finset B}
    (hS : S ∈ D.sixCliques) (hT : T ∈ D.sixCliques) (hST : S ≠ T) :
    (S ∩ T).card = 1 := by
  have heq : (∑ U ∈ D.sixCliques.erase S, (S ∩ U).card) =
      ∑ _ ∈ D.sixCliques.erase S, 1 := by
    rw [D.sum_sixClique_inter_card hS]
    simp [Finset.card_erase_of_mem hS, D.card_sixCliques]
  have hpoint := (Finset.sum_eq_sum_iff_of_le (fun U hU ↦
    D.sixClique_inter_card_le_one hS (Finset.mem_erase.mp hU).2
      (Finset.mem_erase.mp hU).1.symm)).mp heq
  exact hpoint T (Finset.mem_erase.mpr ⟨hST.symm, hT⟩)

end Design
