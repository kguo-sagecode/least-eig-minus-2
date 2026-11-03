/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.SevenPatterns

/-!
# The local six-cliques

The neighbourhood split `hc:lem:split` of the Hall–Connor blueprint, used in
Remark 5.12 and Example 5.13 of [CGSS].
-/

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable (D : Design P B 15 5 21 7 2)

/-- The family in `hc:def:graph` consists of all six-cliques in Mathlib's sense
([CGSS], Remark 5.12). -/
theorem mem_sixCliques (S : Finset B) : S ∈ D.sixCliques ↔ D.Z.IsNClique 6 S := by
  simp only [sixCliques, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcard, hclique⟩
    exact ⟨fun X hX Y hY hXY ↦ ⟨hXY, hclique X hX Y hY hXY⟩, hcard⟩
  · rintro ⟨hclique, hcard⟩
    exact ⟨hcard, fun X hX Y hY hXY ↦ (hclique hX hY hXY).2⟩

/-- The neighbourhood split and uniqueness through an edge, `hc:lem:split`
(Hall–Connor, Section 5; [CGSS], Remark 5.12 and Example 5.13). -/
theorem exists_sixClique_neighborhood_split {X Y : B} (hXY : D.Z.Adj X Y) :
    ∃ S₁ ∈ D.sixCliques, ∃ S₂ ∈ D.sixCliques,
      X ∈ S₁ ∧ Y ∈ S₁ ∧ S₁ ∩ S₂ = {X} ∧
        S₁ ∪ S₂ = insert X (D.Z.neighborFinset X) ∧
        ∀ K ∈ D.sixCliques, X ∈ K → Y ∈ K → K = S₁ := by
  obtain ⟨Z₁, hZ, htwo⟩ := D.exists_common_neighbor_with_two_neighbors hXY
  have hj := D.localDefect_eq_zero hXY hZ htwo
  let M := D.neighborFiber X Y true true
  let U := D.neighborFiber X Y true false
  let A := M.erase Z₁
  have hz : Z₁ ≠ Y ∧ Z₁ ≠ X ∧ D.Z.Adj X Z₁ ∧ D.Z.Adj Y Z₁ := by
    simpa [neighborFiber, and_assoc] using hZ
  have hM (T : B) (hT : T ∈ M) :
      T ≠ Y ∧ T ≠ X ∧ D.Z.Adj X T ∧ D.Z.Adj Y T := by
    simpa [M, neighborFiber, and_assoc] using hT
  have hMU : Disjoint M U :=
    D.disjoint_neighborFiber X Y (by decide : (true, true) ≠ (true, false))
  have hnX : X ∉ M := by simp [M, neighborFiber]
  have hnY : Y ∉ M := by simp [M, neighborFiber]
  have hnXU : X ∉ U := by simp [U, neighborFiber]
  have hnZU : Z₁ ∉ U := fun hZU ↦ Finset.disjoint_left.mp hMU hZ hZU
  have hMcard : M.card = 5 := (D.card_neighborFiber_of_adj hXY).1
  have hUcard : U.card = 4 := (D.card_neighborFiber_of_adj hXY).2.1
  have hAcard : A.card = 4 := by
    dsimp [A]
    rw [Finset.card_erase_of_mem hZ, hMcard]
  have hnotM (T : B) (hT : T ∈ M) : ¬ D.Z.Adj Z₁ T := by
    intro hZT
    have he : M.filter (D.Z.Adj Z₁) = ∅ := Finset.card_eq_zero.mp
      ((D.local_counts hXY hZ htwo).2.1.trans hj)
    have hm := Finset.mem_filter.mpr ⟨hT, hZT⟩
    rw [he] at hm
    exact Finset.notMem_empty T hm
  have hadjU (T : B) (hT : T ∈ U) : D.Z.Adj Z₁ T := by
    by_contra hn
    have he : U.filter (fun T ↦ ¬ D.Z.Adj Z₁ T) = ∅ := Finset.card_eq_zero.mp hj
    have hm : T ∈ U.filter (fun T ↦ ¬ D.Z.Adj Z₁ T) := Finset.mem_filter.mpr ⟨hT, hn⟩
    rw [he] at hm
    exact Finset.notMem_empty T hm
  have hAclique : D.Z.IsClique (A : Set B) := by
    intro T hT W hW hTW
    obtain ⟨hTZ, hTM⟩ := Finset.mem_erase.mp hT
    obtain ⟨hWZ, hWM⟩ := Finset.mem_erase.mp hW
    have h := D.adj_or_adj_or_adj_of_three_neighbors hz.2.2.1
      (hM T hTM).2.2.1 (hM W hWM).2.2.1 hTZ.symm hWZ.symm hTW
    exact h.resolve_left (hnotM T hTM) |>.resolve_left (hnotM W hWM)
  let S₁ := insert X (insert Y A)
  let S₂ := insert X (insert Z₁ U)
  have hnXA : X ∉ A := fun h ↦ hnX (Finset.mem_erase.mp h).2
  have hnYA : Y ∉ A := fun h ↦ hnY (Finset.mem_erase.mp h).2
  have hS₁card : S₁.card = 6 := by
    simp [S₁, Finset.card_insert_of_notMem, hnXA, hnYA, hXY.ne, hAcard]
  have hS₂card : S₂.card = 6 := by
    simp [S₂, Finset.card_insert_of_notMem, hnXU, hnZU, hz.2.1.symm, hUcard]
  have hS₁clique : D.Z.IsClique (S₁ : Set B) := by
    simp only [S₁, Finset.coe_insert, D.Z.isClique_insert]
    refine ⟨⟨hAclique, fun T hT _ ↦ (hM T (Finset.mem_erase.mp hT).2).2.2.2⟩, ?_⟩
    intro T hT _
    rcases hT with rfl | hT
    · exact hXY
    · exact (hM T (Finset.mem_erase.mp hT).2).2.2.1
  have hS₂clique : D.Z.IsClique (S₂ : Set B) := by
    simp only [S₂, Finset.coe_insert, D.Z.isClique_insert]
    refine ⟨⟨D.isClique_neighborFiber_true_false hXY, fun T hT _ ↦ hadjU T hT⟩, ?_⟩
    intro T hT _
    rcases hT with rfl | hT
    · exact hz.2.2.1
    · have ht : T ≠ Y ∧ T ≠ X ∧ D.Z.Adj X T ∧ ¬ D.Z.Adj Y T := by
        simpa [U, neighborFiber, and_assoc] using hT
      exact ht.2.2.1
  refine ⟨S₁, (D.mem_sixCliques S₁).mpr ⟨hS₁clique, hS₁card⟩,
    S₂, (D.mem_sixCliques S₂).mpr ⟨hS₂clique, hS₂card⟩,
    by simp [S₁], by simp [S₁], ?_, ?_, ?_⟩
  · ext T
    have hdis : T ∈ M → T ∈ U → False := fun hTM hTU ↦
      Finset.disjoint_left.mp hMU hTM hTU
    simp only [S₁, S₂, A, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase,
      Finset.mem_singleton]
    by_cases hTX : T = X
    · simp [hTX]
    by_cases hTY : T = Y
    · subst T
      have hnYU : Y ∉ U := by simp [U, neighborFiber]
      simp [hXY.ne.symm, hz.1.symm, hnYU]
    by_cases hTZ : T = Z₁
    · subst T
      simp [hz.1, hz.2.1]
    tauto
  · rw [D.neighborFinset_eq_fibers hXY]
    ext T
    change T ∈ insert X (insert Y (M.erase Z₁)) ∪ insert X (insert Z₁ U) ↔
      T ∈ insert X (insert Y (M ∪ U))
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    by_cases hTZ : T = Z₁
    · subst T
      have hzM : Z₁ ∈ M := hZ
      simp [hzM]
    tauto
  · intro K hK hXK hYK
    obtain ⟨hKclique, hKcard⟩ := (D.mem_sixCliques K).mp hK
    let L := (K.erase X).erase Y
    have hYL : Y ∈ K.erase X := Finset.mem_erase.mpr ⟨hXY.ne.symm, hYK⟩
    have hLcard : L.card = 4 := by
      simp [L, Finset.card_erase_of_mem hYL, Finset.card_erase_of_mem hXK, hKcard]
    have hLM (T : B) (hT : T ∈ L) : T ∈ M := by
      obtain ⟨hTY, hT⟩ := Finset.mem_erase.mp hT
      obtain ⟨hTX, hTK⟩ := Finset.mem_erase.mp hT
      have hXT := hKclique hXK hTK hTX.symm
      have hYT := hKclique hYK hTK hTY.symm
      simp [M, neighborFiber, hTX, hTY, hXT, hYT]
    have hnZK : Z₁ ∉ K := by
      intro hZK
      have hZL : Z₁ ∈ L := by simp [L, hZK, hz.1, hz.2.1]
      have hpos : 0 < (L.erase Z₁).card := by
        rw [Finset.card_erase_of_mem hZL, hLcard]
        decide
      obtain ⟨T, hT⟩ := Finset.card_pos.mp hpos
      obtain ⟨hTZ, hTL⟩ := Finset.mem_erase.mp hT
      have hTK : T ∈ K := (Finset.mem_erase.mp (Finset.mem_erase.mp hTL).2).2
      exact hnotM T (hLM T hTL) (hKclique hZK hTK hTZ.symm)
    apply Finset.eq_of_subset_of_card_le _ (by omega)
    intro T hTK
    by_cases hTX : T = X
    · simp [S₁, hTX]
    by_cases hTY : T = Y
    · simp [S₁, hTY]
    have hTL : T ∈ L := by simp [L, hTK, hTX, hTY]
    have hTZ : T ≠ Z₁ := by rintro rfl; exact hnZK hTK
    simp [S₁, A, hTZ, hLM T hTL]

end Design
