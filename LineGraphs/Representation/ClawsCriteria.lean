/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.ClawsGeneralized
import LineGraphs.Representation.HoffmanRegular

/-!
# Claw-free generalized line graphs

Assertions 1, 2 and 5 of Remark 4.12 of [CGSS], `rem:4.12` in the blueprint.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V]
  (Y : SimpleGraph V) [DecidableRel Y.Adj] (a : V → ℕ)

-- Remark 4.12
/-- The blueprint criterion `rem:4.12`, assertion 2, step `s412two`, supporting
Remark 4.12 of [CGSS] but not stated separately in the paper: claw-freeness is
equivalent to every neighbour of a vertex with petals being an unadorned leaf. -/
theorem generalizedLineGraph_clawFree_iff :
    (generalizedLineGraph Y a).ClawFree ↔
      ∀ i j, 0 < a i → Y.Adj i j → a j = 0 ∧ Y.degree j = 1 := by
  classical
  rw [clawFree_iff_forall_not_isClaw]
  constructor
  · intro h i j hi hij
    have hn : ¬2 ≤ a j + Y.degree j := by
      intro hj
      obtain ⟨T, hT⟩ := (generalizedLineGraph_isClaw_edge_iff Y a hij).mpr
        (Or.inl ⟨hi, hj⟩)
      exact h _ T hT
    have hd := hij.symm.degree_pos_left
    omega
  · rintro h (⟨⟨i, j⟩, hij⟩ | ⟨i, k, b⟩) T hT
    · rcases (generalizedLineGraph_isClaw_edge_iff Y a hij).mp ⟨T, hT⟩ with
        ⟨hi, hj⟩ | ⟨hj, hi⟩
      · obtain ⟨haj, hdj⟩ := h i j hi hij
        dsimp only at hi hj
        omega
      · obtain ⟨hai, hdi⟩ := h j i hj hij.symm
        dsimp only at hi hj
        omega
    · exact generalizedLineGraph_not_isClaw_petal Y a i k b T hT

omit [Fintype V] [DecidableRel Y.Adj] in
-- Remark 4.12
/-- Remark 4.12 of [CGSS], blueprint assertion 5, step `s412five`: a generalized line
graph is four-claw-free exactly when no root edge has petals at both ends. -/
theorem generalizedLineGraph_fourClawFree_iff :
    (generalizedLineGraph Y a).FourClawFree ↔
      ∀ i j, Y.Adj i j → a i = 0 ∨ a j = 0 := by
  classical
  rw [fourClawFree_iff_forall_not_isFourClaw]
  constructor
  · intro h i j hij
    by_contra hn
    have hi : 0 < a i := by omega
    have hj : 0 < a j := by omega
    obtain ⟨T, hT⟩ := (generalizedLineGraph_isFourClaw_edge_iff Y a hij).mpr ⟨hi, hj⟩
    exact h _ T hT
  · rintro h (⟨⟨i, j⟩, hij⟩ | ⟨i, k, b⟩) T hT
    · obtain ⟨hi, hj⟩ := (generalizedLineGraph_isFourClaw_edge_iff Y a hij).mp ⟨T, hT⟩
      dsimp only at hi hj
      rcases h i j hij with hi' | hj' <;> omega
    · obtain ⟨S, _, hS⟩ := hT.exists_subset (l := 3) (by decide)
      exact generalizedLineGraph_not_isClaw_petal Y a i k b S hS

omit [Fintype V] [DecidableRel Y.Adj] in
-- Remark 4.12
/-- Remark 4.12 of [CGSS], blueprint assertion 1, step `s412one`: line graphs are claw-free. -/
theorem lineGraph_clawFree [Finite V] : Y.lineGraph.ClawFree := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply (generalizedLineGraphZeroIso Y).clawFree_iff.mp
  exact (generalizedLineGraph_clawFree_iff Y (fun _ ↦ 0)).mpr (by simp)

-- Remark 4.12
/-- Step `s412one` of Remark 4.12 of [CGSS]: a cocktail party graph is the
generalized line graph of one isolated root vertex. -/
noncomputable def cocktailPartyGeneralizedIso (m : ℕ) :
    cocktailParty m ≃g generalizedLineGraph (⊥ : SimpleGraph (Fin 1)) (fun _ ↦ m) := by
  let f : Fin m × Bool →
      GeneralizedLineGraphVertex (⊥ : SimpleGraph (Fin 1)) (fun _ ↦ m) :=
    fun p ↦ .inr ⟨0, p⟩
  refine { toEquiv := Equiv.ofBijective f ⟨?_, ?_⟩, map_rel_iff' := ?_ }
  · intro p q h
    simpa [f] using h
  · rintro (⟨e, he⟩ | ⟨i, k, b⟩)
    · simp at he
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨(k, b), rfl⟩
  · intro p q
    change (0 = (0 : Fin 1) ∧ p.1.val ≠ q.1.val) ↔ p.1 ≠ q.1
    simp only [true_and, ne_eq, Fin.val_inj]

-- Remark 4.12
/-- Remark 4.12 of [CGSS], blueprint assertion 1, step `s412one`: cocktail party graphs
are claw-free, including the empty graph. -/
theorem cocktailParty_clawFree (m : ℕ) : (cocktailParty m).ClawFree := by
  apply (cocktailPartyGeneralizedIso m).clawFree_iff.mpr
  exact (generalizedLineGraph_clawFree_iff (⊥ : SimpleGraph (Fin 1))
    (fun _ ↦ m)).mpr (by simp)

end SimpleGraph
