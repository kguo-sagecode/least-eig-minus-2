/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.EightVertexModels
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Sublists

/-!
# A local certificate checker for the cubic case of SE4

For `res:414-SE4` (Remark 4.14), fix a vertex and label its neighbours `1,2,3`.
Complete the remaining neighbourhoods in order. Every row has three entries;
symmetry against earlier rows discards incompatible choices immediately.
Only 553 completions remain, instead of searching all labelled graphs.
-/

namespace SimpleGraph

namespace CubicEight

/-- Neighbourhood tables for the local case split in SE4. -/
abbrev Rows := Fin 8 → Finset (Fin 8)

/-- The six cubic models in the order of `res:414-SE4`. -/
def model : Fin 6 → SimpleGraph (Fin 8) :=
  fun i ↦ if i = 0 then twoK4 else if i = 1 then cubeGraph else
    if i = 2 then wagnerGraph else if i = 3 then truncatedK33Graph else
    if i = 4 then twiceTruncatedK4Graph else twoDiamondsGraph

instance (i : Fin 6) : DecidableRel (model i).Adj := by
  unfold model
  split <;> first | infer_instance | (split <;> first | infer_instance |
    (split <;> first | infer_instance | (split <;> first | infer_instance |
      (split <;> infer_instance))))

/-- The earlier neighbours are already forced by symmetry in the SE4 case split. -/
def lowerNeighbors (rows : Rows) (i : Fin 8) : Finset (Fin 8) :=
  ((List.finRange 8).filter (fun j ↦ decide (j < i ∧ i ∈ rows j))).toFinset

/-- Complete a degree-three neighbourhood by choosing only its later neighbours (SE4). -/
def rowChoices (rows : Rows) (i : Fin 8) : List (Finset (Fin 8)) :=
  let lower := lowerNeighbors rows i
  if lower.card ≤ 3 then
    (((List.finRange 8).filter (fun j ↦ decide (i < j))).sublistsLen
      (3 - lower.card)).map (fun t ↦ lower ∪ t.toFinset)
  else []

/-- The forced earlier neighbours and a choice of later neighbours cover every cubic row (SE4). -/
theorem neighborFinset_mem_rowChoices (X : SimpleGraph (Fin 8)) [DecidableRel X.Adj]
    (hr : X.IsRegularOfDegree 3) (rows : Rows) (i : Fin 8)
    (he : ∀ j, j < i → rows j = X.neighborFinset j) :
    X.neighborFinset i ∈ rowChoices rows i := by
  let later := (List.finRange 8).filter (fun j ↦ decide (i < j))
  let t := later.filter (X.Adj i)
  have hl : lowerNeighbors rows i = (X.neighborFinset i).filter (· < i) := by
    ext j
    simp only [lowerNeighbors, List.mem_toFinset, List.mem_filter, List.mem_finRange,
      true_and, decide_eq_true_eq, Finset.mem_filter, mem_neighborFinset]
    constructor
    · rintro ⟨hj, ha⟩
      rw [he j hj, mem_neighborFinset] at ha
      exact ⟨ha.symm, hj⟩
    · rintro ⟨ha, hj⟩
      exact ⟨hj, by simpa [he j hj] using ha.symm⟩
  have ht : t.toFinset = (X.neighborFinset i).filter (i < ·) := by
    ext j
    simp [t, later, and_comm]
  have hu : lowerNeighbors rows i ∪ t.toFinset = X.neighborFinset i := by
    ext j
    simp only [hl, ht, Finset.mem_union, Finset.mem_filter, mem_neighborFinset]
    constructor
    · tauto
    · intro h
      rcases lt_or_gt_of_ne h.ne with hlt | hgt
      · exact Or.inr ⟨h, hlt⟩
      · exact Or.inl ⟨h, hgt⟩
  have hd : Disjoint (lowerNeighbors rows i) t.toFinset := by
    rw [hl, ht, Finset.disjoint_left]
    intro j hj hk
    exact lt_asymm (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
  have hn : t.Nodup := ((List.nodup_finRange 8).filter _).filter _
  have hcard : (lowerNeighbors rows i).card + t.length = 3 := by
    rw [← List.toFinset_card_of_nodup hn, ← Finset.card_union_of_disjoint hd, hu]
    exact hr i
  have hle : (lowerNeighbors rows i).card ≤ 3 := by omega
  simp only [rowChoices, hle, ite_true]
  apply List.mem_map.mpr
  exact ⟨t, List.mem_sublistsLen.mpr ⟨List.filter_sublist, by omega⟩, hu⟩

/-- Symmetry against the rows already assigned in the SE4 case split. -/
def compatible (rows : Rows) (i : Fin 8) (s : Finset (Fin 8)) : Bool :=
  decide (∀ j : Fin 8, j < i → (j ∈ s ↔ i ∈ rows j))

/-- Check a predicate on every completion of the local SE4 neighbourhood table. -/
def checkCompletions (p : Rows → Bool) : List (Fin 8) → Rows → Bool
  | [], rows => p rows
  | i :: rest, rows => (rowChoices rows i).all fun s ↦
      if compatible rows i s then checkCompletions p rest (Function.update rows i s) else true

/-- Completeness of the pruned neighbourhood search for `res:414-SE4`.
The unassigned vertices are increasing, and every assigned row is already correct. -/
theorem checkCompletions_sound (X : SimpleGraph (Fin 8)) [DecidableRel X.Adj]
    (hr : X.IsRegularOfDegree 3) (p : Rows → Bool) (todo : List (Fin 8))
    (hs : todo.Pairwise (· < ·)) (rows : Rows)
    (he : ∀ i, i ∉ todo → rows i = X.neighborFinset i)
    (hc : checkCompletions p todo rows = true) : p (fun i ↦ X.neighborFinset i) = true := by
  induction todo generalizing rows with
  | nil =>
    have hrows : rows = (fun i ↦ X.neighborFinset i) := funext fun i ↦ he i (by simp)
    simpa only [checkCompletions, hrows] using hc
  | cons i rest ih =>
    obtain ⟨hi, hs⟩ := List.pairwise_cons.mp hs
    have earlier (j : Fin 8) (hj : j < i) : j ∉ i :: rest := by
      simp only [List.mem_cons, not_or]
      exact ⟨ne_of_lt hj, fun h ↦ (lt_asymm hj (hi j h))⟩
    have hm : X.neighborFinset i ∈ rowChoices rows i :=
      neighborFinset_mem_rowChoices X hr rows i (fun j hj ↦ he j (earlier j hj))
    have hcompat : compatible rows i (X.neighborFinset i) = true := by
      apply decide_eq_true
      intro j hj
      rw [he j (earlier j hj)]
      simp only [mem_neighborFinset, adj_comm]
    have hnext := List.all_eq_true.mp hc (X.neighborFinset i) hm
    simp only [hcompat, ite_true] at hnext
    apply ih hs (Function.update rows i (X.neighborFinset i)) ?_ hnext
    intro j hj
    by_cases hji : j = i
    · subst j
      simp
    · rw [Function.update_of_ne hji]
      exact he j (by simp [hji, hj])

/-- The fixed first row in the local case split of SE4. -/
def initialRows : Rows := Function.update (fun _ ↦ ∅) 0 {1, 2, 3}

/-- SE4's local search covers every cubic graph with the prescribed first row. -/
theorem checkCompletions_initial_sound (X : SimpleGraph (Fin 8)) [DecidableRel X.Adj]
    (hr : X.IsRegularOfDegree 3) (hzero : X.neighborFinset 0 = {1, 2, 3})
    (p : Rows → Bool)
    (hc : checkCompletions p [1, 2, 3, 4, 5, 6, 7] initialRows = true) :
    p (fun i ↦ X.neighborFinset i) = true := by
  apply checkCompletions_sound X hr p _ (by decide) initialRows ?_ hc
  intro i hi
  have hz : i = 0 := by
    fin_cases i <;> simp_all
  subst i
  simpa [initialRows] using hzero.symm

end CubicEight

end SimpleGraph
