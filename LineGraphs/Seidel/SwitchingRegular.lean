/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.SwitchingDegrees
import LineGraphs.Seidel.SwitchingModels
import LineGraphs.Seidel.CubicEight
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Regular switchings of triangular graphs

The degree reduction in `lem:414-E6` and `lem:414-E8` of Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

variable {n : ℕ} (Z : SimpleGraph (Fin n)) [DecidableRel Z.Adj]

/-- Classical adjacency for the degree arguments in the regular-switching lemmas of 4.14. -/
noncomputable instance switchingRegularDecidableAdj :
    DecidableRel (switchTriangular Z).Adj := Classical.decRel _

/-- Count the switching edges in the complete graph, as in `lem:414-degree`. -/
theorem card_filter_top_edges :
    (Finset.univ.filter fun e : (⊤ : SimpleGraph (Fin n)).edgeSet ↦
      e.val ∈ Z.edgeSet).card = Z.edgeFinset.card := by
  classical
  apply Finset.card_bij (fun e _ ↦ e.val)
  · intro e he
    simpa using (Finset.mem_filter.mp he).2
  · intro e _ f _ h
    exact Subtype.ext h
  · intro e he
    have hz : e ∈ Z.edgeSet := by simpa using he
    exact ⟨⟨e, edgeSet_mono le_top hz⟩, by simp [hz], rfl⟩

/-- The incidence counts in `lem:414-degree` are degrees in the switching graph. -/
theorem card_filter_top_edges_incident (i : Fin n) :
    (Finset.univ.filter fun e : (⊤ : SimpleGraph (Fin n)).edgeSet ↦
      e.val ∈ Z.edgeSet ∧ i ∈ e.val).card = Z.degree i := by
  classical
  rw [← Z.card_incidenceFinset_eq_degree i]
  apply Finset.card_bij (fun e _ ↦ e.val)
  · intro e he
    simpa [incidenceSet] using (Finset.mem_filter.mp he).2
  · intro e _ f _ h
    exact Subtype.ext h
  · intro e he
    have hz : e ∈ Z.edgeSet ∧ i ∈ e := by simpa [incidenceSet] using he
    exact ⟨⟨e, edgeSet_mono le_top hz.1⟩, by simp [hz], rfl⟩

/-- The full triangular switching degree formula, `lem:414-degree` with all vertices. -/
theorem degree_switchTriangular {i j : Fin n} (hij : i ≠ j) :
    ((switchTriangular Z).degree ⟨s(i, j), hij⟩ : ℤ) =
      if Z.Adj i j then
        2 * ((Z.degree i : ℤ) + Z.degree j) - Z.edgeFinset.card - 3 + (n - 2).choose 2
      else 2 * ((n : ℤ) - 2) + Z.edgeFinset.card -
        2 * ((Z.degree i : ℤ) + Z.degree j) := by
  classical
  have h := card_adj_lineGraph_switch_of_complete
    (Y := (⊤ : SimpleGraph (Fin n))) (M := Finset.univ) (by simp)
    {e | e.val ∈ Z.edgeSet} (i := i) (j := j) (by simp) (by simp) hij
  have hK : (⊤ : SimpleGraph (Fin n)).edgeFinsetWithin Finset.univ = Finset.univ := by
    ext e
    simp
  dsimp only at h
  rw [hK] at h
  simp only [← neighborFinset_eq_filter, card_neighborFinset_eq_degree,
    card_filter_top_edges, card_filter_top_edges_incident, Finset.card_univ, Fintype.card_fin,
    Set.mem_ofPred_eq, mem_edgeSet, Nat.cast_add] at h
  refine Eq.trans ?_ h
  congr 1
  unfold degree
  congr 1
  ext f
  simp only [mem_neighborFinset]
  rfl

-- Lemma (regular switchings of T(5)), for Remark 4.14 of [CGSS]
/-- The degree reduction in `lem:414-E6`: a cubic switch of `T(5)` uses a two-regular graph. -/
theorem isRegularOfDegree_two_of_switchTriangular_five
    (Z : SimpleGraph (Fin 5)) [DecidableRel Z.Adj]
    (hr : (switchTriangular Z).IsRegularOfDegree 3) : Z.IsRegularOfDegree 2 := by
  have hp (i j : Fin 5) (hij : i ≠ j) :
      2 * ((Z.degree i : ℤ) + Z.degree j) = Z.edgeFinset.card + 3 := by
    have h := degree_switchTriangular Z hij
    rw [hr] at h
    norm_num [Nat.choose] at h
    split_ifs at h <;> omega
  have hv (i : Fin 5) : 4 * (Z.degree i : ℤ) = Z.edgeFinset.card + 3 := by
    have h := Finset.two_mul_eq_of_forall_add_eq (Finset.univ : Finset (Fin 5))
      (by decide) (fun j ↦ 2 * (Z.degree j : ℤ)) (Z.edgeFinset.card + 3)
      (fun u _ v _ huv ↦ by simpa only [mul_add] using hp u v huv) i (by simp)
    linarith
  have hd : Z.IsRegularOfDegree (Z.degree 0) := by
    intro i
    have hi := hv i
    have h0 := hv 0
    omega
  have hs : 5 * Z.degree 0 = 2 * Z.edgeFinset.card := by
    have hd' (i : Fin 5) : Z.degree i = Z.degree 0 := hd i
    simpa only [hd', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id] using
      Z.sum_degrees_eq_twice_card_edges
  have h0 := hv 0
  have he : Z.degree 0 = 2 := by omega
  simpa only [he] using hd

-- Lemma (regular switchings of T(8)), for Remark 4.14 of [CGSS]
/-- The degree reduction in `lem:414-E8`: a twelve-regular switch of `T(8)` uses a regular graph. -/
theorem exists_isRegularOfDegree_of_switchTriangular_eight
    (Z : SimpleGraph (Fin 8)) [DecidableRel Z.Adj]
    (hr : (switchTriangular Z).IsRegularOfDegree 12) :
    ∃ d ≤ 7, Z.IsRegularOfDegree d := by
  have hp (i j : Fin 8) (hij : i ≠ j) :
      2 * ((Z.degree i : ℤ) + Z.degree j) = Z.edgeFinset.card := by
    have h := degree_switchTriangular Z hij
    rw [hr] at h
    norm_num [Nat.choose] at h
    split_ifs at h <;> omega
  have hv (i : Fin 8) : 4 * (Z.degree i : ℤ) = Z.edgeFinset.card := by
    have h := Finset.two_mul_eq_of_forall_add_eq (Finset.univ : Finset (Fin 8))
      (by decide) (fun j ↦ 2 * (Z.degree j : ℤ)) Z.edgeFinset.card
      (fun u _ v _ huv ↦ by simpa only [mul_add] using hp u v huv) i (by simp)
    linarith
  refine ⟨Z.degree 0, ?_, ?_⟩
  · have h := Z.degree_lt_card_verts 0
    simp only [Fintype.card_fin] at h
    omega
  · intro i
    have hi := hv i
    have h0 := hv 0
    omega

end SimpleGraph
