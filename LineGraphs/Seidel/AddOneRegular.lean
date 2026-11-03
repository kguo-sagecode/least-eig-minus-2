/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.SwitchingRegular

/-! # The degree reduction for `lem:414-E7` (Remark 4.14) -/

namespace SimpleGraph

variable {n : ℕ} (Z : SimpleGraph (Fin n))

/-- Classical adjacency for the E₇ degree argument of Remark 4.14. -/
noncomputable instance addOneRegularDecidableAdj :
    DecidableRel (switchTriangularAddOne Z).Adj := Classical.decRel _

/-- Adjacency between two ordinary vertices in the E₇ switch (`lem:414-E7`). -/
theorem switchTriangularAddOne_adj_inl (e f : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    (switchTriangularAddOne Z).Adj (Sum.inl e) (Sum.inl f) ↔ (switchTriangular Z).Adj e f := by
  simp [switchTriangularAddOne, triangularAddOne, switchTriangular, switch_adj, SimpleGraph.sum]

/-- The extra vertex is adjacent precisely to the switching edges (`lem:414-E7`). -/
theorem switchTriangularAddOne_adj_inr (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (u : Fin 1) :
    (switchTriangularAddOne Z).Adj (Sum.inl e) (Sum.inr u) ↔ e.val ∈ Z.edgeSet := by
  simp [switchTriangularAddOne, triangularAddOne, switch_adj, SimpleGraph.sum]

/-- The extra vertex contributes one neighbour exactly on the switching set (`lem:414-E7`). -/
theorem degree_switchTriangularAddOne_inl [DecidableRel Z.Adj]
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    (switchTriangularAddOne Z).degree (Sum.inl e) =
      (switchTriangular Z).degree e + if e.val ∈ Z.edgeSet then 1 else 0 := by
  classical
  let f : (switchTriangularAddOne Z).neighborSet (Sum.inl e) ≃
      (switchTriangular Z).neighborSet e ⊕ {u : Fin 1 // e.val ∈ Z.edgeSet} :=
    { toFun := by
        rintro ⟨a | u, h⟩
        · exact Sum.inl ⟨a, (switchTriangularAddOne_adj_inl Z e a).mp h⟩
        · exact Sum.inr ⟨u, (switchTriangularAddOne_adj_inr Z e u).mp h⟩
      invFun := by
        rintro (⟨a, h⟩ | ⟨u, h⟩)
        · exact ⟨Sum.inl a, (switchTriangularAddOne_adj_inl Z e a).mpr h⟩
        · exact ⟨Sum.inr u, (switchTriangularAddOne_adj_inr Z e u).mpr h⟩
      left_inv := by rintro ⟨a | u, h⟩ <;> rfl
      right_inv := by rintro (⟨a, h⟩ | ⟨u, h⟩) <;> rfl }
  rw [← card_neighborSet_eq_degree, Fintype.card_congr f, Fintype.card_sum,
    card_neighborSet_eq_degree]
  by_cases h : e.val ∈ Z.edgeSet <;> simp [h]

/-- The degree of the extra vertex gives the switching-set size (`lem:414-E7`). -/
theorem degree_switchTriangularAddOne_inr [DecidableRel Z.Adj] :
    (switchTriangularAddOne Z).degree (Sum.inr 0) = Z.edgeFinset.card := by
  classical
  let f : (switchTriangularAddOne Z).neighborSet (Sum.inr 0) ≃ Z.edgeSet :=
    { toFun := by
        rintro ⟨a | u, h⟩
        · exact ⟨a.val, (switchTriangularAddOne_adj_inr Z a 0).mp h.symm⟩
        · have hu : u = 0 := Subsingleton.elim _ _
          subst u
          exact False.elim ((switchTriangularAddOne Z).loopless.irrefl _ h)
      invFun := fun a ↦ ⟨Sum.inl ⟨a.val, edgeSet_mono le_top a.property⟩,
        ((switchTriangularAddOne_adj_inr Z _ 0).mpr a.property).symm⟩
      left_inv := by
        rintro ⟨a | u, h⟩
        · rfl
        · have hu : u = 0 := Subsingleton.elim _ _
          subst u
          exact False.elim ((switchTriangularAddOne Z).loopless.irrefl _ h)
      right_inv := by rintro ⟨a, h⟩; rfl }
  rw [← card_neighborSet_eq_degree, Fintype.card_congr f, edgeFinset_card]

-- Lemma (regular switchings of T(6) with an isolated vertex), for Remark 4.14 of [CGSS]
/-- The degree reduction in `lem:414-E7`: the switching graph is two-regular. -/
theorem isRegularOfDegree_two_of_switchTriangularAddOne_six
    (Z : SimpleGraph (Fin 6)) [DecidableRel Z.Adj]
    (hr : (switchTriangularAddOne Z).IsRegularOfDegree 6) : Z.IsRegularOfDegree 2 := by
  have hc : Z.edgeFinset.card = 6 := (degree_switchTriangularAddOne_inr Z).symm.trans (hr _)
  have hp (i j : Fin 6) (hij : i ≠ j) : (Z.degree i : ℤ) + Z.degree j = 4 := by
    have h := degree_switchTriangular Z hij
    have h' := degree_switchTriangularAddOne_inl Z (⟨s(i, j), hij⟩ :
      (⊤ : SimpleGraph (Fin 6)).edgeSet)
    rw [hr] at h'
    simp only [mem_edgeSet] at h'
    norm_num [hc, Nat.choose] at h
    by_cases ha : Z.Adj i j <;> simp only [ha, ite_true, ite_false] at h h' <;> omega
  intro i
  have h := Finset.two_mul_eq_of_forall_add_eq (Finset.univ : Finset (Fin 6))
    (by decide) (fun j ↦ (Z.degree j : ℤ)) 4 (fun u _ v _ huv ↦ hp u v huv) i (by simp)
  omega

end SimpleGraph
