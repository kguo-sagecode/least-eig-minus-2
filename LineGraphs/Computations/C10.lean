/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.GeneralizedRepresentation
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Valencies in generalized line graphs

C10 of the Section 4 blueprint for [CGSS], used in Theorem 4.11.
The proof counts neighbours for arbitrary parameters, without a finite cutoff.
-/

open Finset

namespace SimpleGraph

noncomputable local instance decidableAdjDegreeFormula {I : Type*} (G : SimpleGraph I) :
    DecidableRel G.Adj :=
  Classical.decRel _

/-- C10, Section 4 of [CGSS]: count neighbours with a natural-valued indicator sum. -/
theorem degree_eq_sum_indicator {I : Type*} [Fintype I]
    (G : SimpleGraph I) [DecidableRel G.Adj] (u : I) :
    G.degree u = ∑ v, if G.Adj u v then 1 else 0 := by
  simpa using G.degree_eq_sum_if_adj (R := ℕ) u

variable {V : Type*} [Fintype V] [DecidableEq V] (Y : SimpleGraph V)
  [DecidableRel Y.Adj] (a : V → ℕ)

/-- C10, Section 4 of [CGSS]: the edges incident to a vertex are counted by its degree. -/
theorem card_incident_edge_subtype (i : V) :
    Fintype.card {e : Y.edgeSet // i ∈ e.val} = Y.degree i := by
  let e : {e : Y.edgeSet // i ∈ e.val} ≃ Y.incidenceSet i :=
    { toFun := fun e ↦ ⟨e.val.val, e.val.property, e.property⟩
      invFun := fun e ↦ ⟨⟨e.val, e.property.1⟩, e.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Y.card_incidenceSet_eq_degree]

omit [DecidableEq V] in
/-- C10, step `s4c10edge`, of [CGSS]: an edge has the sum of its endpoint
degrees, less two, as its degree in the line graph. -/
theorem lineGraph_degree_mk {i j : V} (hij : Y.Adj i j) :
    Y.lineGraph.degree ⟨s(i, j), hij⟩ + 2 = Y.degree i + Y.degree j := by
  classical
  let e : Y.edgeSet := ⟨s(i, j), hij⟩
  let A : Finset Y.edgeSet := univ.filter (fun f ↦ i ∈ f.val)
  let B : Finset Y.edgeSet := univ.filter (fun f ↦ j ∈ f.val)
  have hA : A.card = Y.degree i := by
    rw [← Y.card_incident_edge_subtype i, Fintype.card_subtype]
  have hB : B.card = Y.degree j := by
    rw [← Y.card_incident_edge_subtype j, Fintype.card_subtype]
  have hAB : A ∩ B = {e} := by
    ext f
    rcases f with ⟨⟨u, v⟩, huv⟩
    simp only [A, B, mem_inter, mem_filter, mem_univ, true_and, Sym2.mem_iff,
      mem_singleton]
    constructor
    · rintro ⟨hi | hi, hj | hj⟩
      · exact (hij.ne (hi.trans hj.symm)).elim
      · apply Subtype.ext
        simp [e, hi, hj]
      · apply Subtype.ext
        simp [e, hi, hj, Sym2.eq_swap]
      · exact (hij.ne (hi.trans hj.symm)).elim
    · intro hf
      have h : s(u, v) = s(i, j) := congrArg Subtype.val hf
      constructor
      · simpa only [← Sym2.mem_iff, h] using (show i ∈ s(i, j) from by simp)
      · simpa only [← Sym2.mem_iff, h] using (show j ∈ s(i, j) from by simp)
  have hN : Y.lineGraph.neighborFinset e = (A ∪ B).erase e := by
    ext f
    simp only [mem_neighborFinset, lineGraph_adj_iff_exists, mem_erase, mem_union,
      A, B, mem_filter, mem_univ, true_and, Sym2.mem_iff, e]
    constructor
    · rintro ⟨hne, k, hk, hkf⟩
      exact ⟨hne.symm, hk.elim (fun h ↦ Or.inl (h ▸ hkf))
        (fun h ↦ Or.inr (h ▸ hkf))⟩
    · rintro ⟨hne, h | h⟩
      · exact ⟨hne.symm, i, Or.inl rfl, h⟩
      · exact ⟨hne.symm, j, Or.inr rfl, h⟩
  have he : e ∈ A ∪ B := by simp [A, e]
  have hc := card_union_add_card_inter A B
  have hec := card_erase_add_one he
  rw [hAB, card_singleton, hA, hB] at hc
  rw [← card_neighborFinset_eq_degree, hN]
  omega

omit [DecidableEq V] in
/-- C10, step `s4c10petal`, of [CGSS]: a signed petal has all incident edges
and both signs of each other petal at its centre as neighbours. -/
theorem generalizedLineGraph_degree_petal (i : V) (k : Fin (a i)) (b : Bool) :
    (generalizedLineGraph Y a).degree (.inr ⟨i, k, b⟩) = 2 * (a i - 1) + Y.degree i := by
  classical
  rw [degree_eq_sum_indicator, Fintype.sum_sum_type]
  have he : (∑ e : Y.edgeSet, if i ∈ e.val then 1 else 0) = Y.degree i := by
    rw [← Y.card_incident_edge_subtype i, Fintype.card_subtype]
    simp only [card_eq_sum_ones, sum_filter]
  have hp : (∑ j : V, ∑ l : Fin (a j) × Bool,
      if i = j ∧ k.val ≠ l.1.val then 1 else 0) = 2 * (a i - 1) := by
    have hsum (j : V) : (∑ l : Fin (a j) × Bool,
        if i = j ∧ k.val ≠ l.1.val then 1 else 0) =
        if i = j then 2 * (a i - 1) else 0 := by
      by_cases h : i = j
      · subst j
        simp only [true_and, ite_true, Fintype.sum_prod_type, Fintype.sum_bool,
          ← two_mul, ne_eq, ← Fin.ext_iff]
        rw [← mul_sum]
        congr 1
        have hc : (univ.filter (fun l : Fin (a i) ↦ k ≠ l)).card = a i - 1 := by
          rw [show univ.filter (fun l : Fin (a i) ↦ k ≠ l) = univ.erase k by
            ext l; simp [eq_comm]]
          simp
        simpa only [card_eq_sum_ones, sum_filter] using hc
      · simp [h]
    simp_rw [hsum]
    simp
  calc
    _ = (∑ e : Y.edgeSet, if i ∈ e.val then 1 else 0) +
        (∑ j : V, ∑ l : Fin (a j) × Bool,
          if i = j ∧ k.val ≠ l.1.val then 1 else 0) := by
      rw [Fintype.sum_sigma]
      congr 1
      · apply sum_congr rfl
        intro e _
        by_cases h : i ∈ e.val <;> simp [generalizedLineGraph, h]
      · apply sum_congr rfl
        intro j _
        apply sum_congr rfl
        intro l _
        by_cases h : i = j ∧ k.val ≠ l.1.val <;> simp [generalizedLineGraph, h]
    _ = _ := by rw [he, hp, Nat.add_comm]

omit [DecidableEq V] in
/-- C10, step `s4c10edge`, of [CGSS]: an edge sees the other incident edges
at both endpoints and the two signed vertices of every petal at either endpoint. -/
theorem generalizedLineGraph_degree_edge {i j : V} (hij : Y.Adj i j) :
    (generalizedLineGraph Y a).degree (.inl ⟨s(i, j), hij⟩) =
      2 * (a i + a j) + Y.degree i + Y.degree j - 2 := by
  classical
  let e : Y.edgeSet := ⟨s(i, j), hij⟩
  have he : (∑ f : Y.edgeSet, if Y.lineGraph.Adj e f then 1 else 0) =
      Y.lineGraph.degree e := (degree_eq_sum_indicator _ _).symm
  have hp : (∑ c : V, ∑ l : Fin (a c) × Bool,
      if c ∈ s(i, j) then 1 else 0) = 2 * (a i + a j) := by
    simp only [sum_ite_irrel, sum_const, card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool, smul_eq_mul, mul_one, mul_zero, Sym2.mem_iff]
    have hsplit (c : V) : (if c = i ∨ c = j then a c * 2 else 0) =
        (if c = i then a c * 2 else 0) + (if c = j then a c * 2 else 0) := by
      by_cases hi : c = i
      · subst c
        simp [hij.ne]
      · by_cases hj : c = j
        · subst c
          simp [hi]
        · simp [hi, hj]
    simp_rw [hsplit, sum_add_distrib]
    simp
    omega
  rw [degree_eq_sum_indicator, Fintype.sum_sum_type]
  calc
    _ = (∑ f : Y.edgeSet, if Y.lineGraph.Adj e f then 1 else 0) +
        (∑ c : V, ∑ l : Fin (a c) × Bool, if c ∈ s(i, j) then 1 else 0) := by
      rw [Fintype.sum_sigma]
      apply congrArg₂ (· + ·)
      · rfl
      · apply sum_congr rfl
        intro c _
        apply sum_congr rfl
        intro l _
        by_cases h : c ∈ s(i, j) <;> simp [generalizedLineGraph, h]
    _ = _ := by
      rw [he, hp]
      have h := Y.lineGraph_degree_mk hij
      change Y.lineGraph.degree e + 2 = _ at h
      omega

end SimpleGraph
