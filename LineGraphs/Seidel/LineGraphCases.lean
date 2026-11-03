/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.LineGraphCounts
import LineGraphs.Seidel.LineGraphRecognition
import LineGraphs.Seidel.Parameters
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Strongly regular line graphs

Lemma LG1 (`lem:4-LG1`) of the blueprint for Theorem 4.13 of [CGSS].
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] {Y : SimpleGraph V}
  [DecidableRel Y.Adj] {n k a c d : ℕ}

noncomputable local instance lineGraphCasesDecidableAdj : DecidableRel Y.lineGraph.Adj :=
  Classical.decRel _

/-- Step `s4lgcommon` of Lemma LG1, Theorem 4.13 of [CGSS], with the
adjacent-pair parameter substituted into the common-neighbour count. -/
theorem IsSRGWith.degree_sub_two_add_eq_of_lineGraph (h : Y.lineGraph.IsSRGWith n k a c)
    {i j l : V} (hij : Y.Adj i j) (hil : Y.Adj i l) (hjl : j ≠ l) :
    Y.degree i - 2 + (if Y.Adj j l then 1 else 0) = a := by
  classical
  have he : s(i, j) ≠ s(i, l) := by simp [hjl, hil.ne]
  have ha := (lineGraph_adj_mk_iff hij hil).mpr ⟨he, Or.inl rfl⟩
  rw [← card_commonNeighbors_lineGraph_of_adj hij hil hjl]
  exact h.of_adj _ _ ha

/-- Step `s4lgKn` of Lemma LG1, Theorem 4.13 of [CGSS]: a regular root
graph containing a triangle is complete. -/
theorem IsSRGWith.eq_top_of_lineGraph_of_triangle (h : Y.lineGraph.IsSRGWith n k a c)
    (hr : Y.IsRegularOfDegree d) (hc : Y.Connected)
    {i j l : V} (hij : Y.Adj i j) (hil : Y.Adj i l) (hjl : Y.Adj j l) : Y = ⊤ := by
  classical
  have ha := h.degree_sub_two_add_eq_of_lineGraph hij hil hjl.ne
  simp only [hr i, hjl, ite_true] at ha
  apply hc.eq_top_of_adj_of_common_neighbor
  intro u v w huv huw hvw
  have hb := h.degree_sub_two_add_eq_of_lineGraph huv huw hvw
  rw [hr u] at hb
  by_contra hn
  simp only [hn, ite_false, add_zero] at hb
  omega

/-- Step `s4lgdisj` of Lemma LG1, Theorem 4.13 of [CGSS]: in the
triangle-free case every disjoint pair has at most two common neighbours. -/
theorem IsSRGWith.nonadjacent_param_le_two_of_lineGraph
    (h : Y.lineGraph.IsSRGWith n k a c)
    (ht : ∀ ⦃i j l⦄, Y.Adj i j → Y.Adj i l → ¬ Y.Adj j l)
    {i j l m : V} (hij : Y.Adj i j) (hlm : Y.Adj l m)
    (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m) : c ≤ 2 := by
  classical
  have he : s(i, j) ≠ s(l, m) := by simp [hil, him]
  have hne : (⟨s(i, j), hij⟩ : Y.edgeSet) ≠ ⟨s(l, m), hlm⟩ :=
    fun heq ↦ he (congrArg Subtype.val heq)
  have hna : ¬Y.lineGraph.Adj ⟨s(i, j), hij⟩ ⟨s(l, m), hlm⟩ := by
    simp [lineGraph_adj_mk_iff, hil, him, hjl, hjm]
  have hc := h.of_not_adj hne hna
  rw [card_commonNeighbors_lineGraph_of_disjoint hij hlm hil him hjl hjm] at hc
  have hi : ¬(Y.Adj i l ∧ Y.Adj i m) := fun hh ↦ ht hh.1 hh.2 hlm
  have hj : ¬(Y.Adj j l ∧ Y.Adj j m) := fun hh ↦ ht hh.1 hh.2 hlm
  split_ifs at hc <;> grind only

/-- Step `s4lgdisj` of Lemma LG1, Theorem 4.13 of [CGSS]: every edge of
a triangle-free regular graph of degree at least two has a disjoint edge. -/
theorem IsRegularOfDegree.exists_disjoint_edge_of_triangle_free
    (hr : Y.IsRegularOfDegree d) (hd : 2 ≤ d)
    (ht : ∀ ⦃i j l⦄, Y.Adj i j → Y.Adj i l → ¬ Y.Adj j l)
    {i j : V} (hij : Y.Adj i j) :
    ∃ l m, Y.Adj l m ∧ i ≠ l ∧ i ≠ m ∧ j ≠ l ∧ j ≠ m := by
  obtain ⟨l, hil, hlj⟩ := (Y.neighborFinset i).exists_mem_ne
    (by rw [card_neighborFinset_eq_degree, hr i]; omega) j
  obtain ⟨m, hlm, hmi⟩ := (Y.neighborFinset l).exists_mem_ne
    (by rw [card_neighborFinset_eq_degree, hr l]; omega) i
  rw [mem_neighborFinset] at hil hlm
  refine ⟨l, m, hlm, hil.ne, hmi.symm, hlj.symm, ?_⟩
  rintro rfl
  exact ht hij hil hlm.symm

/-- Steps `s4lgc0` and `s4lgc1` of Lemma LG1, Theorem 4.13 of [CGSS]:
the triangle-free regular case of degree at least three has `c = 2`.
The exclusion of `c = 1` uses the SRG parameter equation and the degree sum. -/
theorem IsSRGWith.nonadjacent_param_eq_two_of_lineGraph
    (h : Y.lineGraph.IsSRGWith n k a c) (hr : Y.IsRegularOfDegree d) (hd : 3 ≤ d)
    (hc : Y.Connected) (hedge : Y.edgeSet.Nonempty)
    (ht : ∀ ⦃i j l⦄, Y.Adj i j → Y.Adj i l → ¬ Y.Adj j l) : c = 2 := by
  classical
  obtain ⟨⟨i, j⟩, hij⟩ := hedge
  obtain ⟨l, m, hlm, hil, him, hjl, hjm⟩ :=
    hr.exists_disjoint_edge_of_triangle_free (by omega) ht hij
  have hle := h.nonadjacent_param_le_two_of_lineGraph ht hij hlm hil him hjl hjm
  have hconn : Y.lineGraph.Connected :=
    (lineGraph_connected_iff_of_no_isolated ⟨s(i, j), hij⟩ fun v ↦
      (Y.degree_pos_iff_exists_adj v).mp (by rw [hr v]; omega)).mpr hc
  have hnontop : Y.lineGraph ≠ ⊤ := by
    intro he
    have hne : (⟨s(i, j), hij⟩ : Y.edgeSet) ≠ ⟨s(l, m), hlm⟩ := by
      intro heq
      have heq' := congrArg Subtype.val heq
      simp [hil, him] at heq'
    have hadj : Y.lineGraph.Adj ⟨s(i, j), hij⟩ ⟨s(l, m), hlm⟩ := by
      rw [he]
      exact hne
    have ha := (lineGraph_adj_mk_iff hij hlm).mp hadj
    tauto
  have hpos := h.pos_of_connected_of_ne_top hconn hnontop
  by_contra htwo
  have hc1 : c = 1 := by omega
  have hk : k + 2 = 2 * d := by
    have he := degree_lineGraph hij
    rw [h.regular _, hr i, hr j] at he
    omega
  obtain ⟨t, hit, htj⟩ := (Y.neighborFinset i).exists_mem_ne
    (by rw [card_neighborFinset_eq_degree, hr i]; omega) j
  rw [mem_neighborFinset] at hit
  have ha := h.degree_sub_two_add_eq_of_lineGraph hij hit htj.symm
  have hnt := ht hij hit
  simp only [hr i, hnt, ite_false, add_zero] at ha
  have hn : k < n := by
    have he := Y.lineGraph.degree_lt_card_verts ⟨s(i, j), hij⟩
    rwa [h.regular _, h.card] at he
  have hp := h.param_eq Y.lineGraph (by omega)
  rw [hc1, mul_one] at hp
  have hsub : k - a - 1 = d - 1 := by omega
  rw [hsub] at hp
  have hsum : Fintype.card V * d = 2 * n := by
    have he := Y.sum_degrees_eq_twice_card_edges
    simpa only [hr.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← card_edgeSet, h.card] using he
  have hd1 : d - 1 + 1 = d := by omega
  have hn1 : n - k - 1 + k + 1 = n := by omega
  by_cases hv : Fintype.card V ≤ 4 * d - 4
  · have hh := Nat.mul_le_mul_right d hv
    have hd4 : 4 * d - 4 + 4 = 4 * d := by omega
    nlinarith
  · have hh := Nat.mul_le_mul_right d (show 4 * d - 3 ≤ Fintype.card V by omega)
    have hd4 : 4 * d - 3 + 3 = 4 * d := by omega
    nlinarith

/-- Step `s4lgc2` of Lemma LG1, Theorem 4.13 of [CGSS]: the two
neighbourhoods of an edge give a complete bipartite graph. Degree exhaustion
and connectedness show that this subgraph contains every vertex. -/
theorem IsSRGWith.nonempty_iso_completeBipartite_of_lineGraph
    (h : Y.lineGraph.IsSRGWith n k a 2) (hr : Y.IsRegularOfDegree d)
    (hc : Y.Connected) (hedge : Y.edgeSet.Nonempty)
    (ht : ∀ ⦃i j l⦄, Y.Adj i j → Y.Adj i l → ¬ Y.Adj j l) :
    Nonempty (Y ≃g completeBipartiteGraph (Fin d) (Fin d)) := by
  classical
  obtain ⟨⟨i, j⟩, hij⟩ := hedge
  have hcross {u v : V} (hju : Y.Adj j u) (hiv : Y.Adj i v) : Y.Adj u v := by
    by_cases hui : u = i
    · simpa only [hui] using hiv
    by_cases hvj : v = j
    · simpa only [hvj] using hju.symm
    have huv : u ≠ v := by
      rintro rfl
      exact ht hij hiv hju
    have he : (⟨s(j, u), hju⟩ : Y.edgeSet) ≠ ⟨s(i, v), hiv⟩ := by
      intro heq
      have heq' := congrArg Subtype.val heq
      simp [hij.ne.symm, Ne.symm hvj] at heq'
    have hna : ¬Y.lineGraph.Adj ⟨s(j, u), hju⟩ ⟨s(i, v), hiv⟩ := by
      intro ha
      have he' := (lineGraph_adj_mk_iff hju hiv).mp ha
      exact he'.2.elim hij.ne.symm
        (fun he ↦ he.elim (Ne.symm hvj) (fun he ↦ he.elim hui huv))
    have heq := h.of_not_adj he hna
    rw [card_commonNeighbors_lineGraph_of_disjoint hju hiv hij.ne.symm (Ne.symm hvj) hui huv]
      at heq
    have hjv := ht hij hiv
    have hui' := ht hij.symm hju
    have hnu : ¬Y.Adj u i := fun hu ↦ hui' hu.symm
    by_contra hn
    simp [hij.symm, hjv, hnu, hn] at heq
  let P := Y.neighborSet j
  let Q := Y.neighborSet i
  let K := completeBipartiteGraph P Q
  have hP : Fintype.card P = d := (Y.card_neighborSet_eq_degree j).trans (hr j)
  have hQ : Fintype.card Q = d := (Y.card_neighborSet_eq_degree i).trans (hr i)
  let f : K →g Y :=
    { toFun := Sum.elim Subtype.val Subtype.val
      map_rel' := by
        rintro (u | u) (v | v) ha
        · simp [K, completeBipartiteGraph] at ha
        · exact hcross u.property v.property
        · exact (hcross v.property u.property).symm
        · simp [K, completeBipartiteGraph] at ha }
  have hf : Function.Injective f := by
    rintro (u | u) (v | v) he
    · exact congrArg Sum.inl (Subtype.ext he)
    · change (u : V) = (v : V) at he
      have hv : Y.Adj i u := he.symm ▸ v.property
      exact (ht hij hv u.property).elim
    · change (u : V) = (v : V) at he
      have hu : Y.Adj i v := he ▸ u.property
      exact (ht hij hu v.property).elim
    · exact congrArg Sum.inr (Subtype.ext he)
  have hK : K.IsRegularOfDegree d := by
    intro v
    rw [← card_neighborSet_eq_degree]
    change Fintype.card {w // K.Adj v w} = d
    rw [Fintype.card_congr (@Equiv.subtypeSum P Q (fun w ↦ K.Adj v w)), Fintype.card_sum]
    cases v with
    | inl _ => simpa [K, completeBipartiteGraph] using hQ
    | inr _ => simpa [K, completeBipartiteGraph] using hP
  let : Nonempty (P ⊕ Q) := ⟨Sum.inl ⟨i, hij.symm⟩⟩
  obtain ⟨e⟩ := hK.nonempty_iso_of_injective_hom_of_connected hr f hf hc
  exact ⟨e.symm.trans (completeBipartiteGraphCongr
    (Fintype.equivOfCardEq (by simpa using hP)) (Fintype.equivOfCardEq (by simpa using hQ)))⟩

-- Lemma LG1 (Theorem 4.13)
/-- Lemma `lem:4-LG1`, Theorem 4.13 of [CGSS]: a finite connected graph
with an edge and strongly regular line graph is a cycle, a complete graph,
a balanced complete bipartite graph, or a star. -/
theorem lineGraph_isSRGWith_cases (hc : Y.Connected) (hedge : Y.edgeSet.Nonempty)
    (h : Y.lineGraph.IsSRGWith n k a c) :
    (∃ m, 3 ≤ m ∧ Nonempty (Y ≃g cycleGraph m)) ∨
    (∃ m, 2 ≤ m ∧ Nonempty (Y ≃g completeGraph (Fin m))) ∨
    (∃ m, 1 ≤ m ∧ Nonempty (Y ≃g completeBipartiteGraph (Fin m) (Fin m))) ∨
    (∃ m, 1 ≤ m ∧ Nonempty (Y ≃g completeBipartiteGraph (Fin 1) (Fin m))) := by
  classical
  obtain ⟨⟨i, j⟩, hij⟩ := hedge
  let : Nontrivial V := nontrivial_of_ne i j hij.ne
  have hno : ∀ v, 0 < Y.degree v := fun v ↦ hc.preconnected.degree_pos_of_nontrivial v
  have hconn : Y.lineGraph.Connected :=
    (lineGraph_connected_iff_of_no_isolated ⟨s(i, j), hij⟩ fun v ↦
      (Y.degree_pos_iff_exists_adj v).mp (hno v)).mpr hc
  rcases regular_or_semiregular_of_lineGraph_regular ⟨s(i, j), hij⟩ hno hconn h.regular with
    ⟨d, hr⟩ | ⟨P, Q, p, q, hb, hP, hQ, hp, hq, hpq, _⟩
  · by_cases hd1 : d = 1
    · have he := hc.nonempty_iso_completeBipartite_of_neighbor_degree_one i
        (fun v _ ↦ (hr v).trans hd1)
      rw [hr i, hd1] at he
      exact Or.inr (Or.inr (Or.inr ⟨1, le_rfl, he⟩))
    by_cases hd2 : d = 2
    · refine Or.inl ⟨Fintype.card V, ?_, (hd2 ▸ hr).nonempty_iso_cycle hc⟩
      have hi := Y.degree_lt_card_verts i
      rw [hr i, hd2] at hi
      omega
    have hd : 3 ≤ d := by have hi := hno i; rw [hr i] at hi; omega
    by_cases htri : ∃ u v w, Y.Adj u v ∧ Y.Adj u w ∧ Y.Adj v w
    · obtain ⟨u, v, w, huv, huw, hvw⟩ := htri
      have htop := h.eq_top_of_lineGraph_of_triangle hr hc huv huw hvw
      refine Or.inr (Or.inl ⟨Fintype.card V, ?_, ?_⟩)
      · have hi := Y.degree_lt_card_verts i
        rw [hr i] at hi
        omega
      · rw [htop]
        exact ⟨Iso.completeGraph (Fintype.equivFin V)⟩
    have ht : ∀ ⦃u v w⦄, Y.Adj u v → Y.Adj u w → ¬Y.Adj v w :=
      fun {u v w} huv huw hvw ↦ htri ⟨u, v, w, huv, huw, hvw⟩
    have hc2 := h.nonadjacent_param_eq_two_of_lineGraph hr hd hc ⟨s(i, j), hij⟩ ht
    exact Or.inr (Or.inr (Or.inl ⟨d, by omega,
      (hc2 ▸ h).nonempty_iso_completeBipartite_of_lineGraph hr hc ⟨s(i, j), hij⟩ ht⟩))
  · have ht : ∀ ⦃u v w⦄, Y.Adj u v → Y.Adj u w → ¬Y.Adj v w := by
      intro u v w huv huw hvw
      rcases hb.isBipartiteWith.mem_of_adj huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact Set.disjoint_left.mp hb.isBipartiteWith.disjoint
          (hb.isBipartiteWith.symm.mem_of_mem_adj hv hvw)
          (hb.isBipartiteWith.mem_of_mem_adj hu huw)
      · exact Set.disjoint_left.mp hb.isBipartiteWith.disjoint
          (hb.isBipartiteWith.symm.mem_of_mem_adj hu huw)
          (hb.isBipartiteWith.mem_of_mem_adj hv hvw)
    have hdeg (u : V) (hu : 2 ≤ Y.degree u) : a + 2 = Y.degree u := by
      obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp
        (show 1 < (Y.neighborFinset u).card by rw [card_neighborFinset_eq_degree]; omega)
      rw [mem_neighborFinset] at hv hw
      have he := h.degree_sub_two_add_eq_of_lineGraph hv hw hvw
      have hn := ht hv hw
      simp only [hn, ite_false, add_zero] at he
      omega
    have hone : p = 1 ∨ q = 1 := by
      by_contra hn
      obtain ⟨u, hu⟩ := hP
      obtain ⟨v, hv⟩ := hQ
      have he := hdeg u (by rw [hb.degree_left u hu]; omega)
      have hf := hdeg v (by rw [hb.degree_right v hv]; omega)
      rw [hb.degree_left u hu] at he
      rw [hb.degree_right v hv] at hf
      omega
    apply Or.inr ∘ Or.inr ∘ Or.inr
    rcases hone with hp1 | hq1
    · obtain ⟨v, hv⟩ := hQ
      refine ⟨q, hq, ?_⟩
      have he := hc.nonempty_iso_completeBipartite_of_neighbor_degree_one v
        (fun w hw ↦ (hb.degree_left w (hb.isBipartiteWith.symm.mem_of_mem_adj hv hw)).trans
          hp1)
      rwa [hb.degree_right v hv] at he
    · obtain ⟨v, hv⟩ := hP
      refine ⟨p, hp, ?_⟩
      have he := hc.nonempty_iso_completeBipartite_of_neighbor_degree_one v
        (fun w hw ↦ (hb.degree_right w (hb.isBipartiteWith.mem_of_mem_adj hv hw)).trans hq1)
      rwa [hb.degree_left v hv] at he

end SimpleGraph
