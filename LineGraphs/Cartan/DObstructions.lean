/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Affine
import LineGraphs.Cartan.ThreeArmLabelling

/-!
# D obstructions in trees

The high-degree and two-branch exclusions in `lem:unweighted-trees`.
-/

namespace SimpleGraph

open Walk

variable {V : Type*} {X : SimpleGraph V} {u v : V}

/-- A simple path with four distinct external leaves gives an affine D subgraph. -/
theorem Walk.IsPath.smithD_copy {p : X.Walk u v} (hp : p.IsPath)
    (l : Fin 4 → V) (hinj : Function.Injective l)
    (hoff : ∀ j, l j ∉ p.support)
    (hadj : ∀ j, X.Adj (if j.val < 2 then u else v) (l j)) :
    Nonempty (Copy (smithD (p.length + 4)) X) := by
  classical
  simp only [smithD, WeightedGraph.affineD]
  let f : Fin (p.length + 1) ⊕ Fin 4 → V := Sum.elim (fun i => p.getVert i.val) l
  refine ⟨⟨{ toFun := f, map_rel' := ?_ }, ?_⟩⟩
  · rintro (i | i) (j | j) hij
    · change (WeightedGraph.path (p.length + 1) (fun _ => 1)
        (by intro _; norm_num)).support.Adj i j at hij
      rw [WeightedGraph.support_path _ _ _ (by intro _ _; norm_num)] at hij
      change X.Adj (p.getVert i.val) (p.getVert j.val)
      rcases pathGraph_adj.mp hij with hij | hji
      · simpa only [hij] using p.adj_getVert_succ (i := i.val) (by omega)
      · simpa only [hji] using (p.adj_getVert_succ (i := j.val) (by omega)).symm
    · change (0 : ℝ) < (if i = (if j.val < 2 then 0 else Fin.last p.length) then 1 else 0) at hij
      have hi : i = if j.val < 2 then 0 else Fin.last p.length := by
        by_contra hn
        rw [ite_eq_right hn] at hij
        norm_num at hij
      change X.Adj (p.getVert i.val) (l j)
      rw [hi]
      split_ifs with hj
      · simpa [hj] using hadj j
      · simpa [hj] using hadj j
    · change (0 : ℝ) < (if j = (if i.val < 2 then 0 else Fin.last p.length) then 1 else 0) at hij
      have hj : j = if i.val < 2 then 0 else Fin.last p.length := by
        by_contra hn
        rw [ite_eq_right hn] at hij
        norm_num at hij
      change X.Adj (l i) (p.getVert j.val)
      rw [hj]
      split_ifs with hi
      · simpa [hi] using (hadj i).symm
      · simpa [hi] using (hadj i).symm
    · exact (lt_irrefl (0 : ℝ) hij).elim
  · rintro (i | i) (j | j) hij
    · congr 1
      exact Fin.ext (hp.getVert_injOn (by change i.val ≤ p.length; omega)
        (by change j.val ≤ p.length; omega) hij)
    · change p.getVert i.val = l j at hij
      exact (hoff j (hij ▸ p.getVert_mem_support i.val)).elim
    · change l i = p.getVert j.val at hij
      exact (hoff i (hij.symm ▸ p.getVert_mem_support j.val)).elim
    · exact congrArg Sum.inr (hinj hij)

variable [Fintype V] [DecidableRel X.Adj]

/-- Degree at least four embeds the four-leaf affine D star. -/
theorem smithD_four_copy_of_degree_ge_four (v : V) (hv : 4 ≤ X.degree v) :
    Nonempty (Copy (smithD 4) X) := by
  classical
  obtain ⟨s, hs, hcard⟩ := Finset.le_card_iff_exists_subset_card.mp hv
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp hcard
  have hn (x) (hx : x ∈ ({a, b, c, d} : Finset V)) : X.Adj v x :=
    (X.mem_neighborFinset _ _).mp (hs hx)
  have ha := hn a (by simp)
  have hb := hn b (by simp)
  have hc := hn c (by simp)
  have hd := hn d (by simp)
  let l : Fin 4 → V := ![a, b, c, d]
  have hinj : Function.Injective l := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [l]
  have hoff : ∀ j, l j ∉ (Walk.nil : X.Walk v v).support := by
    intro j
    fin_cases j <;> simp [l, ha.ne', hb.ne', hc.ne', hd.ne']
  have hadj : ∀ j, X.Adj (if j.val < 2 then v else v) (l j) := by
    intro j
    fin_cases j <;> simp [l, ha, hb, hc, hd]
  exact Walk.IsPath.nil.smithD_copy l hinj hoff hadj

/-- In a forest, a path endpoint of degree at least three has two neighbors off the path. -/
theorem IsAcyclic.exists_two_neighbors_off_path (hacyc : X.IsAcyclic)
    {p : X.Walk u v} (hp : p.IsPath) (hnil : ¬ p.Nil) (hu : 3 ≤ X.degree u) :
    ∃ a b, a ≠ b ∧ X.Adj u a ∧ X.Adj u b ∧ a ∉ p.support ∧ b ∉ p.support := by
  classical
  have hsnd : p.snd ∈ X.neighborFinset u := (X.mem_neighborFinset _ _).mpr (p.adj_snd hnil)
  have hcard : 1 < (X.neighborFinset u |>.erase p.snd).card := by
    rw [Finset.card_erase_of_mem hsnd, card_neighborFinset_eq_degree]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨hasnd, ha⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbsnd, hb⟩ := Finset.mem_erase.mp hb
  have ha' := (X.mem_neighborFinset _ _).mp ha
  have hb' := (X.mem_neighborFinset _ _).mp hb
  exact ⟨a, b, hab, ha', hb', fun h => hasnd (hacyc.eq_snd_of_adj_start hp ha' h),
    fun h => hbsnd (hacyc.eq_snd_of_adj_start hp hb' h)⟩

/-- Two distinct branch vertices of a finite tree give a non-star affine D subgraph. -/
theorem IsTree.exists_smithD_copy_of_two_branches (hX : X.IsTree)
    (hne : u ≠ v) (hu : 3 ≤ X.degree u) (hv : 3 ≤ X.degree v) :
    ∃ ℓ, 5 ≤ ℓ ∧ Nonempty (Copy (smithD ℓ) X) := by
  classical
  obtain ⟨p, hp⟩ := hX.connected.exists_isPath u v
  have hnil : ¬ p.Nil := not_nil_of_ne hne
  have hlen : 0 < p.length := not_nil_iff_lt_length.mp hnil
  obtain ⟨a, b, hab, ha, hb, hao, hbo⟩ :=
    hX.isAcyclic.exists_two_neighbors_off_path hp hnil hu
  obtain ⟨c, d, hcd, hc, hd, hco, hdo⟩ :=
    hX.isAcyclic.exists_two_neighbors_off_path hp.reverse (not_nil_of_ne hne.symm) hv
  simp only [support_reverse, List.mem_reverse] at hco hdo
  have hcross {x y : V} (hx : X.Adj u x) (hy : X.Adj v y) (hxo : x ∉ p.support) : x ≠ y := by
    intro hxy
    subst y
    have heq := hX.isAcyclic.subsingleton_path u x |>.elim
      ⟨p.concat hy, hp.concat hxo hy⟩ ⟨hx.toWalk, hx.isPath_toWalk⟩
    have hlength := congrArg (fun q : X.Path u x => q.val.length) heq
    simp only [length_concat, Adj.toWalk, length_cons, length_nil] at hlength
    omega
  have hac := hcross ha hc hao
  have had := hcross ha hd hao
  have hbc := hcross hb hc hbo
  have hbd := hcross hb hd hbo
  clear hcross
  let l : Fin 4 → V := ![a, b, c, d]
  refine ⟨p.length + 4, by omega, hp.smithD_copy l ?_ ?_ ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [l]
  · intro j
    fin_cases j <;> simp [l, hao, hbo, hco, hdo]
  · intro j
    fin_cases j <;> simp [l, ha, hb, hc, hd]

end SimpleGraph
