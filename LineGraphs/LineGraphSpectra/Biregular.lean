/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.LineGraphRecovery
import LineGraphs.Spectral.Polynomial

/-!
# Bipartite root graphs

The blueprint's `def:bipartition`, `lem:rootgraph`, and `lem:biregular`, used in
Lemma 5.6 and Remark 5.7 of [CGSS]. Parts are subsets of the original vertex type,
so the biadjacency matrix keeps the chosen bipartition.
-/

open Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] {X : SimpleGraph V} [DecidableRel X.Adj]
  {P Q : Set V} {k₁ k₂ : ℕ}

noncomputable local instance : DecidableRel X.lineGraph.Adj := Classical.decRel _
noncomputable local instance : Decidable X.IsBipartite := Classical.propDecidable _

/-- The blueprint's biadjacency matrix (`def:bipartition`), used in [CGSS, Lemma 5.6]. -/
def biadjMatrix (X : SimpleGraph V) [DecidableRel X.Adj] (P Q : Set V)
    (R : Type*) [Zero R] [One R] : Matrix P Q R :=
  (X.adjMatrix R).submatrix Subtype.val Subtype.val

/-- Blueprint step `s5rgnoiso` for [CGSS, Lemma 5.6]: connectedness and an edge
exclude isolated vertices. -/
theorem Connected.degree_pos_of_edgeSet_nonempty (hc : X.Connected)
    (he : X.edgeSet.Nonempty) (v : V) : 0 < X.degree v := by
  obtain ⟨⟨a, b⟩, hab⟩ := he
  by_cases hva : v = a
  · subst v
    exact (X.degree_pos_iff_exists_adj a).mpr ⟨b, hab⟩
  · exact (hc.preconnected v a).degree_pos_left hva

omit [Fintype V] [DecidableRel X.Adj] in
/-- The component count in blueprint step `s5rgrank` for [CGSS, Lemma 5.6]. -/
theorem Connected.card_bipartite_components (hc : X.Connected) :
    Nat.card {c : X.ConnectedComponent // c.toSimpleGraph.IsBipartite} =
      if X.IsBipartite then 1 else 0 := by
  classical
  have : Nonempty V := hc.nonempty
  have : Subsingleton X.ConnectedComponent := hc.preconnected.subsingleton_connectedComponent
  let : Fintype X.ConnectedComponent := Fintype.ofFinite _
  have hiff (c : X.ConnectedComponent) : c.toSimpleGraph.IsBipartite ↔ X.IsBipartite := by
    constructor
    · intro hb
      have hmem (v : V) : v ∈ c := by
        change X.connectedComponentMk v = c
        exact Subsingleton.elim _ _
      exact Colorable.of_hom
        { toFun := fun v ↦ ⟨v, hmem v⟩, map_rel' := fun h ↦ h } hb
    · exact Colorable.of_hom c.toSimpleGraph_hom
  by_cases hb : X.IsBipartite
  · have : Nonempty {c : X.ConnectedComponent // c.toSimpleGraph.IsBipartite} :=
      ⟨⟨Classical.arbitrary _, (hiff _).mpr hb⟩⟩
    rw [ite_eq_left hb, Nat.card_eq_fintype_card]
    exact le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr inferInstance) Fintype.card_pos
  · have : IsEmpty {c : X.ConnectedComponent // c.toSimpleGraph.IsBipartite} :=
      ⟨fun c ↦ hb ((hiff c.val).mp c.property)⟩
    simp [hb]

section Signless

variable [DecidableEq V]

/-- Blueprint steps `s5rgzero` and `s556st` for [CGSS, Lemma 5.6]: a connected
root has one zero signless eigenvalue exactly when it is bipartite. -/
theorem Connected.multiplicity_zero_signlessLapMatrix (hc : X.Connected) :
    (X.signlessLapMatrix ℝ).eigenvalueMultiplicity 0 =
      if X.IsBipartite then 1 else 0 := by
  rw [X.isHermitian_signlessLapMatrix.eigenvalueMultiplicity_eq_finrank,
    Module.End.eigenspace_zero, X.finrank_ker_signlessLapMatrix_eq_card_bipartite_components,
    hc.card_bipartite_components]

end Signless

namespace IsBiregularWith

/-- Exchanging the parts in the blueprint's biregular bipartition for [CGSS, Lemma 5.6]. -/
theorem symm (hb : X.IsBiregularWith P Q k₁ k₂) :
    X.IsBiregularWith Q P k₂ k₁ :=
  ⟨hb.isBipartiteWith.symm, by rw [Set.union_comm, hb.union_eq],
    hb.degree_right, hb.degree_left⟩

/-- The bipartiteness clause of the blueprint's `lem:rootgraph` for [CGSS, Lemma 5.6]. -/
theorem isBipartite (hb : X.IsBiregularWith P Q k₁ k₂) : X.IsBipartite :=
  hb.isBipartiteWith.isBipartite

/-- Blueprint step `s5rgdeg` for [CGSS, Lemma 5.6]: both degrees are positive. -/
theorem degrees_pos (hb : X.IsBiregularWith P Q k₁ k₂) (he : X.edgeSet.Nonempty) :
    0 < k₁ ∧ 0 < k₂ := by
  obtain ⟨⟨a, b⟩, hab⟩ := he
  have ha := (X.degree_pos_iff_exists_adj a).mpr ⟨b, hab⟩
  have hc := (X.degree_pos_iff_exists_adj b).mpr ⟨a, hab.symm⟩
  rcases hb.isBipartiteWith.mem_of_adj hab with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · exact ⟨hb.degree_left a hp ▸ ha, hb.degree_right b hq ▸ hc⟩
  · exact ⟨hb.degree_left b hp ▸ hc, hb.degree_right a hq ▸ ha⟩

/-- Blueprint step `s5rgiso` for [CGSS, Lemma 5.6]: count edges from the left part. -/
theorem card_mul_degree_left (hb : X.IsBiregularWith P Q k₁ k₂) :
    Nat.card P * k₁ = X.edgeFinset.card := by
  classical
  have hp : X.IsBipartiteWith (P.toFinset : Set V) (Q.toFinset : Set V) := by
    simpa only [Set.coe_toFinset] using hb.isBipartiteWith
  have hs := isBipartiteWith_sum_degrees_eq_card_edges hp
  have hd : ∑ v ∈ P.toFinset, X.degree v = P.toFinset.card * k₁ := by
    calc
      _ = ∑ _v ∈ P.toFinset, k₁ := Finset.sum_congr rfl fun v hv ↦
        hb.degree_left v (Set.mem_toFinset.mp hv)
      _ = _ := by simp
  rw [hd] at hs
  simpa only [Set.toFinset_card, Nat.card_eq_fintype_card] using hs

/-- Blueprint step `s5rgiso` for [CGSS, Lemma 5.6]: count edges from the right part. -/
theorem card_mul_degree_right (hb : X.IsBiregularWith P Q k₁ k₂) :
    Nat.card Q * k₂ = X.edgeFinset.card := hb.symm.card_mul_degree_left

/-- The vertex decomposition in the blueprint's `lem:rootgraph` for [CGSS, Lemma 5.6]. -/
noncomputable def sumEquiv (hb : X.IsBiregularWith P Q k₁ k₂) : P ⊕ Q ≃ V :=
  Equiv.ofBijective (Sum.elim Subtype.val Subtype.val) (by
    constructor
    · intro u v huv
      rcases u with u | u <;> rcases v with v | v
      · exact congrArg Sum.inl (Subtype.ext huv)
      · change (u : V) = v at huv
        exact (Set.disjoint_left.mp hb.isBipartiteWith.disjoint u.property
          (huv.symm ▸ v.property)).elim
      · change (u : V) = v at huv
        exact (Set.disjoint_left.mp hb.isBipartiteWith.disjoint v.property
          (huv ▸ u.property)).elim
      · exact congrArg Sum.inr (Subtype.ext huv)
    · intro v
      have hv : v ∈ P ∪ Q := hb.union_eq.symm ▸ Set.mem_univ v
      rcases hv with hp | hq
      · exact ⟨Sum.inl ⟨v, hp⟩, rfl⟩
      · exact ⟨Sum.inr ⟨v, hq⟩, rfl⟩)

/-- Blueprint step `s5trprod` for [CGSS, Lemma 5.6]: the part sizes add to the order. -/
theorem card_add_card (hb : X.IsBiregularWith P Q k₁ k₂) :
    Nat.card P + Nat.card Q = Fintype.card V := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sum] using
    Fintype.card_congr hb.sumEquiv

/-- Blueprint step `s5trorder` for [CGSS, Lemma 5.6]: the smaller part has larger degree. -/
theorem degree_right_le_left (hb : X.IsBiregularWith P Q k₁ k₂)
    (he : X.edgeSet.Nonempty) (hpq : Nat.card P ≤ Nat.card Q) : k₂ ≤ k₁ := by
  have hdeg := hb.degrees_pos he
  have hm := hb.card_mul_degree_left.trans hb.card_mul_degree_right.symm
  have hP : 0 < Nat.card P := by
    have hparts := hb.card_add_card
    obtain ⟨⟨a, b⟩, hab⟩ := he
    have hnon : Nonempty V := ⟨a⟩
    have hV : 0 < Fintype.card V := Fintype.card_pos
    nlinarith
  nlinarith

/-- The blueprint's `lem:rootgraph`, assertion 2, for [CGSS, Lemma 5.6]:
the degree of the line graph is the sum of the two part degrees minus two. -/
theorem lineGraph_isRegularOfDegree (hb : X.IsBiregularWith P Q k₁ k₂) :
    X.lineGraph.IsRegularOfDegree (k₁ + k₂ - 2) := by
  rintro ⟨⟨u, v⟩, huv⟩
  rw [degree_lineGraph huv]
  rcases hb.isBipartiteWith.mem_of_adj huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [hb.degree_left u hu, hb.degree_right v hv]
  · rw [hb.degree_right u hu, hb.degree_left v hv, Nat.add_comm]

section Signless

variable [DecidableEq V]

/-- The blueprint's `lem:rootgraph`, assertion 4, for [CGSS, Lemma 5.6]. -/
theorem multiplicity_zero_signlessLapMatrix (hb : X.IsBiregularWith P Q k₁ k₂)
    (hc : X.Connected) : (X.signlessLapMatrix ℝ).eigenvalueMultiplicity 0 = 1 := by
  rw [hc.multiplicity_zero_signlessLapMatrix, ite_eq_left hb.isBipartite]

/-- The blueprint's `lem:rootgraph`, assertion 5, for [CGSS, Lemma 5.6]. -/
theorem card_eq_rank_add_one (hb : X.IsBiregularWith P Q k₁ k₂) (hc : X.Connected) :
    Fintype.card V =
      ((2 : ℝ) • (1 : Matrix X.edgeSet X.edgeSet ℝ) + X.lineGraph.adjMatrix ℝ).rank + 1 := by
  have hr := X.isHermitian_signlessLapMatrix.rank_add_eigenvalueMultiplicity_zero
  rw [hb.multiplicity_zero_signlessLapMatrix hc, ← X.edgeIncMatrix_mul_transpose,
    rank_self_mul_transpose] at hr
  rw [← X.transpose_edgeIncMatrix_mul, rank_transpose_mul_self]
  exact hr.symm

/-- The blueprint's `lem:rootgraph`, assertion 3, for [CGSS, Lemma 5.6]: the
signless Laplacian has scalar diagonal blocks in the chosen bipartition. -/
theorem signlessLapMatrix_eq_fromBlocks (hb : X.IsBiregularWith P Q k₁ k₂) :
    (X.signlessLapMatrix ℝ).submatrix hb.sumEquiv hb.sumEquiv =
      fromBlocks ((k₁ : ℝ) • 1) (X.biadjMatrix P Q ℝ)
        (X.biadjMatrix P Q ℝ)ᵀ ((k₂ : ℝ) • 1) := by
  classical
  have hPP (u v : P) : ¬ X.Adj u v := by
    intro huv
    rcases hb.isBipartiteWith.mem_of_adj huv with ⟨_, hv⟩ | ⟨hu, _⟩
    · exact Set.disjoint_left.mp hb.isBipartiteWith.disjoint v.property hv
    · exact Set.disjoint_left.mp hb.isBipartiteWith.disjoint u.property hu
  have hQQ (u v : Q) : ¬ X.Adj u v := by
    intro huv
    rcases hb.isBipartiteWith.mem_of_adj huv with ⟨hu, _⟩ | ⟨_, hv⟩
    · exact Set.disjoint_left.mp hb.isBipartiteWith.disjoint hu u.property
    · exact Set.disjoint_left.mp hb.isBipartiteWith.disjoint hv v.property
  have hPQ (u : P) (v : Q) : (u : V) ≠ v := fun h ↦
    Set.disjoint_left.mp hb.isBipartiteWith.disjoint (h ▸ u.property) v.property
  ext (u | u) (v | v)
  · change X.signlessLapMatrix ℝ u v = ((k₁ : ℝ) • (1 : Matrix P P ℝ)) u v
    simp [signlessLapMatrix, degMatrix, diagonal_apply, adjMatrix_apply, hPP,
      hb.degree_left, Matrix.one_apply, Subtype.ext_iff]
  · change X.signlessLapMatrix ℝ u v = X.biadjMatrix P Q ℝ u v
    simp [signlessLapMatrix, degMatrix, hPQ, biadjMatrix]
  · change X.signlessLapMatrix ℝ u v = X.biadjMatrix P Q ℝ v u
    simp [signlessLapMatrix, degMatrix, (hPQ v u).symm, biadjMatrix,
      adjMatrix_apply, X.adj_comm]
  · change X.signlessLapMatrix ℝ u v = ((k₂ : ℝ) • (1 : Matrix Q Q ℝ)) u v
    simp [signlessLapMatrix, degMatrix, diagonal_apply, adjMatrix_apply, hQQ,
      hb.degree_right, Matrix.one_apply, Subtype.ext_iff]

end Signless

end IsBiregularWith

/-- The blueprint's `lem:biregular` for [CGSS, Lemma 5.6]: order the parts of a
biregular bipartition by cardinality. Connectedness of the line graph supplies an edge. -/
theorem exists_isBiregularWith_of_lineGraph_regular
    (hb : X.IsBipartite) (hno : ∀ v, 0 < X.degree v) (hc : X.lineGraph.Connected)
    {h : ℕ} (hr : X.lineGraph.IsRegularOfDegree h) :
    ∃ P Q : Set V, ∃ k₁ k₂ : ℕ,
      X.IsBiregularWith P Q k₁ k₂ ∧ Nat.card P ≤ Nat.card Q := by
  classical
  have hex : ∃ P Q : Set V, ∃ k₁ k₂ : ℕ, X.IsBiregularWith P Q k₁ k₂ := by
    rcases regular_or_isBiregularWith_of_lineGraph_regular hno hc hr with
      ⟨k, hk⟩ | ⟨P, Q, k₁, k₂, hbi, _⟩
    · obtain ⟨P, Q, hPQ⟩ := hb.exists_isBipartiteWith
      have hcover : P ∪ Q = Set.univ := by
        apply Set.eq_univ_of_forall
        intro v
        obtain ⟨w, hvw⟩ := (X.degree_pos_iff_exists_adj v).mp (hno v)
        rcases hPQ.mem_of_adj hvw with ⟨hp, _⟩ | ⟨hq, _⟩
        · exact Or.inl hp
        · exact Or.inr hq
      exact ⟨P, Q, k, k, ⟨hPQ, hcover, fun v _ ↦ hk v, fun v _ ↦ hk v⟩⟩
    · exact ⟨P, Q, k₁, k₂, hbi⟩
  obtain ⟨P, Q, k₁, k₂, hbi⟩ := hex
  rcases le_total (Nat.card P) (Nat.card Q) with hle | hle
  · exact ⟨P, Q, k₁, k₂, hbi, hle⟩
  · exact ⟨Q, P, k₂, k₁, hbi.symm, hle⟩

end SimpleGraph
