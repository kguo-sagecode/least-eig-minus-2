/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Regular line graphs

Lemma 6.3 and Theorem 6.4 (SP4) of the spectral toolkit, and the form of
Lemma 5.4 of [CGSS] used in `blueprint/sec5-spectral.tex`.
-/

namespace SimpleGraph

variable {V : Type*} {X : SimpleGraph V}

/-- A bipartition covering all vertices, with constant degrees on its two parts. -/
structure IsBiregularWith (X : SimpleGraph V) [Fintype V] [DecidableRel X.Adj]
    (P Q : Set V) (k₁ k₂ : ℕ) : Prop where
  isBipartiteWith : X.IsBipartiteWith P Q
  union_eq : P ∪ Q = Set.univ
  degree_left : ∀ v ∈ P, X.degree v = k₁
  degree_right : ∀ v ∈ Q, X.degree v = k₂

private theorem reachable_of_mem_edge (e : X.edgeSet) {u v : V}
    (hu : u ∈ (e : Sym2 V)) (hv : v ∈ (e : Sym2 V)) : X.Reachable u v := by
  rcases e with ⟨⟨a, b⟩, hab⟩
  simp only [Sym2.mem_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact .refl _
  · exact hab.reachable
  · exact hab.symm.reachable
  · exact .refl _

private theorem reachable_of_lineGraph_reachable {e f : X.edgeSet}
    (h : X.lineGraph.Reachable e f) :
    ∀ u ∈ (e : Sym2 V), ∀ v ∈ (f : Sym2 V), X.Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact fun _ hu _ hv => reachable_of_mem_edge _ hu hv
  | cons hadj _ ih =>
    obtain ⟨_, z, hze, hzf⟩ := lineGraph_adj_iff_exists.mp hadj
    exact fun _ hu v hv => (reachable_of_mem_edge _ hu hze).trans (ih z hzf v hv)

/-- Lemma 6.3 of the spectral toolkit, step `line-back`: deleting isolated vertices is essential
to recover
connectedness from the line graph. -/
theorem connected_of_lineGraph_connected (hno : ∀ v, ∃ w, X.Adj v w)
    (hc : X.lineGraph.Connected) : X.Connected := by
  -- Step `line-incident`: choose incident edges at the two vertices.
  have hpre : X.Preconnected := by
    intro u v
    obtain ⟨u', hu⟩ := hno u
    obtain ⟨v', hv⟩ := hno v
    -- Steps `line-chain`, `line-propagate`, `line-reachable`: follow the line-graph path.
    have hp := hc.preconnected ⟨s(u, u'), hu⟩ ⟨s(v, v'), hv⟩
    exact reachable_of_lineGraph_reachable hp u (by simp) v (by simp)
  obtain ⟨⟨⟨u, v⟩, _⟩⟩ := hc.nonempty
  exact { preconnected := hpre, nonempty := ⟨u⟩ }

/-- Lemma 6.3 of the spectral toolkit: for a graph with an edge and no isolated vertices,
connectedness
is equivalent to connectedness of its line graph. No finiteness is needed. -/
theorem lineGraph_connected_iff_of_no_isolated (hedge : X.edgeSet.Nonempty)
    (hno : ∀ v, ∃ w, X.Adj v w) : X.lineGraph.Connected ↔ X.Connected := by
  classical
  constructor
  · exact connected_of_lineGraph_connected hno
  · intro hc
    -- Steps `line-walk`, `line-delete`: incident edges are equal or adjacent,
    -- so a vertex path gives a line-graph path, allowing repetitions.
    have hcommon {e f : X.edgeSet} {u : V}
        (he : u ∈ (e : Sym2 V)) (hf : u ∈ (f : Sym2 V)) : X.lineGraph.Reachable e f := by
      by_cases hef : e = f
      · subst f; exact .refl _
      · exact (lineGraph_adj_iff_exists.mpr ⟨hef, u, he, hf⟩).reachable
    have hpath {u v : V} (p : X.Walk u v) : ∀ e f : X.edgeSet,
        u ∈ (e : Sym2 V) → v ∈ (f : Sym2 V) → X.lineGraph.Reachable e f := by
      induction p with
      | nil => exact fun _ _ he hf => hcommon he hf
      | @cons u w v huw _ ih =>
        intro e f he hf
        let a : X.edgeSet := ⟨s(u, w), huw⟩
        exact (hcommon he (show u ∈ (a : Sym2 V) by simp [a])).trans
          (ih a f (by simp [a]) hf)
    -- Step `line-forward`: every pair of edge vertices is joined, and an edge exists.
    have hpre : X.lineGraph.Preconnected := by
      rintro ⟨⟨u, u'⟩, hu⟩ ⟨⟨v, v'⟩, hv⟩
      exact hpath (hc.preconnected u v).some _ _ (by simp) (by simp)
    exact { preconnected := hpre, nonempty := hedge.to_subtype }

variable [Fintype V] [DecidableRel X.Adj]

noncomputable local instance : DecidableRel X.lineGraph.Adj := Classical.decRel _

/-- Lemma 6.3 of the spectral toolkit: the degree of the vertex corresponding to an edge `uv` is
`deg(u) + deg(v) - 2`. -/
theorem degree_lineGraph {u v : V} (huv : X.Adj u v) :
    X.lineGraph.degree ⟨s(u, v), huv⟩ = X.degree u + X.degree v - 2 := by
  classical
  let e : X.edgeSet := ⟨s(u, v), huv⟩
  -- Step `line-union`: the neighbours are the incident edges at either end, except e itself.
  have hunion : (X.lineGraph.neighborFinset e).image Subtype.val =
      (X.incidenceFinset u ∪ X.incidenceFinset v).erase s(u, v) := by
    ext f
    simp only [Finset.mem_image, mem_neighborFinset, lineGraph_adj_iff_exists,
      Finset.mem_erase, Finset.mem_union, mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, ⟨hne, z, hz, hzg⟩, rfl⟩
      have hne' : (g : Sym2 V) ≠ s(u, v) := fun h => hne (Subtype.ext h.symm)
      rcases (Sym2.mem_iff.mp hz) with rfl | rfl
      · exact ⟨hne', Or.inl ⟨g.property, hzg⟩⟩
      · exact ⟨hne', Or.inr ⟨g.property, hzg⟩⟩
    · rintro ⟨hne, hf⟩
      rcases hf with ⟨hf, hu⟩ | ⟨hf, hv⟩
      · refine ⟨⟨f, hf⟩, ⟨?_, u, by simp [e], hu⟩, rfl⟩
        exact fun h => hne (congrArg Subtype.val h).symm
      · refine ⟨⟨f, hf⟩, ⟨?_, v, by simp [e], hv⟩, rfl⟩
        exact fun h => hne (congrArg Subtype.val h).symm
  -- Step `line-disjoint`: the incident-edge sets intersect in exactly the original edge.
  have hinter : X.incidenceFinset u ∩ X.incidenceFinset v = {s(u, v)} := by
    apply Finset.coe_injective
    simpa using X.incidenceSet_inter_incidenceSet_of_adj huv
  -- Step `line-count`: count the union, then remove the original edge.
  have hcard := Finset.card_union_add_card_inter (X.incidenceFinset u) (X.incidenceFinset v)
  rw [hinter, Finset.card_singleton, card_incidenceFinset_eq_degree,
    card_incidenceFinset_eq_degree] at hcard
  have hmem : s(u, v) ∈ X.incidenceFinset u ∪ X.incidenceFinset v := by
    simp [huv]
  have hcount := congrArg Finset.card hunion
  rw [Finset.card_image_of_injective _ Subtype.val_injective,
    card_neighborFinset_eq_degree, Finset.card_erase_of_mem hmem] at hcount
  dsimp [e] at hcount
  omega

/-- Theorem 6.4 of the spectral toolkit (SP4): a connected regular line graph comes from a regular
graph
or a bipartite graph with constant positive degrees on its two nonempty parts.
The two part-degree products count the edges. -/
theorem regular_or_semiregular_of_lineGraph_regular
    (hedge : X.edgeSet.Nonempty) (hno : ∀ v, 0 < X.degree v)
    (hc : X.lineGraph.Connected) {h : ℕ} (hr : X.lineGraph.IsRegularOfDegree h) :
    (∃ k, X.IsRegularOfDegree k) ∨
      ∃ P Q : Set V, ∃ k₁ k₂ : ℕ,
        X.IsBiregularWith P Q k₁ k₂ ∧ P.Nonempty ∧ Q.Nonempty ∧
        0 < k₁ ∧ 0 < k₂ ∧ k₁ ≠ k₂ ∧ k₁ + k₂ = h + 2 ∧
        Nat.card P * k₁ = X.edgeFinset.card ∧ Nat.card Q * k₂ = X.edgeFinset.card := by
  classical
  -- Step `sp4-connected`: connectedness and the constant endpoint-degree sum.
  have hconn := connected_of_lineGraph_connected
    (fun v => (X.degree_pos_iff_exists_adj v).mp (hno v)) hc
  have hsum {u v : V} (huv : X.Adj u v) : X.degree u + X.degree v = h + 2 := by
    have hdeg := degree_lineGraph huv
    rw [hr.degree_eq] at hdeg
    have hu := hno u
    have hv := hno v
    omega
  -- Step `sp4-choose`: choose the two positive degree values at an edge.
  obtain ⟨⟨u₀, v₀⟩, huv₀⟩ := hedge
  let k₁ := X.degree u₀
  let k₂ := X.degree v₀
  have hk : k₁ + k₂ = h + 2 := hsum huv₀
  -- Step `sp4-path`: the edge equation alternates these values along every path.
  have hpath {u v : V} (p : X.Walk u v) :
      X.degree v = k₁ ∨ X.degree v = k₂ → X.degree u = k₁ ∨ X.degree u = k₂ := by
    induction p with
    | nil => exact id
    | cons hadj _ ih =>
      intro hv
      have hw := ih hv
      have hs := hsum hadj
      omega
  -- Step `sp4-all`: every vertex is reached from the chosen endpoint.
  have hall (v : V) : X.degree v = k₁ ∨ X.degree v = k₂ :=
    hpath (hconn.preconnected v u₀).some (Or.inl rfl)
  by_cases heq : k₁ = k₂
  · -- Step `sp4-equal`: the two values coincide, giving regularity.
    have hreg : X.IsRegularOfDegree k₁ := fun v => by
      rcases hall v with hv | hv
      · exact hv
      · exact hv.trans heq.symm
    exact Or.inl ⟨k₁, hreg⟩
  · let P : Set V := {v | X.degree v = k₁}
    let Q : Set V := Pᶜ
    -- Step `sp4-partition`: unequal degree classes form the two parts.
    have hb : X.IsBipartiteWith P Q := by
      refine ⟨disjoint_compl_right, ?_⟩
      intro u v huv
      have hs := hsum huv
      have hu := hall u
      have hv := hall v
      change (X.degree u = k₁ ∧ X.degree v ≠ k₁) ∨
        (X.degree u ≠ k₁ ∧ X.degree v = k₁)
      omega
    have hleft (v : V) (hv : v ∈ P) : X.degree v = k₁ := hv
    have hright (v : V) (hv : v ∈ Q) : X.degree v = k₂ :=
      (hall v).resolve_left hv
    have hbi : X.IsBiregularWith P Q k₁ k₂ :=
      ⟨hb, Set.union_compl_self P, hleft, hright⟩
    -- Steps `sp4-firstcount`, `sp4-secondcount`: each edge has one end in either part.
    have hcount (S T : Set V) (k : ℕ) (hb : X.IsBipartiteWith S T)
        (hd : ∀ v ∈ S, X.degree v = k) : Nat.card S * k = X.edgeFinset.card := by
      have hb' : X.IsBipartiteWith (S.toFinset : Set V) (T.toFinset : Set V) := by
        simpa only [Set.coe_toFinset] using hb
      have hs := isBipartiteWith_sum_degrees_eq_card_edges hb'
      have hd' : ∑ v ∈ S.toFinset, X.degree v = S.toFinset.card * k := by
        calc
          _ = ∑ _v ∈ S.toFinset, k := Finset.sum_congr rfl fun v hv => hd v
            (Set.mem_toFinset.mp hv)
          _ = _ := by simp
      rw [hd'] at hs
      simpa only [Set.toFinset_card, Nat.card_eq_fintype_card] using hs
    have hfirst := hcount P Q k₁ hb hleft
    have hsecond := hcount Q P k₂ hb.symm hright
    exact Or.inr ⟨P, Q, k₁, k₂, hbi, ⟨u₀, rfl⟩,
      ⟨v₀, fun hv => heq hv.symm⟩, hno u₀, hno v₀, heq, hk, hfirst, hsecond⟩

/-- Lemma 5.4 of [CGSS], in the blueprint's form. Assumes that `X` has no isolated vertices
(Implicit hypothesis 3 of the errata); connectedness of the line graph already supplies an edge,
and in the nonregular case the two degrees are unequal. -/
theorem regular_or_isBiregularWith_of_lineGraph_regular
    (hno : ∀ v, 0 < X.degree v) (hc : X.lineGraph.Connected)
    {h : ℕ} (hr : X.lineGraph.IsRegularOfDegree h) :
    (∃ k, X.IsRegularOfDegree k) ∨
      ∃ P Q : Set V, ∃ k₁ k₂ : ℕ, X.IsBiregularWith P Q k₁ k₂ ∧ k₁ ≠ k₂ := by
  -- Step `s554edge`: a line-graph vertex is an edge of X.
  have hedge : X.edgeSet.Nonempty := by
    obtain ⟨e⟩ := hc.nonempty
    exact ⟨e.val, e.property⟩
  -- Steps `s554reg`, `s554notreg`: retain the regular or unequal-degree alternative.
  have hcases := regular_or_semiregular_of_lineGraph_regular hedge hno hc hr
  rcases hcases with hreg | ⟨P, Q, k₁, k₂, hb, _, _, _, _, hne, _⟩
  · exact Or.inl hreg
  · exact Or.inr ⟨P, Q, k₁, k₂, hb, hne⟩

end SimpleGraph
