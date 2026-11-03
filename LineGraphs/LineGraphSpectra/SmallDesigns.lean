/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Theorem58
import LineGraphs.Seidel.LineGraphRecognition
import LineGraphs.Graphs.Basic

/-!
# Small and full-block designs

The lemmas `lem:oneblock`, `lem:hexagon`, and `lem:fullblock` used in Corollaries
5.9–5.11 of [CGSS]. Single-block designs are included, as required by Gap 16.
-/

open SimpleGraph

namespace SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Lemma `lem:dense`, used in Corollary 5.9 of [CGSS]: maximum degree gives completeness. -/
theorem eq_top_of_isRegularOfDegree_card_sub_one {V : Type*} [Fintype V]
    (X : SimpleGraph V) [DecidableRel X.Adj]
    (hr : X.IsRegularOfDegree (Fintype.card V - 1)) : X = ⊤ := by
  apply eq_top_iff_forall_ne_adj.mpr
  intro u w huw
  exact (X.degree_eq_card_sub_one u).mp (hr u) huw

/-- Lemma `lem:oneblock`, assertion 1, Corollary 5.9 of [CGSS]: a cospectral mate
of a nonempty complete graph is isomorphic to it. -/
theorem Cospectral.nonempty_iso_of_isRegularOfDegree_card_sub_one
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [Nonempty V]
    {X : SimpleGraph V} {Y : SimpleGraph W} [DecidableRel X.Adj] [DecidableRel Y.Adj]
    (hs : X.Cospectral Y) (hr : X.IsRegularOfDegree (Fintype.card V - 1)) :
    Nonempty (Y ≃g X) := by
  have hy : Y.IsRegularOfDegree (Fintype.card W - 1) := hs.card_eq ▸ hs.isRegularOfDegree hr
  rw [eq_top_of_isRegularOfDegree_card_sub_one X hr,
    eq_top_of_isRegularOfDegree_card_sub_one Y hy]
  exact ⟨Iso.completeGraph (Fintype.equivOfCardEq hs.card_eq.symm)⟩

end SimpleGraph

namespace Design

attribute [local instance] Classical.propDecidable

variable {P B : Type} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam : ℕ}

/-- Lemma `lem:oneblock`, Corollary 5.11 of [CGSS]: the single-block designs in Gap 16. -/
theorem flagGraphCharacterized_of_b_eq_one (D : Design P B v k b r lam) (hb : b = 1) :
    D.FlagGraphCharacterized := by
  have hbk := D.b_mul_k_eq_v_mul_r
  have hkv := D.k_le_v
  have hv := D.one_lt_v
  have hr := D.r_pos
  rw [hb, one_mul] at hbk
  have hr1 : r = 1 := by nlinarith
  have hkv' : k = v := by simpa [hr1] using hbk
  have hreg : D.flagGraph.IsRegularOfDegree (Fintype.card D.incidenceGraph.edgeSet - 1) := by
    simpa only [D.card_flagGraph, hr1, hkv', Nat.mul_one,
      show 1 + v - 2 = v - 1 by omega] using D.flagGraph_isRegularOfDegree
  have : Nonempty D.incidenceGraph.edgeSet := D.flagGraph_connected.nonempty
  intro V _ _ X _ hs
  exact ⟨P, B, inferInstance, inferInstance, inferInstance, inferInstance, D,
    hs.nonempty_iso_of_isRegularOfDegree_card_sub_one hreg⟩

/-- Lemma `lem:hexagon`, Corollaries 5.10–5.11 of [CGSS]: the six-cycle case of Gap 16. -/
theorem flagGraphCharacterized_of_parameters_3_2_1 (D : Design P B 3 2 3 2 1) :
    D.FlagGraphCharacterized := by
  have hr : D.flagGraph.IsRegularOfDegree 2 := D.flagGraph_isRegularOfDegree
  obtain ⟨e⟩ := hr.nonempty_iso_cycle D.flagGraph_connected
  have : Nonempty D.incidenceGraph.edgeSet := D.flagGraph_connected.nonempty
  intro V _ _ X _ hs
  obtain ⟨f⟩ := (hs.isRegularOfDegree hr).nonempty_iso_cycle
    (hs.connected_of_regular hr D.flagGraph_connected)
  have hn := hs.card_eq
  let g : cycleGraph (Fintype.card V) ≃g cycleGraph (Fintype.card D.incidenceGraph.edgeSet) :=
    by rw [hn]
  exact ⟨P, B, inferInstance, inferInstance, inferInstance, inferInstance, D,
    ⟨f.trans (g.trans e.symm)⟩⟩

/-- Lemma `lem:fullblock`, Corollary 5.9 of [CGSS]: the trivial labelled design. -/
def trivial (m n : ℕ) (hm : 0 < m) (hn : 1 < n) :
    Design (Fin n) (Fin m) n n m m m where
  card_points := Fintype.card_fin _
  card_blocks := Fintype.card_fin _
  block := fun _ ↦ Finset.univ
  card_block := by simp
  card_blocksThrough := by simp
  card_blocksThroughPair := by simp
  one_lt_v := hn
  one_lt_k := hn
  b_pos := hm

/-- Lemma `lem:fullblock`, step `s5fbI`, Corollary 5.9 of [CGSS]: full incidence is
complete bipartite, with block labels listed before points. -/
noncomputable def incidenceGraphCompleteBipartiteIso (D : Design P B v v b b b) :
    D.incidenceGraph ≃g completeBipartiteGraph (Fin b) (Fin v) := by
  let eP : P ≃ Fin v := Fintype.equivFinOfCardEq D.card_points
  let eB : B ≃ Fin b := Fintype.equivFinOfCardEq D.card_blocks
  let e := (Equiv.sumComm P B).trans (Equiv.sumCongr eB eP)
  refine { toEquiv := e, map_rel_iff' := ?_ }
  rintro (p | label) (q | other) <;>
    simp [e, incidenceGraph, completeBipartiteGraph, D.block_eq_univ_of_k_eq_v rfl]

/-- Lemma `lem:fullblock`, step `s5fbiso`, Corollary 5.9 of [CGSS]. -/
theorem nonempty_iso_flagGraph_lineGraph_completeBipartite (D : Design P B v v b b b) :
    Nonempty (D.flagGraph ≃g (completeBipartiteGraph (Fin b) (Fin v)).lineGraph) :=
  ⟨D.incidenceGraphCompleteBipartiteIso.lineGraph⟩

end Design
