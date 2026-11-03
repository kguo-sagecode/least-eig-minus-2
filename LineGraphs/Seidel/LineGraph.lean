/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.LineGraphCases
import LineGraphs.Graphs.Basic

/-!
# The line-graph lemma for Remark 4.14

Lemma `lem:414-linegraph` of the blueprint for Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

variable {V W : Type*} {X : SimpleGraph V} {Y : SimpleGraph W}

/-- Step `s414lgsame` of Lemma `lem:414-linegraph`, Remark 4.14 of [CGSS]:
deleting isolated vertices preserves the line graph. -/
noncomputable def lineGraphInduceSupportIso (Y : SimpleGraph W) :
    (Y.induce Y.support).lineGraph ≃g Y.lineGraph := by
  let f := (Copy.induce Y Y.support).toLineGraphEmbedding
  have hs : Function.Surjective f := by
    rintro ⟨⟨i, j⟩, hij⟩
    let i' : Y.support := ⟨i, ⟨j, hij⟩⟩
    let j' : Y.support := ⟨j, ⟨i, hij.symm⟩⟩
    exact ⟨⟨s(i', j'), hij⟩, rfl⟩
  exact { toEquiv := Equiv.ofBijective f ⟨f.injective, hs⟩
          map_rel_iff' := f.map_rel_iff }

/-- Step `s414lgstar` of Lemma `lem:414-linegraph`, Remark 4.14 of [CGSS]:
the line graph of a star is complete. -/
theorem lineGraph_completeBipartiteGraph_eq_top [Subsingleton V] :
    (completeBipartiteGraph V W).lineGraph = ⊤ := by
  apply eq_top_iff_forall_ne_adj.mpr
  intro u v huv
  obtain ⟨p, rfl⟩ := (completeBipartiteEdgeEquiv V W).surjective u
  obtain ⟨q, rfl⟩ := (completeBipartiteEdgeEquiv V W).surjective v
  exact (lineGraph_completeBipartiteGraph_adj p q).mpr
    ⟨fun he ↦ huv (congrArg _ he), Or.inl (Subsingleton.elim _ _)⟩

variable [Fintype V] [DecidableEq V] [DecidableRel X.Adj]
  [Fintype W] [DecidableEq W] [DecidableRel Y.Adj] {n k a c : ℕ}

noncomputable local instance lineGraphClassificationDecidableAdj : DecidableRel Y.lineGraph.Adj :=
  Classical.decRel _

omit [Fintype W] [DecidableEq W] [DecidableRel Y.Adj] in
/-- The connected-root case of Lemma `lem:414-linegraph`, Remark 4.14 of
[CGSS]. In the cycle case the linear relation `k - 2a + c = 4` gives `c = 2`
directly, so the complete-bipartite recognition of LG1 applies again. -/
theorem IsSRGWith.nonempty_iso_lineGraph_complete_or_completeBipartite_of_connected
    [Finite W]
    (h : X.IsSRGWith n k a c)
    (hdet : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).det = 0)
    (hc : Y.Connected) (hedge : Y.edgeSet.Nonempty) (e : X ≃g Y.lineGraph) :
    ∃ m, 2 ≤ m ∧ (Nonempty (X ≃g (completeGraph (Fin m)).lineGraph) ∨
      Nonempty (X ≃g (completeBipartiteGraph (Fin m) (Fin m)).lineGraph)) := by
  classical
  let : Fintype W := Fintype.ofFinite W
  have hY := h.of_iso e
  have hlin := h.linear_relation_of_det_two_add_adjMatrix_eq_zero hdet
  have hnt := (h.ne_bot_and_ne_top_of_det_two_add_adjMatrix_eq_zero hdet).2
  have hstar (m : ℕ) (f : Y ≃g completeBipartiteGraph (Fin 1) (Fin m)) : False := by
    let g := e.trans f.lineGraph
    apply hnt
    apply eq_top_iff_forall_ne_adj.mpr
    intro u v huv
    apply g.map_rel_iff.mp
    exact eq_top_iff_forall_ne_adj.mp lineGraph_completeBipartiteGraph_eq_top
      (g u) (g v) (g.injective.ne huv)
  rcases lineGraph_isSRGWith_cases hc hedge hY with
    ⟨m, hm, ⟨f⟩⟩ | ⟨m, hm, ⟨f⟩⟩ | ⟨m, hm, ⟨f⟩⟩ | ⟨m, _, ⟨f⟩⟩
  · have hr : Y.IsRegularOfDegree 2 := by
      intro v
      rw [← f.degree_eq v]
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
      exact cycleGraph_degree_three_le
    by_cases htri : ∃ u v w, Y.Adj u v ∧ Y.Adj u w ∧ Y.Adj v w
    · obtain ⟨u, v, w, huv, huw, hvw⟩ := htri
      have htop := hY.eq_top_of_lineGraph_of_triangle hr hc huv huw hvw
      have hf : Nonempty (Y ≃g completeGraph (Fin (Fintype.card W))) := by
        rw [htop]
        exact ⟨Iso.completeGraph (Fintype.equivFin W)⟩
      refine ⟨Fintype.card W, ?_, Or.inl ⟨e.trans hf.some.lineGraph⟩⟩
      have hu := Y.degree_lt_card_verts u
      rw [hr u] at hu
      omega
    have ht : ∀ ⦃u v w⦄, Y.Adj u v → Y.Adj u w → ¬Y.Adj v w :=
      fun {u v w} huv huw hvw ↦ htri ⟨u, v, w, huv, huw, hvw⟩
    obtain ⟨⟨i, j⟩, hij⟩ := hedge
    have hk : k = 2 := by
      have he := degree_lineGraph hij
      rw [hY.regular _, hr i, hr j] at he
      omega
    obtain ⟨l, hil, hlj⟩ := (Y.neighborFinset i).exists_mem_ne
      (by rw [card_neighborFinset_eq_degree, hr i]; omega) j
    rw [mem_neighborFinset] at hil
    have ha := hY.degree_sub_two_add_eq_of_lineGraph hij hil hlj.symm
    have hnjl := ht hij hil
    simp only [hr i, hnjl, ite_false, add_zero] at ha
    have hc2 : c = 2 := by omega
    obtain ⟨g⟩ := (hc2 ▸ hY).nonempty_iso_completeBipartite_of_lineGraph hr hc
      ⟨s(i, j), hij⟩ ht
    exact ⟨2, le_rfl, Or.inr ⟨e.trans g.lineGraph⟩⟩
  · exact ⟨m, hm, Or.inl ⟨e.trans f.lineGraph⟩⟩
  · by_cases hm2 : 2 ≤ m
    · exact ⟨m, hm2, Or.inr ⟨e.trans f.lineGraph⟩⟩
    · have hm1 : m = 1 := by omega
      subst m
      exact (hstar 1 f).elim
  · exact (hstar m f).elim

omit [Fintype W] [DecidableEq W] [DecidableRel Y.Adj] in
-- Lemma (strongly regular line graphs), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-linegraph`, Remark 4.14 of [CGSS]: a connected strongly
regular line graph with eigenvalue minus two is a triangular graph or a
balanced complete-bipartite line graph. Isolated vertices in the root graph
are allowed and are removed before applying LG1. -/
theorem IsSRGWith.nonempty_iso_lineGraph_complete_or_completeBipartite
    (h : X.IsSRGWith n k a c) (hc : X.Connected)
    (hdet : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).det = 0)
    (e : X ≃g Y.lineGraph) :
    ∃ m, 2 ≤ m ∧ (Nonempty (X ≃g (completeGraph (Fin m)).lineGraph) ∨
      Nonempty (X ≃g (completeBipartiteGraph (Fin m) (Fin m)).lineGraph)) := by
  classical
  let : Fintype Y.edgeSet := Fintype.ofEquiv V e.toEquiv
  let M : Finset W := Finset.univ.biUnion fun f : Y.edgeSet ↦ f.val.toFinset
  have hfinite : Y.support.Finite := by
    apply M.finite_toSet.subset
    rintro v ⟨w, hvw⟩
    exact Finset.mem_biUnion.mpr
      ⟨⟨s(v, w), hvw⟩, Finset.mem_univ _, by simp⟩
  let : Fintype Y.support := hfinite.fintype
  let Z := Y.induce Y.support
  let f : X ≃g Z.lineGraph := e.trans (lineGraphInduceSupportIso Y).symm
  have hcL : Z.lineGraph.Connected := f.connected_iff.mp hc
  have hno (v : Y.support) : ∃ w, Z.Adj v w := by
    obtain ⟨w, hvw⟩ := v.property
    exact ⟨⟨w, ⟨v, hvw.symm⟩⟩, hvw⟩
  have hcZ : Z.Connected := connected_of_lineGraph_connected hno hcL
  have hedge : Z.edgeSet.Nonempty := by
    obtain ⟨v⟩ := hcL.nonempty
    exact ⟨v.val, v.property⟩
  exact h.nonempty_iso_lineGraph_complete_or_completeBipartite_of_connected hdet hcZ hedge f

end SimpleGraph
