/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Transversal
import LineGraphs.Seidel.ApexGraphs
import LineGraphs.Seidel.TriangularSwitching
import LineGraphs.Seidel.AddOneSwitching

/-! # The three exceptional switching cases

Steps `s414mpetsw`, `s414mshrsw`, `s414mchangsw` of the proof of Remark 4.14.
-/

open scoped RealInnerProductSpace
open LineSystem

namespace SimpleGraph

/-- The common inner product with the endpoint vectors in step `s414trip`
of `lem:414-transversal`. -/
theorem inner_c_lineGraphVector (Y : SimpleGraph (Fin 8)) (e : Y.edgeSet) :
    ⟪E₈.c, Y.lineGraphVector e⟫ = 1 := by
  rcases e with ⟨⟨i, j⟩, hij⟩
  rw [Y.lineGraphVector_mk hij]
  norm_num [E₈.c, inner_add_right, EuclideanSpace.inner_single_right]

/-- C20's `E₆` pairs in the actual edge type, for step `s414mpetsw`. -/
theorem E₆_apex_pairs {z : EuclideanSpace ℝ (Fin 8)} (hz : z ∈ E₆.N E₈.c) :
    ∃ p : apexGraph6.edgeSet,
      z = apexGraph6.lineGraphVector p ∨ z = E₈.c - apexGraph6.lineGraphVector p := by
  rw [E₆.N_c] at hz
  obtain ⟨p, hp, h⟩ := hz
  refine ⟨apexGraph6Edge ⟨p, hp⟩, ?_⟩
  have hv := apexGraph6.lineGraphVector_mk (apexGraph6Edge ⟨p, hp⟩).property
  change apexGraph6.lineGraphVector (apexGraph6Edge ⟨p, hp⟩) = _ at hv
  rw [hv]
  simpa only [sub_add_eq_sub_sub] using h

/-- C20's `E₇` pairs in the actual edge type, for step `s414mshrsw`. -/
theorem E₇_apex_pairs {z : EuclideanSpace ℝ (Fin 8)} (hz : z ∈ E₇.N E₈.c) :
    ∃ p : apexGraph7.edgeSet,
      z = apexGraph7.lineGraphVector p ∨ z = E₈.c - apexGraph7.lineGraphVector p := by
  rw [E₇.N_c] at hz
  obtain ⟨p, hp, h⟩ := hz
  refine ⟨apexGraph7Edge ⟨p, hp⟩, ?_⟩
  have hv := apexGraph7.lineGraphVector_mk (apexGraph7Edge ⟨p, hp⟩).property
  change apexGraph7.lineGraphVector (apexGraph7Edge ⟨p, hp⟩) = _ at hv
  rw [hv]
  simpa only [sub_add_eq_sub_sub] using h

/-- C20's `E₈` pairs in the actual edge type, for step `s414mchangsw`. -/
theorem E₈_apex_pairs {z : EuclideanSpace ℝ (Fin 8)} (hz : z ∈ E₈.N E₈.c) :
    ∃ p : (⊤ : SimpleGraph (Fin 8)).edgeSet,
      z = (⊤ : SimpleGraph (Fin 8)).lineGraphVector p ∨
        z = E₈.c - (⊤ : SimpleGraph (Fin 8)).lineGraphVector p := by
  rw [E₈.N_c] at hz
  obtain ⟨p, hp, h⟩ := hz
  refine ⟨completeGraphEdgeEquiv (Fin 8) ⟨p, hp⟩, ?_⟩
  have hv := (⊤ : SimpleGraph (Fin 8)).lineGraphVector_mk
    (show (⊤ : SimpleGraph (Fin 8)).Adj p.1 p.2 from hp.ne)
  change (⊤ : SimpleGraph (Fin 8)).lineGraphVector
    (completeGraphEdgeEquiv (Fin 8) ⟨p, hp⟩) = _ at hv
  rw [hv]
  simpa only [sub_add_eq_sub_sub] using h

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

/-- Step `s414mpet` in Remark 4.14: the `E₆` lattice type and Petersen parameters
give the Petersen graph by the apex and the arbitrary-cut classification. -/
theorem IsRepresentation.nonempty_iso_petersen_of_latticeRoots
    (hx : X.IsRepresentation x) (hr : X.IsRegularOfDegree 3)
    (hn : Fintype.card V = 10) (e : hx.latticeRoots.Iso E₆) : Nonempty (X ≃g petersen) := by
  classical
  obtain ⟨H, ⟨f⟩⟩ := hx.nonempty_iso_lineGraph_switch hr E₆ e isMaximal_E₆ E₈.c E₆.c_mem
    (fun _ h ↦ E₆.exists_isometry_apply_eq_c h) apexGraph6 (fun _ h ↦ E₆_apex_pairs h)
    (inner_c_lineGraphVector apexGraph6)
    (by rw [hx.inner_apex_self hr, hn]; norm_num)
    (by rw [← Fintype.card_congr apexGraph6EdgeEquiv, E₆.card_CEdge, hn])
  let g : X ≃g (⊤ : SimpleGraph (Fin 5)).lineGraph.switch (apexGraph6LineIso '' H) :=
    f.trans (apexGraph6LineIso.switch H)
  have hg : IsRegularOfDegree
      ((⊤ : SimpleGraph (Fin 5)).lineGraph.switch (apexGraph6LineIso '' H)) 3 := by
    intro v
    obtain ⟨u, rfl⟩ := g.surjective v
    exact (g.degree_eq u).trans (hr u)
  obtain ⟨q⟩ := nonempty_iso_petersen_of_switch_triangular5 _ hg
  exact ⟨g.trans q⟩

/-- Step `s414mshr` in Remark 4.14: the `E₇` lattice type and `(16,6,2,2)` parameters
give Shrikhande or the line graph of `K₄,₄`. -/
theorem IsRepresentation.nonempty_iso_shrikhande_or_lattice_of_latticeRoots
    (hx : X.IsRepresentation x) (hr : X.IsRegularOfDegree 6)
    (hn : Fintype.card V = 16) (e : hx.latticeRoots.Iso E₇) :
    Nonempty (X ≃g shrikhande) ∨
      Nonempty (X ≃g (completeBipartiteGraph (Fin 4) (Fin 4)).lineGraph) := by
  classical
  obtain ⟨H, ⟨f⟩⟩ := hx.nonempty_iso_lineGraph_switch hr E₇ e isMaximal_E₇ E₈.c E₇.c_mem
    (fun _ h ↦ E₇.exists_isometry_apply_eq_c h) apexGraph7 (fun _ h ↦ E₇_apex_pairs h)
    (inner_c_lineGraphVector apexGraph7)
    (by rw [hx.inner_apex_self hr, hn]; norm_num)
    (by rw [← Fintype.card_congr apexGraph7EdgeEquiv, E₇.card_CEdge, hn])
  let g : X ≃g (triangularAddOne 6).switch (apexGraph7LineIso '' H) :=
    f.trans (apexGraph7LineIso.switch H)
  have hg : ((triangularAddOne 6).switch (apexGraph7LineIso '' H)).IsRegularOfDegree 6 := by
    intro v
    obtain ⟨u, rfl⟩ := g.surjective v
    exact (g.degree_eq u).trans (hr u)
  rcases nonempty_iso_shrikhande_or_lineGraph_completeBipartite_of_switch_triangular6AddOne
    _ hg with h | h
  · obtain ⟨q⟩ := h
    exact Or.inl ⟨g.trans q⟩
  · obtain ⟨q⟩ := h
    exact Or.inr ⟨g.trans q⟩

/-- Step `s414mchang` in Remark 4.14: the `E₈` lattice type and `(28,12,6,4)` parameters
give a triangular graph or a Chang graph. -/
theorem IsRepresentation.nonempty_iso_triangular_or_chang_of_latticeRoots
    (hx : X.IsRepresentation x) (hr : X.IsRegularOfDegree 12)
    (hn : Fintype.card V = 28) (e : hx.latticeRoots.Iso E₈) :
    Nonempty (X ≃g (⊤ : SimpleGraph (Fin 8)).lineGraph) ∨
      Nonempty (X ≃g changI) ∨ Nonempty (X ≃g changII) ∨ Nonempty (X ≃g changIII) := by
  classical
  obtain ⟨H, ⟨g⟩⟩ := hx.nonempty_iso_lineGraph_switch hr E₈ e isMaximal_E₈ E₈.c E₈.c_mem
    (fun _ h ↦ E₈.exists_isometry_apply_eq_c h) (⊤ : SimpleGraph (Fin 8))
    (fun _ h ↦ E₈_apex_pairs h) (inner_c_lineGraphVector _)
    (by rw [hx.inner_apex_self hr, hn]; norm_num)
    (by rw [← Fintype.card_congr (completeGraphEdgeEquiv (Fin 8)), E₈.card_CEdge, hn])
  have hg : ((⊤ : SimpleGraph (Fin 8)).lineGraph.switch H).IsRegularOfDegree 12 := by
    intro v
    obtain ⟨u, rfl⟩ := g.surjective v
    exact (g.degree_eq u).trans (hr u)
  rcases nonempty_iso_triangular8_or_chang_of_switch_triangular8 H hg with h | h | h | h
  · obtain ⟨q⟩ := h
    exact Or.inl ⟨g.trans q⟩
  · obtain ⟨q⟩ := h
    exact Or.inr (Or.inl ⟨g.trans q⟩)
  · obtain ⟨q⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨g.trans q⟩))
  · obtain ⟨q⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨g.trans q⟩))

end SimpleGraph
