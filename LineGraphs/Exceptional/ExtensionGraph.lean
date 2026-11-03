/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.CertificateDefs

/-! # Adding a vertex to a graph

The graph construction and its connectivity and Gram identities in `lem:extension`
(Lemma 3.4) of [Exc].
-/

open Matrix
open scoped RealInnerProductSpace

namespace SimpleGraph

variable {V E : Type*} (X : SimpleGraph V) (N : Set V)

-- Lemma 3.4 [Exc]
/-- Classical adjacency for the graph in `lem:extension` (Lemma 3.4) of [Exc]. -/
noncomputable instance adjoinVertexDecidableAdj : DecidableRel (X.adjoinVertex N).Adj :=
  Classical.decRel _

-- Lemma 3.4 [Exc]
/-- Old adjacency in `lem:extension` (Lemma 3.4) of [Exc]. -/
@[simp] theorem adjoinVertex_adj_some_some (u v : V) :
    (X.adjoinVertex N).Adj (some u) (some v) ↔ X.Adj u v := Iff.rfl

-- Lemma 3.4 [Exc]
/-- New adjacency in `lem:extension` (Lemma 3.4) of [Exc]. -/
@[simp] theorem adjoinVertex_adj_none_some (u : V) :
    (X.adjoinVertex N).Adj none (some u) ↔ u ∈ N := Iff.rfl

-- Lemma 3.4 [Exc]
/-- Symmetric new adjacency in `lem:extension` (Lemma 3.4) of [Exc]. -/
@[simp] theorem adjoinVertex_adj_some_none (u : V) :
    (X.adjoinVertex N).Adj (some u) none ↔ u ∈ N := Iff.rfl

-- Lemma 3.4 [Exc]
/-- The new vertex has no loop in `lem:extension` (Lemma 3.4) of [Exc]. -/
@[simp] theorem not_adjoinVertex_adj_none_none : ¬ (X.adjoinVertex N).Adj none none := id

-- Lemma 3.4 [Exc]
/-- The old graph is an induced subgraph of the graph in `lem:extension`
(Lemma 3.4) of [Exc]. -/
def adjoinVertexEmbedding : X ↪g X.adjoinVertex N where
  toFun := some
  inj' := Option.some_injective V
  map_rel_iff' := Iff.rfl

-- Lemma 3.4 [Exc]
/-- Adding a vertex with a nonempty neighbour set preserves connectivity in
`lem:extension` (Lemma 3.4) of [Exc]. -/
theorem Connected.adjoinVertex (hX : X.Connected) (hN : N.Nonempty) :
    (X.adjoinVertex N).Connected := by
  obtain ⟨w, hw⟩ := hN
  apply (connected_iff_exists_forall_reachable (G := X.adjoinVertex N)).mpr
  refine ⟨none, ?_⟩
  rintro (_ | u)
  · exact Reachable.rfl
  · exact (show (X.adjoinVertex N).Adj none (some w) from hw).reachable.trans
      ((hX w u).map (X.adjoinVertexEmbedding N).toHom)

open Classical in
-- Lemma 3.4 [Exc]
/-- The indicator of `N ∩ B` in `lem:extension` (Lemma 3.4) of [Exc]. -/
noncomputable def certificateIndicator (N : Set V) (B : Finset V) : B → ℤ :=
  fun b => if (b : V) ∈ N then 1 else 0

variable [DecidableEq V] [DecidableRel X.Adj]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x : V → E}

-- Lemma 3.4 [Exc]
/-- A representation of the enlarged graph restricts to a representation of the old
graph in `lem:extension` (Lemma 3.4) of [Exc]. -/
theorem IsRepresentation.of_adjoinVertex {y : Option V → E}
    (hy : (X.adjoinVertex N).IsRepresentation y) : X.IsRepresentation (fun u => y (some u)) := by
  apply isRepresentation_iff.mpr
  intro u v
  simpa only [Option.some.injEq, adjoinVertex_adj_some_some] using
    isRepresentation_iff.mp hy (some u) (some v)

open Classical in
-- Lemma 3.4 [Exc]
/-- Construct the representation in the converse of `lem:extension` (Lemma 3.4) of [Exc]. -/
theorem IsRepresentation.adjoinVertex (hx : X.IsRepresentation x) (y : E)
    (hy : ⟪y, y⟫ = 2) (hn : ∀ u, ⟪y, x u⟫ = if u ∈ N then 1 else 0) :
    (X.adjoinVertex N).IsRepresentation (Option.elim' y x) := by
  apply isRepresentation_iff.mpr
  rintro (_ | u) (_ | v)
  · simpa using hy
  · simpa using hn v
  · simpa only [Option.elim'_some, Option.elim'_none, Option.some_ne_none,
      ite_false, adjoinVertex_adj_some_none, real_inner_comm (x u) y] using hn u
  · simpa only [Option.elim'_some, Option.some.injEq, adjoinVertex_adj_some_some] using
      isRepresentation_iff.mp hx u v

end SimpleGraph
