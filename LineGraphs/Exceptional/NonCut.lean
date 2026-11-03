/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Basic
import LineGraphs.LineSystem.Models
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # Deleting a non-cut vertex

Lemma `lem:noncut` (Lemma 3.1) of [Exc]. Mathlib already supplies the spanning-tree argument.
-/

namespace SimpleGraph

variable {V : Type*} [Finite V] [Nontrivial V] {Z : SimpleGraph V}

-- Lemma 3.1 [Exc]
/-- Lemma `lem:noncut` (Lemma 3.1) of [Exc]: a finite connected graph with at least
two vertices has a vertex whose deletion leaves a connected graph, and that vertex has a
neighbour. The cardinality hypothesis is expressed by `Nontrivial V`. -/
theorem Connected.exists_noncut_with_neighbor (hZ : Z.Connected) :
    ∃ v : V, (Z.induce {v}ᶜ).Connected ∧ ∃ u, Z.Adj v u := by
  obtain ⟨v, hv⟩ := hZ.exists_connected_induce_compl_singleton_of_finite_nontrivial
  exact ⟨v, hv, hZ.preconnected.exists_adj_of_nontrivial v⟩

-- Lemma 3.1 [Exc]
/-- Lemma `lem:noncut` (Lemma 3.1) of [Exc]: the non-cut deletion also preserves a
representation in `E₈`. -/
theorem Connected.exists_noncut_isRepresentedIn_E₈ [DecidableEq V] [DecidableRel Z.Adj]
    (hZ : Z.Connected) (hE : Z.IsRepresentedIn LineSystem.E₈) :
    ∃ v : V, (Z.induce {v}ᶜ).Connected ∧ (∃ u, Z.Adj v u) ∧
      (Z.induce {v}ᶜ).IsRepresentedIn LineSystem.E₈ := by
  obtain ⟨v, hv, hn⟩ := hZ.exists_noncut_with_neighbor
  exact ⟨v, hv, hn, hE.induce _⟩

end SimpleGraph
