/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.ExtensionGraph
import LineGraphs.Exceptional.NonCut
import LineGraphs.Representation.SymmetricSquare

/-! # Graph isomorphisms and the levels of the growth

The graph-theoretic ingredients of `thm:growth` (Theorem 3.6) of [Exc].
-/

namespace SimpleGraph

variable {V W : Type*}

-- Theorem 3.6 [Exc]
/-- Transporting a neighbour set through an isomorphism in the proof of `thm:growth`
(Theorem 3.6) of [Exc]. -/
def Iso.adjoinVertex {X : SimpleGraph V} {Y : SimpleGraph W} (e : X ≃g Y) (N : Set W) :
    X.adjoinVertex (e ⁻¹' N) ≃g Y.adjoinVertex N where
  toEquiv := Equiv.optionCongr e.toEquiv
  map_rel_iff' := by
    rintro (_ | u) (_ | v)
    · exact Iff.rfl
    · exact Iff.rfl
    · exact Iff.rfl
    · exact e.map_rel_iff

-- Lemma 3.1 / Theorem 3.6 [Exc]
/-- Reconstruct a graph from a vertex and its deletion, in `lem:noncut` (Lemma 3.1)
and `thm:growth` (Theorem 3.6) of [Exc]. -/
def Iso.adjoinVertexInduceCompl [DecidableEq W] {X : SimpleGraph V} {Z : SimpleGraph W}
    (v : W) (e : X ≃g Z.induce {v}ᶜ) :
    X.adjoinVertex {u | Z.Adj v (e u)} ≃g Z where
  toEquiv := (Equiv.optionCongr e.toEquiv).trans (Equiv.optionSubtypeNe v)
  map_rel_iff' := by
    rintro (_ | u) (_ | w)
    · exact ⟨fun h => (Z.loopless.irrefl v h).elim, False.elim⟩
    · exact Iff.rfl
    · exact Z.adj_comm _ _
    · exact e.map_rel_iff

-- Theorem 3.6 [Exc]
/-- The levels in `thm:growth` (Theorem 3.6) of [Exc] are invariant under graph isomorphism. -/
theorem mem_levels_of_iso {n : ℕ} {X Y : SimpleGraph (Fin n)} (e : X ≃g Y)
    (hX : X ∈ levels n) : Y ∈ levels n := by
  classical
  exact ⟨e.connected_iff.mp hX.1, hX.2.comp_iso e.symm⟩

-- Theorem 3.6 [Exc]
/-- The singleton graph starts the growth in `thm:growth` (Theorem 3.6) of [Exc]. -/
theorem bot_mem_levels_one : (⊥ : SimpleGraph (Fin 1)) ∈ levels 1 := by
  have h (X : SimpleGraph (Fin 1)) : X ∈ levels 1 := by
    classical
    refine ⟨Connected.of_subsingleton, ?_⟩
    refine ⟨fun _ => LineSystem.e₇Normal, isRepresentation_iff.mpr ?_,
      fun _ => LineSystem.e₇Normal_mem_E₈⟩
    intro u v
    obtain rfl : u = v := Subsingleton.elim _ _
    simpa only [ite_true] using LineSystem.E₈.inner_self _ LineSystem.e₇Normal_mem_E₈
  exact h ⊥

-- Theorem 3.6 [Exc]
/-- The levels are empty at and above 37 vertices, as stated before `thm:growth`
(Theorem 3.6) of [Exc], by [CGSS, Theorem 4.3]. -/
theorem levels_eq_empty_of_ge {n : ℕ} (hn : 37 ≤ n) : levels n = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro X hX
  have hc := hX.2.card_le_36
  simp only [Fintype.card_fin] at hc
  omega

-- Theorem 3.6 [Exc]
/-- Every level graph above one vertex has a connected parent, as used in
`thm:growth` (Theorem 3.6) of [Exc]. -/
theorem exists_parent_of_mem_levels {n : ℕ} (hn : 1 ≤ n) {Z : SimpleGraph (Fin (n + 1))}
    (hZ : Z ∈ levels (n + 1)) :
    ∃ X ∈ levels n, ∃ N : Set (Fin n), N.Nonempty ∧ Nonempty (X.adjoinVertex N ≃g Z) := by
  classical
  have : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨v, hv, ⟨w, hw⟩, hE⟩ := hZ.1.exists_noncut_isRepresentedIn_E₈ hZ.2
  let e : Fin n ≃ ({v}ᶜ : Set (Fin (n + 1))) := finSuccAboveEquiv v
  let X := (Z.induce {v}ᶜ).comap e
  let f : X ≃g Z.induce {v}ᶜ := Iso.comap e _
  refine ⟨X, ⟨f.connected_iff.mpr hv, hE.comp_iso f⟩, {u | Z.Adj v (f u)}, ?_,
    ⟨f.adjoinVertexInduceCompl v⟩⟩
  have hw' : w ∈ ({v}ᶜ : Set (Fin (n + 1))) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hw.ne.symm
  obtain ⟨u, hu⟩ := f.surjective ⟨w, hw'⟩
  refine ⟨u, ?_⟩
  change Z.Adj v (f u)
  rw [hu]
  exact hw

-- Theorem 3.6 [Exc]
/-- A canonical form is idempotent, as used for uniqueness in `thm:growth`
(Theorem 3.6) of [Exc]. -/
theorem CanonicalForm.idempotent (q : CanonicalForm) {n : ℕ} (X : SimpleGraph (Fin n)) :
    q.canon (q.canon X) = q.canon X :=
  (q.eq_iff _ _).mpr ⟨q.iso X⟩

-- Theorem 3.6 [Exc]
/-- Every generated graph is a canonical form in `thm:growth` (Theorem 3.6) of [Exc]. -/
theorem canon_eq_self_of_mem_growth (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} {X : SimpleGraph (Fin n)} (hX : X ∈ growth c q n) : q.canon X = X := by
  cases n with
  | zero => exact hX.elim
  | succ n =>
    cases n with
    | zero =>
      have : Subsingleton (SimpleGraph (Fin 1)) := SimpleGraph.subsingleton_iff.mpr inferInstance
      exact Subsingleton.elim _ _
    | succ n =>
      obtain ⟨_, _, Z, _, rfl⟩ := hX
      exact q.idempotent Z

-- Theorem 3.6 [Exc]
/-- At most one generated graph represents an isomorphism class in `thm:growth`
(Theorem 3.6) of [Exc]. -/
theorem eq_of_mem_growth_of_iso (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} {X Y : SimpleGraph (Fin n)} (hX : X ∈ growth c q n) (hY : Y ∈ growth c q n)
    (he : Nonempty (X ≃g Y)) : X = Y := by
  have h := (q.eq_iff X Y).mpr he
  rwa [canon_eq_self_of_mem_growth c q hX, canon_eq_self_of_mem_growth c q hY] at h

end SimpleGraph
