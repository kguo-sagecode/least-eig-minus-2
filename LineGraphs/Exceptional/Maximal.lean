/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.Admissible
import LineGraphs.Representation.Hoffman

/-! # Maximal exceptional graphs

Proposition `prop:maximal` (Proposition 3.7) of [Exc]. Maximality is expressed by
surjectivity of every induced embedding into a finite exceptional graph. The definition
uses targets on `Fin n`; `IsMaximalExceptional.embedding_surjective` allows any finite
vertex type, so this entails no restriction on the containing graph.
-/

namespace SimpleGraph

variable {V W E : Type*} [DecidableEq V] [DecidableEq W]
  {X : SimpleGraph V} {Z : SimpleGraph W} [DecidableRel X.Adj] [DecidableRel Z.Adj]

-- Proposition 3.7 [Exc]
/-- The restriction step in `prop:maximal` (Proposition 3.7) of [Exc]: a root-system
representation restricts along every induced graph embedding. -/
theorem IsRepresentedIn.comp_embedding [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : LineSystem E} (hZ : Z.IsRepresentedIn S) (f : X ↪g Z) : X.IsRepresentedIn S :=
  (hZ.induce (Set.range f)).comp_iso f.isoInduceRange

-- Proposition 3.7 [Exc]
omit [DecidableEq V] [DecidableEq W] [DecidableRel X.Adj] [DecidableRel Z.Adj] in
/-- The hereditary property used in `prop:maximal` (Proposition 3.7) of [Exc], via
[CGSS, Theorem 4.2]: induced subgraphs of generalized line graphs are generalized line graphs. -/
theorem IsGeneralizedLineGraph.of_embedding (hZ : Z.IsGeneralizedLineGraph) (f : X ↪g Z) :
    X.IsGeneralizedLineGraph := by
  classical
  obtain ⟨n, hn⟩ := hZ.exists_isRepresentedIn_Dn
  exact ((hn.comp_embedding f).of_isometricInclusion
    (LineSystem.Dn.inclusionOfLE (Nat.le_succ n))).isGeneralizedLineGraph_of_Dn (Nat.succ_pos n)

variable [Finite V] [Finite W]

-- Proposition 3.7 [Exc]
/-- The representation fact used in `prop:maximal` (Proposition 3.7) of [Exc]: an
exceptional graph is represented in `E₈`, by Hoffman's theorem [CGSS, Theorem 4.10]. -/
theorem IsExceptional.isRepresentedIn_E₈ (hX : X.IsExceptional) :
    X.IsRepresentedIn LineSystem.E₈ :=
  (hoffman hX.1 hX.2.1).resolve_left hX.2.2

-- Proposition 3.7 [Exc]
/-- The paragraph before `prop:maximal` (Proposition 3.7) of [Exc]: every certificate
of an exceptional graph has at most eight vertices. -/
theorem IsExceptional.card_certificate_le_eight (hX : X.IsExceptional) {B : Finset V}
    (hB : X.integralGramMatrix.IsGramCertificate B) : B.card ≤ 8 := by
  let := Fintype.ofFinite V
  rw [hB.card_eq_rank X.integralGramMatrix_isSymm, X.integralGramMatrix_cast]
  exact hX.isRepresentedIn_E₈.posSemidef_two_add_adjMatrix_and_rank_le_eight.2

-- Proposition 3.7 [Exc]
/-- Exceptionalness is invariant under isomorphism, as used for the maximal classes
in `prop:maximal` (Proposition 3.7) of [Exc]. -/
theorem Iso.isExceptional_iff (e : X ≃g Z) : X.IsExceptional ↔ Z.IsExceptional := by
  let := Fintype.ofFinite V
  let := Fintype.ofFinite W
  constructor
  · intro hX
    exact ⟨e.connected_iff.mp hX.1,
      (hX.isRepresentedIn_E₈.comp_iso e.symm).posSemidef_two_add_adjMatrix_and_rank_le_eight.1,
      fun hZ => hX.2.2 (hZ.of_embedding e.toEmbedding)⟩
  · intro hZ
    exact ⟨e.connected_iff.mpr hZ.1,
      (hZ.isRepresentedIn_E₈.comp_iso e).posSemidef_two_add_adjMatrix_and_rank_le_eight.1,
      fun hX => hZ.2.2 (hX.of_embedding e.symm.toEmbedding)⟩

-- Proposition 3.7 [Exc]
/-- The definition preceding `prop:maximal` (Proposition 3.7) of [Exc]: an exceptional
graph has no proper induced embedding into any finite exceptional graph. Targets on
`Fin n` suffice; see `IsMaximalExceptional.embedding_surjective` for arbitrary finite targets.
Agreement with the note requires a finite source vertex type; the unrestricted
predicate also has a formal meaning on infinite types, outside the note's scope. -/
def IsMaximalExceptional (X : SimpleGraph V) [DecidableRel X.Adj] : Prop :=
  X.IsExceptional ∧ ∀ (n : ℕ) (Z : SimpleGraph (Fin n)) [DecidableRel Z.Adj],
    Z.IsExceptional → ∀ f : X ↪g Z, Function.Surjective f

-- Proposition 3.7 [Exc]
omit [Finite V] in
/-- The definition in `prop:maximal` (Proposition 3.7) applies to containing graphs
on any finite vertex type, not just the labelled targets used in the definition. -/
theorem IsMaximalExceptional.embedding_surjective (hX : X.IsMaximalExceptional)
    (hZ : Z.IsExceptional) (f : X ↪g Z) : Function.Surjective f := by
  classical
  let := Fintype.ofFinite W
  let e := Iso.comap (Fintype.equivFin W).symm Z
  have hs := hX.2 _ _ (e.isExceptional_iff.mpr hZ) (f.trans e.symm.toEmbedding)
  intro w
  obtain ⟨v, hv⟩ := hs (e.symm w)
  exact ⟨v, e.symm.injective hv⟩

-- Proposition 3.7 [Exc]
omit [DecidableEq W] [DecidableRel Z.Adj] [Finite W] in
/-- The boundary-vertex step of `prop:maximal` (Proposition 3.7) of [Exc]: in a
connected graph every nonempty proper vertex set has an edge to its complement. -/
theorem Connected.exists_adj_mem_notMem (hZ : Z.Connected) {S : Set W}
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) : ∃ u ∈ S, ∃ v ∉ S, Z.Adj u v := by
  classical
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hSc
  obtain ⟨p⟩ := hZ u v
  have boundary : ∀ {a b : W}, Z.Walk a b → a ∈ S → b ∉ S →
      ∃ u ∈ S, ∃ v ∉ S, Z.Adj u v := by
    intro a b p
    induction p with
    | nil => exact fun ha hb => (hb ha).elim
    | @cons a b c hab p ih =>
      intro ha hc
      by_cases hb : b ∈ S
      · exact ih hb hc
      · exact ⟨a, ha, b, hb, hab⟩
  exact boundary p hu hv

-- Proposition 3.7 [Exc]
/-- The induced one-vertex extension used in `prop:maximal` (Proposition 3.7) of [Exc]. -/
def Embedding.adjoinVertex (f : X ↪g Z) (v : W) (hv : v ∉ Set.range f) :
    X.adjoinVertex {u | Z.Adj v (f u)} ↪g Z where
  toFun := fun w => w.elim v f
  inj' := by
    rintro (_ | u) (_ | w) h
    · rfl
    · exact (hv ⟨w, h.symm⟩).elim
    · exact (hv ⟨u, h⟩).elim
    · exact congrArg some (f.injective h)
  map_rel_iff' := by
    rintro (_ | u) (_ | w)
    · exact iff_false_intro (Z.loopless.irrefl v)
    · exact Iff.rfl
    · exact Z.adj_comm _ _
    · exact f.map_rel_iff

-- Proposition 3.7 [Exc]
/-- A represented nonempty-neighbour extension of an exceptional graph remains
exceptional, as proved in `prop:maximal` (Proposition 3.7) of [Exc]. -/
theorem IsExceptional.adjoinVertex (hX : X.IsExceptional) {N : Set V} (hN : N.Nonempty)
    (hY : (X.adjoinVertex N).IsRepresentedIn LineSystem.E₈) :
    (X.adjoinVertex N).IsExceptional := by
  classical
  let := Fintype.ofFinite V
  exact ⟨hX.1.adjoinVertex X N hN,
    hY.posSemidef_two_add_adjMatrix_and_rank_le_eight.1,
    fun h => hX.2.2 (h.of_embedding (X.adjoinVertexEmbedding N))⟩

-- Proposition 3.7 [Exc]
/-- Proposition `prop:maximal` (Proposition 3.7) of [Exc]: maximality is equivalent
to absence of a nonempty-neighbour extension represented in `E₈`. -/
theorem IsExceptional.isMaximalExceptional_iff_no_extension (hX : X.IsExceptional) :
    X.IsMaximalExceptional ↔
      ∀ N : Set V, N.Nonempty → ¬ (X.adjoinVertex N).IsRepresentedIn LineSystem.E₈ := by
  classical
  constructor
  · intro hm N hN hY
    obtain ⟨v, hv⟩ := hm.embedding_surjective (hX.adjoinVertex hN hY)
      (X.adjoinVertexEmbedding N) none
    exact Option.some_ne_none v hv
  · intro hext
    refine ⟨hX, ?_⟩
    intro n Z _ hZ f
    by_contra hsurj
    have hSc : (Set.range f)ᶜ.Nonempty := by
      change ¬ ∀ w, ∃ v, f v = w at hsurj
      push Not at hsurj
      obtain ⟨v, hv⟩ := hsurj
      exact ⟨v, fun ⟨u, hu⟩ => hv u hu⟩
    have hS : (Set.range f).Nonempty := Set.range_nonempty_iff_nonempty.mpr hX.1.nonempty
    obtain ⟨_, ⟨u, rfl⟩, v, hv, huv⟩ := hZ.1.exists_adj_mem_notMem hS hSc
    exact hext {u | Z.Adj v (f u)} ⟨u, huv.symm⟩
      (hZ.isRepresentedIn_E₈.comp_embedding (f.adjoinVertex v hv))

-- Proposition 3.7 [Exc]
/-- Proposition `prop:maximal` (Proposition 3.7) of [Exc]: an exceptional graph is
maximal exactly when its chosen certificate has no nonzero admissible vector. -/
theorem IsExceptional.isMaximalExceptional_iff_no_admissible (hX : X.IsExceptional)
    {B : Finset V} (hB : X.integralGramMatrix.IsGramCertificate B) :
    X.IsMaximalExceptional ↔
      ∀ s : B → ℤ, s ≠ 0 → ¬ X.integralGramMatrix.IsAdmissible B s := by
  rw [hX.isMaximalExceptional_iff_no_extension]
  have hr := hX.card_certificate_le_eight hB
  constructor
  · intro h s hne hs
    exact h _ (hs.neighbors_nonempty (hB.det_pos X.integralGramMatrix_isSymm).ne' hne)
      (isRepresentedIn_adjoinVertex_admissibleNeighbors hX.1 hB hr hs hne)
  · intro h N hN hY
    obtain ⟨s, hne, hs, _⟩ :=
      (isRepresentedIn_adjoinVertex_iff_exists_admissible hX.1 hB hr hN).mp hY
    exact h s hne hs

-- Proposition 3.7 [Exc]
/-- Maximal exceptionalness is invariant under isomorphism, as required by the
paragraph after `prop:maximal` (Proposition 3.7) of [Exc]. -/
theorem Iso.isMaximalExceptional_iff (e : X ≃g Z) :
    X.IsMaximalExceptional ↔ Z.IsMaximalExceptional := by
  constructor
  · intro hX
    refine ⟨e.isExceptional_iff.mp hX.1, ?_⟩
    intro n Y _ hY f y
    obtain ⟨x, hx⟩ := hX.2 n Y hY (e.toEmbedding.trans f) y
    exact ⟨e x, hx⟩
  · intro hZ
    refine ⟨e.isExceptional_iff.mpr hZ.1, ?_⟩
    intro n Y _ hY f y
    obtain ⟨z, hz⟩ := hZ.2 n Y hY (e.symm.toEmbedding.trans f) y
    exact ⟨e.symm z, hz⟩

end SimpleGraph
