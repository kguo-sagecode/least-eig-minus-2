/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.GraphRepresentation
import LineGraphs.LineSystem.Inclusions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The representation interface of Section 4

Definition `def:represented` and Lemmas `lem:4-lines`, `lem:4-transport`, and `lem:4-sub`
of the Section 4 blueprint for [CGSS]. The matrix definition `IsRepresentation` and its
spectral consequences are imported from `Spectral.GraphRepresentation`.
-/

open scoped RealInnerProductSpace

namespace SimpleGraph

variable {V W E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The three graph conventions of [CGSS], notation §4: distinct vectors are adjacent
when their inner product is the specified value. -/
def innerGraph (x : V → E) (t : ℝ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ⟪x u, x v⟫ = t
  symm.symm u v h := ⟨h.1.symm, (real_inner_comm _ _).trans h.2⟩

/-- Definition `def:represented`, Section 4 of [CGSS]: adjacency means inner product one. -/
abbrev representedGraph (x : V → E) : SimpleGraph V := innerGraph x 1

noncomputable instance (x : V → E) (t : ℝ) : DecidableRel (innerGraph x t).Adj :=
  Classical.decRel _

variable [DecidableEq V] {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

/-- Definition `def:represented`, Section 4 of [CGSS], entry by entry. -/
theorem isRepresentation_iff : X.IsRepresentation x ↔
    ∀ u v, ⟪x u, x v⟫ = if u = v then 2 else if X.Adj u v then 1 else 0 := by
  constructor
  · intro h u v
    have huv := congrFun (congrFun h u) v
    change ⟪x u, x v⟫ = _ at huv
    by_cases he : u = v <;>
      simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, adjMatrix_apply, he] using huv
  · intro h
    ext u v
    change ⟪x u, x v⟫ = _
    rw [h u v]
    by_cases he : u = v <;>
      simp [Matrix.add_apply, Matrix.smul_apply, adjMatrix_apply, he]

/-- Lemma `lem:4-lines`, step `s4linesinj`, Section 4 of [CGSS]: squared norms are two. -/
theorem IsRepresentation.inner_self (hx : X.IsRepresentation x) (u : V) :
    ⟪x u, x u⟫ = 2 := by
  simpa using isRepresentation_iff.mp hx u u

/-- Definition `def:represented`, Section 4 of [CGSS]: adjacent products are one. -/
theorem IsRepresentation.inner_of_adj (hx : X.IsRepresentation x) {u v : V}
    (huv : X.Adj u v) : ⟪x u, x v⟫ = 1 := by
  simpa [huv, huv.ne] using isRepresentation_iff.mp hx u v

/-- Definition `def:represented`, Section 4 of [CGSS]: distinct nonadjacent products vanish. -/
theorem IsRepresentation.inner_of_not_adj (hx : X.IsRepresentation x) {u v : V}
    (hne : u ≠ v) (huv : ¬ X.Adj u v) : ⟪x u, x v⟫ = 0 := by
  simpa [huv, hne] using isRepresentation_iff.mp hx u v

/-- Lemma `lem:4-lines`, step `s4linesinj`, Section 4 of [CGSS]: off-diagonal products. -/
theorem IsRepresentation.inner_eq_zero_or_one (hx : X.IsRepresentation x) {u v : V}
    (hne : u ≠ v) : ⟪x u, x v⟫ = 0 ∨ ⟪x u, x v⟫ = 1 := by
  by_cases h : X.Adj u v
  · exact Or.inr (hx.inner_of_adj h)
  · exact Or.inl (hx.inner_of_not_adj hne h)

/-- Definition `def:represented`, Section 4 of [CGSS]: all products are nonnegative. -/
theorem IsRepresentation.inner_nonneg (hx : X.IsRepresentation x) (u v : V) :
    0 ≤ ⟪x u, x v⟫ := by
  rw [isRepresentation_iff.mp hx u v]
  split_ifs <;> norm_num

/-- Lemma `lem:4-lines`, step `s4linesinj`, Section 4 of [CGSS]: vertices give distinct roots. -/
theorem IsRepresentation.injective (hx : X.IsRepresentation x) : Function.Injective x := by
  intro u v huv
  by_contra hne
  have h := hx.inner_eq_zero_or_one hne
  rw [huv, hx.inner_self] at h
  norm_num at h

/-- Lemma `lem:4-lines`, step `s4linesinj`, Section 4 of [CGSS]: opposite roots cannot occur. -/
theorem IsRepresentation.ne_neg (hx : X.IsRepresentation x) (u v : V) : x u ≠ -x v := by
  intro h
  have hn := hx.inner_nonneg u v
  rw [h, inner_neg_left, hx.inner_self] at hn
  norm_num at hn

/-- Definition `def:represented`, Section 4 of [CGSS]: the Gram family recovers adjacency. -/
theorem IsRepresentation.adj_iff (hx : X.IsRepresentation x) (u v : V) :
    X.Adj u v ↔ ⟪x u, x v⟫ = 1 := by
  constructor
  · exact hx.inner_of_adj
  intro h
  by_cases he : u = v
  · subst v
    rw [hx.inner_self] at h
    norm_num at h
  by_contra hn
  rw [hx.inner_of_not_adj he hn] at h
  norm_num at h

/-- Definition `def:represented`, Section 4 of [CGSS]: the represented graph is the given graph. -/
theorem IsRepresentation.representedGraph_eq (hx : X.IsRepresentation x) :
    representedGraph x = X := by
  ext u v
  exact ⟨fun h ↦ (hx.adj_iff u v).mpr h.2,
    fun h ↦ ⟨h.ne, hx.inner_of_adj h⟩⟩

/-- Definition `def:represented`, Section 4 of [CGSS]: constructing a graph from its vectors. -/
theorem isRepresentation_representedGraph (x : V → E) (hn : ∀ u, ⟪x u, x u⟫ = 2)
    (hp : ∀ u v, u ≠ v → ⟪x u, x v⟫ = 0 ∨ ⟪x u, x v⟫ = 1) :
    (representedGraph x).IsRepresentation x := by
  apply isRepresentation_iff.mpr
  intro u v
  by_cases he : u = v
  · subst v
    simpa only [ite_true] using hn u
  rcases hp u v he with h | h <;> simp [he, representedGraph, innerGraph, h]

/-- Lemma `lem:4-sub`, Section 4 of [CGSS]: restrict the Gram identity to a principal submatrix. -/
theorem IsRepresentation.induce (hx : X.IsRepresentation x) (U : Set V) :
    (X.induce U).IsRepresentation (fun u : U ↦ x u) := by
  apply isRepresentation_iff.mpr
  intro u v
  simpa [Subtype.ext_iff] using isRepresentation_iff.mp hx u v

/-- Lemma `lem:4-transport`, Section 4 of [CGSS]: graph isomorphisms reindex a representation. -/
theorem IsRepresentation.comp_iso (hx : X.IsRepresentation x) [DecidableEq W]
    {Y : SimpleGraph W} [DecidableRel Y.Adj] (e : Y ≃g X) :
    Y.IsRepresentation (fun u ↦ x (e u)) := by
  apply isRepresentation_iff.mpr
  intro u v
  simpa only [e.injective.eq_iff, e.map_rel_iff] using isRepresentation_iff.mp hx (e u) (e v)

/-- Definition `def:represented`, Section 4 of [CGSS]: a representation by roots of `S`. -/
def IsRepresentedIn (X : SimpleGraph V) [DecidableRel X.Adj] (S : LineSystem E) : Prop :=
  ∃ x : V → E, X.IsRepresentation x ∧ ∀ u, x u ∈ S.Φ

/-- Lemma `lem:4-transport`, Section 4 of [CGSS]: an isometric inclusion preserves
the Gram matrix. -/
theorem IsRepresentation.of_isometricInclusion (hx : X.IsRepresentation x)
    {S : LineSystem E} {T : LineSystem F} (G : S.IsometricInclusion T)
    (hm : ∀ u, x u ∈ S.Φ) :
    X.IsRepresentation (fun u ↦ G.root (x u) (hm u)) := by
  apply isRepresentation_iff.mpr
  intro u v
  rw [G.inner_root]
  exact isRepresentation_iff.mp hx u v

/-- Lemma `lem:4-transport`, Section 4 of [CGSS]: transport through an inclusion of line systems. -/
theorem IsRepresentedIn.of_isometricInclusion {S : LineSystem E} {T : LineSystem F}
    (hX : X.IsRepresentedIn S) (G : S.IsometricInclusion T) : X.IsRepresentedIn T := by
  obtain ⟨x, hx, hm⟩ := hX
  exact ⟨_, hx.of_isometricInclusion G hm, fun u ↦ G.root_mem (x u) (hm u)⟩

/-- Lemma `lem:4-transport`, Section 4 of [CGSS]: root-set inclusion preserves representations. -/
theorem IsRepresentedIn.mono {S T : LineSystem E} (hX : X.IsRepresentedIn S)
    (hST : S.Φ ⊆ T.Φ) : X.IsRepresentedIn T := by
  obtain ⟨x, hx, hm⟩ := hX
  exact ⟨x, hx, fun u ↦ hST (hm u)⟩

/-- Lemma `lem:4-transport`, Section 4 of [CGSS]: transport through a line-system isomorphism. -/
theorem IsRepresentedIn.of_iso {S : LineSystem E} {T : LineSystem F}
    (hX : X.IsRepresentedIn S) (e : S.Iso T) : X.IsRepresentedIn T := by
  obtain ⟨x, hx, hm⟩ := hX
  refine ⟨fun u ↦ (e.toEquiv ⟨x u, hm u⟩ : F), ?_, fun u ↦ (e.toEquiv _).property⟩
  apply isRepresentation_iff.mpr
  intro u v
  rw [e.inner_map]
  exact isRepresentation_iff.mp hx u v

/-- Lemma `lem:4-sub`, Section 4 of [CGSS]: induced subgraphs use the same roots. -/
theorem IsRepresentedIn.induce {S : LineSystem E} (hX : X.IsRepresentedIn S) (U : Set V) :
    (X.induce U).IsRepresentedIn S := by
  obtain ⟨x, hx, hm⟩ := hX
  exact ⟨_, hx.induce U, fun u ↦ hm u⟩

/-- Lemma `lem:4-transport`, Section 4 of [CGSS]: reindex by a graph isomorphism. -/
theorem IsRepresentedIn.comp_iso {S : LineSystem E} (hX : X.IsRepresentedIn S)
    [DecidableEq W] {Y : SimpleGraph W} [DecidableRel Y.Adj] (e : Y ≃g X) :
    Y.IsRepresentedIn S := by
  obtain ⟨x, hx, hm⟩ := hX
  exact ⟨_, hx.comp_iso e, fun u ↦ hm (e u)⟩

end SimpleGraph
