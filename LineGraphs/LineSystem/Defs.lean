/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Basic

/-!
# Line systems

A set of lines at 60° and 90° (Section 2 of [CGSS]) is recorded by the set `Φ` of vectors of
squared norm 2 on its lines, taken with both signs. This file defines line systems, the properties
of Definitions 2.1 and 2.2, indecomposability, isomorphisms, and the number of lines. The names
follow `cgss/notation.md` §10.

## Main definitions

* `LineSystem V`: a finite set `Φ ⊆ V` with `Φ = -Φ`, `⟪r, r⟫ = 2` and `⟪r, s⟫ ∈ {-2, …, 2}`.
* `LineSystem.IsStarClosed`: Definition 2.1 of [CGSS].
* `LineSystem.IsMaximal`: Definition 2.2 of [CGSS].
* `LineSystem.IsIndecomposable`: `Φ` is not the union of two mutually orthogonal parts.
* `LineSystem.Iso`: a bijection of the vector sets that preserves inner products.
* `LineSystem.numLines`: the number of lines, `|Φ| / 2`.
-/

open scoped RealInnerProductSpace

/-- A set of lines at 60° and 90° (Section 2 of [CGSS]), recorded by the vectors of squared
norm 2 on its lines, with both signs. The values `±2` occur only for `s = ±r`.
Spanning is not assumed. In finite dimension the angle and normalization conditions
force finiteness, so recording it loses no systems from the paper. -/
structure LineSystem (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  /-- The vectors of squared norm 2 on the lines, with both signs. -/
  Φ : Set V
  finite : Φ.Finite
  inner_self : ∀ r ∈ Φ, ⟪r, r⟫ = 2
  neg_mem : ∀ r ∈ Φ, -r ∈ Φ
  inner_mem : ∀ r ∈ Φ, ∀ s ∈ Φ, ⟪r, s⟫ ∈ ({-2, -1, 0, 1, 2} : Set ℝ)

namespace LineSystem

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

-- Definition 2.1
/-- Definition 2.1 of [CGSS]: with two lines of a star, `S` contains the third. -/
def IsStarClosed (S : LineSystem V) : Prop :=
  ∀ r ∈ S.Φ, ∀ s ∈ S.Φ, ⟪r, s⟫ = -1 → r + s ∈ S.Φ

-- Definition 2.2
/-- Definition 2.2 of [CGSS]: `S` contains every line of its span at 60° or 90° to all of its
lines. The paper takes the lines to span `ℝⁿ` (Section 2, first paragraph), so maximality is
within `Submodule.span ℝ S.Φ`; in the ambient space, `An n` and `E₇` would never be maximal. The
values `±2` allow a line already in `S` (errata, Implicit hypothesis 7). -/
def IsMaximal (S : LineSystem V) : Prop :=
  ∀ v ∈ Submodule.span ℝ S.Φ, ⟪v, v⟫ = 2 →
    (∀ r ∈ S.Φ, ⟪v, r⟫ ∈ ({-2, -1, 0, 1, 2} : Set ℝ)) → v ∈ S.Φ

/-- Indecomposability in Section 2 of [CGSS]: `Φ` is not the union of two nonempty,
mutually orthogonal parts. For a spanning nonempty system this is the paper's
condition on proper orthogonal subspaces (blueprint `def:indecomposable`).
The empty system satisfies this predicate; classification also assumes nonemptiness
(errata, Implicit hypothesis 4). -/
def IsIndecomposable (S : LineSystem V) : Prop :=
  ∀ P Q : Set V, P ∪ Q = S.Φ → (∀ p ∈ P, ∀ q ∈ Q, ⟪p, q⟫ = 0) → P = ∅ ∨ Q = ∅

/-- An isomorphism of line systems: a bijection of the vectors that preserves inner products. -/
structure Iso (S : LineSystem V) (T : LineSystem W) extends S.Φ ≃ T.Φ where
  inner_map (r s : S.Φ) : ⟪(toEquiv r : W), toEquiv s⟫ = ⟪(r : V), s⟫

/-- The number of lines of `S`: each line carries two vectors of `Φ`. -/
noncomputable def numLines (S : LineSystem V) : ℕ :=
  S.Φ.ncard / 2

/-- Restriction of a line system to the orthogonal complement of `v`. -/
noncomputable def orthogonalTo {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (S : LineSystem V) (v : V) : LineSystem V where
  Φ := {r | r ∈ S.Φ ∧ ⟪r, v⟫ = 0}
  finite := S.finite.subset (fun _ h ↦ h.1)
  inner_self := fun r hr ↦ S.inner_self r hr.1
  neg_mem := by
    intro r hr
    exact ⟨S.neg_mem r hr.1, by simp [hr.2]⟩
  inner_mem := fun r hr s hs ↦ S.inner_mem r hr.1 s hs.1

/-- Restriction to an orthogonal complement only removes roots. -/
theorem orthogonalTo_Φ_subset (S : LineSystem V) (v : V) :
    (S.orthogonalTo v).Φ ⊆ S.Φ := fun _ h ↦ h.1

/-- Orthogonal restriction preserves star-closure. -/
theorem IsStarClosed.orthogonalTo {S : LineSystem V} (hS : S.IsStarClosed) (v : V) :
    (S.orthogonalTo v).IsStarClosed := by
  intro r hr s hs hrs
  exact ⟨hS r hr.1 s hs.1 hrs, by rw [inner_add_left, hr.2, hs.2, add_zero]⟩

end LineSystem
