/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.RootLattice
import LineGraphs.Exceptional.LatticeIntegral
import LineGraphs.Representation.TypeDNormalForm

/-! # Recognizing exceptional graphs by their root lattices

Assertions (1) and (2) of Proposition `prop:types` (Proposition 2.6) of [Exc].
The type is that of the lattice roots, rather than a containing root system.
-/

open Module Submodule
open scoped RealInnerProductSpace

namespace LineSystem.RootType

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6) of [Exc]: the classical types
in the simply laced classification are `A` and `D`. -/
def IsClassical : RootType → Prop
  | .A _ _ | .D _ _ => True
  | .E₆ | .E₇ | .E₈ => False

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6) of [Exc]: the three exceptional
types in the simply laced classification. This is a predicate on root types;
`SimpleGraph.IsExceptional` is the separate predicate on graphs. -/
def IsExceptional (t : RootType) : Prop := t = .E₆ ∨ t = .E₇ ∨ t = .E₈

-- Proposition 2.6 [Exc]
/-- The exhaustive type distinction in Proposition `prop:types`
(Proposition 2.6) of [Exc]. -/
theorem not_isClassical_iff_isExceptional (t : RootType) :
    ¬ t.IsClassical ↔ t.IsExceptional := by
  cases t <;> simp [IsClassical, IsExceptional]

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6) of [Exc]: rank and lattice
determinant recognize the three exceptional types. -/
theorem isExceptional_iff_rank_latticeDet (t : RootType) :
    t.IsExceptional ↔ (t.rank, t.latticeDet) = (6, 3) ∨
      (t.rank, t.latticeDet) = (7, 2) ∨ (t.rank, t.latticeDet) = (8, 1) := by
  cases t <;> simp [IsExceptional, rank, latticeDet]
  omega

-- Proposition 2.6 [Exc]
/-- The containment step in Proposition `prop:types` (Proposition 2.6) of
[Exc]: every exceptional model lattice contains the simple roots of `E₆`
with their Gram matrix. -/
theorem exists_E₆_simple_roots (t : RootType) (ht : t.IsExceptional) :
    ∃ z : Fin 6 → span ℤ t.model.Φ,
      Matrix.gram ℝ (fun i ↦ (z i : EuclideanSpace ℝ (Fin t.dim))) =
        Matrix.gram ℝ LineSystem.E₆.simpleRoot := by
  rcases ht with rfl | rfl | rfl
  · exact ⟨fun i ↦ ⟨_, subset_span (LineSystem.E₆.simpleRoot_mem i)⟩, rfl⟩
  · exact ⟨fun i ↦ ⟨_, subset_span
      (E₆_Φ_subset_E₇ (LineSystem.E₆.simpleRoot_mem i))⟩, rfl⟩
  · exact ⟨fun i ↦ ⟨_, subset_span
      (E₇_Φ_subset_E₈ (E₆_Φ_subset_E₇ (LineSystem.E₆.simpleRoot_mem i)))⟩, rfl⟩

end LineSystem.RootType

namespace SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6)(1) of [Exc]: a generalized
line graph cannot have an exceptional lattice-root type. -/
theorem IsRepresentation.not_rootType_isExceptional_of_isGeneralizedLineGraph
    (hx : X.IsRepresentation x) {t : LineSystem.RootType}
    (e : hx.latticeRoots.Iso t.model) (hX : X.IsGeneralizedLineGraph) :
    ¬ t.IsExceptional := by
  intro ht
  obtain ⟨n, y, hy, hm⟩ := hX.exists_isRepresentedIn_Dn
  obtain ⟨f, hf⟩ := e.symm.exists_span_int_equiv
  let f' := f.trans (LinearEquiv.ofEq _ _ hx.span_int_latticeRoots)
  obtain ⟨g, hg, _⟩ :=
    InnerProductSpace.exists_span_int_equiv_of_gram_eq x y (hx.trans hy.symm)
  obtain ⟨s, hs⟩ := t.exists_E₆_simple_roots ht
  have hspan : span ℤ (Set.range y) ≤ span ℤ (LineSystem.Dn n).Φ :=
    span_mono (Set.range_subset_iff.mpr hm)
  let z : Fin 6 → span ℤ (LineSystem.Dn n).Φ := fun i ↦
    ⟨g (f' (s i)), hspan (g (f' (s i))).property⟩
  apply LineSystem.E₆.not_exists_gram_in_span_Dn n
  refine ⟨z, ?_⟩
  ext i j
  calc
    _ = ⟪(f' (s i) : E), (f' (s j) : E)⟫ := hg _ _
    _ = ⟪(s i : EuclideanSpace ℝ (Fin t.dim)),
        (s j : EuclideanSpace ℝ (Fin t.dim))⟫ := hf _ _
    _ = _ := congrFun (congrFun hs i) j

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6)(1) of [Exc]: a graph whose
lattice roots have type `t` is a generalized line graph exactly when `t` is
classical. The specified lattice-root isomorphism makes connectedness redundant.
For a connected graph with positive semidefinite `M(X)`, choose a representation
using `exists_representation_iff_posSemidef` and this isomorphism using
`IsRepresentation.exists_unique_root_lattice` to recover the note's graph-only form. -/
theorem IsRepresentation.isGeneralizedLineGraph_iff_rootType_isClassical
    (hx : X.IsRepresentation x) {t : LineSystem.RootType}
    (e : hx.latticeRoots.Iso t.model) : X.IsGeneralizedLineGraph ↔ t.IsClassical := by
  constructor
  · intro hX
    have ht := hx.not_rootType_isExceptional_of_isGeneralizedLineGraph e hX
    have := t.not_isClassical_iff_isExceptional
    tauto
  · intro ht
    have hr := hx.isRepresentedIn_latticeRoots.of_iso e
    cases t with
    | A n hn =>
      exact (hr.mono (LineSystem.An_Φ_subset_Dn n)).isGeneralizedLineGraph_of_Dn (by omega)
    | D n hn => exact hr.isGeneralizedLineGraph_of_Dn (by omega)
    | E₆ | E₇ | E₈ => exact ht.elim

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6)(2) of [Exc]: a connected
represented graph is exceptional exactly when its lattice roots have one of
the three exceptional types. -/
theorem IsRepresentation.isExceptional_iff_rootType_isExceptional
    (hx : X.IsRepresentation x) (hX : X.Connected) {t : LineSystem.RootType}
    (e : hx.latticeRoots.Iso t.model) : X.IsExceptional ↔ t.IsExceptional := by
  rw [IsExceptional, and_iff_right hX, and_iff_right (hx.posSemidef X),
    hx.isGeneralizedLineGraph_iff_rootType_isClassical e,
    t.not_isClassical_iff_isExceptional]

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6)(2) of [Exc]: the pairs
`(6,3)`, `(7,2)` and `(8,1)` recognize exceptional connected represented graphs. -/
theorem IsRepresentation.isExceptional_iff_rank_latticeDet
    (hx : X.IsRepresentation x) (hX : X.Connected) :
    X.IsExceptional ↔
      (((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank, X.latticeDet) = (6, 3) ∨
      (((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank, X.latticeDet) = (7, 2) ∨
      (((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank, X.latticeDet) = (8, 1) := by
  obtain ⟨t, ⟨⟨e⟩, ht, _, _, hd⟩, _⟩ := hx.exists_unique_root_lattice hX
  rw [hx.isExceptional_iff_rootType_isExceptional hX e, t.isExceptional_iff_rank_latticeDet,
    hx.rank_two_add_adjMatrix X, ← ht, hd]

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6)(2) of [Exc], expressed using
only the graph: exceptionalness is decided by its rank and lattice determinant. -/
theorem isExceptional_iff_rank_latticeDet (X : SimpleGraph V) [DecidableRel X.Adj]
    (hX : X.Connected)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef) :
    X.IsExceptional ↔
      (((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank, X.latticeDet) = (6, 3) ∨
      (((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank, X.latticeDet) = (7, 2) ∨
      (((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank, X.latticeDet) = (8, 1) := by
  obtain ⟨x, hx⟩ := X.exists_representation_iff_posSemidef.mpr hp
  exact hx.isExceptional_iff_rank_latticeDet hX

end SimpleGraph
