/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.RootLatticeClassical
import LineGraphs.LineSystem.Classification

/-! # Classification and determinants of graph root lattices

Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]. The lattice, rather than an arbitrary
containing root system, determines the type and its determinant.
-/

open Module Submodule
open scoped RealInnerProductSpace

namespace LineSystem

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {S : LineSystem E} {T : LineSystem F}

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: an isomorphism of root systems
induces an integral isometry of their root lattices. -/
theorem Iso.exists_span_int_equiv (e : S.Iso T) :
    ∃ f : span ℤ S.Φ ≃ₗ[ℤ] span ℤ T.Φ,
      ∀ u v, ⟪(f u : F), (f v : F)⟫ = ⟪(u : E), (v : E)⟫ := by
  let : Fintype S.Φ := S.finite.fintype
  let x : S.Φ → E := Subtype.val
  let y : S.Φ → F := fun r ↦ e.toEquiv r
  have hx : Set.range x = S.Φ := by ext r; simp [x]
  have hy : Set.range y = T.Φ := by
    ext r
    constructor
    · rintro ⟨a, rfl⟩
      exact (e.toEquiv a).property
    · intro hr
      exact ⟨e.toEquiv.symm ⟨r, hr⟩,
        congrArg Subtype.val (e.toEquiv.apply_symm_apply ⟨r, hr⟩)⟩
  have hgram : Matrix.gram ℝ x = Matrix.gram ℝ y := by
    ext i j
    exact (e.inner_map i j).symm
  obtain ⟨f, hf, _⟩ := InnerProductSpace.exists_span_int_equiv_of_gram_eq x y hgram
  have hh : ∃ f : span ℤ (Set.range x) ≃ₗ[ℤ] span ℤ (Set.range y),
      ∀ u v, ⟪(f u : F), (f v : F)⟫ = ⟪(u : E), (v : E)⟫ := ⟨f, hf⟩
  rw [hx, hy] at hh
  exact hh

namespace RootType

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: each model has a simple-root
integral basis of the stated rank and determinant. -/
theorem exists_int_basis_det (t : RootType) :
    ∃ b : Basis (Fin t.rank) ℤ (span ℤ t.model.Φ),
      (Matrix.gram ℝ (fun i ↦ (b i : EuclideanSpace ℝ (Fin t.dim)))).det = t.latticeDet := by
  cases t with
  | A n _ =>
    refine ⟨An.simpleIntBasis n, ?_⟩
    change (Matrix.gram ℝ (fun i ↦ (An.simpleIntBasis n i :
      EuclideanSpace ℝ (Fin (n + 1))))).det = (n + 1 : ℕ)
    simp only [An.simpleIntBasis_apply, An.det_gram_simpleRoot, Nat.cast_add,
      Nat.cast_one]
  | D n hn =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    refine ⟨Dn.simpleIntBasis (m + 2), ?_⟩
    change (Matrix.gram ℝ (fun i ↦ (Dn.simpleIntBasis (m + 2) i :
      EuclideanSpace ℝ (Fin (m + 2 + 2))))).det = (4 : ℕ)
    simp only [Dn.simpleIntBasis_apply, Dn.det_gram_simpleRoot, Nat.cast_ofNat]
  | E₆ =>
    refine ⟨E₆.simpleIntBasis, ?_⟩
    change (Matrix.gram ℝ (fun i ↦ (E₆.simpleIntBasis i : EuclideanSpace ℝ (Fin 8)))).det =
      (3 : ℕ)
    simp only [E₆.simpleIntBasis_apply, E₆.det_gram_simpleRoot, Nat.cast_ofNat]
  | E₇ =>
    refine ⟨E₇.simpleIntBasis, ?_⟩
    change (Matrix.gram ℝ (fun i ↦ (E₇.simpleIntBasis i : EuclideanSpace ℝ (Fin 8)))).det =
      (2 : ℕ)
    simp only [E₇.simpleIntBasis_apply, E₇.det_gram_simpleRoot, Nat.cast_ofNat]
  | E₈ =>
    refine ⟨E₈.simpleIntBasis, ?_⟩
    change (Matrix.gram ℝ (fun i ↦ (E₈.simpleIntBasis i : EuclideanSpace ℝ (Fin 8)))).det =
      (1 : ℕ)
    simp only [E₈.simpleIntBasis_apply, E₈.det_gram_simpleRoot, Nat.cast_one]

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: every integral basis of a model
root lattice has the tabulated Gram determinant. -/
theorem det_gram_int_basis (t : RootType) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (span ℤ t.model.Φ)) :
    (Matrix.gram ℝ (fun i ↦ (b i : EuclideanSpace ℝ (Fin t.dim)))).det = t.latticeDet := by
  obtain ⟨c, hc⟩ := t.exists_int_basis_det
  exact (b.det_gram_eq c).trans hc

end RootType
end LineSystem

namespace SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: taking norm-two lattice roots
preserves the integer span, not only its real span. -/
theorem IsRepresentation.span_int_latticeRoots (hx : X.IsRepresentation x) :
    span ℤ hx.latticeRoots.Φ = span ℤ (Set.range x) := by
  apply le_antisymm
  · exact span_le.mpr fun _ hr ↦ hr.1
  · exact span_mono (Set.range_subset_iff.mpr hx.mem_latticeRoots)

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: transport of the model's
simple-root basis gives an integral basis of the graph lattice with the same determinant. -/
theorem IsRepresentation.exists_lattice_basis_of_iso (hx : X.IsRepresentation x)
    {t : LineSystem.RootType} (e : hx.latticeRoots.Iso t.model) :
    ∃ b : Basis (Fin t.rank) ℤ (span ℤ (Set.range x)),
      (Matrix.gram ℝ (fun i ↦ (b i : E))).det = t.latticeDet := by
  obtain ⟨c, hc⟩ := t.exists_int_basis_det
  obtain ⟨f, hf⟩ := e.symm.exists_span_int_equiv
  let b := (c.map f).map (LinearEquiv.ofEq _ _ hx.span_int_latticeRoots)
  refine ⟨b, ?_⟩
  have he : Matrix.gram ℝ (fun i ↦ (b i : E)) =
      Matrix.gram ℝ (fun i ↦ (c i : EuclideanSpace ℝ (Fin t.dim))) := by
    ext i j
    exact hf (c i) (c j)
  rw [he, hc]

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the type of the lattice roots
determines the graph lattice determinant. -/
theorem IsRepresentation.latticeDet_eq_of_iso (hx : X.IsRepresentation x)
    {t : LineSystem.RootType} (e : hx.latticeRoots.Iso t.model) :
    X.latticeDet = t.latticeDet := by
  obtain ⟨b, hb⟩ := hx.exists_lattice_basis_of_iso e
  exact_mod_cast (hx.latticeDet_eq_det_gram b).trans hb

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: every integral basis of the
graph lattice has the determinant of the type of its lattice-root system. -/
theorem IsRepresentation.det_gram_lattice_basis_of_iso {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hx : X.IsRepresentation x) {t : LineSystem.RootType} (e : hx.latticeRoots.Iso t.model)
    (b : Basis ι ℤ (span ℤ (Set.range x))) :
    (Matrix.gram ℝ (fun i ↦ (b i : E))).det = t.latticeDet := by
  rw [← hx.latticeDet_eq_det_gram b, hx.latticeDet_eq_of_iso e]

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the lattice roots of a connected
graph have a unique root type; its rank, integral span, basis cardinality and determinant
are those of the graph lattice. The displayed span dimension is the rank of `M(X)`
by `IsRepresentation.rank_two_add_adjMatrix`. The ambient inner product space may
be infinite-dimensional. -/
theorem IsRepresentation.exists_unique_root_lattice (hx : X.IsRepresentation x)
    (hX : X.Connected) :
    ∃! t : LineSystem.RootType,
      Nonempty (hx.latticeRoots.Iso t.model) ∧
      t.rank = finrank ℝ (span ℝ (Set.range x)) ∧
      span ℤ hx.latticeRoots.Φ = span ℤ (Set.range x) ∧
      Nonempty (Basis (Fin t.rank) ℤ (span ℤ (Set.range x))) ∧
      X.latticeDet = t.latticeDet := by
  obtain ⟨t, ⟨e⟩, ht⟩ :=
    (hx.latticeRoots.classification (hx.latticeRoots_nonempty hX)).mp
      ⟨hx.isIndecomposable_latticeRoots hX, hx.isStarClosed_latticeRoots⟩
  obtain ⟨b, _⟩ := hx.exists_lattice_basis_of_iso e
  refine ⟨t, ⟨⟨e⟩, ?_, hx.span_int_latticeRoots, ⟨b⟩, hx.latticeDet_eq_of_iso e⟩,
    fun s hs ↦ ht s hs.1⟩
  rw [← t.finrank_span_model, ← e.finrank_span_eq, hx.span_latticeRoots]

end SimpleGraph
