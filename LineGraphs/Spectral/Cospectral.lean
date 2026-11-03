/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Regularity

/-!
# Cospectrality and regular graphs

Proposition 2.6 and Corollary 5.5 of the spectral toolkit. Vertex types may differ;
nonemptiness is transferred by equality of the characteristic polynomials' degrees.
-/

namespace Matrix.IsHermitian

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {A : Matrix V V ℝ} {B : Matrix W W ℝ}

/-- Equal spectra, with multiplicities, are equivalent to equal characteristic polynomials. -/
theorem spectrumMultiset_eq_iff_charpoly_eq (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A.spectrumMultiset = B.spectrumMultiset ↔ A.charpoly = B.charpoly := by
  constructor
  · intro hs
    -- Step `cos-back`: both monic characteristic polynomials split over ℝ.
    have hroots : A.charpoly.roots = B.charpoly.roots := hs
    rw [hA.splits_charpoly.eq_prod_roots_of_monic A.charpoly_monic,
      hB.splits_charpoly.eq_prod_roots_of_monic B.charpoly_monic, hroots]
  · exact fun h => congrArg Polynomial.roots h

end Matrix.IsHermitian

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {X : SimpleGraph V} {Y : SimpleGraph W} [DecidableRel X.Adj] [DecidableRel Y.Adj]

/-- Proposition 2.6 of the spectral toolkit: graph cospectrality is equality of adjacency spectral
multisets. -/
theorem cospectral_iff_spectrumMultiset_eq : X.Cospectral Y ↔
    X.spectrumMultiset = Y.spectrumMultiset :=
  ((X.isHermitian_adjMatrix ℝ).spectrumMultiset_eq_iff_charpoly_eq
    (Y.isHermitian_adjMatrix ℝ)).symm

/-- Cospectral graphs have equal spectral multisets. -/
theorem Cospectral.spectrumMultiset_eq (h : X.Cospectral Y) :
    X.spectrumMultiset = Y.spectrumMultiset := cospectral_iff_spectrumMultiset_eq.mp h

/-- Cospectral graphs have the same order. -/
theorem Cospectral.card_eq (h : X.Cospectral Y) : Fintype.card V = Fintype.card W := by
  -- Step `cos-orders`: take the cardinality of the common spectral multiset.
  have hs := congrArg Multiset.card h.spectrumMultiset_eq
  simpa only [spectrumMultiset, Matrix.IsHermitian.card_spectrumMultiset
    (X.isHermitian_adjMatrix ℝ), Matrix.IsHermitian.card_spectrumMultiset
    (Y.isHermitian_adjMatrix ℝ)] using hs

/-- Cospectral graphs have equal adjacency eigenvalue multiplicities. -/
theorem Cospectral.eigenvalueMultiplicity_eq (h : X.Cospectral Y) (μ : ℝ) :
    X.eigenvalueMultiplicity μ = Y.eigenvalueMultiplicity μ :=
  congrArg (Multiset.count μ) h.spectrumMultiset_eq

/-- The largest eigenvalue is determined by the nonempty spectral multiset. -/
theorem Cospectral.largestEigenvalue_eq [Nonempty V] [Nonempty W] (h : X.Cospectral Y) :
    X.largestEigenvalue = Y.largestEigenvalue := by
  -- Step `mates-invariants`: each largest eigenvalue belongs to the other's spectrum.
  have hx := (X.isHermitian_adjMatrix ℝ).largestEigenvalue_mem_spectrumMultiset
  have hy := (Y.isHermitian_adjMatrix ℝ).largestEigenvalue_mem_spectrumMultiset
  have hs := h.spectrumMultiset_eq
  change (X.adjMatrix ℝ).spectrumMultiset = (Y.adjMatrix ℝ).spectrumMultiset at hs
  apply le_antisymm
  · exact (Y.isHermitian_adjMatrix ℝ).le_largestEigenvalue_of_mem (hs ▸ hx)
  · exact (X.isHermitian_adjMatrix ℝ).le_largestEigenvalue_of_mem (hs.symm ▸ hy)

/-- Corollary 5.5 of the spectral toolkit: a cospectral mate of a nonempty k-regular graph is
k-regular. -/
theorem Cospectral.isRegularOfDegree [Nonempty V] (h : X.Cospectral Y)
    {k : ℕ} (hk : X.IsRegularOfDegree k) : Y.IsRegularOfDegree k := by
  have hn : 0 < Fintype.card W := h.card_eq ▸ Fintype.card_pos
  have : Nonempty W := Fintype.card_pos_iff.mp hn
  -- Step `mates-invariants`: the order, second moment, and largest eigenvalue agree.
  have hmom := X.isRegular_iff_sum_sq_eigenvalues.mp ⟨k, hk⟩
  rw [h.spectrumMultiset_eq, h.card_eq, h.largestEigenvalue_eq] at hmom
  -- Step `mates-regular`: SP2 gives regularity and SP1 identifies the degree.
  have hreg := Y.isRegular_iff_sum_sq_eigenvalues.mpr hmom
  obtain ⟨l, hl⟩ := hreg
  have hlk : l = k := by
    have he := h.largestEigenvalue_eq
    rw [hk.largestEigenvalue_eq, hl.largestEigenvalue_eq] at he
    exact_mod_cast he.symm
  exact hlk ▸ hl

/-- Corollary 5.5 of the spectral toolkit: cospectral regular graphs have equally many connected
components. -/
theorem Cospectral.card_connectedComponent_eq_of_regular [Nonempty V]
    (h : X.Cospectral Y) {k : ℕ} (hk : X.IsRegularOfDegree k) :
    Fintype.card X.ConnectedComponent = Fintype.card Y.ConnectedComponent := by
  -- Step `mates-count`: SP1 expresses both component counts as the multiplicity of k.
  have hy := h.isRegularOfDegree hk
  rw [← hk.multiplicity_eq_card_components, ← hy.multiplicity_eq_card_components]
  exact h.eigenvalueMultiplicity_eq k

/-- Corollary 5.5 of the spectral toolkit: a cospectral mate of a connected regular graph is
connected. -/
theorem Cospectral.connected_of_regular (h : X.Cospectral Y) {k : ℕ}
    (hk : X.IsRegularOfDegree k) (hc : X.Connected) : Y.Connected := by
  have : Nonempty V := hc.nonempty
  have : Subsingleton X.ConnectedComponent := hc.preconnected.subsingleton_connectedComponent
  have hn : 0 < Fintype.card W := h.card_eq ▸ Fintype.card_pos
  have : Nonempty W := Fintype.card_pos_iff.mp hn
  -- Step `mates-connected`: a single component is equivalent to reachability of all pairs.
  have hcard : Fintype.card Y.ConnectedComponent = 1 := by
    rw [← h.card_connectedComponent_eq_of_regular hk]
    exact le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr inferInstance) Fintype.card_pos
  have : Subsingleton Y.ConnectedComponent :=
    (Fintype.card_le_one_iff_subsingleton).mp (by omega)
  have hpre : Y.Preconnected := fun u v =>
    ConnectedComponent.eq.mp (Subsingleton.elim (Y.connectedComponentMk u)
      (Y.connectedComponentMk v))
  exact { preconnected := hpre, nonempty := ‹Nonempty W› }

end SimpleGraph
