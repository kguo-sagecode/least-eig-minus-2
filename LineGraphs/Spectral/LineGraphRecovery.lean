/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Incidence
import LineGraphs.Spectral.GramProducts
import LineGraphs.Spectral.Cospectral

/-!
# Recovering regular graphs from their line-graph spectra

Theorem 6.5 of the spectral toolkit and Lemma 5.5 of [CGSS]. The original
regular graphs need not be connected. The existence of an edge excludes degree zero.
-/

open Matrix

private theorem charpoly_smul_one_add {U : Type*} [Fintype U] [DecidableEq U]
    (D : Matrix U U ℝ) (c : ℝ) :
    (c • 1 + D).charpoly = D.charpoly.comp (Polynomial.X - Polynomial.C c) := by
  have hs : Matrix.scalar U (-c) = -(c • (1 : Matrix U U ℝ)) := by
    ext u v
    simp only [Matrix.scalar_apply, Matrix.diagonal, Matrix.of_apply, Matrix.neg_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  have he : c • 1 + D = D - Matrix.scalar U (-c) := by
    rw [hs, sub_neg_eq_add, add_comm]
  rw [he, Matrix.charpoly_sub_scalar]
  simp [sub_eq_add_neg]

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {X : SimpleGraph V} {Y : SimpleGraph W} [DecidableRel X.Adj] [DecidableRel Y.Adj]

noncomputable local instance : DecidableRel X.lineGraph.Adj := Classical.decRel _
noncomputable local instance : DecidableRel Y.lineGraph.Adj := Classical.decRel _

omit [DecidableEq V] in
/-- A k-regular graph has a (2k-2)-regular line graph. This also holds at k = 0. -/
theorem IsRegularOfDegree.lineGraph_isRegularOfDegree {k : ℕ} (hk : X.IsRegularOfDegree k) :
    X.lineGraph.IsRegularOfDegree (k + k - 2) := by
  -- Step `recover-h`: use the endpoint degree formula at each edge.
  have hdegree (e : X.edgeSet) : X.lineGraph.degree e = k + k - 2 := by
    rcases e with ⟨⟨u, v⟩, huv⟩
    rw [degree_lineGraph huv, hk.degree_eq, hk.degree_eq]
  exact hdegree

/-- In a regular graph, the signless spectrum is the adjacency spectrum shifted by k. -/
theorem IsRegularOfDegree.spectrumMultiset_signlessLapMatrix {k : ℕ}
    (hk : X.IsRegularOfDegree k) :
    (X.signlessLapMatrix ℝ).spectrumMultiset = X.spectrumMultiset.map (fun μ => (k : ℝ) + μ) := by
  -- Step `recover-products`: the degree matrix is k times the identity.
  have hmatrix : X.signlessLapMatrix ℝ = (k : ℝ) • 1 + (1 : ℝ) • X.adjMatrix ℝ := by
    rw [signlessLapMatrix, hk.degMatrix_eq ℝ, one_smul, Nat.cast_smul_eq_nsmul, nsmul_one]
  rw [hmatrix, (X.isHermitian_adjMatrix ℝ).spectrumMultiset_smul_one_add_smul]
  simp only [one_mul, spectrumMultiset]

/-- Theorem 6.5 of the spectral toolkit: regular roots of cospectral nonempty line graphs have
equal degree. -/
theorem IsRegularOfDegree.degree_eq_of_lineGraph_cospectral {k l : ℕ}
    (hk : X.IsRegularOfDegree k) (hl : Y.IsRegularOfDegree l)
    (heX : X.edgeSet.Nonempty) (heY : Y.edgeSet.Nonempty)
    (h : X.lineGraph.Cospectral Y.lineGraph) : k = l := by
  have : Nonempty X.edgeSet := heX.to_subtype
  have : Nonempty Y.edgeSet := heY.to_subtype
  -- Step `recover-kpos`: an edge gives positive degree in each original graph.
  have hkpos : 0 < k := by
    obtain ⟨⟨u, v⟩, huv⟩ := heX
    rw [← hk.degree_eq u]
    exact (X.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩
  have hlpos : 0 < l := by
    obtain ⟨⟨u, v⟩, huv⟩ := heY
    rw [← hl.degree_eq u]
    exact (Y.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩
  -- Steps `recover-h`, `recover-formulas`: the common largest eigenvalue is 2k-2 = 2l-2.
  have he := h.largestEigenvalue_eq
  rw [hk.lineGraph_isRegularOfDegree.largestEigenvalue_eq,
    hl.lineGraph_isRegularOfDegree.largestEigenvalue_eq] at he
  have hn : k + k - 2 = l + l - 2 := by exact_mod_cast he
  omega

/-- Theorem 6.5 of the spectral toolkit: regular roots of cospectral nonempty line graphs have
equal order. -/
theorem IsRegularOfDegree.card_eq_of_lineGraph_cospectral {k l : ℕ}
    (hk : X.IsRegularOfDegree k) (hl : Y.IsRegularOfDegree l)
    (heX : X.edgeSet.Nonempty) (heY : Y.edgeSet.Nonempty)
    (h : X.lineGraph.Cospectral Y.lineGraph) : Fintype.card V = Fintype.card W := by
  have hkl := hk.degree_eq_of_lineGraph_cospectral hl heX heY h
  subst l
  -- Step `recover-m`: the line graph's order is the original edge count.
  have hm : X.edgeFinset.card = Y.edgeFinset.card := by
    simpa only [card_edgeSet] using h.card_eq
  -- Step `recover-m`: apply the handshake identity to both regular graphs.
  have hX : Fintype.card V * k = 2 * X.edgeFinset.card := by
    simpa only [hk.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      using X.sum_degrees_eq_twice_card_edges
  have hY : Fintype.card W * k = 2 * Y.edgeFinset.card := by
    simpa only [hl.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      using Y.sum_degrees_eq_twice_card_edges
  -- Step `recover-formulas`: cancellation is justified by a positive degree.
  have hkpos : 0 < k := by
    obtain ⟨⟨u, v⟩, huv⟩ := heX
    rw [← hk.degree_eq u]
    exact (X.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩
  exact Nat.eq_of_mul_eq_mul_right hkpos ((hX.trans (congrArg (2 * ·) hm)).trans hY.symm)

/-- Theorem 6.5 of the spectral toolkit: the line-graph spectrum determines the positive regular
degree
and then the original order by the handshake identity. -/
theorem IsRegularOfDegree.lineGraph_parameters {k : ℕ} (hk : X.IsRegularOfDegree k)
    [Nonempty X.edgeSet] :
    (k : ℝ) = (X.lineGraph.largestEigenvalue + 2) / 2 ∧
      (Fintype.card V : ℝ) = 2 * (X.edgeFinset.card : ℝ) / (k : ℝ) := by
  -- Step `recover-kpos`: the original regular degree is positive.
  have hkpos : 0 < k := by
    obtain ⟨⟨⟨u, v⟩, huv⟩⟩ := ‹Nonempty X.edgeSet›
    rw [← hk.degree_eq u]
    exact (X.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩
  -- Step `recover-h`: convert the natural-number line degree to real arithmetic.
  have htop : X.lineGraph.largestEigenvalue = 2 * (k : ℝ) - 2 := by
    rw [hk.lineGraph_isRegularOfDegree.largestEigenvalue_eq,
      Nat.cast_sub (show 2 ≤ k + k by omega), Nat.cast_add, Nat.cast_ofNat]
    ring
  -- Step `recover-m`: count incidences by vertices and by edges.
  have hcount : Fintype.card V * k = 2 * X.edgeFinset.card := by
    simpa only [hk.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      using X.sum_degrees_eq_twice_card_edges
  -- Step `recover-formulas`: solve the two equalities over ℝ.
  constructor
  · rw [htop]; ring
  · apply (eq_div_iff (Nat.cast_ne_zero.mpr hkpos.ne')).mpr
    exact_mod_cast hcount

/-- Theorem 6.5 of the spectral toolkit: recover the adjacency spectrum by retaining the positive
spectrum
of 2I+A(L(X)), adjoining the missing zero modes, and subtracting the regular degree. -/
theorem spectrumMultiset_of_regular_lineGraph {k : ℕ} (hk : X.IsRegularOfDegree k) :
    X.spectrumMultiset =
      ((Matrix.spectrumMultiset
        ((2 : ℝ) • (1 : Matrix X.edgeSet X.edgeSet ℝ) + X.lineGraph.adjMatrix ℝ)).filter (0 < ·) +
          Multiset.replicate (Fintype.card V - (X.edgeIncMatrix ℝ).rank) 0).map
        (fun μ => μ - (k : ℝ)) := by
  let M := X.edgeIncMatrix ℝ
  -- Step `recover-nonzero`: the two Gram products share their positive spectral entries.
  have hgram := Matrix.spectrumMultiset_gram_products M
  have hs := hgram.1.spectrumMultiset_eq_filter_pos_add_replicate_zero
  rw [hgram.2.2.1, hgram.2.2.2.1] at hs
  -- Step `recover-products`: identify the two incidence products.
  have hrow : M * Mᵀ = X.signlessLapMatrix ℝ := X.edgeIncMatrix_mul_transpose
  have hcol : Mᵀ * M = (2 : ℝ) • 1 + X.lineGraph.adjMatrix ℝ :=
    X.transpose_edgeIncMatrix_mul
  rw [hrow, hcol] at hs
  -- Step `recover-shift`: subtract k from the shifted adjacency spectrum.
  have hmap := congrArg (Multiset.map (fun μ => μ - (k : ℝ))) hs
  rw [hk.spectrumMultiset_signlessLapMatrix, Multiset.map_map] at hmap
  simpa only [Function.comp_def, add_sub_cancel_left, Multiset.map_id'] using hmap

/-- Theorem 6.5 of the spectral toolkit: the equivalent characteristic-polynomial identity, with no
negative exponents and valid also for regular graphs with no edges. -/
theorem IsRegularOfDegree.charpoly_lineGraph {k : ℕ} (hk : X.IsRegularOfDegree k) :
    (Polynomial.X + Polynomial.C (2 : ℝ)) ^ Fintype.card V *
        (X.lineGraph.adjMatrix ℝ).charpoly =
      (Polynomial.X + Polynomial.C (2 : ℝ)) ^ X.edgeFinset.card *
        (X.adjMatrix ℝ).charpoly.comp (Polynomial.X + Polynomial.C (2 - (k : ℝ))) := by
  let M := X.edgeIncMatrix ℝ
  -- Step `recover-products`: identify the two incidence products.
  have hrow : M * Mᵀ = (k : ℝ) • 1 + X.adjMatrix ℝ := by
    change X.edgeIncMatrix ℝ * (X.edgeIncMatrix ℝ)ᵀ = _
    rw [X.edgeIncMatrix_mul_transpose, signlessLapMatrix, hk.degMatrix_eq ℝ,
      Nat.cast_smul_eq_nsmul, nsmul_one]
  have hcol : Mᵀ * M = (2 : ℝ) • 1 + X.lineGraph.adjMatrix ℝ :=
    X.transpose_edgeIncMatrix_mul
  have hp := Matrix.charpoly_mul_comm' M Mᵀ
  rw [hrow, hcol, charpoly_smul_one_add, charpoly_smul_one_add] at hp
  -- Step `recover-substitute`: substitute t+2 in the rectangular polynomial identity.
  have hcomp := congrArg (fun p : Polynomial ℝ =>
    p.comp (Polynomial.X + Polynomial.C (2 : ℝ))) hp
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.C_comp] at hcomp
  have hpoly : Polynomial.X + Polynomial.C (2 : ℝ) - Polynomial.C (k : ℝ) =
      Polynomial.X + Polynomial.C (2 - (k : ℝ)) := by rw [map_sub]; ring
  rw [hpoly, add_sub_cancel_right, Polynomial.comp_X, X.card_edgeSet] at hcomp
  exact hcomp.symm

/-- Lemma 5.5 of [CGSS], Theorem 6.5 of the toolkit: regular graphs with an edge
are cospectral whenever their line graphs are cospectral. -/
theorem cospectral_of_lineGraph_cospectral {k l : ℕ}
    (hk : X.IsRegularOfDegree k) (hl : Y.IsRegularOfDegree l)
    (heX : X.edgeSet.Nonempty) (heY : Y.edgeSet.Nonempty)
    (h : X.lineGraph.Cospectral Y.lineGraph) : X.Cospectral Y := by
  -- Steps `recover-parameters`, `recover-mates`: the degrees and orders agree.
  have hkl := hk.degree_eq_of_lineGraph_cospectral hl heX heY h
  have hn := hk.card_eq_of_lineGraph_cospectral hl heX heY h
  subst l
  let MX := X.edgeIncMatrix ℝ
  let MY := Y.edgeIncMatrix ℝ
  have hm := h.card_eq
  -- Step `recover-products`: cospectral line graphs give cospectral second Gram products.
  have hcol : (MXᵀ * MX).spectrumMultiset = (MYᵀ * MY).spectrumMultiset := by
    change ((X.edgeIncMatrix ℝ)ᵀ * X.edgeIncMatrix ℝ).spectrumMultiset =
      ((Y.edgeIncMatrix ℝ)ᵀ * Y.edgeIncMatrix ℝ).spectrumMultiset
    rw [X.transpose_edgeIncMatrix_mul, Y.transpose_edgeIncMatrix_mul]
    have hX := (X.lineGraph.isHermitian_adjMatrix ℝ).spectrumMultiset_smul_one_add_smul 2 1
    have hY := (Y.lineGraph.isHermitian_adjMatrix ℝ).spectrumMultiset_smul_one_add_smul 2 1
    simp only [one_smul, one_mul] at hX hY
    rw [hX, hY]
    exact congrArg (Multiset.map (fun μ : ℝ => 2 + μ)) h.spectrumMultiset_eq
  -- Step `recover-nonzero`: cancel the common extra zero roots in the rectangular identity.
  have hrow : (MX * MXᵀ).spectrumMultiset = (MY * MYᵀ).spectrumMultiset := by
    have hX := Matrix.spectrumMultiset_mul_comm_add_zeros MX MXᵀ
    have hY := Matrix.spectrumMultiset_mul_comm_add_zeros MY MYᵀ
    rw [hn, hcol, hm] at hX
    exact add_left_cancel (hX.trans hY.symm)
  change (X.edgeIncMatrix ℝ * (X.edgeIncMatrix ℝ)ᵀ).spectrumMultiset =
    (Y.edgeIncMatrix ℝ * (Y.edgeIncMatrix ℝ)ᵀ).spectrumMultiset at hrow
  rw [X.edgeIncMatrix_mul_transpose, Y.edgeIncMatrix_mul_transpose,
    hk.spectrumMultiset_signlessLapMatrix, hl.spectrumMultiset_signlessLapMatrix] at hrow
  -- Step `recover-mates`: translation is injective on spectral multisets.
  have hs : X.spectrumMultiset = Y.spectrumMultiset :=
    (Multiset.map_injective (fun a b hab => add_left_cancel hab)) hrow
  exact cospectral_iff_spectrumMultiset_eq.mpr hs

end SimpleGraph
