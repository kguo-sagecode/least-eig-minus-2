/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.DesignReconstruction
import LineGraphs.LineGraphSpectra.ExceptionalParameters
import LineGraphs.LineGraphSpectra.GraphRecognition
import LineGraphs.Representation.HoffmanRegular

/-!
# Cospectral mates of design flag graphs

Theorem 5.8 (`thm:5.8`) of [CGSS], with the hypothesis `v ≤ b` from Error 16.

The design is the shared Hall–Connor structure. `Design.realIncMatrix` explicitly
casts its integer incidence matrix to ℝ, and `Design.ofIncMatrix` reconstructs a
labelled design from the real zero-one matrix in the bipartite branch.

Case (iii) uses natural numbers for the positive integer parameters, doubled point
and block counts, and `NonbipartiteParameters` for the arithmetic conjunction.
These are equivalent encodings of the blueprint statement, not extra hypotheses.
-/

open scoped BigOperators
open Matrix SimpleGraph

namespace Design

attribute [local instance] Classical.propDecidable

variable {P B V : Type} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  [Fintype V] [DecidableEq V] {v k b r lam : ℕ} (D : Design P B v k b r lam)

-- Theorem 5.8
/-- Theorem 5.8 of [CGSS], `thm:5.8`, with Error 16's necessary hypothesis `v ≤ b`.
The three alternatives are an E₈ representation of small rank, a flag graph with
the same design parameters, and the nonbipartite line-graph alternative with its
full spectrum and parity condition. The design-family reading is Implicit hypothesis 6. -/
theorem flagGraph_cospectral (hvb : v ≤ b) (X : SimpleGraph V) [DecidableRel X.Adj]
    (hs : D.flagGraph.Cospectral X) :
    (v + b ≤ 9 ∧ X.IsRepresentedIn LineSystem.E₈) ∨
      (∃ (P₂ B₂ : Type) (_ : Fintype P₂) (_ : Fintype B₂)
        (_ : DecidableEq P₂) (_ : DecidableEq B₂) (D₂ : Design P₂ B₂ v k b r lam),
        Nonempty (X ≃g D₂.flagGraph)) ∨
      ∃ s t : ℕ, NonbipartiteParameters v k b r lam s t ∧ Even (t * (s + 1)) ∧
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (Y : SimpleGraph W)
          (_ : DecidableRel Y.Adj),
          Y.Connected ∧ Y.IsRegularOfDegree ((s + 1) * t) ∧
          Fintype.card W = s * (s + 2) ∧
          Y.spectrumMultiset =
            {((s : ℝ) + 1) * t} + Multiset.replicate (s + 1) (-(t : ℝ)) +
            Multiset.replicate ((s - 1) * (s + 2) / 2)
              (Real.sqrt (t * (s + 1) * ((s : ℝ) - t) / (s - 1))) +
            Multiset.replicate ((s - 1) * (s + 2) / 2)
              (-Real.sqrt (t * (s + 1) * ((s : ℝ) - t) / (s - 1))) ∧
          Nonempty (X ≃g Y.lineGraph) := by
  -- Steps `s558X1` and `s558X2reg`.
  have : Nonempty D.incidenceGraph.edgeSet := D.flagGraph_connected.nonempty
  have hrX := hs.isRegularOfDegree D.flagGraph_isRegularOfDegree
  have hcX := hs.connected_of_regular D.flagGraph_isRegularOfDegree D.flagGraph_connected
  have : Nonempty V := hcX.nonempty
  have hcard := hs.card_eq
  -- Step `s558X2psd`.
  have hpX : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef := by
    apply X.posSemidef_two_add_adjMatrix_iff.mpr
    intro μ hμ
    apply D.flagGraph.posSemidef_two_add_adjMatrix_iff.mp
      D.posSemidef_two_add_adjMatrix_flagGraph μ
    rwa [hs.spectrumMultiset_eq]
  -- Step `s558X2rank`.
  have hrank : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank = v + b - 1 := by
    have h₁ := D.flagGraph.rank_two_add_adjMatrix_add_multiplicity_neg_two
    have h₂ := X.rank_two_add_adjMatrix_add_multiplicity_neg_two
    rw [D.rank_two_add_adjMatrix_flagGraph] at h₁
    have hm := hs.eigenvalueMultiplicity_eq (-2)
    omega
  -- Step `s558hrc`.
  rcases SimpleGraph.hoffman_rayChaudhuri hcX hrX hpX with hline | hcp | hE
  · -- Step `s558Yp`: remove isolated vertices before Lemma 5.6.
    obtain ⟨m, Y, ⟨e⟩⟩ := hline
    obtain ⟨Z, hno, ⟨f⟩⟩ := exists_forall_degree_pos_nonempty_iso_lineGraph Y
    let e' : X ≃g Z.lineGraph := e.trans f.symm
    have hsZ : D.flagGraph.Cospectral Z.lineGraph := hs.trans e'.cospectral
    obtain ⟨hcZ, hcases⟩ := lineGraph_cospectral_bipartite_forall_isBiregularWith
      D.incidenceGraph_connected D.incidenceGraph_isBiregularWith.isBipartite
      D.incidenceGraph_edgeSet_nonempty D.flagGraph_isRegularOfDegree hno hsZ
    rcases hcases with hbip | ⟨_, ⟨κ, hκ, hκeq⟩, hnb, hn⟩
    · -- Steps `s558bippick`–`s558bipiso`.
      obtain ⟨S, T, hST, hS, hT, hspec⟩ := hbip.2 D.pointPart D.blockPart r k
        D.incidenceGraph_isBiregularWith (by
          simpa only [D.card_pointPart, D.card_blockPart] using hvb)
      rw [D.card_pointPart] at hS
      rw [D.card_blockPart] at hT
      obtain ⟨D₂, ⟨g⟩⟩ := D.exists_design_of_biregular_gram_spectrum Z S T hST hS hT
        (hspec.symm.trans D.spectrumMultiset_biadjMatrix_mul_transpose)
      exact Or.inr (Or.inl ⟨S, T, inferInstance, inferInstance, inferInstance, inferInstance,
        D₂, ⟨e'.trans g.lineGraph.symm⟩⟩)
    · -- Steps `s558nbfacts` and `s558nbhand`.
      obtain ⟨hkr, hspec⟩ := D.lineGraph_spectrum_of_not_isBipartite hvb Z hno hnb hsZ
      have hsumκ : 2 * κ = r + k := by have := D.one_lt_k; have := D.r_pos; omega
      rw [Fintype.card_sum, D.card_points, D.card_blocks] at hn
      have hnZ : Fintype.card Y.support = v + b - 1 := by omega
      have hedges : Fintype.card Z.edgeSet = v * r := hsZ.card_eq.symm.trans D.card_flagGraph
      have hhand := Z.sum_degrees_eq_twice_card_edges
      simp only [hκ.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        SimpleGraph.edgeFinset_card, hedges, hnZ] at hhand
      have hhand' : (r + k) * (v + b - 1) = 4 * v * r := by nlinarith
      -- Steps `s558nbv`–`s558nbineq`, using the integer computations C11.
      obtain ⟨s, t, hp⟩ := D.exists_nonbipartite_parameters hkr
        ⟨κ, by omega⟩ hhand'
      have hrZ : Z.IsRegularOfDegree ((s + 1) * t) := hp.root_degree hsumκ ▸ hκ
      have horder : Fintype.card Y.support = s * (s + 2) := hnZ.trans hp.root_order
      -- Step `s558nbspec`: both rank cases were proved in DesignSpectrum.
      have hfull := Computations.C11.spectrum_of_parameters Z v b k r s t lam hp.two_le_s
        hp.point_count hp.block_count hp.block_size hp.replication hp.pair_count_real hspec
      have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hp.two_le_s
      have htR : (0 : ℝ) ≤ t := Nat.cast_nonneg _
      have hst : (t : ℝ) ≤ s := by
        have hbR : 2 * (t : ℝ) ≤ s + 1 := by exact_mod_cast hp.bound
        linarith
      have hc : 0 ≤ (t : ℝ) * (s + 1) * ((s : ℝ) - t) / (s - 1) :=
        div_nonneg (mul_nonneg (mul_nonneg htR (by positivity)) (sub_nonneg.mpr hst))
          (by linarith)
      have hsupport : ∀ μ ∈ Z.spectrumMultiset, μ ≠ (((s + 1) * t : ℕ) : ℝ) →
          μ = -(t : ℝ) ∨ μ ^ 2 = t * (s + 1) * ((s : ℝ) - t) / (s - 1) := by
        intro μ hμ hne
        rw [hfull] at hμ
        simp only [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_replicate] at hμ
        rcases hμ with ((hμ | ⟨_, hμ⟩) | ⟨_, hμ⟩) | ⟨_, hμ⟩
        · exact (hne (by simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hμ)).elim
        · exact Or.inl hμ
        · exact Or.inr (hμ ▸ Real.sq_sqrt hc)
        · exact Or.inr (by rw [hμ, neg_sq, Real.sq_sqrt hc])
      -- Steps `s558nbhp`–`s558nbeven`, including the real-to-integer cast.
      have heven := Z.even_mul_of_nonbipartite_design_spectrum hp.two_le_s hcZ hrZ
        horder hsupport
      exact Or.inr (Or.inr ⟨s, t, hp, heven, Y.support, inferInstance, inferInstance,
        Z, inferInstance, hcZ, hrZ, horder, hfull, ⟨e'⟩⟩)
  · -- Steps `s558CPX2` and `s558CPX1`: the omitted cocktail party case, Gap 15.
    obtain ⟨m, ⟨e⟩⟩ := hcp
    have hcpCard : Fintype.card V = 2 * m := by
      simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]
        using Fintype.card_congr e.toEquiv
    have hm : 1 ≤ m := by have := Fintype.card_pos (α := V); omega
    have hsCP := hs.trans e.cospectral
    have : Nonempty (Fin m × Bool) := ⟨(⟨0, hm⟩, false)⟩
    have hrD := SimpleGraph.Cospectral.isRegularOfDegree hsCP.symm
      (cocktailParty_isRegularOfDegree m)
    obtain ⟨g⟩ := hrD.nonempty_iso_cocktailParty hm (hcard.trans hcpCard)
    exact Or.inr (Or.inl ⟨P, B, inferInstance, inferInstance, inferInstance, inferInstance,
      D, ⟨e.trans g.symm⟩⟩)
  · -- Step `s558E8`: the Gram matrix has rank at most eight.
    have hle := hE.posSemidef_two_add_adjMatrix_and_rank_le_eight.2
    have := D.one_lt_v
    exact Or.inl ⟨by omega, hE⟩

end Design
