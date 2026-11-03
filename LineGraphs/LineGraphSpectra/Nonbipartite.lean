/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Bipartite
import LineGraphs.LineGraphSpectra.BlockMultiplicity

/-!
# The nonbipartite rival spectrum

Remark 5.7 of [CGSS], in the blueprint's form and with Error 14 corrected.
The second root is only assumed to have no isolated vertices and not to be bipartite.
Lemma 5.6 supplies connectedness and regularity.
-/

open Matrix

namespace SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {X : SimpleGraph V} {Y : SimpleGraph W} [DecidableRel X.Adj] [DecidableRel Y.Adj]

/-- The missing zero in blueprint step `s557ii` for [CGSS, Remark 5.7], Error 14:
the bipartite signless spectrum is the nonbipartite one with a single zero adjoined. -/
theorem Cospectral.spectrumMultiset_signlessLapMatrix_add_singleton_zero
    (h : X.lineGraph.Cospectral Y.lineGraph) (hcX : X.Connected) (hcY : Y.Connected)
    (hbX : X.IsBipartite) (hbY : ¬ Y.IsBipartite) :
    (Y.signlessLapMatrix ℝ).spectrumMultiset + {0} =
      (X.signlessLapMatrix ℝ).spectrumMultiset := by
  apply Multiset.ext.mpr
  intro μ
  rw [Multiset.count_add]
  change (Y.signlessLapMatrix ℝ).eigenvalueMultiplicity μ + Multiset.count μ {0} =
    (X.signlessLapMatrix ℝ).eigenvalueMultiplicity μ
  by_cases hμ : μ = 0
  · subst μ
    rw [hcX.multiplicity_zero_signlessLapMatrix, hcY.multiplicity_zero_signlessLapMatrix,
      ite_eq_left hbX, ite_eq_right hbY]
    simp
  · rw [← h.eigenvalueMultiplicity_signlessLapMatrix_of_ne_zero hμ]
    simp [hμ]

-- Remark 5.7
/-- Remark 5.7 of [CGSS], in the blueprint's form, with Error 14 corrected.
Only absence of isolates and nonbipartiteness are assumed of the second root.
The top Gram eigenvalue occurs once; its negative partner is removed. The two
maps of `Λ'` express the sum of the pairs `δμ, -δμ`, with multiplicities.
The first root has an edge, excluding `K₁`. This theorem states the final adjacency
spectrum; the intermediate block spectrum is supplied by
`Matrix.spectrumMultiset_fromBlocks_scalar_of_ne`, rather than restated here. -/
theorem lineGraph_cospectral_bipartite_spectrum_of_not_isBipartite
    (hcX : X.Connected) (heX : X.edgeSet.Nonempty) {P Q : Set V} {k₁ k₂ : ℕ}
    (hb : X.IsBiregularWith P Q k₁ k₂) (hne : k₁ ≠ k₂)
    (hpq : Nat.card P ≤ Nat.card Q) (hnoY : ∀ v, 0 < Y.degree v)
    (hbY : ¬ Y.IsBipartite) (hs : X.lineGraph.Cospectral Y.lineGraph) :
    k₂ < k₁ ∧ 1 ≤ k₂ ∧
      (X.biadjMatrix P Q ℝ * (X.biadjMatrix P Q ℝ)ᵀ).eigenvalueMultiplicity
          ((k₁ : ℝ) * k₂) = 1 ∧
      let B := X.biadjMatrix P Q ℝ
      let Λ' := ((B * Bᵀ).spectrumMultiset.filter (0 < ·)).erase ((k₁ : ℝ) * k₂)
      Y.spectrumMultiset = {((k₁ : ℝ) + k₂) / 2} +
        Λ'.map (fun μ ↦ Real.sqrt (μ + ((k₁ : ℝ) - k₂) ^ 2 / 4)) +
        Λ'.map (fun μ ↦ -Real.sqrt (μ + ((k₁ : ℝ) - k₂) ^ 2 / 4)) +
        Multiset.replicate (Nat.card P - B.rank) (((k₁ : ℝ) - k₂) / 2) +
        Multiset.replicate (Nat.card Q - B.rank) (-((k₁ : ℝ) - k₂) / 2) := by
  -- Step `s557deg`: edge counting orders the positive degrees.
  have hpos := hb.degrees_pos heX
  have hord := hb.degree_right_le_left heX hpq
  have hlt : k₂ < k₁ := by omega
  have hk₂ : 1 ≤ k₂ := hpos.2
  have hneR : (k₁ : ℝ) ≠ k₂ := by exact_mod_cast hne
  -- Step `s557ii`: Lemma 5.6 supplies the hypotheses of the rival-spectrum calculation.
  obtain ⟨hcY, hcases⟩ := lineGraph_cospectral_bipartite_forall_isBiregularWith
    hcX hb.isBipartite heX hb.lineGraph_isRegularOfDegree hnoY hs
  have hnon := hcases.resolve_left (fun h ↦ hbY h.1)
  obtain ⟨κ, hκ, hκeq⟩ := hnon.2.1
  have hκsum : 2 * κ = k₁ + k₂ := by omega
  have hκR : (κ : ℝ) = ((k₁ : ℝ) + k₂) / 2 := by
    have hreal : 2 * (κ : ℝ) = (k₁ : ℝ) + k₂ := by exact_mod_cast hκsum
    linarith
  let B := X.biadjMatrix P Q ℝ
  let Λ := (B * Bᵀ).spectrumMultiset.filter (0 < ·)
  have hblock : (X.signlessLapMatrix ℝ).spectrumMultiset =
      (fromBlocks ((k₁ : ℝ) • 1) B Bᵀ ((k₂ : ℝ) • 1)).spectrumMultiset := by
    rw [← spectrumMultiset_submatrix_equiv (X.signlessLapMatrix ℝ) hb.sumEquiv,
      hb.signlessLapMatrix_eq_fromBlocks]
  -- The root zero is simple, so its paired Gram eigenvalue k₁k₂ is simple as well.
  have htop : (B * Bᵀ).eigenvalueMultiplicity ((k₁ : ℝ) * k₂) = 1 := by
    have he := eigenvalueMultiplicity_fromBlocks_scalar_of_ne B k₁ k₂ 0
      (by exact_mod_cast hpos.2.ne)
    have hcount := congrArg (Multiset.count (0 : ℝ)) hblock
    change (X.signlessLapMatrix ℝ).eigenvalueMultiplicity 0 =
      (fromBlocks ((k₁ : ℝ) • 1) B Bᵀ ((k₂ : ℝ) • 1)).eigenvalueMultiplicity 0 at hcount
    rw [hb.multiplicity_zero_signlessLapMatrix hcX, he] at hcount
    simpa using hcount.symm
  refine ⟨hlt, hk₂, htop, ?_⟩
  have hprodpos : (0 : ℝ) < (k₁ : ℝ) * k₂ := by
    exact_mod_cast Nat.mul_pos hpos.1 hpos.2
  have hcountpos : 0 < (B * Bᵀ).eigenvalueMultiplicity ((k₁ : ℝ) * k₂) := by omega
  have hmem : (k₁ : ℝ) * k₂ ∈ Λ :=
    Multiset.mem_filter.mpr ⟨Multiset.count_pos.mp hcountpos, hprodpos⟩
  -- Error 14: remove exactly one zero before translating the signless spectrum.
  have hsignless := hs.spectrumMultiset_signlessLapMatrix_add_singleton_zero
    hcX hcY hb.isBipartite hbY
  have hshift := congrArg (Multiset.map (fun θ : ℝ ↦ θ - (κ : ℝ))) hsignless
  rw [Multiset.map_add, hκ.spectrumMultiset_signlessLapMatrix, Multiset.map_map] at hshift
  simp only [Function.comp_def, add_sub_cancel_left, Multiset.map_id',
    Multiset.map_singleton, zero_sub] at hshift
  rw [hκR, hblock, spectrumMultiset_sub_center_fromBlocks_scalar B k₁ k₂ hneR] at hshift
  have hdelta : Real.sqrt ((k₁ : ℝ) * k₂ + ((k₁ : ℝ) - k₂) ^ 2 / 4) =
      ((k₁ : ℝ) + k₂) / 2 := by
    rw [show (k₁ : ℝ) * k₂ + ((k₁ : ℝ) - k₂) ^ 2 / 4 =
      (((k₁ : ℝ) + k₂) / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  change Y.spectrumMultiset + {-(((k₁ : ℝ) + k₂) / 2)} =
    Λ.map (fun μ ↦ Real.sqrt (μ + ((k₁ : ℝ) - k₂) ^ 2 / 4)) +
      Λ.map (fun μ ↦ -Real.sqrt (μ + ((k₁ : ℝ) - k₂) ^ 2 / 4)) +
      Multiset.replicate (Fintype.card P - B.rank) (((k₁ : ℝ) - k₂) / 2) +
      Multiset.replicate (Fintype.card Q - B.rank) (-((k₁ : ℝ) - k₂) / 2) at hshift
  rw [← Multiset.cons_erase hmem, Multiset.map_cons, Multiset.map_cons, hdelta] at hshift
  dsimp only
  apply add_right_cancel (b := {-(((k₁ : ℝ) + k₂) / 2)})
  rw [hshift]
  simp only [← Multiset.singleton_add, Nat.card_eq_fintype_card]
  dsimp only [Λ, B]
  abel

end SimpleGraph
