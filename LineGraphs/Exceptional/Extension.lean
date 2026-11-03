/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.CertificateExistence
import LineGraphs.Exceptional.ExtensionArithmetic
import LineGraphs.Exceptional.ExtensionRepresentation

/-! # The exact test for adding a vertex

Lemma `lem:extension` (Lemma 3.4) of [Exc].
-/

open Matrix Module Submodule
open scoped RealInnerProductSpace

namespace SimpleGraph

variable {V : Type*} [Finite V] [DecidableEq V]
  {X : SimpleGraph V} [DecidableRel X.Adj] {B : Finset V} {N : Set V}

open Classical in
-- Lemma 3.4 [Exc]
/-- Lemma `lem:extension` (Lemma 3.4) of [Exc]: the exact integer criterion for a
connected one-vertex extension to be represented in `E₈`. The indicator of `N ∩ B`
is built into the statement. -/
theorem isRepresentedIn_adjoinVertex_iff (hX : X.Connected)
    (hB : X.integralGramMatrix.IsGramCertificate B) (hr : B.card ≤ 8) (hN : N.Nonempty) :
    let s := certificateIndicator N B
    (X.adjoinVertex N).IsRepresentedIn LineSystem.E₈ ↔
      (∀ u, (s ᵥ* X.integralGramMatrix.certificateCoordinates B) u =
        X.integralGramMatrix.certificateDet B * (if u ∈ N then 1 else 0)) ∧
      s ⬝ᵥ ((X.integralGramMatrix.certificateMatrix B).adjugate *ᵥ s) ≤
        2 * X.integralGramMatrix.certificateDet B ∧
      (B.card = 8 → s ⬝ᵥ ((X.integralGramMatrix.certificateMatrix B).adjugate *ᵥ s) =
        2 * X.integralGramMatrix.certificateDet B) := by
  classical
  let := Fintype.ofFinite V
  let s := certificateIndicator N B
  let D := X.integralGramMatrix.certificateDet B
  let Q := s ⬝ᵥ ((X.integralGramMatrix.certificateMatrix B).adjugate *ᵥ s)
  have hM := X.integralGramMatrix_isSymm
  have hD : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hB.det_pos hM
  change (X.adjoinVertex N).IsRepresentedIn LineSystem.E₈ ↔
    (∀ u, (s ᵥ* X.integralGramMatrix.certificateCoordinates B) u =
      D * (if u ∈ N then 1 else 0)) ∧ Q ≤ 2 * D ∧ (B.card = 8 → Q = 2 * D)
  constructor
  · rintro ⟨y, hy, _⟩
    let x := fun u : V => y (some u)
    have hx : X.IsRepresentation x := hy.of_adjoinVertex X N
    have hxM : gram ℝ x = X.integralGramMatrix.map (Int.cast : ℤ → ℝ) := by
      rw [X.integralGramMatrix_cast]
      exact hx
    let z := fun b : B => x b
    have hi := hB.linearIndependent_gram hM hxM
    have hp : (gram ℝ z).PosDef := posDef_gram_of_linearIndependent hi
    let p := gramProjection z (fun b => (s b : ℝ))
    have hys : ∀ b : B, ⟪y none, z b⟫ = (s b : ℝ) := by
      intro b
      simpa [s, certificateIndicator, z, x] using isRepresentation_iff.mp hy none (some b)
    have hyn : ∀ u, ⟪y none, x u⟫ = if u ∈ N then 1 else 0 := by
      intro u
      simpa [x] using isRepresentation_iff.mp hy none (some u)
    have hnorm : ⟪p, p⟫ = (Q : ℝ) / (D : ℝ) :=
      hB.gramProjection_inner_self hM hxM s
    refine ⟨?_, ?_, ?_⟩
    · intro u
      have hu : x u ∈ span ℝ (Set.range z) := by
        rw [hB.span_gram hM hxM]
        exact subset_span (Set.mem_range_self u)
      have he := gramProjection_inner_eq_of_mem_span z hp (fun b => (s b : ℝ)) hys hu
      have hf := hB.gramProjection_inner hM hxM s u
      have hquot : ((s ᵥ* X.integralGramMatrix.certificateCoordinates B) u : ℝ) / (D : ℝ) =
          if u ∈ N then 1 else 0 := hf.symm.trans (he.trans (hyn u))
      have hm := (div_eq_iff hD.ne').mp hquot
      by_cases huN : u ∈ N <;> simp only [huN, ite_true, ite_false, one_mul, zero_mul,
        mul_one, mul_zero] at hm ⊢ <;> exact_mod_cast hm
    · have hn := gramProjection_inner_self_le z hp (fun b => (s b : ℝ)) hys
      rw [hy.inner_self, hnorm] at hn
      have hn' := (div_le_iff₀ hD).mp hn
      exact_mod_cast hn'
    · intro hr8
      have htop : span ℝ (Set.range z) = ⊤ :=
        hi.span_eq_top_of_card_eq_finrank' (by simpa using hr8)
      have hn := gramProjection_inner_self_eq_of_mem_span z hp (fun b => (s b : ℝ))
        hys (by rw [htop]; trivial)
      rw [hy.inner_self, hnorm] at hn
      have hn' := (div_eq_iff hD.ne').mp hn
      exact_mod_cast hn'
  · rintro ⟨hc, hq, hq8⟩
    have hpos := hB.posSemidef hM
    obtain ⟨x, hxM⟩ := hpos.exists_gram_euclideanSpace (hB.card_eq_rank hM).symm.le
    have hx : X.IsRepresentation x := by
      simpa only [IsRepresentation, X.integralGramMatrix_cast] using hxM
    let z := fun b : B => x b
    let p := gramProjection z (fun b => (s b : ℝ))
    have hnorm : ⟪p, p⟫ = (Q : ℝ) / (D : ℝ) :=
      hB.gramProjection_inner_self hM hxM s
    apply hx.isRepresentedIn_adjoinVertex_of_norm_le hX hN p
    · intro u
      rw [hB.gramProjection_inner hM hxM s u]
      apply (div_eq_iff hD.ne').mpr
      have hu := hc u
      by_cases huN : u ∈ N <;> simp only [huN, ite_true, ite_false, one_mul, zero_mul,
        mul_one, mul_zero] at hu ⊢ <;> exact_mod_cast hu
    · rw [hnorm]
      apply (div_le_iff₀ hD).mpr
      exact_mod_cast hq
    · simpa using hr
    · intro he
      rw [hnorm]
      apply (div_eq_iff hD.ne').mpr
      have he' : B.card = 8 := by simpa using he
      exact_mod_cast hq8 he'

end SimpleGraph
