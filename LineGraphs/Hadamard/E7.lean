/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.ComponentStars
import LineGraphs.Computations.C6
import LineGraphs.Computations.C20E7

/-!
# No component of type E₇

Blueprint Lemma `lem:6-E7`, Section 6 of [CGSS], repairing Gap 17. The injection
`(r, s) ↦ (r + s, r)` would map 3136 ordered pairs into a set of cardinality 448.
For `s6eNt` we use the blueprint's permitted C20 neighborhood count, transported through the
root isomorphism. The C6 frame identity is also recorded for the component realization.
-/

open scoped BigOperators RealInnerProductSpace
open Finset

namespace LineSystem

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The root-neighborhood bijection in step `s6eNt` of `lem:6-E7`, Section 6 of [CGSS]. -/
noncomputable def Iso.neighborEquiv {S : LineSystem V} {T : LineSystem W} (e : S.Iso T)
    (r : S.Φ) : S.N r ≃ T.N (e.toEquiv r) := Equiv.ofBijective
  (fun (x : S.N r) ↦ (⟨e.toEquiv ⟨x, x.property.1⟩,
    (e.toEquiv ⟨x, x.property.1⟩).property,
    (e.inner_map ⟨x, x.property.1⟩ r).trans x.property.2⟩ : T.N (e.toEquiv r))) (by
    constructor
    · intro x y h
      apply Subtype.ext
      have he : e.toEquiv ⟨x, x.property.1⟩ = e.toEquiv ⟨y, y.property.1⟩ :=
        Subtype.ext (congrArg (fun z : T.N (e.toEquiv r) ↦ (z : W)) h)
      exact congrArg (fun z : S.Φ ↦ (z : V)) (e.toEquiv.injective he)
    · intro y
      let x := e.toEquiv.symm ⟨y, y.property.1⟩
      have hx : ⟪(x : V), (r : V)⟫ = 1 := by
        rw [← e.inner_map x r]
        simpa only [x, Equiv.apply_symm_apply] using y.property.2
      refine ⟨⟨x, x.property, hx⟩, Subtype.ext ?_⟩
      exact congrArg (fun z : T.Φ ↦ (z : W))
        (e.toEquiv.apply_symm_apply ⟨y, y.property.1⟩))

/-- Steps `s6ecounts` and `s6eNt` of `lem:6-E7`: every copy of `E₇` has 126 roots,
frame constant 36 (C6), and 32 roots in each `N_r` (the permitted C20 leaf). -/
theorem Iso.e₇_data {S : LineSystem V} (e : S.Iso E₇) :
    S.Φ.ncard = 126 ∧ S.IsFrame 36 ∧ ∀ r ∈ S.Φ, (S.N r).ncard = 32 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq,
      Nat.card_congr (e.toEquiv.trans E₇.integerModel.equiv.symm)]
    change Nat.card E₇Index = 126
    rw [Nat.card_eq_fintype_card, card_E₇Index]
  · have hf := frame_identity RootType.E₇ ⟨e⟩
    rw [e.numLines_eq, numLines_E₇] at hf
    norm_num [RootType.rank] at hf
    exact hf
  · intro r hr
    rw [Set.ncard_congr' (e.neighborEquiv ⟨r, hr⟩)]
    exact E₇.card_N (e.toEquiv ⟨r, hr⟩).property

end LineSystem

namespace Matrix.IsHadamard

-- Lemma (no component of type E₇), Section 6
/-- Blueprint `lem:6-E7`, Section 6 of [CGSS], conditional on Theorem 3.5. The original
112 roots give 3136 ordered pairs at inner product minus one. Their third roots lie among
the 14 new roots, each having only 32 neighbors, contradicting injectivity. -/
theorem not_component_E₇_of_classification {H : Matrix (Fin 16) (Fin 16) ℤ}
    (hH : H.IsHadamard) (ha : H.AgreeSixteenths)
    (hclass : ∀ S : LineSystem (EuclideanSpace ℝ (Fin 16)), S.Φ.Nonempty →
      S.IsIndecomposable → S.IsStarClosed →
        ∃! t : LineSystem.RootType, Nonempty (S.Iso t.model))
    (K : H.hadamardGraph.ConnectedComponent) :
    ¬ Nonempty ((hH.componentStarClosure (dvd_refl 16) (le_refl 16) ha K).Iso LineSystem.E₇) := by
  classical
  intro hE
  let S := hH.componentLineSystem (dvd_refl 16) (le_refl 16) ha K
  let R := hH.componentStarClosure (dvd_refl 16) (le_refl 16) ha K
  obtain ⟨hne, hi, hsc, hsub, _⟩ :=
    hH.componentStarClosure_properties (dvd_refl 16) (le_refl 16) ha K
  obtain ⟨t, ht, _⟩ :=
    hH.component_rootType_of_classification (dvd_refl 16) (le_refl 16) ha hclass K
  have htE : t = LineSystem.RootType.E₇ := (hclass R hne hi hsc).unique ht.1 hE
  have hrank : componentRank K = 7 := by
    have hr := ht.2.1
    rw [htE] at hr
    exact hr.symm
  obtain ⟨e⟩ := hE
  obtain ⟨hR, _hframe, hN⟩ := e.e₇_data
  have hS : S.Φ.ncard = 112 := by
    rw [hH.ncard_componentLineSystem, hH.two_mul_card_component, hrank]
  let D := R.Φ \ S.Φ
  have hDfinite : D.Finite := R.finite.subset fun _ h ↦ h.1
  have hD : D.ncard = 14 := by
    rw [Set.ncard_sdiff' hsub R.finite, hR, hS]
  let M (r : S.Φ) := {s | s ∈ S.Φ ∧ ⟪(r : EuclideanSpace ℝ (Fin 16)), s⟫ = -1}
  let Q := (r : S.Φ) × M r
  let T := (t : D) × R.N t
  let : Fintype S.Φ := S.finite.fintype
  let : ∀ r : S.Φ, Fintype (M r) := fun _ ↦ (S.finite.subset fun _ h ↦ h.1).fintype
  let : Fintype D := hDfinite.fintype
  let : ∀ t : D, Fintype (R.N t) := fun t ↦ (R.finite_N t).fintype
  have hQ : Fintype.card Q = 3136 := by
    have hrow (r : S.Φ) : Fintype.card (M r) = 28 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact hH.ncard_component_inner_eq_neg_one (dvd_refl 16) (le_refl 16) ha K r.property
    have hS' : Fintype.card S.Φ = 112 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hS]
    change Fintype.card ((r : S.Φ) × M r) = _
    rw [Fintype.card_sigma]
    simp only [hrow, sum_const, card_univ, smul_eq_mul, hS']
  have hT : Fintype.card T = 448 := by
    have hrow (t : D) : Fintype.card (R.N t) = 32 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact hN t t.property.1
    have hD' : Fintype.card D = 14 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hD]
    change Fintype.card ((t : D) × R.N t) = _
    rw [Fintype.card_sigma]
    simp only [hrow, sum_const, card_univ, smul_eq_mul, hD']
  let f : Q → T := fun q ↦
    let h := hH.add_mem_componentStarClosure_sdiff (dvd_refl 16) (le_refl 16) ha K
      q.1.property q.2.property.1 q.2.property.2
    ⟨⟨q.1 + q.2, h.1⟩, ⟨q.1, hsub q.1.property, h.2⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨r, s⟩ ⟨r', s'⟩ h
    have hfirst : (r : EuclideanSpace ℝ (Fin 16)) + s = r' + s' :=
      congrArg (fun t : T ↦ (t.1 : EuclideanSpace ℝ (Fin 16))) h
    have hsecond : (r : EuclideanSpace ℝ (Fin 16)) = r' :=
      congrArg (fun t : T ↦ (t.2 : EuclideanSpace ℝ (Fin 16))) h
    have he : r = r' := Subtype.ext hsecond
    subst r'
    exact congrArg (Sigma.mk r) (Subtype.ext (add_left_cancel hfirst))
  have hle := Fintype.card_le_of_injective f hf
  rw [hQ, hT] at hle
  norm_num at hle

end Matrix.IsHadamard
