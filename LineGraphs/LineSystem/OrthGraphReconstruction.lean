/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.OrthGraphGram
import LineGraphs.LineSystem.SpanTransport

/-! # Reconstruction from the orthogonality graph in [CGSS, Lemma 2.12] -/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Steps 212relations–212isometry of `lem:2.12` ([CGSS, Lemma 2.12]): equal Gram
matrices of two finite spanning families give a surjective linear isometry with the
prescribed values, by factoring linear combinations through their kernel. -/
theorem exists_isometry_of_eq_gram {I : Type*} [Finite I] (r : I → V) (s : I → W)
    (hr : span ℝ (Set.range r) = ⊤) (hs : span ℝ (Set.range s) = ⊤)
    (hgram : ∀ i j, ⟪s i, s j⟫ = ⟪r i, r j⟫) :
    ∃ F : V ≃ₗᵢ[ℝ] W, ∀ i, F (r i) = s i := by
  classical
  let := Fintype.ofFinite I
  let f := Fintype.linearCombination ℝ r
  let g := Fintype.linearCombination ℝ s
  -- 212ranges.
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hr]
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hs]
  -- 212norms and 212inner: bilinearity, first for equal and then arbitrary coefficients.
  have hi (a b : I → ℝ) : ⟪g a, g b⟫ = ⟪f a, f b⟫ := by
    simp only [f, g, Fintype.linearCombination_apply, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right, hgram]
  -- 212relations and 212kernel: the codomain is already the chosen spanning space.
  have hk : LinearMap.ker f ≤ LinearMap.ker g := by
    intro a ha
    apply LinearMap.mem_ker.mpr
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hi, LinearMap.mem_ker.mp ha, inner_zero_left]
  -- 212quotient, 212rangemap and 212compose.
  let F := ((LinearMap.ker f).liftQ g hk).comp
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap
  -- 212oncombinations: quotienting and its inverse retain the coefficient formula.
  have hF (a : I → ℝ) : F (f a) = g a := by simp [F]
  let G := F.isometryOfInner (by
    intro x y
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [hF, hF, hi])
  -- 212linearonto and 212injective.
  have hG : Function.Surjective G := by
    intro y
    obtain ⟨a, rfl⟩ := hg y
    exact ⟨f a, hF a⟩
  refine ⟨LinearIsometryEquiv.ofSurjective G hG, fun i ↦ ?_⟩
  -- 212generatorvalues: the coefficient function supported at `i`.
  change F (r i) = s i
  simpa only [f, g, Fintype.linearCombination_apply_single, one_smul] using
    hF (Pi.single i 1)

namespace Hyp24

variable (H : Hyp24 V)

/-- The finite family indexed by the ordered star and `Γa` in step 212metric of
`lem:2.12` ([CGSS, Lemma 2.12]). -/
def starFamily : Fin 3 ⊕ H.Γa → V := Sum.elim ![H.a, H.b, H.c] Subtype.val

/-- Step 212recover of `lem:2.12` ([CGSS, Lemma 2.12]): every vector of the star
family belongs to the signed root set. -/
theorem starFamily_mem (i : Fin 3 ⊕ H.Γa) : H.starFamily i ∈ H.S.Φ := by
  rcases i with i | x
  · fin_cases i <;> first | exact H.a_mem | exact H.b_mem | exact H.c_mem
  · exact x.property.1

/-- Steps 212recover and 212ranges of `lem:2.12` ([CGSS, Lemma 2.12]): the ordered
star together with `Γa` spans the full root span. -/
theorem span_range_starFamily : span ℝ (Set.range H.starFamily) = span ℝ H.S.Φ := by
  apply le_antisymm
  · exact span_mono (by rintro _ ⟨i, rfl⟩; exact H.starFamily_mem i)
  · -- 212formulas: the existing Lemma 2.7 recovery equality gives the reverse inclusion.
    rw [H.span_Φ_eq_span_pair_union_Γa]
    apply span_mono
    rintro x (hx | hx)
    · rcases hx with rfl | hx
      · exact ⟨Sum.inl 0, rfl⟩
      · exact ⟨Sum.inl 1, (Set.mem_singleton_iff.mp hx).symm⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩

/-- Steps 212gram, 212stargram and 212graphgram of `lem:2.12` ([CGSS, Lemma 2.12]): a graph
isomorphism preserves the Gram matrix of the star family. -/
theorem inner_starFamily_map (H' : Hyp24 W) (e : H.orthGraph ≃g H'.orthGraph)
    (i j : Fin 3 ⊕ H.Γa) :
    ⟪H'.starFamily (Sum.map id e i), H'.starFamily (Sum.map id e j)⟫ =
      ⟪H.starFamily i, H.starFamily j⟫ := by
  classical
  rcases i with i | x <;> rcases j with j | y
  · fin_cases i <;> fin_cases j <;>
      simp only [Sum.map_inl, starFamily, Sum.elim_inl, id_eq,
        Matrix.cons_val_zero', Matrix.cons_val_succ', H.S.inner_self _ H.a_mem,
        H.S.inner_self _ H.b_mem, H.S.inner_self _ H.c_mem,
        H'.S.inner_self _ H'.a_mem, H'.S.inner_self _ H'.b_mem, H'.S.inner_self _ H'.c_mem,
        H.inner_a_b, H.inner_b_a, H.inner_a_c, H.inner_c_a, H.inner_b_c, H.inner_c_b,
        H'.inner_a_b, H'.inner_b_a, H'.inner_a_c, H'.inner_c_a, H'.inner_b_c, H'.inner_c_b]
  · fin_cases i <;>
      simp only [Sum.map_inl, Sum.map_inr, starFamily, Sum.elim_inl, Sum.elim_inr, id_eq,
        Matrix.cons_val_zero', Matrix.cons_val_succ']
    all_goals rw [real_inner_comm (e y : W) _, real_inner_comm (y : V) _]
    · exact (H'.inner_a_of_mem_Γa (e y).property).trans (H.inner_a_of_mem_Γa y.property).symm
    · exact (H'.inner_b_of_mem_Γa (e y).property).trans (H.inner_b_of_mem_Γa y.property).symm
    · exact (H'.inner_c_of_mem_Γa (e y).property).trans (H.inner_c_of_mem_Γa y.property).symm
  · fin_cases j <;>
      simp only [Sum.map_inl, Sum.map_inr, starFamily, Sum.elim_inl, Sum.elim_inr, id_eq,
        Matrix.cons_val_zero', Matrix.cons_val_succ']
    · exact (H'.inner_a_of_mem_Γa (e x).property).trans (H.inner_a_of_mem_Γa x.property).symm
    · exact (H'.inner_b_of_mem_Γa (e x).property).trans (H.inner_b_of_mem_Γa x.property).symm
    · exact (H'.inner_c_of_mem_Γa (e x).property).trans (H.inner_c_of_mem_Γa x.property).symm
  · change ⟪(e x : W), e y⟫ = ⟪(x : V), y⟫
    simp only [H.inner_Γa_eq, H'.inner_Γa_eq, e.injective.eq_iff, e.map_adj_iff]

/-- Step 212metric of `lem:2.12` ([CGSS, Lemma 2.12]): every graph isomorphism
extends to a surjective linear isometry of the root spans with the prescribed star-family
values. No finite-dimensional ambient-space assumption is needed. -/
theorem exists_spanIsometry_of_orthGraphIso (H' : Hyp24 W)
    (e : H.orthGraph ≃g H'.orthGraph) :
    ∃ F : span ℝ H.S.Φ ≃ₗᵢ[ℝ] span ℝ H'.S.Φ,
      ∀ i, (F ⟨H.starFamily i, subset_span (H.starFamily_mem i)⟩ : W) =
        H'.starFamily (Sum.map id e i) := by
  classical
  let r (i : Fin 3 ⊕ H.Γa) : span ℝ H.S.Φ :=
    ⟨H.starFamily i, subset_span (H.starFamily_mem i)⟩
  let s (i : Fin 3 ⊕ H.Γa) : span ℝ H'.S.Φ :=
    ⟨H'.starFamily (Sum.map id e i), subset_span (H'.starFamily_mem _)⟩
  have hr : span ℝ (Set.range r) = ⊤ :=
    (span_range_subtype_eq_top_iff _ _).mpr H.span_range_starFamily
  have hs : span ℝ (Set.range s) = ⊤ := by
    apply (span_range_subtype_eq_top_iff _ _).mpr
    have he : Function.Surjective (Sum.map (id : Fin 3 → Fin 3) e) :=
      (Equiv.sumCongr (Equiv.refl _) e.toEquiv).surjective
    change span ℝ (Set.range (H'.starFamily ∘ Sum.map id e)) = _
    rw [he.range_comp, H'.span_range_starFamily]
  obtain ⟨F, hF⟩ := exists_isometry_of_eq_gram r s hr hs (H.inner_starFamily_map H' e)
  exact ⟨F, fun i ↦ congrArg Subtype.val (hF i)⟩

/-- Steps 212image–212onto of `lem:2.12` ([CGSS, Lemma 2.12]): the isometry of root
spans carries the recovered signed root sets onto one another and extends the graph map. -/
theorem exists_iso_of_orthGraphIso (H' : Hyp24 W) (e : H.orthGraph ≃g H'.orthGraph) :
    ∃ q : H.S.Iso H'.S,
      (q.toEquiv ⟨H.a, H.a_mem⟩ : W) = H'.a ∧
      (q.toEquiv ⟨H.b, H.b_mem⟩ : W) = H'.b ∧
      (q.toEquiv ⟨H.c, H.c_mem⟩ : W) = H'.c ∧
      ∀ x : H.Γa, (q.toEquiv ⟨x, x.property.1⟩ : W) = (e x : W) := by
  obtain ⟨F, hF⟩ := H.exists_spanIsometry_of_orthGraphIso H' e
  have ha : (F ⟨H.a, subset_span H.a_mem⟩ : W) = H'.a := hF (Sum.inl 0)
  have hb : (F ⟨H.b, subset_span H.b_mem⟩ : W) = H'.b := hF (Sum.inl 1)
  have hc : (F ⟨H.c, subset_span H.c_mem⟩ : W) = H'.c := hF (Sum.inl 2)
  have hx (x : H.Γa) : (F ⟨x, subset_span x.property.1⟩ : W) = (e x : W) :=
    hF (Sum.inr x)
  -- Use an ambient linear extension only to invoke the existing recovery equalities.
  obtain ⟨g, hg⟩ := ((span ℝ H'.S.Φ).subtype.comp F.toLinearMap).exists_extend
  have hgv (x : span ℝ H.S.Φ) : g x = (F x : W) := LinearMap.congr_fun hg x
  have hga : g H.a = H'.a := (hgv ⟨H.a, subset_span H.a_mem⟩).trans ha
  have hgb : g H.b = H'.b := (hgv ⟨H.b, subset_span H.b_mem⟩).trans hb
  have hgx (x : H.Γa) : g x = (e x : W) :=
    (hgv ⟨x, subset_span x.property.1⟩).trans (hx x)
  have hΓ : g '' H.Γa = H'.Γa := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hgx ⟨x, hx⟩] using (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [hgx]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  have hi : ∀ x ∈ H.Γa, ∀ y ∈ H.Γa, ⟪g x, g y⟫ = ⟪x, y⟫ := by
    intro x hx y hy
    rw [hgv ⟨x, subset_span hx.1⟩, hgv ⟨y, subset_span hy.1⟩]
    exact F.inner_map_map _ _
  -- 212imagea–212imagesigns and 212ontostar–212ontosigns are the two inclusions
  -- of the recovery transport theorem. In detail, 212imageplus and 212imageminus
  -- transport the translations, while 212imagedifference uses 212differenceproduct (`hi`).
  -- Surjectivity in `hΓ` gives 212ontogamma, and linearity then gives 212ontoplus,
  -- 212ontominus and 212ontodifference. Negation gives both signs in both directions.
  have hΦ := H.image_Φ_eq H' g hga hgb hΓ hi
  have hFΦ : F '' H.S.restrictSpan.Φ = H'.S.restrictSpan.Φ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (F x : W) ∈ H'.S.Φ
      rw [← hgv x, ← hΦ]
      exact Set.mem_image_of_mem g hx
    · intro hy
      have hy' : (y : W) ∈ g '' H.S.Φ := by
        simpa only [hΦ] using (show (y : W) ∈ H'.S.Φ from hy)
      obtain ⟨x, hx, he⟩ := hy'
      refine ⟨⟨x, subset_span hx⟩, hx, Subtype.ext ?_⟩
      exact (hgv ⟨x, subset_span hx⟩).symm.trans he
  -- 212rootiso: restrict the isometry to the recovered root sets.
  exact ⟨Iso.ofSpanIsometry _ _ F hFΦ, ha, hb, hc, hx⟩

end Hyp24

-- Lemma 2.12
/-- Lemma 2.12 of [CGSS] (`lem:2.12`): extend an isomorphism of the orthogonality
graphs to an isomorphism of the line systems. Its `spanIsometry` is a surjective linear
isometry carrying the ordered stars and inducing the given graph map. -/
noncomputable def Iso.ofOrthGraphIso (H : Hyp24 V) (H' : Hyp24 W)
    (e : H.orthGraph ≃g H'.orthGraph) : H.S.Iso H'.S :=
  (H.exists_iso_of_orthGraphIso H' e).choose

/-- The first ordered-star value in step 212imagea of `lem:2.12`
([CGSS, Lemma 2.12]). -/
theorem Iso.ofOrthGraphIso_a (H : Hyp24 V) (H' : Hyp24 W)
    (e : H.orthGraph ≃g H'.orthGraph) :
    ((Iso.ofOrthGraphIso H H' e).toEquiv ⟨H.a, H.a_mem⟩ : W) = H'.a :=
  (H.exists_iso_of_orthGraphIso H' e).choose_spec.1

/-- The second ordered-star value in step 212imageb of `lem:2.12`
([CGSS, Lemma 2.12]). -/
theorem Iso.ofOrthGraphIso_b (H : Hyp24 V) (H' : Hyp24 W)
    (e : H.orthGraph ≃g H'.orthGraph) :
    ((Iso.ofOrthGraphIso H H' e).toEquiv ⟨H.b, H.b_mem⟩ : W) = H'.b :=
  (H.exists_iso_of_orthGraphIso H' e).choose_spec.2.1

/-- The third ordered-star value in step 212imagec of `lem:2.12`
([CGSS, Lemma 2.12]). -/
theorem Iso.ofOrthGraphIso_c (H : Hyp24 V) (H' : Hyp24 W)
    (e : H.orthGraph ≃g H'.orthGraph) :
    ((Iso.ofOrthGraphIso H H' e).toEquiv ⟨H.c, H.c_mem⟩ : W) = H'.c :=
  (H.exists_iso_of_orthGraphIso H' e).choose_spec.2.2.1

/-- Step 212imagegamma of `lem:2.12` ([CGSS, Lemma 2.12]): the reconstructed root
isomorphism induces the original graph isomorphism on `Γa`. -/
theorem Iso.ofOrthGraphIso_Γa (H : Hyp24 V) (H' : Hyp24 W)
    (e : H.orthGraph ≃g H'.orthGraph) (x : H.Γa) :
    ((Iso.ofOrthGraphIso H H' e).toEquiv ⟨x, x.property.1⟩ : W) = (e x : W) :=
  (H.exists_iso_of_orthGraphIso H' e).choose_spec.2.2.2 x

/-- Step 213delta of `thm:2.13` ([CGSS, Theorem 2.13]): graph reconstruction preserves
the cardinality of the signed set `Δ`, using the marked-set transport from the root iso. -/
theorem Hyp24.card_Δ_eq_of_orthGraphIso (H : Hyp24 V) (H' : Hyp24 W)
    (e : H.orthGraph ≃g H'.orthGraph) : H.Δ.ncard = H'.Δ.ncard := by
  let q := Iso.ofOrthGraphIso H H' e
  have him := q.image_Δ (Iso.ofOrthGraphIso_a H H' e) (Iso.ofOrthGraphIso_b H H' e)
  have hinj : Function.Injective (fun r : H.S.Φ ↦ (q.toEquiv r : W)) :=
    Subtype.val_injective.comp q.toEquiv.injective
  rw [← him, Set.ncard_image_of_injective _ hinj, Set.ncard_subtype]
  change H.Δ.ncard = (H.Δ ∩ H.S.Φ).ncard
  rw [Set.inter_eq_left.mpr H.Δ_subset_Φ]

end LineSystem
