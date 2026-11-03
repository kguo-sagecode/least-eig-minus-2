/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Frame
import LineGraphs.LineSystem.Inclusions
import LineGraphs.Computations.ModelIsoProperties
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Transport and restriction to root spans

The lemmas `lem:sec3-transport` and `lem:sec3-restrict` of the Section 3 blueprint, used in
Theorems 3.5 and 3.6 of [CGSS]. A root isomorphism extends uniquely by factoring linear
combinations through their kernel. No finite-dimensional ambient space is required.
-/

open scoped RealInnerProductSpace
open Submodule Module

namespace LineSystem

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The defining set `Γa` of Hypothesis 2.4 of [CGSS], for any line system and vectors
`a`, `b`: the roots with products `(0, 1, -1)` against `(a, b, -a - b)`. -/
def Γa (S : LineSystem V) (a b : V) : Set V :=
  {x ∈ S.Φ | ⟪x, a⟫ = 0 ∧ ⟪x, b⟫ = 1 ∧ ⟪x, -a - b⟫ = -1}

/-- The defining set `Δ` of Hypothesis 2.4 of [CGSS], for any line system and vectors
`a`, `b`: the roots orthogonal to `a`, `b` and `-a - b`, with both signs. -/
def Δ (S : LineSystem V) (a b : V) : Set V :=
  {x ∈ S.Φ | ⟪x, a⟫ = 0 ∧ ⟪x, b⟫ = 0 ∧ ⟪x, -a - b⟫ = 0}

namespace Iso

variable {S : LineSystem V} {T : LineSystem W}

/-- `lem:sec3-transport`: the inverse root bijection preserves inner products. -/
def symm (e : S.Iso T) : T.Iso S where
  toEquiv := e.toEquiv.symm
  inner_map r s := by
    simpa only [Equiv.apply_symm_apply] using
      (e.inner_map (e.toEquiv.symm r) (e.toEquiv.symm s)).symm

/-- `lem:sec3-transport`, steps `s3trrelations`--`s3trisometry`: factor the coefficient
map through its kernel to obtain a surjective linear isometry extending the root bijection. -/
theorem exists_spanIsometry (e : S.Iso T) :
    ∃ F : span ℝ S.Φ ≃ₗᵢ[ℝ] span ℝ T.Φ,
      ∀ r : S.Φ, (F ⟨r, subset_span r.property⟩ : W) = e.toEquiv r := by
  classical
  let := S.finite.fintype
  let v : S.Φ → span ℝ S.Φ := fun r ↦ ⟨r, subset_span r.property⟩
  let w : S.Φ → span ℝ T.Φ := fun r ↦ ⟨e.toEquiv r, subset_span (e.toEquiv r).property⟩
  let f := Fintype.linearCombination ℝ v
  let g := Fintype.linearCombination ℝ w
  have hv : Set.range v = Subtype.val ⁻¹' S.Φ := by
    ext x
    exact ⟨fun ⟨r, hr⟩ ↦ hr ▸ r.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have hw : Set.range w = Subtype.val ⁻¹' T.Φ := by
    ext x
    constructor
    · rintro ⟨r, rfl⟩
      exact (e.toEquiv r).property
    · intro hx
      refine ⟨e.toEquiv.symm ⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact congrArg (fun r : T.Φ ↦ (r : W)) (e.toEquiv.apply_symm_apply ⟨x, hx⟩)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]
    exact span_span_coe_preimage
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hw]
    exact span_span_coe_preimage
  have hinner (a b : S.Φ → ℝ) : ⟪g a, g b⟫ = ⟪f a, f b⟫ := by
    simp only [f, g, Fintype.linearCombination_apply, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [show ⟪w s, w r⟫ = ⟪v s, v r⟫ from e.inner_map s r]
  have hk : LinearMap.ker f ≤ LinearMap.ker g := by
    intro a ha
    apply LinearMap.mem_ker.mpr
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hinner, LinearMap.mem_ker.mp ha, inner_zero_left]
  let F := ((LinearMap.ker f).liftQ g hk).comp
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hF (a : S.Φ → ℝ) : F (f a) = g a := by
    simp [F]
  let G := F.isometryOfInner (by
    intro x y
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [hF, hF, hinner])
  have hG : Function.Surjective G := by
    intro y
    obtain ⟨a, rfl⟩ := hg y
    exact ⟨f a, hF a⟩
  refine ⟨LinearIsometryEquiv.ofSurjective G hG, fun r ↦ ?_⟩
  change (F (v r) : W) = (w r : W)
  have h := hF (Pi.single r 1)
  simpa only [f, g, Fintype.linearCombination_apply_single, one_smul] using
    congrArg Subtype.val h

/-- `lem:sec3-transport`: the surjective linear isometry of root spans induced by an `Iso`. -/
noncomputable def spanIsometry (e : S.Iso T) : span ℝ S.Φ ≃ₗᵢ[ℝ] span ℝ T.Φ :=
  e.exists_spanIsometry.choose

/-- `lem:sec3-transport`: the span isometry agrees with the given map on every root. -/
theorem spanIsometry_apply (e : S.Iso T) (r : S.Φ) :
    (e.spanIsometry ⟨r, subset_span r.property⟩ : W) = e.toEquiv r :=
  e.exists_spanIsometry.choose_spec r

/-- `lem:sec3-transport`: uniqueness of the linear extension from the spanning roots. -/
theorem spanIsometry_unique (e : S.Iso T) (F : span ℝ S.Φ ≃ₗᵢ[ℝ] span ℝ T.Φ)
    (hF : ∀ r : S.Φ, (F ⟨r, subset_span r.property⟩ : W) = e.toEquiv r) :
    F = e.spanIsometry := by
  have h : F.toLinearMap = e.spanIsometry.toLinearMap :=
    (Submodule.linearMap_eq_iff_of_eq_span _ _ rfl).mpr
      (fun r ↦ Subtype.ext ((hF r).trans (e.spanIsometry_apply r).symm))
  ext x
  exact congrArg Subtype.val (LinearMap.congr_fun h x)

/-- `lem:sec3-transport`: extending the inverse root bijection gives the inverse isometry. -/
theorem spanIsometry_symm (e : S.Iso T) : e.symm.spanIsometry = e.spanIsometry.symm := by
  symm
  apply e.symm.spanIsometry_unique
  intro r
  have h : e.spanIsometry ⟨e.toEquiv.symm r, subset_span (e.toEquiv.symm r).property⟩ =
      ⟨r, subset_span r.property⟩ := by
    apply Subtype.ext
    rw [e.spanIsometry_apply, Equiv.apply_symm_apply]
  exact congrArg Subtype.val (e.spanIsometry.symm_apply_eq.mpr h.symm)

/-- `lem:sec3-transport`, step `s3trrank`: isomorphic systems have equal span dimensions. -/
theorem finrank_span_eq (e : S.Iso T) : finrank ℝ (span ℝ S.Φ) = finrank ℝ (span ℝ T.Φ) :=
  e.spanIsometry.toLinearEquiv.finrank_eq

/-- `lem:sec3-transport`, step `s3trlines`: isomorphic systems have the same number of lines. -/
theorem numLines_eq (e : S.Iso T) : S.numLines = T.numLines := by
  rw [numLines, numLines, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr e.toEquiv]

/-- `lem:sec3-transport`: nonemptiness is preserved by the root bijection. -/
theorem nonempty_iff (e : S.Iso T) : S.Φ.Nonempty ↔ T.Φ.Nonempty := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨e.toEquiv ⟨r, hr⟩, (e.toEquiv ⟨r, hr⟩).property⟩
  · rintro ⟨r, hr⟩
    exact ⟨e.toEquiv.symm ⟨r, hr⟩, (e.toEquiv.symm ⟨r, hr⟩).property⟩

/-- `lem:sec3-transport`, step `s3trinner`: inner products on the spans are preserved. -/
theorem inner_spanIsometry (e : S.Iso T) (x y : span ℝ S.Φ) :
    ⟪(e.spanIsometry x : W), (e.spanIsometry y : W)⟫ = ⟪(x : V), (y : V)⟫ :=
  e.spanIsometry.inner_map_map x y

/-- `lem:sec3-transport`: a vector of the source span is a root exactly when its image is. -/
theorem spanIsometry_mem_iff (e : S.Iso T) (x : span ℝ S.Φ) :
    (e.spanIsometry x : W) ∈ T.Φ ↔ (x : V) ∈ S.Φ := by
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := e.toEquiv.surjective ⟨e.spanIsometry x, hx⟩
    have h : e.spanIsometry ⟨r, subset_span r.property⟩ = e.spanIsometry x := by
      apply Subtype.ext
      exact (e.spanIsometry_apply r).trans (congrArg (fun r : T.Φ ↦ (r : W)) hr)
    exact congrArg Subtype.val (e.spanIsometry.injective h) ▸ r.property
  · intro hx
    rw [e.spanIsometry_apply ⟨x, hx⟩]
    exact (e.toEquiv ⟨x, hx⟩).property

/-- `lem:sec3-transport`, step `s3trclosed`: star-closure is an isomorphism invariant. -/
theorem isStarClosed_iff (e : S.Iso T) : S.IsStarClosed ↔ T.IsStarClosed :=
  ⟨e.symm.isStarClosed, e.isStarClosed⟩

/-- `lem:sec3-transport`, step `s3trindecomp`: indecomposability is an isomorphism invariant. -/
theorem isIndecomposable_iff (e : S.Iso T) : S.IsIndecomposable ↔ T.IsIndecomposable :=
  ⟨e.symm.isIndecomposable, e.isIndecomposable⟩

/-- `lem:sec3-transport`, step `s3trmaximal`: pull back span maximality, Definition 2.2
of [CGSS], using the surjective isometry of spans. -/
theorem isMaximal (e : S.Iso T) (hT : T.IsMaximal) : S.IsMaximal := by
  intro x hx hnorm hprod
  let x' : span ℝ S.Φ := ⟨x, hx⟩
  apply (e.spanIsometry_mem_iff x').mp
  apply hT _ (e.spanIsometry x').property ((e.inner_spanIsometry x' x').trans hnorm)
  intro y hy
  obtain ⟨r, hr⟩ := e.toEquiv.surjective ⟨y, hy⟩
  have hry : (e.toEquiv r : W) = y := congrArg (fun r : T.Φ ↦ (r : W)) hr
  rw [← hry, ← e.spanIsometry_apply r, e.inner_spanIsometry]
  exact hprod r r.property

/-- `lem:sec3-transport`, step `s3trmaximal`: maximality within the root span is invariant. -/
theorem isMaximal_iff (e : S.Iso T) : S.IsMaximal ↔ T.IsMaximal :=
  ⟨e.symm.isMaximal, e.isMaximal⟩

/-- `lem:sec3-transport`: an isomorphism also supplies an isometric inclusion of spans. -/
noncomputable def toIsometricInclusion (e : S.Iso T) : S.IsometricInclusion T where
  toLinearIsometry := e.spanIsometry.toLinearIsometry
  map_mem r hr := (e.spanIsometry_mem_iff ⟨r, subset_span hr⟩).mpr hr

/-- `lem:sec3-transport`, step `s3trmarked`: membership in the defining set `Γa` is
preserved for any line systems and roots `a`, `b`, without assumptions on their product. -/
theorem mem_Γa_iff' (e : S.Iso T) (a b r : S.Φ) :
    (e.toEquiv r : W) ∈ T.Γa (e.toEquiv a) (e.toEquiv b) ↔ (r : V) ∈ S.Γa a b := by
  simp only [LineSystem.Γa, Set.mem_ofPred_eq, (e.toEquiv r).property, r.property,
    true_and, inner_sub_right, inner_neg_right, e.inner_map]

/-- `lem:sec3-transport`, step `s3trmarked`: the root bijection carries the defining
set `Γa` onto that for the image roots in arbitrary line systems. -/
theorem image_Γa' (e : S.Iso T) (a b : S.Φ) :
    (fun r : S.Φ ↦ (e.toEquiv r : W)) '' {r | (r : V) ∈ S.Γa a b} =
      T.Γa (e.toEquiv a) (e.toEquiv b) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (e.mem_Γa_iff' a b r).mpr hr
  · intro hy
    obtain ⟨r, hr⟩ := e.toEquiv.surjective ⟨y, hy.1⟩
    have hry : (e.toEquiv r : W) = y := congrArg (fun r : T.Φ ↦ (r : W)) hr
    exact ⟨r, (e.mem_Γa_iff' a b r).mp (hry.symm ▸ hy), hry⟩

/-- `lem:sec3-transport`, step `s3trmarked`: membership in the defining set `Δ` is
preserved for any line systems and roots `a`, `b`, without assumptions on their product. -/
theorem mem_Δ_iff' (e : S.Iso T) (a b r : S.Φ) :
    (e.toEquiv r : W) ∈ T.Δ (e.toEquiv a) (e.toEquiv b) ↔ (r : V) ∈ S.Δ a b := by
  simp only [LineSystem.Δ, Set.mem_ofPred_eq, (e.toEquiv r).property, r.property,
    true_and, inner_sub_right, inner_neg_right, e.inner_map]

/-- `lem:sec3-transport`, step `s3trmarked`: the root bijection carries the defining
set `Δ` onto that for the image roots in arbitrary line systems. -/
theorem image_Δ' (e : S.Iso T) (a b : S.Φ) :
    (fun r : S.Φ ↦ (e.toEquiv r : W)) '' {r | (r : V) ∈ S.Δ a b} =
      T.Δ (e.toEquiv a) (e.toEquiv b) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (e.mem_Δ_iff' a b r).mpr hr
  · intro hy
    obtain ⟨r, hr⟩ := e.toEquiv.surjective ⟨y, hy.1⟩
    have hry : (e.toEquiv r : W) = y := congrArg (fun r : T.Φ ↦ (r : W)) hr
    exact ⟨r, (e.mem_Δ_iff' a b r).mp (hry.symm ▸ hy), hry⟩

/-- `lem:sec3-transport`, step `s3trmarked`: orthogonality of any two roots is
preserved, in particular on the defining set `Γa` of an arbitrary line system. -/
theorem inner_eq_zero_iff (e : S.Iso T) (r s : S.Φ) :
    ⟪(e.toEquiv r : W), (e.toEquiv s : W)⟫ = 0 ↔ ⟪(r : V), (s : V)⟫ = 0 := by
  rw [e.inner_map]

/-- `lem:sec3-transport`, step `s3trmarked`: membership in `Γa` of Hypothesis 2.4 of
[CGSS] is preserved when the ordered star is mapped to the ordered star. -/
theorem mem_Γa_iff {H : Hyp24 V} {H' : Hyp24 W} (e : H.S.Iso H'.S)
    (ha : (e.toEquiv ⟨H.a, H.a_mem⟩ : W) = H'.a)
    (hb : (e.toEquiv ⟨H.b, H.b_mem⟩ : W) = H'.b) (r : H.S.Φ) :
    (e.toEquiv r : W) ∈ H'.Γa ↔ (r : V) ∈ H.Γa := by
  simpa only [LineSystem.Γa, Hyp24.Γa, Hyp24.c, ha, hb] using
    e.mem_Γa_iff' ⟨H.a, H.a_mem⟩ ⟨H.b, H.b_mem⟩ r

/-- `lem:sec3-transport`, step `s3trmarked`: the root bijection maps `Γa` onto `Γa`
for the image star, using the definitions of Hypothesis 2.4 of [CGSS]. -/
theorem image_Γa {H : Hyp24 V} {H' : Hyp24 W} (e : H.S.Iso H'.S)
    (ha : (e.toEquiv ⟨H.a, H.a_mem⟩ : W) = H'.a)
    (hb : (e.toEquiv ⟨H.b, H.b_mem⟩ : W) = H'.b) :
    (fun r : H.S.Φ ↦ (e.toEquiv r : W)) '' {r | (r : V) ∈ H.Γa} = H'.Γa := by
  simpa only [LineSystem.Γa, Hyp24.Γa, Hyp24.c, ha, hb] using
    e.image_Γa' ⟨H.a, H.a_mem⟩ ⟨H.b, H.b_mem⟩

/-- `lem:sec3-transport`, step `s3trmarked`: membership in `Δ` of Hypothesis 2.4 of
[CGSS] is preserved for the image ordered star. -/
theorem mem_Δ_iff {H : Hyp24 V} {H' : Hyp24 W} (e : H.S.Iso H'.S)
    (ha : (e.toEquiv ⟨H.a, H.a_mem⟩ : W) = H'.a)
    (hb : (e.toEquiv ⟨H.b, H.b_mem⟩ : W) = H'.b) (r : H.S.Φ) :
    (e.toEquiv r : W) ∈ H'.Δ ↔ (r : V) ∈ H.Δ := by
  simpa only [LineSystem.Δ, Hyp24.Δ, Hyp24.c, ha, hb] using
    e.mem_Δ_iff' ⟨H.a, H.a_mem⟩ ⟨H.b, H.b_mem⟩ r

/-- `lem:sec3-transport`, step `s3trmarked`: the root bijection maps `Δ` onto `Δ`
for the image star, using the definitions of Hypothesis 2.4 of [CGSS]. -/
theorem image_Δ {H : Hyp24 V} {H' : Hyp24 W} (e : H.S.Iso H'.S)
    (ha : (e.toEquiv ⟨H.a, H.a_mem⟩ : W) = H'.a)
    (hb : (e.toEquiv ⟨H.b, H.b_mem⟩ : W) = H'.b) :
    (fun r : H.S.Φ ↦ (e.toEquiv r : W)) '' {r | (r : V) ∈ H.Δ} = H'.Δ := by
  simpa only [LineSystem.Δ, Hyp24.Δ, Hyp24.c, ha, hb] using
    e.image_Δ' ⟨H.a, H.a_mem⟩ ⟨H.b, H.b_mem⟩

/-- `lem:sec3-transport`, step `s3trmarked`: the induced bijection of `Γa` is an
isomorphism of the orthogonality graphs of Hypothesis 2.4 of [CGSS]. -/
noncomputable def orthGraphIso {H : Hyp24 V} {H' : Hyp24 W} (e : H.S.Iso H'.S)
    (ha : (e.toEquiv ⟨H.a, H.a_mem⟩ : W) = H'.a)
    (hb : (e.toEquiv ⟨H.b, H.b_mem⟩ : W) = H'.b) : H.orthGraph ≃g H'.orthGraph where
  toEquiv := Equiv.ofBijective
    (fun r ↦ ⟨e.toEquiv ⟨r, H.Γa_subset_Φ r.property⟩,
      (e.mem_Γa_iff ha hb _).mpr r.property⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun r : H.S.Φ ↦ (r : V)) (e.toEquiv.injective
        (Subtype.ext (congrArg (fun r : H'.Γa ↦ (r : W)) h))), by
      intro y
      obtain ⟨r, hr⟩ := e.toEquiv.surjective ⟨y, H'.Γa_subset_Φ y.property⟩
      have hry : (e.toEquiv r : W) = y := congrArg (fun r : H'.S.Φ ↦ (r : W)) hr
      exact ⟨⟨r, (e.mem_Γa_iff ha hb r).mp (hry.symm ▸ y.property)⟩,
        Subtype.ext hry⟩⟩
  map_rel_iff' := by
    intro x y
    exact e.inner_eq_zero_iff ⟨x, H.Γa_subset_Φ x.property⟩ ⟨y, H.Γa_subset_Φ y.property⟩

/-- `lem:sec3-transport`, step `s3trmarked`: the graph isomorphism acts by the given
root bijection on `Γa` of Hypothesis 2.4 of [CGSS]. -/
theorem orthGraphIso_apply {H : Hyp24 V} {H' : Hyp24 W} (e : H.S.Iso H'.S)
    (ha : (e.toEquiv ⟨H.a, H.a_mem⟩ : W) = H'.a)
    (hb : (e.toEquiv ⟨H.b, H.b_mem⟩ : W) = H'.b) (r : H.Γa) :
    (e.orthGraphIso ha hb r : W) = e.toEquiv ⟨r, H.Γa_subset_Φ r.property⟩ := rfl

end Iso

/-- `lem:sec3-restrict`, step `s3reslines`: the same roots, considered inside their span. -/
def restrictSpan (S : LineSystem V) : LineSystem (span ℝ S.Φ) where
  Φ := Subtype.val ⁻¹' S.Φ
  finite := S.finite.preimage Subtype.val_injective.injOn
  inner_self r hr := S.inner_self r hr
  neg_mem r hr := S.neg_mem r hr
  inner_mem r hr s hs := S.inner_mem r hr s hs

/-- `lem:sec3-restrict`, step `s3resinner`: the identity on roots is an isomorphism. -/
def Iso.restrictSpan (S : LineSystem V) : S.restrictSpan.Iso S where
  toEquiv :=
    { toFun := fun r ↦ ⟨r.val.val, r.property⟩
      invFun := fun r ↦ ⟨⟨r, subset_span r.property⟩, r.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  inner_map _ _ := rfl

/-- `lem:sec3-restrict`, step `s3resspan`: the restricted root set spans its ambient space. -/
theorem restrictSpan_span_eq_top (S : LineSystem V) : span ℝ S.restrictSpan.Φ = ⊤ :=
  span_span_coe_preimage

/-- `lem:sec3-restrict`, step `s3resisometry`, used in steps `s335coords` and
`s335orthogonal` of Theorem 3.5 of [CGSS]: imaging the restricted roots is precisely imaging
the original roots considered as vectors of their span. -/
theorem restrictSpan_image_eq_iff (S : LineSystem V) (F : span ℝ S.Φ ≃ₗᵢ[ℝ] W)
    (R : Set W) : F '' S.restrictSpan.Φ = R ↔
      Set.range (fun r : S.Φ ↦ F ⟨r, subset_span r.property⟩) = R := by
  have h : F '' S.restrictSpan.Φ =
      Set.range (fun r : S.Φ ↦ F ⟨r, subset_span r.property⟩) := by
    ext y
    exact ⟨fun ⟨x, hx, hxy⟩ ↦ ⟨⟨x, hx⟩, hxy⟩,
      fun ⟨r, hry⟩ ↦ ⟨⟨r, subset_span r.property⟩, r.property, hry⟩⟩
  rw [h]

/-- `lem:sec3-restrict`, step `s3resisometry`: an isometry on the span imaging the
restricted roots onto `T.Φ` induces the original-root isomorphism used in Theorem 3.5 of [CGSS]. -/
noncomputable def Iso.ofRestrictSpanImage (S : LineSystem V) (T : LineSystem W)
    (F : span ℝ S.Φ ≃ₗᵢ[ℝ] W) (hF : F '' S.restrictSpan.Φ = T.Φ) : S.Iso T where
  toEquiv := Equiv.ofBijective
    (fun r ↦ ⟨F ⟨r, subset_span r.property⟩,
      hF ▸ Set.mem_image_of_mem F r.property⟩)
    ⟨by
      intro r s hrs
      apply Subtype.ext
      exact congrArg (fun x : span ℝ S.Φ ↦ (x : V))
        (F.injective (congrArg Subtype.val hrs)), by
      intro t
      have ht : (t : W) ∈ F '' S.restrictSpan.Φ := by rw [hF]; exact t.property
      obtain ⟨x, hx, hxt⟩ := ht
      exact ⟨⟨x, hx⟩, Subtype.ext hxt⟩⟩
  inner_map r s := F.inner_map_map ⟨r, subset_span r.property⟩ ⟨s, subset_span s.property⟩

/-- `lem:sec3-restrict`, step `s3resisometry`: the isomorphism used in Theorem 3.5 of
[CGSS] acts on each original root by the prescribed span isometry. -/
theorem ofRestrictSpanImage_apply (S : LineSystem V) (T : LineSystem W)
    (F : span ℝ S.Φ ≃ₗᵢ[ℝ] W) (hF : F '' S.restrictSpan.Φ = T.Φ) (r : S.Φ) :
    ((Iso.ofRestrictSpanImage S T F hF).toEquiv r : W) =
      F ⟨r, subset_span r.property⟩ := rfl

/-- `lem:sec3-restrict`, step `s3resisometry`: the final span isometry in the forward
proof of Theorem 3.5 of [CGSS] induces an isomorphism of the original systems. -/
noncomputable def Iso.ofSpanIsometry (S : LineSystem V) (T : LineSystem W)
    (F : span ℝ S.Φ ≃ₗᵢ[ℝ] span ℝ T.Φ)
    (hF : F '' S.restrictSpan.Φ = T.restrictSpan.Φ) : S.Iso T where
  toEquiv := (Iso.ofRestrictSpanImage S T.restrictSpan F hF).toEquiv.trans
    (Iso.restrictSpan T).toEquiv
  inner_map r s := (Iso.ofRestrictSpanImage S T.restrictSpan F hF).inner_map r s

/-- `lem:sec3-restrict`, step `s3resisometry`: the root bijection induced by the final
span isometry of Theorem 3.5 of [CGSS] agrees with that isometry on original roots. -/
theorem ofSpanIsometry_apply (S : LineSystem V) (T : LineSystem W)
    (F : span ℝ S.Φ ≃ₗᵢ[ℝ] span ℝ T.Φ)
    (hF : F '' S.restrictSpan.Φ = T.restrictSpan.Φ) (r : S.Φ) :
    ((Iso.ofSpanIsometry S T F hF).toEquiv r : W) =
      (F ⟨r, subset_span r.property⟩ : W) := rfl

end LineSystem
