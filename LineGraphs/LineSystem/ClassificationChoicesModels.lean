/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.ClassificationChoices
import LineGraphs.Computations.C2

/-!
# The perpendicular choices in the other two models

The rest of Lemma (independence of the perpendicular choices), `lem:sec3-choices` of
`blueprint/sec3-rootsystems.tex` (Section 3 of [CGSS], errata Gap 5): step `s3choiceSteiner`,
and the final `\qedstep`, which transfers the assertions proved for the default model in
`ClassificationChoices.lean` to models (i) and (iii) through the C3 isomorphisms
`E₈viaA₈.isoE₈` and `E₈viaSteiner.isoE₈`, and identifies the cuts `T₇`, `T₆` of Definition 3.3
with `E₇`, `E₆`.

A C3 isomorphism is a bijection of roots, not a map of the ambient space. It restricts to the
perpendicular cuts (`Iso.orthogonalTo`), and it transports isometries: in a finite-dimensional
space every automorphism of a line system is induced by an isometry of the space
(`Iso.exists_isometry`, through the span isometry of `lem:sec3-transport` and
`LinearIsometry.extend`; for model (i) the span is the zero-sum hyperplane of `ℝ⁹`).

## Main statements

* `E₈viaA₈.exists_isometry_of_ordered_stars`, `E₈viaSteiner.exists_isometry_of_ordered_stars`:
  any two ordered stars are carried to each other by an isometry of the ambient space; for model
  (iii), `E₈viaSteiner.exists_isometry_of_ordered_star` carries every ordered star to the star
  `(t₇Normal, t₆Normal)` of step `s3choiceSteiner`.
* `E₈viaA₈.exists_isometry_of_roots`, `E₈viaSteiner.exists_isometry_of_roots`: the same for
  roots; `E₈.exists_isometry_of_root` and `E₈viaSteiner.exists_isometry_of_root` carry every root
  to the fixed root `e₇Normal`, `t₇Normal`.
* `E₈viaA₈.nonempty_iso_E₇_orthogonalTo`, `E₈viaA₈.nonempty_iso_E₆_orthogonalTo` and their
  model (iii) analogues: the cuts perpendicular to any root or any star.
* `T₇_eq_orthogonalTo`, `T₆_eq_orthogonalTo`, `T₇.nonempty_iso_E₇`, `T₆.nonempty_iso_E₆`.
-/

open Submodule
open scoped RealInnerProductSpace

namespace LineSystem

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- A line system is determined by its set of roots, as used by `orthogonalTo_smul`
in step `s3choiceSteiner` of `lem:sec3-choices`. -/
@[ext] theorem ext {S T : LineSystem V} (h : S.Φ = T.Φ) : S = T := by
  cases S
  cases T
  subst h
  rfl

/-- The cut perpendicular to a nonzero multiple of `v` is the cut perpendicular to `v`
(step `s3choiceSteiner` of `lem:sec3-choices`). -/
theorem orthogonalTo_smul (S : LineSystem V) {c : ℝ} (hc : c ≠ 0) (v : V) :
    S.orthogonalTo (c • v) = S.orthogonalTo v := by
  apply LineSystem.ext
  ext x
  change x ∈ S.Φ ∧ ⟪x, c • v⟫ = 0 ↔ x ∈ S.Φ ∧ ⟪x, v⟫ = 0
  rw [real_inner_smul_right, mul_eq_zero, or_iff_right hc]

/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS]): an isomorphism `e`
restricts to the cuts perpendicular to `v` and to `w` when `⟪e x, w⟫ = ⟪x, v⟫` for every root
`x`; for instance when `v` is a root and `w` is its image. -/
def Iso.orthogonalTo {S : LineSystem V} {T : LineSystem W} (e : S.Iso T) {v : V} {w : W}
    (h : ∀ x : S.Φ, ⟪(e.toEquiv x : W), w⟫ = ⟪(x : V), v⟫) :
    (S.orthogonalTo v).Iso (T.orthogonalTo w) where
  toEquiv :=
    { toFun := fun x ↦ ⟨e.toEquiv ⟨x, x.2.1⟩, (e.toEquiv ⟨x, x.2.1⟩).2, (h _).trans x.2.2⟩
      invFun := fun y ↦ ⟨e.toEquiv.symm ⟨y, y.2.1⟩, (e.toEquiv.symm ⟨y, y.2.1⟩).2, by
        rw [← h, Equiv.apply_symm_apply]
        exact y.2.2⟩
      left_inv := fun x ↦ Subtype.ext (by simp)
      right_inv := fun y ↦ Subtype.ext (by simp) }
  inner_map x y := e.inner_map ⟨x, x.2.1⟩ ⟨y, y.2.1⟩

/-- `lem:sec3-transport` (Section 3 of [CGSS]), for the automorphisms of `lem:sec3-choices`: in a
finite-dimensional space, every automorphism of a line system is induced by a linear isometry of
the space that maps `Φ` onto itself. The span isometry is extended by `LinearIsometry.extend`. -/
theorem Iso.exists_isometry [FiniteDimensional ℝ V] {S : LineSystem V} (f : S.Iso S) :
    ∃ g ∈ S.isometryGroup, ∀ r : S.Φ, g r = f.toEquiv r := by
  let L : span ℝ S.Φ →ₗᵢ[ℝ] V := (span ℝ S.Φ).subtypeₗᵢ.comp f.spanIsometry.toLinearIsometry
  let g : V ≃ₗᵢ[ℝ] V := L.extend.toLinearIsometryEquiv rfl
  have hg (r : S.Φ) : g r = f.toEquiv r := by
    change L.extend ((⟨r, subset_span r.2⟩ : span ℝ S.Φ) : V) = _
    rw [LinearIsometry.extend_apply]
    exact f.spanIsometry_apply r
  refine ⟨g, fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩, hg⟩
  · obtain ⟨y, hy⟩ := f.toEquiv.surjective ⟨g x, hx⟩
    have hxy : g y = g x := by rw [hg y, hy]
    rw [← g.injective hxy]
    exact y.2
  · rw [hg ⟨x, hx⟩]
    exact (f.toEquiv ⟨x, hx⟩).2

/-- Step `s3choicepair` of `lem:sec3-choices` (Section 3 of [CGSS]), transported by an
isomorphism with `E₈`: any two ordered stars of `S` are carried to each other by a linear
isometry of the space that maps `Φ` onto itself. -/
theorem Iso.exists_isometry_of_ordered_stars [FiniteDimensional ℝ V] {S : LineSystem V}
    (e : S.Iso E₈) {r s r' s' : V} (hr : r ∈ S.Φ) (hs : s ∈ S.Φ) (hrs : ⟪r, s⟫ = -1)
    (hr' : r' ∈ S.Φ) (hs' : s' ∈ S.Φ) (hrs' : ⟪r', s'⟫ = -1) :
    ∃ g ∈ S.isometryGroup, g r = r' ∧ g s = s' := by
  obtain ⟨h₁, hh₁, h₁r, h₁s⟩ := E₈.exists_isometry_of_ordered_star (e.toEquiv ⟨r, hr⟩).2
    (e.toEquiv ⟨s, hs⟩).2 ((e.inner_map _ _).trans hrs)
  obtain ⟨h₂, hh₂, h₂r, h₂s⟩ := E₈.exists_isometry_of_ordered_star (e.toEquiv ⟨r', hr'⟩).2
    (e.toEquiv ⟨s', hs'⟩).2 ((e.inner_map _ _).trans hrs')
  let h := h₁.trans h₂.symm
  have hh : ∀ x, h x ∈ E₈.Φ ↔ x ∈ E₈.Φ := by
    intro x
    change h₂.symm (h₁ x) ∈ E₈.Φ ↔ x ∈ E₈.Φ
    rw [← hh₂ (h₂.symm (h₁ x)), h₂.apply_symm_apply, hh₁]
  let f : S.Iso S := e.trans ((Iso.ofLinearIsometryEquiv E₈ E₈ h hh).trans e.symm)
  obtain ⟨g, hg, hgf⟩ := f.exists_isometry
  have key {x y : V} (hx : x ∈ S.Φ) (hy : y ∈ S.Φ)
      (hxy : h (e.toEquiv ⟨x, hx⟩) = e.toEquiv ⟨y, hy⟩) : g x = y := by
    have h₀ : (Iso.ofLinearIsometryEquiv E₈ E₈ h hh).toEquiv (e.toEquiv ⟨x, hx⟩) =
        e.toEquiv ⟨y, hy⟩ := Subtype.ext hxy
    have hf : f.toEquiv ⟨x, hx⟩ = ⟨y, hy⟩ := by
      change e.toEquiv.symm ((Iso.ofLinearIsometryEquiv E₈ E₈ h hh).toEquiv
        (e.toEquiv ⟨x, hx⟩)) = _
      rw [h₀, Equiv.symm_apply_apply]
    rw [hgf ⟨x, hx⟩, hf]
  refine ⟨g, hg, key hr hr' ?_, key hs hs' ?_⟩
  · change h₂.symm (h₁ _) = _
    rw [h₁r, ← h₂r, h₂.symm_apply_apply]
  · change h₂.symm (h₁ _) = _
    rw [h₁s, ← h₂s, h₂.symm_apply_apply]

/-- Step `s3choiceroot` of `lem:sec3-choices` (Section 3 of [CGSS]), transported by an
isomorphism with `E₈`: every root has a partner of inner product `-1`. -/
theorem Iso.exists_inner_eq_neg_one {S : LineSystem V} (e : S.Iso E₈) {r : V} (hr : r ∈ S.Φ) :
    ∃ s ∈ S.Φ, ⟪r, s⟫ = -1 := by
  obtain ⟨t, ht, hrt⟩ := E₈.exists_inner_eq_neg_one (e.toEquiv ⟨r, hr⟩).2
  refine ⟨e.toEquiv.symm ⟨t, ht⟩, (e.toEquiv.symm ⟨t, ht⟩).2, ?_⟩
  have h := e.inner_map ⟨r, hr⟩ (e.toEquiv.symm ⟨t, ht⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm.trans hrt

/-- The second assertion of `lem:sec3-choices` (Section 3 of [CGSS]), transported by an
isomorphism with `E₈`: any root of `S` is carried to any other by a linear isometry of the space
that maps `Φ` onto itself, without a chosen partner. -/
theorem Iso.exists_isometry_of_roots [FiniteDimensional ℝ V] {S : LineSystem V} (e : S.Iso E₈)
    {r r' : V} (hr : r ∈ S.Φ) (hr' : r' ∈ S.Φ) : ∃ g ∈ S.isometryGroup, g r = r' := by
  obtain ⟨s, hs, hrs⟩ := e.exists_inner_eq_neg_one hr
  obtain ⟨s', hs', hrs'⟩ := e.exists_inner_eq_neg_one hr'
  obtain ⟨g, hg, hgr, -⟩ := e.exists_isometry_of_ordered_stars hr hs hrs hr' hs' hrs'
  exact ⟨g, hg, hgr⟩

-- Lemma "independence of the perpendicular choices"
/-- The second assertion of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for the
default model, by steps `s3choiceroot` and `s3choicepair`: every root of `E₈` is carried to
`e₇ - e₈` by a linear isometry of `ℝ⁸` that maps the roots onto themselves, without a chosen
partner. -/
theorem E₈.exists_isometry_of_root {r : EuclideanSpace ℝ (Fin 8)} (hr : r ∈ E₈.Φ) :
    ∃ g ∈ E₈.isometryGroup, g r = e₇Normal := by
  obtain ⟨s, hs, hrs⟩ := E₈.exists_inner_eq_neg_one hr
  obtain ⟨g, hg, hgr, -⟩ := E₈.exists_isometry_of_ordered_star hr hs hrs
  exact ⟨g, hg, hgr⟩

/-- Step `s3choiceSeven` of `lem:sec3-choices` (Section 3 of [CGSS]), transported by an
isomorphism with `E₈`: the cut of `S` perpendicular to any root is isomorphic to `E₇`. -/
theorem Iso.nonempty_iso_E₇_orthogonalTo {S : LineSystem V} (e : S.Iso E₈) {r : V}
    (hr : r ∈ S.Φ) : Nonempty ((S.orthogonalTo r).Iso E₇) := by
  obtain ⟨f⟩ := E₈.nonempty_iso_E₇_orthogonalTo (e.toEquiv ⟨r, hr⟩).2
  exact ⟨(e.orthogonalTo fun x ↦ e.inner_map x ⟨r, hr⟩).trans f⟩

/-- Step `s3choiceSix` of `lem:sec3-choices` (Section 3 of [CGSS]), transported by an
isomorphism with `E₈`: the cut of `S` perpendicular to any star `r, s, -r-s` is isomorphic to
`E₆`. -/
theorem Iso.nonempty_iso_E₆_orthogonalTo {S : LineSystem V} (e : S.Iso E₈) {r s : V}
    (hr : r ∈ S.Φ) (hs : s ∈ S.Φ) (hrs : ⟪r, s⟫ = -1) :
    Nonempty (((S.orthogonalTo r).orthogonalTo s).Iso E₆) := by
  obtain ⟨f⟩ := E₈.nonempty_iso_E₆_orthogonalTo (e.toEquiv ⟨r, hr⟩).2 (e.toEquiv ⟨s, hs⟩).2
    ((e.inner_map _ _).trans hrs)
  exact ⟨((e.orthogonalTo fun x ↦ e.inner_map x ⟨r, hr⟩).orthogonalTo
    fun x ↦ e.inner_map ⟨x, x.2.1⟩ ⟨s, hs⟩).trans f⟩

/-- Step `s3choiceSteiner` of `lem:sec3-choices` (Section 3 of [CGSS]): the root `√2 e₈` of
model (iii), at index 7 in `Fin 8`. -/
noncomputable def t₇Normal : EuclideanSpace ℝ (Fin 8) :=
  Real.sqrt 2 • EuclideanSpace.single 7 1

/-- Step `s3choiceSteiner` of `lem:sec3-choices` (Section 3 of [CGSS]): the root
`-(e₅ + e₆ + e₇ + e₈) / √2` of model (iii), from the block 5678, at indices 4 to 7 in `Fin 8`. -/
noncomputable def t₆Normal : EuclideanSpace ℝ (Fin 8) :=
  -(Real.sqrt 2)⁻¹ • (EuclideanSpace.single 4 1 + EuclideanSpace.single 5 1 +
    EuclideanSpace.single 6 1 + EuclideanSpace.single 7 1)

/-- The raw vector of `t₇Normal` is the axis root `2 e₈`
(step `s3choiceSteiner` of `lem:sec3-choices`). -/
theorem t₇Normal_eq_integerVector :
    t₇Normal = integerVector (Real.sqrt 2)⁻¹ (e₈SteinerRoot (.inl (7, false))) := by
  have h : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
    rw [inv_mul_eq_div, div_eq_iff (Real.sqrt_ne_zero'.mpr two_pos),
      Real.mul_self_sqrt zero_le_two]
  ext i
  fin_cases i <;> simp [t₇Normal, e₈SteinerRoot, axisRoot, rootSign, h]

/-- The raw vector of `t₆Normal` is the block root of 5678 with all four signs negative
(step `s3choiceSteiner` of `lem:sec3-choices`). -/
theorem t₆Normal_eq_integerVector :
    t₆Normal = integerVector (Real.sqrt 2)⁻¹
      (e₈SteinerRoot (.inr ⟨⟨{4, 5, 6, 7}, by decide⟩, fun _ ↦ true⟩)) := by
  ext i
  fin_cases i <;> simp [t₆Normal, e₈SteinerRoot, steinerRoot, rootSign]

/-- Step `s3choiceSteiner` of `lem:sec3-choices` (Section 3 of [CGSS]): `√2 e₈` is a root of
model (iii). -/
theorem t₇Normal_mem_E₈viaSteiner : t₇Normal ∈ E₈viaSteiner.Φ :=
  ⟨_, t₇Normal_eq_integerVector.symm⟩

/-- Step `s3choiceSteiner` of `lem:sec3-choices` (Section 3 of [CGSS]):
`-(e₅ + e₆ + e₇ + e₈) / √2` is a root of model (iii), by the block 5678. -/
theorem t₆Normal_mem_E₈viaSteiner : t₆Normal ∈ E₈viaSteiner.Φ :=
  ⟨_, t₆Normal_eq_integerVector.symm⟩

/-- Step `s3choiceSteiner` of `lem:sec3-choices` (Section 3 of [CGSS]): the two roots of
model (iii) have inner product `-1`, so they generate a star. -/
theorem inner_t₇Normal_t₆Normal : ⟪t₇Normal, t₆Normal⟫ = -1 := by
  rw [t₇Normal_eq_integerVector, t₆Normal_eq_integerVector, inner_integerVector]
  have hc := E₈viaSteiner.integerModel.hc
  change (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * ((2 : ℤ) : ℝ) = 1 at hc
  have hv : integerInner (e₈SteinerRoot (.inl (7, false)))
      (e₈SteinerRoot (.inr ⟨⟨{4, 5, 6, 7}, by decide⟩, fun _ ↦ true⟩)) = -2 := by
    decide +kernel
  rw [hv]
  push_cast at hc ⊢
  linarith

-- Lemma "independence of the perpendicular choices"
/-- Step `s3choiceSteiner` of `lem:sec3-choices` (Section 3 of [CGSS]): `T₇` is the cut of
model (iii) perpendicular to the root `√2 e₈`. -/
theorem T₇_eq_orthogonalTo : T₇ = E₈viaSteiner.orthogonalTo t₇Normal := by
  rw [t₇Normal, orthogonalTo_smul _ (Real.sqrt_ne_zero'.mpr two_pos)]
  rfl

-- Lemma "independence of the perpendicular choices"
/-- Step `s3choiceSteiner` of `lem:sec3-choices` (Section 3 of [CGSS]): `T₆` is the cut of
model (iii) perpendicular to the star of `√2 e₈` and `-(e₅ + e₆ + e₇ + e₈) / √2`. -/
theorem T₆_eq_orthogonalTo :
    T₆ = (E₈viaSteiner.orthogonalTo t₇Normal).orthogonalTo t₆Normal := by
  rw [← T₇_eq_orthogonalTo, t₆Normal, orthogonalTo_smul _ (neg_ne_zero.mpr (by positivity))]
  rfl

-- Lemma "independence of the perpendicular choices"
/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for model (i):
any two ordered stars of `E₈viaA₈` are carried to each other by a linear isometry of `ℝ⁹` that
maps the roots onto themselves, through the C3 isomorphism `E₈viaA₈.isoE₈`.
Model (i) has no fixed star in the blueprint, so the assertion is stated between any two
ordered stars, which gives it for any choice of fixed star. -/
theorem E₈viaA₈.exists_isometry_of_ordered_stars {r s r' s' : EuclideanSpace ℝ (Fin 9)}
    (hr : r ∈ E₈viaA₈.Φ) (hs : s ∈ E₈viaA₈.Φ) (hrs : ⟪r, s⟫ = -1) (hr' : r' ∈ E₈viaA₈.Φ)
    (hs' : s' ∈ E₈viaA₈.Φ) (hrs' : ⟪r', s'⟫ = -1) :
    ∃ g ∈ E₈viaA₈.isometryGroup, g r = r' ∧ g s = s' :=
  E₈viaA₈.isoE₈.exists_isometry_of_ordered_stars hr hs hrs hr' hs' hrs'

-- Lemma "independence of the perpendicular choices"
/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for model (i):
any root of `E₈viaA₈` is carried to any other by a linear isometry of `ℝ⁹` that maps the roots
onto themselves. -/
theorem E₈viaA₈.exists_isometry_of_roots {r r' : EuclideanSpace ℝ (Fin 9)}
    (hr : r ∈ E₈viaA₈.Φ) (hr' : r' ∈ E₈viaA₈.Φ) : ∃ g ∈ E₈viaA₈.isometryGroup, g r = r' :=
  E₈viaA₈.isoE₈.exists_isometry_of_roots hr hr'

-- Lemma "independence of the perpendicular choices"
/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for model (i):
the cut of `E₈viaA₈` perpendicular to any root is isomorphic to `E₇`. -/
theorem E₈viaA₈.nonempty_iso_E₇_orthogonalTo {r : EuclideanSpace ℝ (Fin 9)}
    (hr : r ∈ E₈viaA₈.Φ) : Nonempty ((E₈viaA₈.orthogonalTo r).Iso E₇) :=
  E₈viaA₈.isoE₈.nonempty_iso_E₇_orthogonalTo hr

-- Lemma "independence of the perpendicular choices"
/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for model (i):
the cut of `E₈viaA₈` perpendicular to any star `r, s, -r-s` is isomorphic to `E₆`. -/
theorem E₈viaA₈.nonempty_iso_E₆_orthogonalTo {r s : EuclideanSpace ℝ (Fin 9)}
    (hr : r ∈ E₈viaA₈.Φ) (hs : s ∈ E₈viaA₈.Φ) (hrs : ⟪r, s⟫ = -1) :
    Nonempty (((E₈viaA₈.orthogonalTo r).orthogonalTo s).Iso E₆) :=
  E₈viaA₈.isoE₈.nonempty_iso_E₆_orthogonalTo hr hs hrs

-- Lemma "independence of the perpendicular choices"
/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for model
(iii): any two ordered stars of `E₈viaSteiner` are carried to each other by a linear isometry of
`ℝ⁸` that maps the roots onto themselves, through the C3 isomorphism `E₈viaSteiner.isoE₈`. -/
theorem E₈viaSteiner.exists_isometry_of_ordered_stars {r s r' s' : EuclideanSpace ℝ (Fin 8)}
    (hr : r ∈ E₈viaSteiner.Φ) (hs : s ∈ E₈viaSteiner.Φ) (hrs : ⟪r, s⟫ = -1)
    (hr' : r' ∈ E₈viaSteiner.Φ) (hs' : s' ∈ E₈viaSteiner.Φ) (hrs' : ⟪r', s'⟫ = -1) :
    ∃ g ∈ E₈viaSteiner.isometryGroup, g r = r' ∧ g s = s' :=
  E₈viaSteiner.isoE₈.exists_isometry_of_ordered_stars hr hs hrs hr' hs' hrs'

-- Lemma "independence of the perpendicular choices"
/-- `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for model (iii) with the fixed star of
step `s3choiceSteiner`: every ordered star of `E₈viaSteiner` is carried to `(√2 e₈,
-(e₅ + e₆ + e₇ + e₈) / √2)` by a linear isometry of `ℝ⁸` that maps the roots onto themselves. -/
theorem E₈viaSteiner.exists_isometry_of_ordered_star {r s : EuclideanSpace ℝ (Fin 8)}
    (hr : r ∈ E₈viaSteiner.Φ) (hs : s ∈ E₈viaSteiner.Φ) (hrs : ⟪r, s⟫ = -1) :
    ∃ g ∈ E₈viaSteiner.isometryGroup, g r = t₇Normal ∧ g s = t₆Normal :=
  E₈viaSteiner.exists_isometry_of_ordered_stars hr hs hrs t₇Normal_mem_E₈viaSteiner
    t₆Normal_mem_E₈viaSteiner inner_t₇Normal_t₆Normal

-- Lemma "independence of the perpendicular choices"
/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for model
(iii): any root of `E₈viaSteiner` is carried to any other by a linear isometry of `ℝ⁸` that maps
the roots onto themselves. -/
theorem E₈viaSteiner.exists_isometry_of_roots {r r' : EuclideanSpace ℝ (Fin 8)}
    (hr : r ∈ E₈viaSteiner.Φ) (hr' : r' ∈ E₈viaSteiner.Φ) :
    ∃ g ∈ E₈viaSteiner.isometryGroup, g r = r' :=
  E₈viaSteiner.isoE₈.exists_isometry_of_roots hr hr'

-- Lemma "independence of the perpendicular choices"
/-- `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for model (iii) with the fixed root of
step `s3choiceSteiner`: every root of `E₈viaSteiner` is carried to `√2 e₈` by a linear isometry of
`ℝ⁸` that maps the roots onto themselves, without a chosen partner. -/
theorem E₈viaSteiner.exists_isometry_of_root {r : EuclideanSpace ℝ (Fin 8)}
    (hr : r ∈ E₈viaSteiner.Φ) : ∃ g ∈ E₈viaSteiner.isometryGroup, g r = t₇Normal :=
  E₈viaSteiner.exists_isometry_of_roots hr t₇Normal_mem_E₈viaSteiner

-- Lemma "independence of the perpendicular choices"
/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for model
(iii): the cut of `E₈viaSteiner` perpendicular to any root is isomorphic to `E₇`. -/
theorem E₈viaSteiner.nonempty_iso_E₇_orthogonalTo {r : EuclideanSpace ℝ (Fin 8)}
    (hr : r ∈ E₈viaSteiner.Φ) : Nonempty ((E₈viaSteiner.orthogonalTo r).Iso E₇) :=
  E₈viaSteiner.isoE₈.nonempty_iso_E₇_orthogonalTo hr

-- Lemma "independence of the perpendicular choices"
/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5), for model
(iii): the cut of `E₈viaSteiner` perpendicular to any star `r, s, -r-s` is isomorphic to `E₆`. -/
theorem E₈viaSteiner.nonempty_iso_E₆_orthogonalTo {r s : EuclideanSpace ℝ (Fin 8)}
    (hr : r ∈ E₈viaSteiner.Φ) (hs : s ∈ E₈viaSteiner.Φ) (hrs : ⟪r, s⟫ = -1) :
    Nonempty (((E₈viaSteiner.orthogonalTo r).orthogonalTo s).Iso E₆) :=
  E₈viaSteiner.isoE₈.nonempty_iso_E₆_orthogonalTo hr hs hrs

-- Lemma "independence of the perpendicular choices"
/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5): `T₇ ≅ E₇`. -/
theorem T₇.nonempty_iso_E₇ : Nonempty (T₇.Iso E₇) := by
  rw [T₇_eq_orthogonalTo]
  exact E₈viaSteiner.nonempty_iso_E₇_orthogonalTo t₇Normal_mem_E₈viaSteiner

-- Lemma "independence of the perpendicular choices"
/-- The final `\qedstep` of `lem:sec3-choices` (Section 3 of [CGSS], errata Gap 5): `T₆ ≅ E₆`. -/
theorem T₆.nonempty_iso_E₆ : Nonempty (T₆.Iso E₆) := by
  rw [T₆_eq_orthogonalTo]
  exact E₈viaSteiner.nonempty_iso_E₆_orthogonalTo t₇Normal_mem_E₈viaSteiner
    t₆Normal_mem_E₈viaSteiner inner_t₇Normal_t₆Normal

end LineSystem
