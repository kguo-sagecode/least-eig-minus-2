/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.ClassificationChoices
import LineGraphs.RootSetClassification.ESystems
import LineGraphs.RootSystems.LineSystem

/-!
# Section 3 of [CGSS]: the inclusions of equal rank, and the two coordinate forms of E₇, E₆

Two claims of Section 3 of [CGSS] that the library proves only in pieces.

The proof of Theorem 3.6 ([CGSS], J. Algebra 43 (1976), p. 312) begins: "Apart from
the obvious `A_8 ⊂ E_8`, `D_8 ⊂ E_8` the only further inclusion (up to isometry) between sets of
the same dimension is `A_7 ⊂ E_7`." The library has the three inclusions (computation C5,
`LineSystem.An.inclusionE₇`, `LineSystem.An.inclusionE₈`, `LineSystem.Dn.inclusionE₈`), the four
non-inclusions of C5 (`LineSystem.not_embeds_An_Dn`, `LineSystem.not_embeds_An_E₆`,
`LineSystem.not_embeds_Dn_E₆`, `LineSystem.not_embeds_Dn_E₇`), and the root counts used inside
`LineSystem.isMaximal_Dn`, `LineSystem.isMaximal_E₆`, `LineSystem.isMaximal_E₇` and
`LineSystem.isMaximal_E₈`. Here they are put together in one statement about the models of
`LineSystem.RootType`. An isometric inclusion is that of `LineSystem.IsometricInclusion`: a linear
isometry of the spans that sends roots to roots.

Remark 3.11 (p. 314) says that the root systems with roots of one length are "necessarily
one of those described by Theorem 3.10". The library classifies Root Systems by the coordinate
models of `RootSetClassification` (`RootSetModel.E₇`, `RootSetModel.E₆`, the roots of `E₈`
orthogonal to `u₇ + u₈`, and to `u₇ + u₈` and `u₆ - u₇`), while the line systems of Definition 3.3
(p. 311) are `LineSystem.E₇`, `LineSystem.E₆` (orthogonal to `e₇ - e₈`, and to `e₇ - e₈` and
`e₆ - e₇`). Both follow Definition 3.3, which takes any line, or any star, of `E₈`; they differ
in that choice. We prove that the first two are the roots of `LineSystem.E₈` orthogonal to their
normals, and conclude, since the normals are roots of `E₈` with inner product `-1`, that they are
isomorphic to `LineSystem.E₇` and `LineSystem.E₆`. The paper's indices `u₆, u₇, u₈` are
`unit 5`, `unit 6`, `unit 7` in Lean.

## Main statements

* `LineSystem.RootType.nonempty_isometricInclusion_iff`: for distinct types of equal rank, an
  isometric inclusion of the models exists exactly for `A₇ ⊂ E₇`, `A₈ ⊂ E₈` and `D₈ ⊂ E₈`
  (proof of Theorem 3.6, p. 312).
* `RootSetModel.image_val_E₇`, `RootSetModel.image_val_E₆`: the coordinate sets of Remark 3.11
  are the roots of `LineSystem.E₈` orthogonal to `u₇ + u₈`, and to `u₇ + u₈` and `u₆ - u₇`.
* `RootSetModel.nonempty_iso_E₇`, `RootSetModel.nonempty_iso_E₆`: as line systems, they are
  isomorphic to `LineSystem.E₇` and `LineSystem.E₆` (Remark 3.11, p. 314).
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- An isometric inclusion is injective on roots, so the source has at most as many roots as
the target (used for the proof of Theorem 3.6 of [CGSS], p. 312). -/
theorem IsometricInclusion.ncard_le {S : LineSystem V} {T : LineSystem W}
    (G : IsometricInclusion S T) : S.Φ.ncard ≤ T.Φ.ncard := by
  have : Finite T.Φ := T.finite.to_subtype
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective (fun r : S.Φ ↦ (⟨G.root r r.2, G.root_mem r r.2⟩ : T.Φ))
    fun r s h ↦ Subtype.ext (G.root_injective r.2 s.2 (congrArg (Subtype.val : T.Φ → W) h))

-- Theorem 3.6, proof
/-- The proof of Theorem 3.6 of [CGSS] (p. 312): "Apart from the obvious `A_8 ⊂ E_8`,
`D_8 ⊂ E_8` the only further inclusion (up to isometry) between sets of the same dimension is
`A_7 ⊂ E_7`." For distinct types `s`, `t` of equal rank, the model of `s` has an isometric
inclusion in the model of `t` exactly for `(A₇, E₇)`, `(A₈, E₈)` and `(D₈, E₈)`. The inclusions
and the non-inclusions `Aℓ ⊄ Dℓ`, `A₆ ⊄ E₆`, `D₆ ⊄ E₆`, `D₇ ⊄ E₇` are computation C5; the other
pairs have too many roots for their target (`Dℓ` against `Aℓ`, and the `E` types against `A` and
`D`). -/
theorem RootType.nonempty_isometricInclusion_iff {s t : RootType} (hst : s ≠ t)
    (hrank : s.rank = t.rank) :
    Nonempty (IsometricInclusion s.model t.model) ↔
      (s = RootType.A 7 (by norm_num) ∧ t = RootType.E₇) ∨
        (s = RootType.A 8 (by norm_num) ∧ t = RootType.E₈) ∨
        (s = RootType.D 8 (by norm_num) ∧ t = RootType.E₈) := by
  constructor
  · rintro ⟨G⟩
    have hc := G.ncard_le
    cases s with
    | A ℓ h =>
      cases t with
      | A ℓ' h' =>
        simp only [RootType.rank] at hrank
        subst hrank
        exact absurd rfl hst
      | D ℓ' h' =>
        simp only [RootType.rank] at hrank
        subst hrank
        exact ((not_embeds_An_Dn h').false G).elim
      | E₆ =>
        simp only [RootType.rank] at hrank
        subst hrank
        exact (not_embeds_An_E₆.false G).elim
      | E₇ =>
        simp only [RootType.rank] at hrank
        subst hrank
        exact Or.inl ⟨rfl, rfl⟩
      | E₈ =>
        simp only [RootType.rank] at hrank
        subst hrank
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | D ℓ h =>
      cases t with
      | A ℓ' h' =>
        simp only [RootType.rank] at hrank
        subst hrank
        rw [RootType.ncard_model_A, RootType.ncard_model_D] at hc
        obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
        rw [choose_two_mul_four] at hc
        nlinarith
      | D ℓ' h' =>
        simp only [RootType.rank] at hrank
        subst hrank
        exact absurd rfl hst
      | E₆ =>
        simp only [RootType.rank] at hrank
        subst hrank
        exact (not_embeds_Dn_E₆.false G).elim
      | E₇ =>
        simp only [RootType.rank] at hrank
        subst hrank
        exact (not_embeds_Dn_E₇.false G).elim
      | E₈ =>
        simp only [RootType.rank] at hrank
        subst hrank
        exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | E₆ =>
      cases t <;> simp only [RootType.rank] at hrank <;> subst_vars <;>
        simp only [RootType.ncard_model_A, RootType.ncard_model_D, RootType.ncard_model_E₆,
          RootType.ncard_model_E₇, RootType.ncard_model_E₈] at hc <;>
        first | exact absurd rfl hst | omega | exact absurd hc (by decide)
    | E₇ =>
      cases t <;> simp only [RootType.rank] at hrank <;> subst_vars <;>
        simp only [RootType.ncard_model_A, RootType.ncard_model_D, RootType.ncard_model_E₆,
          RootType.ncard_model_E₇, RootType.ncard_model_E₈] at hc <;>
        first | exact absurd rfl hst | omega | exact absurd hc (by decide)
    | E₈ =>
      cases t <;> simp only [RootType.rank] at hrank <;> subst_vars <;>
        simp only [RootType.ncard_model_A, RootType.ncard_model_D, RootType.ncard_model_E₆,
          RootType.ncard_model_E₇, RootType.ncard_model_E₈] at hc <;>
        first | exact absurd rfl hst | omega | exact absurd hc (by decide)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨An.inclusionE₇⟩
    · exact ⟨An.inclusionE₈⟩
    · exact ⟨Dn.inclusionE₈⟩

/-- Every coordinate sum `e_i + e_j` is a root of the default `E₈` (Definition 3.2 of [CGSS]). -/
theorem add_single_mem_E₈ (i j : Fin 8) (hij : i < j) :
    EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j 1 ∈ E₈.Φ := by
  refine ⟨Sum.inl (⟨(i, j), hij⟩, false, false), ?_⟩
  ext k
  simp [integerVector, e₈Root, dnRoot, pairVector, rootSign, Pi.single_apply,
    PiLp.single_apply]

end LineSystem

namespace RootSetModel

open LineSystem

/-- The E₇ space of Remark 3.11 of [CGSS] is the orthogonal complement of `u₇ + u₈`. -/
theorem mem_e₇Space_iff_inner (x : EuclideanSpace ℝ (Fin 8)) :
    x ∈ e₇Space ↔ ⟪x, unit 6 + unit 7⟫ = 0 := by
  change ⟪unit 6 + unit 7, x⟫ = 0 ↔ _
  rw [real_inner_comm x (unit 6 + unit 7)]

/-- The E₆ space of Remark 3.11 of [CGSS] is the orthogonal complement of `u₇ + u₈` and
`u₆ - u₇`. -/
theorem mem_e₆Space_iff_inner (x : EuclideanSpace ℝ (Fin 8)) :
    x ∈ e₆Space ↔ ⟪x, unit 6 + unit 7⟫ = 0 ∧ ⟪x, unit 5 - unit 6⟫ = 0 := by
  change ⟪unit 6 + unit 7, x⟫ = 0 ∧ ⟪unit 5 - unit 6, x⟫ = 0 ↔ _
  rw [real_inner_comm x (unit 6 + unit 7), real_inner_comm x (unit 5 - unit 6)]

-- Remark 3.11, Definition 3.3
/-- The coordinate set `E₇` of Remark 3.11 of [CGSS] (p. 314), read in `ℝ⁸`, is the set of
roots of `LineSystem.E₈` orthogonal to `u₇ + u₈` (Definition 3.3, p. 311, with the normal
`u₇ + u₈` in place of `e₇ - e₈`). -/
theorem image_val_E₇ :
    Subtype.val '' E₇ = (LineSystem.E₈.orthogonalTo (unit 6 + unit 7)).Φ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, (mem_e₇Space_iff_inner _).1 y.2⟩
  · rintro ⟨hx, h0⟩
    exact ⟨⟨x, (mem_e₇Space_iff_inner x).2 h0⟩, hx, rfl⟩

-- Remark 3.11, Definition 3.3
/-- The coordinate set `E₆` of Remark 3.11 of [CGSS] (p. 314), read in `ℝ⁸`, is the set of
roots of `LineSystem.E₈` orthogonal to `u₇ + u₈` and `u₆ - u₇` (Definition 3.3, p. 311, with
these normals in place of `e₇ - e₈` and `e₆ - e₇`). -/
theorem image_val_E₆ :
    Subtype.val '' E₆ =
      ((LineSystem.E₈.orthogonalTo (unit 6 + unit 7)).orthogonalTo (unit 5 - unit 6)).Φ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h₁, h₂⟩ := (mem_e₆Space_iff_inner _).1 y.2
    exact ⟨⟨hy, h₁⟩, h₂⟩
  · rintro ⟨⟨hx, h₁⟩, h₂⟩
    exact ⟨⟨x, (mem_e₆Space_iff_inner x).2 ⟨h₁, h₂⟩⟩, hx, rfl⟩

/-- The roots of the coordinate set `E₇` of Remark 3.11 of [CGSS] have squared norm 2. -/
theorem inner_self_E₇ : ∀ r ∈ E₇, ⟪r, r⟫ = 2 :=
  fun r hr ↦ LineSystem.E₈.inner_self (r : EuclideanSpace ℝ (Fin 8)) hr

/-- The roots of the coordinate set `E₆` of Remark 3.11 of [CGSS] have squared norm 2. -/
theorem inner_self_E₆ : ∀ r ∈ E₆, ⟪r, r⟫ = 2 :=
  fun r hr ↦ LineSystem.E₈.inner_self (r : EuclideanSpace ℝ (Fin 8)) hr

/-- The coordinate set `E₇` of Remark 3.11 of [CGSS], as a line system in its space, is
isomorphic to the roots of `LineSystem.E₈` orthogonal to `u₇ + u₈`, by the inclusion of
`e₇Space` in `ℝ⁸`. -/
noncomputable def isoE₇OrthogonalTo :
    (E₇_isRootSet.toLineSystem inner_self_E₇).Iso
      (LineSystem.E₈.orthogonalTo (unit 6 + unit 7)) where
  toEquiv := (Equiv.Set.image Subtype.val E₇ Subtype.val_injective).trans
    (Equiv.subtypeEquivRight fun x ↦ Set.ext_iff.mp image_val_E₇ x)
  inner_map _ _ := rfl

/-- The coordinate set `E₆` of Remark 3.11 of [CGSS], as a line system in its space, is
isomorphic to the roots of `LineSystem.E₈` orthogonal to `u₇ + u₈` and `u₆ - u₇`, by the
inclusion of `e₆Space` in `ℝ⁸`. -/
noncomputable def isoE₆OrthogonalTo :
    (E₆_isRootSet.toLineSystem inner_self_E₆).Iso
      ((LineSystem.E₈.orthogonalTo (unit 6 + unit 7)).orthogonalTo (unit 5 - unit 6)) where
  toEquiv := (Equiv.Set.image Subtype.val E₆ Subtype.val_injective).trans
    (Equiv.subtypeEquivRight fun x ↦ Set.ext_iff.mp image_val_E₆ x)
  inner_map _ _ := rfl

/-- The normal `u₇ + u₈` of the E₇ space of Remark 3.11 of [CGSS] is a root of `E₈`. -/
theorem unit_add_unit_mem_E₈ : (unit 6 + unit 7 : EuclideanSpace ℝ (Fin 8)) ∈ LineSystem.E₈.Φ :=
  add_single_mem_E₈ 6 7 (by decide)

/-- The normal `u₆ - u₇` of the E₆ space of Remark 3.11 of [CGSS] is a root of `E₈`. -/
theorem unit_sub_unit_mem_E₈ : (unit 5 - unit 6 : EuclideanSpace ℝ (Fin 8)) ∈ LineSystem.E₈.Φ :=
  sub_single_mem_E₈ 5 6 (by decide)

/-- The two normals of the E₆ space of Remark 3.11 of [CGSS] span a star: their inner product
is `-1`. -/
theorem inner_unit_add_unit_unit_sub_unit :
    ⟪(unit 6 + unit 7 : EuclideanSpace ℝ (Fin 8)), unit 5 - unit 6⟫ = -1 := by
  simp [unit, inner_add_left, inner_sub_right, EuclideanSpace.inner_single_left]

-- Remark 3.11
/-- Remark 3.11 of [CGSS] (p. 314) reaches the line systems of Definition 3.3: the
coordinate set `E₇` of Remark 3.11, as a line system in its space, is isomorphic to
`LineSystem.E₇`. The two differ by the choice of the normal, a root of `E₈` in both cases
(`LineSystem.E₈.nonempty_iso_E₇_orthogonalTo`). -/
theorem nonempty_iso_E₇ : Nonempty ((E₇_isRootSet.toLineSystem inner_self_E₇).Iso LineSystem.E₇) :=
  (LineSystem.E₈.nonempty_iso_E₇_orthogonalTo unit_add_unit_mem_E₈).map
    isoE₇OrthogonalTo.trans

-- Remark 3.11
/-- Remark 3.11 of [CGSS] (p. 314) reaches the line systems of Definition 3.3: the
coordinate set `E₆` of Remark 3.11, as a line system in its space, is isomorphic to
`LineSystem.E₆`. Each pair of normals is a pair of roots of `E₈` with inner product `-1`, so
it generates a star (`LineSystem.E₈.nonempty_iso_E₆_orthogonalTo`). -/
theorem nonempty_iso_E₆ : Nonempty ((E₆_isRootSet.toLineSystem inner_self_E₆).Iso LineSystem.E₆) :=
  (LineSystem.E₈.nonempty_iso_E₆_orthogonalTo unit_add_unit_mem_E₈ unit_sub_unit_mem_E₈
    inner_unit_add_unit_unit_sub_unit).map isoE₆OrthogonalTo.trans

end RootSetModel
