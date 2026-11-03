/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Models

/-!
# The integer realizations and computation C2

Lemma (integer realizations), `lem:sec3-integer`, and Computation C2, `comp:C2`, of
`blueprint/sec3-rootsystems.tex` (Section 3 of [CGSS]). The models of Definitions 3.1 and 3.2
are built in `LineSystem/Models.lean` from integer roots; this file bundles their integer
presentations and their line counts, and adds the two cuts `T₇`, `T₆` of model (iii) that the
blueprint's Definition 3.3 names for the printed counting argument of Lemma 3.4.

## Main definitions

* `LineSystem.T₇`, `LineSystem.T₆`: the cuts `E₈⁽ⁱⁱⁱ⁾ ∩ e₈^⊥` and `T₇ ∩ (e₅ + e₆ + e₇ + e₈)^⊥`,
  with their integer presentations `T₇.integerModel`, `T₆.integerModel`.
* `Computations.C2.IsIntegerPresentation S v q c`: the clauses of `lem:sec3-integer` for one
  model.

## Main statements

* `Computations.C2.model_presentations`: `lem:sec3-integer`.
* `Computations.C2.line_counts`: `comp:C2`.
-/

open scoped RealInnerProductSpace

namespace LineSystem

/-- Step `s3inttwounique` of `lem:sec3-integer` (Section 3 of [CGSS]): every sign vector of even
parity is a half root of model (ii); its first seven signs determine the last. -/
theorem exists_halfRoot_eq {ε : Fin 8 → ℤ} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hprod : ∏ i, ε i = 1) : ∃ s, halfRoot s = ε := by
  have hs (i : Fin 7) : rootSign (decide (ε i.castSucc = -1)) = ε i.castSucc := by
    rcases hε i.castSucc with h | h <;> simp [rootSign, h]
  refine ⟨fun i ↦ decide (ε i.castSucc = -1), funext fun i ↦ ?_⟩
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [halfRoot, Fin.lastCases_last, rootSign_foldl_xor, hs]
    rw [Fin.prod_univ_castSucc] at hprod
    rcases hε (Fin.last 7) with h | h <;> rw [h] at hprod ⊢ <;> linarith
  · simp only [halfRoot, Fin.lastCases_castSucc, hs]

/-- Definition 3.2 (ii) and step `s3inttwounique` of `lem:sec3-integer` (Section 3 of [CGSS]):
the half roots of model (ii) are exactly the sign vectors `ε` with `∏ ε(i) = 1`. -/
theorem range_halfRoot :
    Set.range halfRoot = {ε : Fin 8 → ℤ | (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∏ i, ε i = 1} := by
  ext ε
  exact ⟨fun ⟨s, hs⟩ ↦ hs ▸ ⟨halfRoot_mem s, prod_halfRoot s⟩,
    fun ⟨h₁, h₂⟩ ↦ exists_halfRoot_eq h₁ h₂⟩

/-- Step `s3intblocks` of `lem:sec3-integer` (Section 3 of [CGSS]): two distinct blocks of
`S(3,4,8)` meet in 0 or 2 points. -/
theorem steinerBlock_inter_card_of_ne : ∀ b c : SteinerBlock, b ≠ c →
    (b.val ∩ c.val).card = 0 ∨ (b.val ∩ c.val).card = 2 := by
  decide +kernel

/-- Orthogonality to a coordinate vector is the vanishing of that integer coordinate
(`def:3.3`, for steps `s3countTseven` and `s3countTsix` of `comp:C2`). -/
theorem integerVector_inner_single_eq_zero {n : ℕ} (v : Fin n → ℤ) {c : ℝ} (hc : c ≠ 0)
    (i : Fin n) : ⟪integerVector c v, EuclideanSpace.single i 1⟫ = 0 ↔ v i = 0 := by
  rw [EuclideanSpace.inner_single_right]
  simp [hc]

/-- Orthogonality to `e₅ + e₆ + e₇ + e₈` (indices 4 to 7 in `Fin 8`) is the vanishing of the sum
of those four integer coordinates (`def:3.3`, for step `s3countTsix` of `comp:C2`). -/
theorem integerVector_inner_e₅₆₇₈_eq_zero (v : Fin 8 → ℤ) {c : ℝ} (hc : c ≠ 0) :
    ⟪integerVector c v, EuclideanSpace.single 4 1 + EuclideanSpace.single 5 1 +
      EuclideanSpace.single 6 1 + EuclideanSpace.single 7 1⟫ = 0 ↔
      v 4 + v 5 + v 6 + v 7 = 0 := by
  simp only [inner_add_right, EuclideanSpace.inner_single_right, integerVector_apply,
    conj_trivial, one_mul, ← mul_add]
  rw [mul_eq_zero, or_iff_right hc]
  norm_cast

-- Definition 3.3
/-- The cut `T₇ = E₈⁽ⁱⁱⁱ⁾ ∩ e₈^⊥` of the Steiner model, which Definition 3.3 of the blueprint
(`def:3.3` of `blueprint/sec3-rootsystems.tex`) names for the counting argument of Lemma 3.4 of
[CGSS]; the paper's `e₈` is `EuclideanSpace.single 7 1`. -/
noncomputable def T₇ : LineSystem (EuclideanSpace ℝ (Fin 8)) :=
  E₈viaSteiner.orthogonalTo (EuclideanSpace.single 7 1)

-- Definition 3.3
/-- The cut `T₆ = T₇ ∩ (e₅ + e₆ + e₇ + e₈)^⊥` of the Steiner model, which Definition 3.3 of the
blueprint (`def:3.3`) names with `T₇`; the paper's `e₅, …, e₈` are indices 4 to 7 in `Fin 8`. -/
noncomputable def T₆ : LineSystem (EuclideanSpace ℝ (Fin 8)) :=
  T₇.orthogonalTo (EuclideanSpace.single 4 1 + EuclideanSpace.single 5 1 +
    EuclideanSpace.single 6 1 + EuclideanSpace.single 7 1)

/-- Integer indices of the roots of `T₇`: the Steiner roots with last coordinate zero
(`def:3.3`, for step `s3countTseven` of `comp:C2`). -/
abbrev T₇.Index := {a : E₈viaSteiner.Index // E₈viaSteiner.root a 7 = 0}

/-- Integer indices of the roots of `T₆`: those of `T₇` whose coordinates 4 to 7 sum to zero
(`def:3.3`, for step `s3countTsix` of `comp:C2`). -/
abbrev T₆.Index := {a : E₈viaSteiner.Index // E₈viaSteiner.root a 7 = 0 ∧
  E₈viaSteiner.root a 4 + E₈viaSteiner.root a 5 + E₈viaSteiner.root a 6 +
    E₈viaSteiner.root a 7 = 0}

/-- The Steiner normalization `1 / √2` is nonzero. -/
private theorem inv_sqrt_two_ne_zero : (Real.sqrt 2)⁻¹ ≠ 0 := by positivity

/-- The filtered integer indices give precisely the roots of `T₇`
(`def:3.3`, for step `s3countTseven` of `comp:C2`). -/
theorem T₇_roots_eq_range :
    T₇.Φ = Set.range (fun a : T₇.Index ↦ integerVector (Real.sqrt 2)⁻¹ (e₈SteinerRoot a.val)) := by
  ext v
  constructor
  · rintro ⟨⟨a, rfl⟩, ha⟩
    exact ⟨⟨a, (integerVector_inner_single_eq_zero _ inv_sqrt_two_ne_zero 7).mp ha⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.val, rfl⟩,
      (integerVector_inner_single_eq_zero _ inv_sqrt_two_ne_zero 7).mpr a.property⟩

/-- The filtered integer indices give precisely the roots of `T₆`
(`def:3.3`, for step `s3countTsix` of `comp:C2`). -/
theorem T₆_roots_eq_range :
    T₆.Φ = Set.range (fun a : T₆.Index ↦ integerVector (Real.sqrt 2)⁻¹ (e₈SteinerRoot a.val)) := by
  ext v
  constructor
  · rintro ⟨⟨⟨a, rfl⟩, ha⟩, hb⟩
    exact ⟨⟨a, (integerVector_inner_single_eq_zero _ inv_sqrt_two_ne_zero 7).mp ha,
      (integerVector_inner_e₅₆₇₈_eq_zero _ inv_sqrt_two_ne_zero).mp hb⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨⟨a.val, rfl⟩,
      (integerVector_inner_single_eq_zero _ inv_sqrt_two_ne_zero 7).mpr a.property.1⟩,
      (integerVector_inner_e₅₆₇₈_eq_zero _ inv_sqrt_two_ne_zero).mpr a.property.2⟩

/-- Integer presentation of the cut `T₇` of the Steiner model
(`def:3.3`, for step `s3countTseven` of `comp:C2`). -/
noncomputable instance T₇.integerModel : IntegerModel T₇ where
  ι := T₇.Index
  fintype := inferInstance
  v := fun a ↦ e₈SteinerRoot a.val
  q := 2
  c := (Real.sqrt 2)⁻¹
  hc := E₈viaSteiner.integerModel.hc
  inj := e₈SteinerRoot_injective.comp Subtype.val_injective
  Φ_eq := T₇_roots_eq_range

/-- Integer presentation of the cut `T₆` of the Steiner model
(`def:3.3`, for step `s3countTsix` of `comp:C2`). -/
noncomputable instance T₆.integerModel : IntegerModel T₆ where
  ι := T₆.Index
  fintype := inferInstance
  v := fun a ↦ e₈SteinerRoot a.val
  q := 2
  c := (Real.sqrt 2)⁻¹
  hc := E₈viaSteiner.integerModel.hc
  inj := e₈SteinerRoot_injective.comp Subtype.val_injective
  Φ_eq := T₆_roots_eq_range

/-- Step `s3countTseven` of `comp:C2` (Section 3 of [CGSS]): the cut `T₇` has `14 + 7 · 16`
oriented roots, the seven axes and the seven blocks avoiding the last point. -/
theorem card_T₇Index : Fintype.card T₇.Index = 126 := by decide +kernel

/-- Step `s3countTsix` of `comp:C2` (Section 3 of [CGSS]): the cut `T₆` has `8 + 16 + 6 · 8`
oriented roots. -/
theorem card_T₆Index : Fintype.card T₆.Index = 72 := by decide +kernel

-- Computation C2
/-- Step `s3countTseven` of `comp:C2` (Section 3 of [CGSS]): `T₇` has `7 + 8 · 7 = 63` lines. -/
theorem numLines_T₇ : T₇.numLines = 63 := by
  rw [T₇.integerModel.numLines_eq,
    Fintype.card_congr (show T₇.integerModel.ι ≃ T₇.Index from Equiv.refl _), card_T₇Index]

-- Computation C2
/-- Step `s3countTsix` of `comp:C2` (Section 3 of [CGSS]): `T₆` has `4 + 8 + 4 · 6 = 36`
lines. -/
theorem numLines_T₆ : T₆.numLines = 36 := by
  rw [T₆.integerModel.numLines_eq,
    Fintype.card_congr (show T₆.integerModel.ι ≃ T₆.Index from Equiv.refl _), card_T₆Index]

end LineSystem

namespace Computations.C2

open LineSystem

/-- The clauses of `lem:sec3-integer` (Section 3 of [CGSS]) for one model `S` with raw vectors
`v`, written `r = c v` with `c² q = 1`: the roots are the vectors `c v a`, the list `v` has no
repetitions and is closed under negation, every raw squared norm is `2q`, and every raw product
lies in `q {-2, -1, 0, 1, 2}`. -/
structure IsIntegerPresentation {n : ℕ} {ι : Type*} (S : LineSystem (EuclideanSpace ℝ (Fin n)))
    (v : ι → Fin n → ℤ) (q : ℤ) (c : ℝ) : Prop where
  /-- The roots are the vectors `c v a`. -/
  Φ_eq : S.Φ = Set.range (fun a ↦ integerVector c (v a))
  /-- The normalization `c² q = 1`. -/
  hc : c * c * (q : ℝ) = 1
  /-- The list of raw vectors has no repetitions. -/
  injective : Function.Injective v
  /-- The list of raw vectors is closed under negation. -/
  neg_mem : ∀ a, ∃ b, v b = -v a
  /-- Every raw squared norm is `2q`. -/
  inner_self : ∀ a, integerInner (v a) (v a) = 2 * q
  /-- Every raw product lies in `q {-2, -1, 0, 1, 2}`. -/
  inner_mem : ∀ a b, integerInner (v a) (v b) ∈ ({-2 * q, -q, 0, q, 2 * q} : Set ℤ)

-- Lemma "integer realizations"
/-- Lemma (integer realizations), `lem:sec3-integer` of Section 3 of [CGSS]: the coordinate sets of
Definitions 3.1 and 3.2 are line systems with the integral presentations of the table, in the
parameter ranges of Definition 3.1 (`1 ≤ ℓ` for `Aₗ`, `4 ≤ ℓ` for `Dₗ`; the Lean facts hold for
every `ℓ`).

* `Aₗ`: `q = 1`, `c = 1`, raw vectors `eᵢ - eⱼ` for ordered pairs `i ≠ j`.
* `Dₗ`: `q = 1`, `c = 1`, raw vectors `s eᵢ + t eⱼ` for `i < j` and signs `s`, `t`.
* `E₈` (i): `q = 9`, `c = 1/3`, raw vectors `3 (eᵢ - eⱼ)` and `±(𝟏 - 3 · 𝟏_T)` for 3-sets `T`.
* `E₈` (ii): `q = 4`, `c = 1/2`, raw vectors `2 (s eᵢ + t eⱼ)` and the sign vectors `ε` with
  `∏ ε(i) = 1` (seven free signs, `LineSystem.halfRoot`).
* `E₈` (iii): `q = 2`, `c = 1/√2`, raw vectors `±2 eᵢ` and `ε 𝟏_B` for blocks `B` and all
  sign choices on `B`.

Every presentation has no repetitions, raw squared norm `2q` and raw products in
`q {-2, -1, 0, 1, 2}` (`IsIntegerPresentation`). The 14 blocks of `S(3,4,8)` have four points,
each triple of points lies in exactly one block, and distinct blocks meet in 0 or 2 points. -/
theorem model_presentations :
    (∀ ℓ, 1 ≤ ℓ → IsIntegerPresentation (An ℓ) An.root 1 1 ∧
      ∀ p : An.Index ℓ, An.root p = Pi.single p.val.1 1 - Pi.single p.val.2 1) ∧
    (∀ ℓ, 4 ≤ ℓ → IsIntegerPresentation (Dn ℓ) Dn.root 1 1 ∧
      ∀ p : Dn.Index ℓ,
        Dn.root p = Pi.single p.1.val.1 (rootSign p.2.1) + Pi.single p.1.val.2 (rootSign p.2.2)) ∧
    (IsIntegerPresentation E₈viaA₈ E₈viaA₈.root 9 (1 / 3) ∧
      (∀ p, E₈viaA₈.root (.inl p) = (3 : ℤ) • An.root p) ∧
      ∀ t b i, E₈viaA₈.root (.inr (t, b)) i =
        rootSign b * (1 - 3 * if i ∈ t.val then 1 else 0)) ∧
    (IsIntegerPresentation E₈viaD₈ E₈viaD₈.root 4 (1 / 2) ∧
      (∀ p, E₈viaD₈.root (.inl p) = (2 : ℤ) • Dn.root p) ∧
      Set.range (fun s ↦ E₈viaD₈.root (.inr s)) =
        {ε : Fin 8 → ℤ | (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∏ i, ε i = 1}) ∧
    (IsIntegerPresentation E₈viaSteiner E₈viaSteiner.root 2 (Real.sqrt 2)⁻¹ ∧
      (∀ p, E₈viaSteiner.root (.inl p) = Pi.single p.1 (2 * rootSign p.2)) ∧
      ∀ p i, E₈viaSteiner.root (.inr p) i =
        if h : i ∈ p.1.val then rootSign (p.2 ⟨i, h⟩) else 0) ∧
    steiner348.card = 14 ∧ (∀ b : SteinerBlock, b.val.card = 4) ∧
    (∀ t : {t : Finset (Fin 8) // t.card = 3}, ∃! b : SteinerBlock, t.val ⊆ b.val) ∧
    ∀ b c : SteinerBlock, b ≠ c → (b.val ∩ c.val).card = 0 ∨ (b.val ∩ c.val).card = 2 := by
  refine ⟨fun ℓ _ ↦ ⟨⟨rfl, by norm_num, anRoot_injective, anRoot_neg, integerInner_anRoot_self,
      integerInner_anRoot_mem⟩, fun p ↦ ?_⟩,
    fun ℓ _ ↦ ⟨⟨rfl, by norm_num, dnRoot_injective, dnRoot_neg, integerInner_dnRoot_self,
      integerInner_dnRoot_mem⟩, fun _ ↦ rfl⟩,
    ⟨⟨rfl, by norm_num, e₈ARoot_injective, e₈ARoot_neg, integerInner_e₈ARoot_self,
      integerInner_e₈ARoot_mem⟩, fun _ ↦ rfl, fun t b i ↦ ?_⟩,
    ⟨⟨rfl, by norm_num, e₈Root_injective, e₈Root_neg, integerInner_e₈Root_self,
      integerInner_e₈Root_mem⟩, fun _ ↦ rfl, range_halfRoot⟩,
    ⟨⟨rfl, E₈viaSteiner.integerModel.hc, e₈SteinerRoot_injective, e₈SteinerRoot_neg,
      integerInner_e₈SteinerRoot_self, integerInner_e₈SteinerRoot_mem⟩, fun _ ↦ rfl,
      fun _ _ ↦ rfl⟩,
    card_steiner348, steinerBlock_card, existsUnique_subset_steiner348,
    steinerBlock_inter_card_of_ne⟩
  · change pairVector p.val.1 p.val.2 1 (-1) = _
    rw [pairVector, sub_eq_add_neg, ← Pi.single_neg]
  · change rootSign b * tripleRoot t i = _
    simp only [tripleRoot]
    split_ifs <;> ring

-- Computation C2
/-- Computation C2, `comp:C2` of Section 3 of [CGSS]: the line counts `ℓ(ℓ+1)/2` and `ℓ(ℓ-1)`
in the ranges of Definition 3.1 (Lemma 3.4, `numLines_An` and `numLines_Dn`, holds for every `ℓ`),
120 in each of the three `E₈` models, 63 for `E₇` and `T₇`, and 36 for `E₆` and `T₆`. -/
theorem line_counts :
    (∀ ℓ, 1 ≤ ℓ → (An ℓ).numLines = ℓ * (ℓ + 1) / 2) ∧
    (∀ ℓ, 4 ≤ ℓ → (Dn ℓ).numLines = ℓ * (ℓ - 1)) ∧
    E₈viaA₈.numLines = 120 ∧ E₈viaD₈.numLines = 120 ∧ E₈viaSteiner.numLines = 120 ∧
    E₇.numLines = 63 ∧ T₇.numLines = 63 ∧ E₆.numLines = 36 ∧ T₆.numLines = 36 :=
  ⟨fun ℓ _ ↦ numLines_An ℓ, fun ℓ _ ↦ numLines_Dn ℓ, numLines_E₈viaA₈, numLines_E₈,
    numLines_E₈viaSteiner, numLines_E₇, numLines_T₇, numLines_E₆, numLines_T₆⟩

end Computations.C2
