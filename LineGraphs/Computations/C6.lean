/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C6Classical
import LineGraphs.Computations.C6E8
import LineGraphs.Computations.C6E7E6
import LineGraphs.LineSystem.RootType
import LineGraphs.LineSystem.SpanTransport

/-!
# Computation C6 and Theorem 3.7

Computation C6 of `blueprint/sec3-rootsystems.tex` (`Computations.C6.coordinate_frame_matrices`:
the seven coordinate frame matrices), the frame identity within the span for every type and every
isometric copy (`LineSystem.frame_identity`, `LineSystem.frame_identity_signing`), and Theorem 3.7
of [CGSS]: for every signing of `Aℓ`, `Dℓ`, `E₈`, `E₇`, `E₆`, in any realization,
`(C + 2I)(C - θI) = 0` with `θ = ℓ - 1`, `2(ℓ - 2)`, `28`, `16`, `10` (errata Error 1: the paper
prints 18 for `E₈`).

The frame identities hold on the span of the roots, not on the ambient space: the models `Aℓ`,
`E₈viaA₈`, `E₇` and `E₆` do not span it (blueprint `lem:sec3-frame`; errata, Error 1). The passage
to an isomorphic copy
uses only inner products of roots (`LineSystem.Iso.isFrame`), so no linear extension of the
isomorphism is needed. Theorem 3.7 needs no hypothesis `ℓ ≥ 1` or `ℓ ≥ 4`: for `ℓ = 0` both
sides are empty matrices, and the frame identities of C6 hold in every dimension.
-/

open scoped RealInnerProductSpace
open Finset Submodule

namespace Computations.C6

open LineSystem

-- Computation C6
/-- Computation C6 of the blueprint: the coordinate frame matrices `K = ∑ v vᵀ` over the raw
integer roots (both signs) of the seven models, as exact integer identities. -/
theorem coordinate_frame_matrices :
    (∀ (n : ℕ) (k l : Fin (n + 1)), ∑ a : An.Index n, An.root a k * An.root a l =
      2 * (((n : ℤ) + 1) * (if k = l then 1 else 0) - 1)) ∧
    (∀ (n : ℕ) (k l : Fin n), ∑ a : Dn.Index n, Dn.root a k * Dn.root a l =
      4 * ((n : ℤ) - 1) * (if k = l then 1 else 0)) ∧
    (∀ k l : Fin 9, ∑ a : E₈viaA₈.Index, E₈viaA₈.root a k * E₈viaA₈.root a l =
      540 * (if k = l then 1 else 0) - 60) ∧
    (∀ k l : Fin 8, ∑ a : E₈viaD₈.Index, E₈viaD₈.root a k * E₈viaD₈.root a l =
      240 * (if k = l then 1 else 0)) ∧
    (∀ k l : Fin 8, ∑ a : E₈viaSteiner.Index, E₈viaSteiner.root a k * E₈viaSteiner.root a l =
      120 * (if k = l then 1 else 0)) ∧
    (∀ k l : Fin 8, ∑ a : E₇.Index, E₇.root a k * E₇.root a l =
      if k.val < 6 then (if k = l then 144 else 0) else (if l.val < 6 then 0 else 72)) ∧
    (∀ k l : Fin 8, ∑ a : E₆.Index, E₆.root a k * E₆.root a l =
      if k.val < 5 then (if k = l then 96 else 0) else (if l.val < 5 then 0 else 32)) :=
  ⟨an_frame_matrix, dn_frame_matrix, e₈viaA₈_frame_matrix, e₈_frame_matrix,
    e₈viaSteiner_frame_matrix, e₇_frame_matrix, e₆_frame_matrix⟩

end Computations.C6

namespace LineSystem

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

-- Lemma "the frame identity within the span"
/-- C6 for the models of the types: the frame operator is `4N/ℓ` times the identity on the span,
with `N` lines and rank `ℓ`. -/
theorem RootType.isFrame_model (t : RootType) :
    t.model.IsFrame (4 * t.numLines / t.rank) := by
  cases t with
  | A ℓ h =>
    have hℓ : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
    have hd : ((ℓ * (ℓ + 1) / 2 : ℕ) : ℝ) = (ℓ : ℝ) * (ℓ + 1) / 2 := by
      rw [Nat.cast_div (Nat.even_mul_succ_self ℓ).two_dvd (by norm_num)]
      push_cast
      ring
    have hc : (4 * ((ℓ * (ℓ + 1) / 2 : ℕ) : ℝ) / ℓ) = 2 * ((ℓ : ℝ) + 1) := by
      rw [hd]
      field_simp
      ring
    change (An ℓ).IsFrame (4 * ((ℓ * (ℓ + 1) / 2 : ℕ) : ℝ) / ℓ)
    rw [hc]
    exact isFrame_An ℓ
  | D ℓ h =>
    have hℓ : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
    have hc : (4 * ((ℓ * (ℓ - 1) : ℕ) : ℝ) / ℓ) = 4 * ((ℓ : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]
      field_simp
      push_cast
      ring
    change (Dn ℓ).IsFrame (4 * ((ℓ * (ℓ - 1) : ℕ) : ℝ) / ℓ)
    rw [hc]
    exact isFrame_Dn ℓ
  | E₆ =>
    change LineSystem.E₆.IsFrame (4 * (36 : ℕ) / (6 : ℕ))
    norm_num
    exact isFrame_E₆
  | E₇ =>
    change LineSystem.E₇.IsFrame (4 * (63 : ℕ) / (7 : ℕ))
    norm_num
    exact isFrame_E₇
  | E₈ =>
    change LineSystem.E₈.IsFrame (4 * (120 : ℕ) / (8 : ℕ))
    norm_num
    exact isFrame_E₈

-- Lemma "the frame identity within the span"
/-- The frame identity within the span (blueprint, `lem:sec3-frame`), full-root form: for `S`
isomorphic to the model of a type of rank `ℓ`, with `N` lines,
`∑_{r ∈ Φ} ⟪r, x⟫ r = (4N/ℓ) x` for every `x` in the span of `Φ`. -/
theorem frame_identity (t : RootType) {S : LineSystem V} (h : Nonempty (S.Iso t.model)) :
    S.IsFrame (4 * S.numLines / t.rank) := by
  obtain ⟨e⟩ := h
  rw [e.numLines_eq, t.numLines_model]
  exact e.isFrame t.isFrame_model

-- Lemma "the frame identity within the span"
/-- `lem:sec3-frame` and `lem:sec3-transport`, used in Theorem 3.7 of [CGSS]: the
full-root frame constant uses the dimension of the root span of the given realization. -/
theorem frame_identity_span (t : RootType) {S : LineSystem V}
    (h : Nonempty (S.Iso t.model)) :
    S.IsFrame (4 * S.numLines / Module.finrank ℝ (span ℝ S.Φ)) := by
  obtain ⟨e⟩ := h
  rw [e.finrank_span_eq, t.finrank_span_model]
  exact frame_identity t ⟨e⟩

-- Lemma "the frame identity within the span"
/-- The frame identity within the span (blueprint, `lem:sec3-frame`), signing form: for every
signing `σ`, `∑ᵢ ⟪σ i, x⟫ σ i = (2N/ℓ) x` for every `x` in the span of `Φ`. -/
theorem frame_identity_signing (t : RootType) {S : LineSystem V} (h : Nonempty (S.Iso t.model))
    {I : Type*} [Fintype I] (σ : S.Signing I) {x : V} (hx : x ∈ span ℝ S.Φ) :
    ∑ i, ⟪σ i, x⟫ • σ i = (2 * S.numLines / t.rank : ℝ) • x := by
  rw [σ.sum_eq_of_isFrame (frame_identity t h) hx]
  congr 1
  ring

-- Theorem 3.7
/-- Theorem 3.7 of [CGSS], uniform form: `(C + 2I)(C - (2N/ℓ - 2)I) = 0` for every signing of
every isometric copy of the model of a type. -/
theorem signedAdj_quadratic (t : RootType) {S : LineSystem V} (h : Nonempty (S.Iso t.model))
    {I : Type*} [Fintype I] [DecidableEq I] (σ : S.Signing I) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) *
      (signedAdj σ - (2 * S.numLines / t.rank - 2 : ℝ) • (1 : Matrix I I ℝ)) = 0 :=
  signedAdj_quadratic_of_frame σ fun _ hx => frame_identity_signing t h σ hx

/-- A frame constant `t` gives Theorem 3.7 with `θ = t/2 - 2` for every copy and signing. -/
private theorem signedAdj_quadratic_of_iso {n : ℕ} {T : LineSystem (EuclideanSpace ℝ (Fin n))}
    {t θ : ℝ} (hT : T.IsFrame t) (hθ : t / 2 - 2 = θ) {S : LineSystem V}
    (h : Nonempty (S.Iso T)) {I : Type*} [Fintype I] [DecidableEq I] (σ : S.Signing I) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) * (signedAdj σ - θ • (1 : Matrix I I ℝ)) = 0 := by
  obtain ⟨e⟩ := h
  rw [← hθ]
  exact signedAdj_quadratic_of_isFrame σ (e.isFrame hT)

-- Theorem 3.7
/-- Theorem 3.7 of [CGSS] for `Aₙ`: `(C + 2I)(C - (n - 1)I) = 0`. -/
theorem signedAdj_quadratic_An (n : ℕ) {S : LineSystem V} (h : Nonempty (S.Iso (An n)))
    {I : Type*} [Fintype I] [DecidableEq I] (σ : S.Signing I) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) *
      (signedAdj σ - ((n : ℝ) - 1) • (1 : Matrix I I ℝ)) = 0 :=
  signedAdj_quadratic_of_iso (isFrame_An n) (by ring) h σ

-- Theorem 3.7
/-- Theorem 3.7 of [CGSS] for `Dₙ`: `(C + 2I)(C - 2(n - 2)I) = 0`. -/
theorem signedAdj_quadratic_Dn (n : ℕ) {S : LineSystem V} (h : Nonempty (S.Iso (Dn n)))
    {I : Type*} [Fintype I] [DecidableEq I] (σ : S.Signing I) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) *
      (signedAdj σ - (2 * ((n : ℝ) - 2)) • (1 : Matrix I I ℝ)) = 0 :=
  signedAdj_quadratic_of_iso (isFrame_Dn n) (by ring) h σ

-- Theorem 3.7
/-- Theorem 3.7 of [CGSS] for `E₈`: `(C + 2I)(C - 28I) = 0` (errata Error 1: not 18). -/
theorem signedAdj_quadratic_E₈ {S : LineSystem V} (h : Nonempty (S.Iso E₈))
    {I : Type*} [Fintype I] [DecidableEq I] (σ : S.Signing I) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) *
      (signedAdj σ - (28 : ℝ) • (1 : Matrix I I ℝ)) = 0 :=
  signedAdj_quadratic_of_iso isFrame_E₈ (by norm_num) h σ

-- Theorem 3.7
/-- Theorem 3.7 of [CGSS] for `E₇`: `(C + 2I)(C - 16I) = 0`. -/
theorem signedAdj_quadratic_E₇ {S : LineSystem V} (h : Nonempty (S.Iso E₇))
    {I : Type*} [Fintype I] [DecidableEq I] (σ : S.Signing I) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) *
      (signedAdj σ - (16 : ℝ) • (1 : Matrix I I ℝ)) = 0 :=
  signedAdj_quadratic_of_iso isFrame_E₇ (by norm_num) h σ

-- Theorem 3.7
/-- Theorem 3.7 of [CGSS] for `E₆`: `(C + 2I)(C - 10I) = 0`. -/
theorem signedAdj_quadratic_E₆ {S : LineSystem V} (h : Nonempty (S.Iso E₆))
    {I : Type*} [Fintype I] [DecidableEq I] (σ : S.Signing I) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) *
      (signedAdj σ - (10 : ℝ) • (1 : Matrix I I ℝ)) = 0 :=
  signedAdj_quadratic_of_iso isFrame_E₆ (by norm_num) h σ

/-- Theorem 3.7 for model (i) of `E₈` directly, without C3. -/
theorem signedAdj_quadratic_E₈viaA₈ {S : LineSystem V} (h : Nonempty (S.Iso E₈viaA₈))
    {I : Type*} [Fintype I] [DecidableEq I] (σ : S.Signing I) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) *
      (signedAdj σ - (28 : ℝ) • (1 : Matrix I I ℝ)) = 0 :=
  signedAdj_quadratic_of_iso isFrame_E₈viaA₈ (by norm_num) h σ

/-- Theorem 3.7 for model (iii) of `E₈` directly, without C3. -/
theorem signedAdj_quadratic_E₈viaSteiner {S : LineSystem V}
    (h : Nonempty (S.Iso E₈viaSteiner)) {I : Type*} [Fintype I] [DecidableEq I]
    (σ : S.Signing I) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) *
      (signedAdj σ - (28 : ℝ) • (1 : Matrix I I ℝ)) = 0 :=
  signedAdj_quadratic_of_iso isFrame_E₈viaSteiner (by norm_num) h σ

end LineSystem
