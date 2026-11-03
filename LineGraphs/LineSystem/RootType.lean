/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.ModelSpans

/-!
# The types of Theorem 3.5

The list of Theorem 3.5 of [CGSS] as an index type (`blueprint/sec3-rootsystems.tex`, the note in
Theorem 3.5): `Aℓ` with `1 ≤ ℓ`, `Dℓ` with `4 ≤ ℓ`, and `E₆`, `E₇`, `E₈`. Each type has an ambient
dimension, a model in the Euclidean space of that dimension (the default `E₈`, model (ii)), a
rank (the dimension of the span of the model, `finrank_span_model`) and a number of lines
(Lemma 3.4, `numLines_model`).
-/

open Module Submodule

namespace LineSystem

/-- The types of Theorem 3.5: `Aℓ` (`1 ≤ ℓ`), `Dℓ` (`4 ≤ ℓ`), `E₆`, `E₇`, `E₈`. -/
inductive RootType where
  /-- The type `Aℓ`, `ℓ ≥ 1`. -/
  | A (ℓ : ℕ) (h : 1 ≤ ℓ)
  /-- The type `Dℓ`, `ℓ ≥ 4`. -/
  | D (ℓ : ℕ) (h : 4 ≤ ℓ)
  /-- The type `E₆`. -/
  | E₆
  /-- The type `E₇`. -/
  | E₇
  /-- The type `E₈`. -/
  | E₈

namespace RootType

/-- The ambient dimension of the model: `ℓ + 1` for `Aℓ`, `ℓ` for `Dℓ`, `8` for `E₆, E₇, E₈`. -/
def dim : RootType → ℕ
  | A ℓ _ => ℓ + 1
  | D ℓ _ => ℓ
  | E₆ => 8
  | E₇ => 8
  | E₈ => 8

/-- The model of a type (Definitions 3.1–3.3); for `E₈` the default model (ii). -/
noncomputable def model : (t : RootType) → LineSystem (EuclideanSpace ℝ (Fin t.dim))
  | A ℓ _ => An ℓ
  | D ℓ _ => Dn ℓ
  | E₆ => LineSystem.E₆
  | E₇ => LineSystem.E₇
  | E₈ => LineSystem.E₈

/-- The rank of a type. -/
def rank : RootType → ℕ
  | A ℓ _ => ℓ
  | D ℓ _ => ℓ
  | E₆ => 6
  | E₇ => 7
  | E₈ => 8

/-- The number of lines of a type (Lemma 3.4). -/
def numLines : RootType → ℕ
  | A ℓ _ => ℓ * (ℓ + 1) / 2
  | D ℓ _ => ℓ * (ℓ - 1)
  | E₆ => 36
  | E₇ => 63
  | E₈ => 120

theorem rank_pos (t : RootType) : 0 < t.rank := by
  cases t <;> simp only [rank] <;> omega

/-- The rank is the dimension of the span of the model (`lem:sec3-spans`). -/
theorem finrank_span_model (t : RootType) : finrank ℝ (span ℝ t.model.Φ) = t.rank := by
  cases t with
  | A ℓ _ => exact finrank_span_An ℓ
  | D ℓ h => exact finrank_span_Dn (n := ℓ) (by omega)
  | E₆ => exact finrank_span_E₆
  | E₇ => exact finrank_span_E₇
  | E₈ => exact finrank_span_E₈

-- Lemma 3.4
/-- Lemma 3.4 of [CGSS] for the models of the types. -/
theorem numLines_model (t : RootType) : t.model.numLines = t.numLines := by
  cases t with
  | A ℓ _ => exact numLines_An ℓ
  | D ℓ _ => exact numLines_Dn ℓ
  | E₆ => exact numLines_E₆
  | E₇ => exact numLines_E₇
  | E₈ => exact numLines_E₈

end RootType

end LineSystem
