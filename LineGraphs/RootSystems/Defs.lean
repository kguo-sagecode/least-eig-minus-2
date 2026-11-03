/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Reflections
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.Tactic

/-!
# Root sets in the sense of [CGSS]

Definition 3.9 (`def:roots`, also `def:3.9`) is in `blueprint/sec3-remark311.tex`.
The six requirements include the explicit nonzero-root repair. Conditions (a), (b), (c)
are respectively integrality, reducedness, and reflection closure. Finite dimensionality
follows from finiteness and spanning, so need not be an ambient typeclass assumption.

The reflection and coroot lemmas follow `lem:rem-reflection` and
`lem:pairing-construction`; the finite root pairing itself is built in `Pairing.lean`.
-/

open scoped RealInnerProductSpace
open Submodule

-- Definition 3.9
/-- Definition 3.9 of [CGSS] (`def:roots`, `def:3.9`): a finite spanning reduced
crystallographic root set, with nonzero roots and closure under root reflections. -/
structure IsRootSet {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Φ : Set V) : Prop where
  finite : Φ.Finite
  zero_notMem : (0 : V) ∉ Φ
  span_eq_top : span ℝ Φ = ⊤
  /-- Condition (a) of Definition 3.9. -/
  crystallographic : ∀ r ∈ Φ, ∀ s ∈ Φ, ∃ z : ℤ, (z : ℝ) = 2 * ⟪r, s⟫ / ⟪r, r⟫
  /-- Condition (b) of Definition 3.9, with the printed `S` corrected to `Φ`. -/
  reduced : ∀ r ∈ Φ, ∀ t : ℝ, t • r ∈ Φ → t = 1 ∨ t = -1
  /-- Condition (c) of Definition 3.9. -/
  reflection_mem : ∀ r ∈ Φ, ∀ s ∈ Φ, s - (2 * ⟪r, s⟫ / ⟪r, r⟫) • r ∈ Φ

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Φ : Set V} (hΦ : IsRootSet Φ)

/-- Nonzero roots in Definition 3.9 of [CGSS] (`def:roots`). -/
theorem ne_zero (hΦ : IsRootSet Φ) {r : V} (hr : r ∈ Φ) : r ≠ 0 :=
  fun h ↦ hΦ.zero_notMem (h ▸ hr)

/-- The ambient space in Definition 3.9 of [CGSS] is finite dimensional (`rpcperfect`). -/
theorem finiteDimensional (hΦ : IsRootSet Φ) : FiniteDimensional ℝ V := by
  exact Module.Finite.of_fg_top (hΦ.span_eq_top ▸ Submodule.fg_span hΦ.finite)

/-- Indecomposability as used in blueprint `def:roots`, for the classification following
Definition 3.9 of [CGSS]. This extra predicate, absent from that definition in the paper,
includes nonemptiness. -/
def IsIndecomposable (_hΦ : IsRootSet Φ) : Prop :=
  Φ.Nonempty ∧ ∀ A B : Set V, A ∪ B = Φ →
    (∀ a ∈ A, ∀ b ∈ B, ⟪a, b⟫ = 0) → A = ∅ ∨ B = ∅

/-- The coroot formula in `lem:pairing-construction` (`rpccoroot`), for Definition 3.9
of [CGSS]. It is defined at zero as well, with value zero. -/
noncomputable def coroot (r : V) : V := (2 / ⟪r, r⟫) • r

/-- Step `rpctwice` of the bridge for Definition 3.9 of [CGSS]: taking coroots twice
recovers the vector. -/
theorem coroot_coroot (r : V) : coroot (coroot r) = r := by
  by_cases hr : r = 0
  · simp [hr, coroot]
  have hq : ⟪r, r⟫ ≠ 0 := by simpa using hr
  unfold coroot
  rw [real_inner_smul_left, real_inner_smul_right, smul_smul]
  have hc : 2 / (2 / ⟪r, r⟫ * (2 / ⟪r, r⟫ * ⟪r, r⟫)) * (2 / ⟪r, r⟫) = 1 := by
    field_simp
  rw [hc, one_smul]

/-- Step `rpccoroot` of the bridge for Definition 3.9 of [CGSS]: coroots are injective. -/
theorem coroot_injective : Function.Injective (coroot : V → V) :=
  Function.LeftInverse.injective coroot_coroot

/-- Step `rpcself` of the bridge for Definition 3.9 of [CGSS]. -/
theorem inner_coroot_self {r : V} (hr : r ≠ 0) : ⟪coroot r, r⟫ = 2 := by
  have hq : ⟪r, r⟫ ≠ 0 := by simpa using hr
  rw [coroot, real_inner_smul_left, div_mul_cancel₀ _ hq]

/-- The orthogonal reflection of Definition 3.9 of [CGSS], constructed as a linear
isometry (`lem:rem-reflection`, steps `rrlinear`, `rrinvolution`, `rrmetric`). -/
noncomputable def reflection (r : V) (hr : r ≠ 0) : V ≃ₗᵢ[ℝ] V :=
  LinearEquiv.isometryOfInner
    (Module.reflection (show innerₗ V (coroot r) r = 2 from inner_coroot_self hr)) (by
      intro x y
      change ⟪x - ⟪coroot r, x⟫ • r, y - ⟪coroot r, y⟫ • r⟫ = ⟪x, y⟫
      have hq : ⟪r, r⟫ ≠ 0 := by simpa using hr
      simp only [coroot, inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, real_inner_comm x r]
      field_simp
      ring)

/-- The reflection formula in Definition 3.9 of [CGSS] (`rrformula`). -/
theorem reflection_apply (r : V) (hr : r ≠ 0) (x : V) :
    reflection r hr x = x - (2 * ⟪r, x⟫ / ⟪r, r⟫) • r := by
  change x - ⟪coroot r, x⟫ • r = _
  simp only [coroot, real_inner_smul_left, div_mul_eq_mul_div]

/-- Step `rrinvolution` of `lem:rem-reflection`, for Definition 3.9 of [CGSS]. -/
theorem reflection_involutive (r : V) (hr : r ≠ 0) :
    Function.Involutive (reflection r hr) :=
  Module.involutive_reflection (show innerₗ V (coroot r) r = 2 from inner_coroot_self hr)

/-- Step `rreigen` of `lem:rem-reflection`, for Definition 3.9 of [CGSS]. -/
theorem reflection_self (r : V) (hr : r ≠ 0) : reflection r hr r = -r :=
  Module.reflection_apply_self (show innerₗ V (coroot r) r = 2 from inner_coroot_self hr)

/-- Step `rrroots` of `lem:rem-reflection`: Definition 3.9 of [CGSS] implies closure
under negation. -/
theorem neg_mem (hΦ : IsRootSet Φ) {r : V} (hr : r ∈ Φ) : -r ∈ Φ := by
  have h := hΦ.reflection_mem r hr r hr
  rw [← reflection_apply r (hΦ.ne_zero hr), reflection_self] at h
  exact h

/-- Step `rpcnorm` of the bridge for Definition 3.9 of [CGSS]: coroot normalization
commutes with orthogonal reflection. -/
theorem coroot_reflection (r : V) (hr : r ≠ 0) (s : V) :
    coroot (reflection r hr s) = reflection r hr (coroot s) := by
  simp only [coroot, LinearIsometryEquiv.inner_map_map, map_smul]

/-- Step `rpcreflection` of the bridge for Definition 3.9 of [CGSS]: reflections
permute the prescribed finite root set. -/
noncomputable def reflectionPerm (r : Φ) : Φ ≃ Φ :=
  (show Function.Involutive (fun s : Φ ↦
      (⟨reflection (r : V) (hΦ.ne_zero r.property) s,
        by rw [reflection_apply]; exact hΦ.reflection_mem r r.property s s.property⟩ : Φ)) from
    fun s ↦ Subtype.ext (reflection_involutive (r : V) (hΦ.ne_zero r.property) s)).toPerm

end IsRootSet
