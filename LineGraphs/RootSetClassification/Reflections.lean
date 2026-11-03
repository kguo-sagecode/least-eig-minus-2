/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.Defs

/-!
# The reflection identities

`lem:rem-reflection` of the blueprint for Remark 3.11 of [CGSS], used in `lem:angles` and
`lem:tight-frame`. The reflection `IsRootSet.reflection` and its formula, involutivity and
value at the root are in `LineGraphs/RootSystems/Defs.lean`; this file adds the `-1`
eigenspace (`rreigen`), the sign independence (`rrsign`) and the conjugation by isometries
(`rrconj`), and bundles the lemma.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Step `rreigen` of `lem:rem-reflection` in Remark 3.11: the `-1` eigenspace of the
reflection in `r` is the line `ℝ r`. -/
theorem reflection_eq_neg_iff (r : V) (hr : r ≠ 0) (x : V) :
    reflection r hr x = -x ↔ x ∈ ℝ ∙ r := by
  constructor
  · intro h
    rw [reflection_apply] at h
    refine mem_span_singleton.mpr ⟨⟪r, x⟫ / ⟪r, r⟫, ?_⟩
    have h2 : (2 : ℝ) • ((⟪r, x⟫ / ⟪r, r⟫) • r) = (2 : ℝ) • x := by
      rw [smul_smul, two_smul ℝ x]
      calc (2 * (⟪r, x⟫ / ⟪r, r⟫)) • r = x - (x - (2 * ⟪r, x⟫ / ⟪r, r⟫) • r) := by
            rw [mul_div_assoc]
            abel
        _ = x + x := by rw [h, sub_neg_eq_add]
    exact smul_right_injective V (two_ne_zero) h2
  · intro h
    obtain ⟨c, rfl⟩ := mem_span_singleton.mp h
    rw [map_smul, reflection_self, smul_neg]

/-- Step `rrsign` of `lem:rem-reflection` in Remark 3.11: `s₋ᵣ = sᵣ`. -/
theorem reflection_neg (r : V) (hr : r ≠ 0) :
    reflection (-r) (neg_ne_zero.mpr hr) = reflection r hr := by
  ext x
  simp only [reflection_apply, inner_neg_left, inner_neg_right, neg_neg, mul_neg, neg_div,
    neg_smul, smul_neg]

/-- Step `rrconj` of `lem:rem-reflection` in Remark 3.11: for a linear isometry `f`,
`s_{f r} (f x) = f (sᵣ x)`. -/
theorem reflection_map (f : V ≃ₗᵢ[ℝ] W) (r : V) (hr : r ≠ 0) (x : V) :
    reflection (f r) (fun h ↦ hr (f.map_eq_zero_iff.mp h)) (f x) = f (reflection r hr x) := by
  simp only [reflection_apply, LinearIsometryEquiv.inner_map_map, map_sub, map_smul]

-- Remark 3.11, lem:rem-reflection
/-- The reflection identities, `lem:rem-reflection` of Remark 3.11 of [CGSS]: for `r ≠ 0`
the reflection `sᵣ` is an orthogonal linear involution with `sᵣ r = -r`, its `-1`
eigenspace is `ℝ r`, `s₋ᵣ = sᵣ`, and `s_{f r} f = f sᵣ` for every linear isometry `f`;
in a root set the reflections in roots permute the roots, and `Φ = -Φ`. -/
theorem reflection_identities (r : V) (hr : r ≠ 0) :
    Function.Involutive (reflection r hr) ∧
    (∀ x y, ⟪reflection r hr x, reflection r hr y⟫ = ⟪x, y⟫) ∧
    reflection r hr r = -r ∧
    (∀ x, reflection r hr x = -x ↔ x ∈ ℝ ∙ r) ∧
    reflection (-r) (neg_ne_zero.mpr hr) = reflection r hr ∧
    (∀ (f : V ≃ₗᵢ[ℝ] W) (x : V),
      reflection (f r) (fun h ↦ hr (f.map_eq_zero_iff.mp h)) (f x) =
        f (reflection r hr x)) ∧
    (∀ {Φ : Set V}, IsRootSet Φ → r ∈ Φ →
      (∀ s ∈ Φ, reflection r hr s ∈ Φ) ∧ -r ∈ Φ) :=
  ⟨reflection_involutive r hr, fun x y ↦ LinearIsometryEquiv.inner_map_map _ x y,
    reflection_self r hr, reflection_eq_neg_iff r hr, reflection_neg r hr,
    fun f x ↦ reflection_map f r hr x, fun hΦ hrΦ ↦
      ⟨fun s hs ↦ by rw [reflection_apply]; exact hΦ.reflection_mem r hrΦ s hs,
        hΦ.neg_mem hrΦ⟩⟩

end IsRootSet
