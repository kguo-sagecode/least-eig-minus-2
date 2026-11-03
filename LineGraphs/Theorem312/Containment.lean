/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Theorem312.Seeds

/-!
# Normalized containment for Theorem 3.12 of [CGSS]

The two assertions of `cor:312-containment`: the ambient construction uses completed
seeds, and the construction in the span uses the original seeds on the subspace type.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The line-containment step in `cor:312-containment`, Theorem 3.12 of [CGSS]. -/
theorem rootLines_mono {T U : Set V} (h : T ⊆ U) : rootLines T ⊆ rootLines U := by
  rintro ℓ ⟨r, hr, hℓ⟩
  exact ⟨r, h hr, hℓ⟩

-- Theorem 3.12
/-- `t312containAmbient` of `cor:312-containment`, Theorem 3.12 of [CGSS].
The containing root set spans the given ambient space and has squared norms 2 or 4. -/
theorem exists_rootSet_of_hasBipartition [FiniteDimensional ℝ V]
    {S : Set (Submodule ℝ V)} (hline : ∀ ℓ ∈ S, Module.finrank ℝ ℓ = 1)
    (hS : HasBipartition S) :
    ∃ Φ : Set V, IsRootSet Φ ∧ S ⊆ rootLines Φ ∧
      ∀ r ∈ Φ, ⟪r, r⟫ = 2 ∨ ⟪r, r⟫ = 4 := by
  obtain ⟨T, hfin, hlines, -, hnorm, hint, heven⟩ :=
    exists_integral_seeds_of_hasBipartition hline hS
  obtain ⟨T', hfin', hsub, hspan', hnorm', hint', heven'⟩ :=
    exists_spanning_integral_seed_extension hfin hnorm hint heven
  obtain ⟨hroot, hsub', hnorm''⟩ :=
    isRootSet_integralSpanRoots hfin' hspan' hnorm' hint' heven'
  exact ⟨integralSpanRoots T', hroot, hlines ▸ rootLines_mono (hsub.trans hsub'), hnorm''⟩

/-- `t312containSpan` of `cor:312-containment`, Theorem 3.12 of [CGSS].
The root set in the span uses the induced inner product, and its image in `V`
contains the prescribed lines. The zero span is allowed. -/
theorem exists_rootSet_in_span_of_hasBipartition [FiniteDimensional ℝ V]
    {S : Set (Submodule ℝ V)} (hline : ∀ ℓ ∈ S, Module.finrank ℝ ℓ = 1)
    (hS : HasBipartition S) :
    let W := span ℝ {x | ∃ ℓ ∈ S, x ∈ ℓ}
    ∃ Φ : Set W, IsRootSet Φ ∧ S ⊆ rootLines (Subtype.val '' Φ) ∧
      ∀ r ∈ Φ, ⟪r, r⟫ = 2 ∨ ⟪r, r⟫ = 4 := by
  classical
  obtain ⟨T, hfin, hlines, hspan, hnorm, hint, heven⟩ :=
    exists_integral_seeds_of_hasBipartition hline hS
  let W := span ℝ {x | ∃ ℓ ∈ S, x ∈ ℓ}
  let TW : Set W := Subtype.val ⁻¹' T
  have hTWfin : TW.Finite := Set.Finite.preimage Subtype.val_injective.injOn hfin
  have htW (t : V) (ht : t ∈ T) : t ∈ W := by
    change t ∈ span ℝ {x | ∃ ℓ ∈ S, x ∈ ℓ}
    rw [← hspan]
    exact subset_span ht
  have himage : (Subtype.val : W → V) '' TW = T := by
    apply Set.image_preimage_eq_of_subset
    exact fun t ht ↦ ⟨⟨t, htW t ht⟩, rfl⟩
  have hTWspan : span ℝ TW = ⊤ := by
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [map_span, map_subtype_top]
    change span ℝ ((Subtype.val : W → V) '' TW) = W
    rw [himage]
    exact hspan
  have hTWnorm : ∀ t ∈ TW, ⟪t, t⟫ = 2 ∨ ⟪t, t⟫ = 4 :=
    fun t ht ↦ hnorm t ht
  have hTWint : ∀ t ∈ TW, ∀ u ∈ TW, ∃ z : ℤ, ⟪t, u⟫ = z :=
    fun t ht u hu ↦ hint t ht u hu
  have hTWeven : ∀ t ∈ TW, ⟪t, t⟫ = 4 → ∀ u ∈ TW, ∃ z : ℤ, ⟪t, u⟫ = 2 * z :=
    fun t ht h u hu ↦ heven t ht h u hu
  obtain ⟨hroot, hsub, hnorm'⟩ :=
    isRootSet_integralSpanRoots hTWfin hTWspan hTWnorm hTWint hTWeven
  refine ⟨integralSpanRoots TW, hroot, ?_, hnorm'⟩
  have hinc : T ⊆ (Subtype.val : W → V) '' integralSpanRoots TW :=
    fun t ht ↦ ⟨⟨t, htW t ht⟩, hsub ht, rfl⟩
  intro ℓ hℓ
  exact rootLines_mono hinc (hlines.symm ▸ hℓ)

end LineSystem
