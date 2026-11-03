/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Theorem312.Necessary

/-!
# Theorem 3.12 of [CGSS]

`thm:3.12` and the Section 2 bridge `lem:312-bridge` of `blueprint/sec3-thm312.tex`.
The equivalence uses the explicit integer-span construction for sufficiency and
the parity of the integer logarithm of squared root lengths for necessity.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Theorem 3.12
/-- Theorem 3.12 of [CGSS] (`thm:3.12`, steps `t312mainNecessary` and
`t312mainSufficient`). For one-dimensional subspaces with squared cosines 0,
1/4 or 1/2, root-line containment is equivalent to a compatible bipartition.
The set and either colour fibre may be empty (Implicit hypothesis 8); finiteness
is derived and no spanning hypothesis is imposed on the lines. The containing
root set spans the given ambient space. The cross-part condition reads "or"
(Error 13, item 3); the explicit construction fills Gap 11. -/
theorem subset_rootSet_iff_bipartition [FiniteDimensional ℝ V]
    {S : Set (Submodule ℝ V)} (hline : ∀ ℓ ∈ S, Module.finrank ℝ ℓ = 1)
    (hangle : HasAllowedAngles S) :
    (∃ Φ : Set V, IsRootSet Φ ∧ S ⊆ rootLines Φ) ↔ HasBipartition S := by
  constructor
  · rintro ⟨Φ, hΦ, hsub⟩
    exact hasBipartition_of_subset_rootLines hΦ hsub hangle
  · intro hS
    obtain ⟨Φ, hΦ, hsub, -⟩ := exists_rootSet_of_hasBipartition hline hS
    exact ⟨Φ, hΦ, hsub⟩

/-- `t312bridgeDimension`--`t312bridgeSmall` of `lem:312-bridge`,
Theorem 3.12 of [CGSS]: distinct Section 2 root lines have squared cosine 0 or 1/4. -/
private theorem squared_cosine_rootLines (R : LineSystem V)
    {ℓ m : Submodule ℝ V} (hℓ : ℓ ∈ rootLines R.Φ) (hm : m ∈ rootLines R.Φ)
    (hne : ℓ ≠ m) : HasSquaredCosine ℓ m 0 ∨ HasSquaredCosine ℓ m (1 / 4) := by
  obtain ⟨r, hr, rfl⟩ := hℓ
  obtain ⟨s, hs, rfl⟩ := hm
  have hrn := R.inner_self r hr
  have hsn := R.inner_self s hs
  have hr0 : r ≠ 0 := by intro h; simp [h] at hrn
  have hs0 : s ≠ 0 := by intro h; simp [h] at hsn
  have hiff (a : ℝ) := hasSquaredCosine_iff (a := a)
    (finrank_span_singleton hr0) (finrank_span_singleton hs0)
    (mem_span_singleton_self r) hr0 (mem_span_singleton_self s) hs0
  have hend : ⟪r, s⟫ ≠ 2 ∧ ⟪r, s⟫ ≠ -2 := by
    constructor
    · intro h
      exact hne (congrArg (fun x : V ↦ span ℝ {x}) ((R.inner_eq_two_iff hr hs).mp h))
    · intro h
      have he : r = -s := (R.inner_eq_neg_two_iff hr hs).mp h
      apply hne
      rw [he]
      simpa only [Set.neg_singleton] using (Submodule.span_neg (R := ℝ) ({s} : Set V))
  have hp := R.inner_mem r hr s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp | hp | hp
  · exact False.elim (hend.2 hp)
  · right
    apply (hiff _).mpr
    rw [hp, hrn, hsn]
    norm_num
  · left
    apply (hiff _).mpr
    rw [hp, hrn, hsn]
    norm_num
  · right
    apply (hiff _).mpr
    rw [hp, hrn, hsn]
    norm_num
  · exact False.elim (hend.1 hp)

/-- `t312bridgeAllowed` of `lem:312-bridge`, Theorem 3.12 of [CGSS]. -/
theorem hasAllowedAngles_rootLines (R : LineSystem V) : HasAllowedAngles (rootLines R.Φ) := by
  intro ℓ hℓ m hm hne
  rcases squared_cosine_rootLines R hℓ hm hne with h | h
  · exact ⟨0, by simp, h⟩
  · exact ⟨1 / 4, by simp, h⟩

/-- `t312bridgeColour` of `lem:312-bridge`, Theorem 3.12 of [CGSS].
The constant false colouring is compatible, so its true fibre may be empty. -/
theorem hasBipartition_rootLines (R : LineSystem V) : HasBipartition (rootLines R.Φ) := by
  refine ⟨fun _ ↦ false, ?_⟩
  intro ℓ m hne
  refine ⟨fun _ ↦ ?_, fun h ↦ False.elim (h rfl)⟩
  exact squared_cosine_rootLines R ℓ.property m.property (fun h ↦ hne (Subtype.ext h))

end LineSystem
