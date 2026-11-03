/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Classification

/-!
# Fixed-length root subsystems

Steps `rangfixed` and `rangADE` of `lem:angles` in the blueprint
for Remark 3.11 of [CGSS]. Restrict to the roots of a given length, then to
their span, and apply blueprint Theorem B separately to their orthogonal components.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ : Set V}

/-- The roots of one length in `rangfixed` of Remark 3.11. -/
def fixedLength (Φ : Set V) (a : ℝ) : Set V := {r ∈ Φ | ‖r‖ = a}

/-- The fixed-length roots in their own span, as required by `lem:angles`. -/
def fixedLengthInSpan (Φ : Set V) (a : ℝ) : Set (span ℝ (fixedLength Φ a)) :=
  Subtype.val ⁻¹' fixedLength Φ a

-- Remark 3.11, lem:angles
/-- Steps `rangfixedbasic`--`rangfixedspan`: roots of a fixed length form a
root set in their own span. This also holds for an absent length, with empty roots. -/
theorem fixedLength_isRootSet (hΦ : IsRootSet Φ) (a : ℝ) :
    IsRootSet (fixedLengthInSpan Φ a) := by
  apply hΦ.restrictSpan_isRootSet (fun _ h ↦ h.1)
  intro r hr s hs
  refine ⟨hΦ.reflection_mem r hr.1 s hs.1, ?_⟩
  rw [← reflection_apply r (hΦ.ne_zero hr.1), LinearIsometryEquiv.norm_map, hs.2]

/-- Step `rangADE`: a root set whose roots all have the same squared
length can be similar only to an A, D, or E model. -/
theorem IsSimilarToModel.isSimplyLaced_of_constant {T : (n : ℕ) × CartanMatrix.FiniteType n}
    (hT : IsSimilarToModel Φ T) {b : ℝ} (hb : ∀ r ∈ Φ, ⟪r, r⟫ = b) :
    RootSetModel.IsSimplyLaced T.2 := by
  obtain ⟨f, a, hf⟩ := hT
  have hconst (s : RootSetModel.Space T.2) (hs : s ∈ RootSetModel.roots T.2) :
      ⟪s, s⟫ = a * b := by
    obtain ⟨r, hr, rfl⟩ := hf.image_eq ▸ hs
    rw [hf.inner_map, hb r hr]
  obtain ⟨r, hr, hmin⟩ := RootSetModel.exists_minLengthSq T.2
  have hmaxmem : RootSetModel.maxLengthSq T.2 ∈ squaredLengths (RootSetModel.roots T.2) := by
    rw [RootSetModel.squaredLengths_eq]
    exact Or.inr rfl
  obtain ⟨s, hs, hmax⟩ := hmaxmem
  change ⟪s, s⟫ = RootSetModel.maxLengthSq T.2 at hmax
  apply (RootSetModel.maxLengthSq_eq_min_iff T.2).mp
  rw [← hmax, ← hmin, hconst r hr, hconst s hs]

-- Remark 3.11, lem:angles
/-- Step `rangADE`: each component of a fixed-length subsystem has a
unique model, and it is A, D, or E. Orthogonality and the internal direct sum are
given by `orthogonal_components` applied to `fixedLength_isRootSet`. -/
theorem fixedLength_components_simplyLaced (hΦ : IsRootSet Φ) (a : ℝ)
    (C : (rootGraph (fixedLengthInSpan Φ a)).ConnectedComponent) :
    ∃! T : (n : ℕ) × CartanMatrix.FiniteType n,
      RootSetModel.IsSimplyLaced T.2 ∧
        IsSimilarToModel ((Subtype.val : componentSpan C → span ℝ (fixedLength Φ a)) ⁻¹'
          componentRoots C) T := by
  let hΨ := hΦ.fixedLength_isRootSet a
  obtain ⟨T, hT, hu⟩ := (hΨ.component_isRootSet C).classification_of_isIndecomposable
    (hΨ.component_isIndecomposable C)
  refine ⟨T, ⟨?_, hT⟩, fun U hU ↦ hu U hU.2⟩
  apply hT.isSimplyLaced_of_constant (b := a ^ 2)
  intro r hr
  have hmem : (r : span ℝ (fixedLength Φ a)) ∈ fixedLengthInSpan Φ a := hr.choose
  change ⟪((r : span ℝ (fixedLength Φ a)) : V),
    ((r : span ℝ (fixedLength Φ a)) : V)⟫ = a ^ 2
  rw [real_inner_self_eq_norm_sq, hmem.2]

end IsRootSet
