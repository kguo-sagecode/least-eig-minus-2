/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.Defs
import Mathlib.LinearAlgebra.RootSystem.Irreducible
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-!
# The finite root set bridge to Mathlib

The construction follows `lem:pairing-construction` in `blueprint/sec3-remark311.tex`
(RS1, Definition 3.9 of [CGSS]). Roots are indexed by the prescribed set `Φ`; root and
coroot spaces are both the original real inner product space. In particular, this does
not use `RootPairing.ofBilinear`, which would select all nonzero real vectors.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Φ : Set V} (hΦ : IsRootSet Φ)

/-- Step `rpcperfect` of the bridge for Definition 3.9 of [CGSS]: the inner product
is a perfect pairing, by injectivity on both sides and finite dimensionality. -/
theorem inner_isPerfPair (hΦ : IsRootSet Φ) : (innerₗ V).IsPerfPair := by
  let := hΦ.finiteDimensional
  have hi : Function.Injective (innerₗ V) :=
    fun x y h ↦ ext_inner_right ℝ (fun z ↦ LinearMap.congr_fun h z)
  exact LinearMap.IsPerfPair.of_injective hi (by simpa only [flip_innerₗ] using hi)

/-- Steps `rpcstructure` and `rpcfinite` of `lem:pairing-construction`: the root pairing
of Definition 3.9 of [CGSS], on the prescribed finite set of root indices. -/
noncomputable def toRootPairing : RootPairing Φ ℝ V V where
  toLinearMap := innerₗ V
  isPerfPair_toLinearMap := hΦ.inner_isPerfPair
  root := ⟨Subtype.val, Subtype.val_injective⟩
  coroot := ⟨fun r ↦ coroot (r : V), coroot_injective.comp Subtype.val_injective⟩
  root_coroot_two r := by
    change ⟪(r : V), coroot (r : V)⟫ = 2
    rw [real_inner_comm]
    exact inner_coroot_self (hΦ.ne_zero r.property)
  reflectionPerm := hΦ.reflectionPerm
  reflectionPerm_root r s := by
    change (s : V) - ⟪(s : V), coroot (r : V)⟫ • (r : V) =
      reflection (r : V) (hΦ.ne_zero r.property) (s : V)
    rw [reflection_apply, coroot, real_inner_smul_right, real_inner_comm (s : V)]
    rw [div_mul_eq_mul_div]
  reflectionPerm_coroot r s := by
    change coroot (s : V) - ⟪(r : V), coroot (s : V)⟫ • coroot (r : V) =
      coroot (reflection (r : V) (hΦ.ne_zero r.property) (s : V))
    rw [coroot_reflection, reflection_apply]
    simp only [coroot, real_inner_smul_right, smul_smul]
    congr 2
    ring

/-- Step `rpcfinite` of the bridge for Definition 3.9 of [CGSS]. -/
theorem finite_root_index (hΦ : IsRootSet Φ) : Finite Φ := hΦ.finite.to_subtype

/-- Step `rpcstructure`: the pairing convention of the bridge for Definition 3.9
of [CGSS] has the squared norm of the second root in the denominator. -/
theorem toRootPairing_pairing (r s : Φ) :
    hΦ.toRootPairing.pairing r s = 2 * ⟪(r : V), (s : V)⟫ / ⟪(s : V), (s : V)⟫ := by
  change ⟪(r : V), coroot (s : V)⟫ = _
  rw [coroot, real_inner_smul_right]
  ring

/-- Step `rpccrystal` of the bridge for Definition 3.9 of [CGSS]. -/
instance toRootPairing_isCrystallographic : hΦ.toRootPairing.IsCrystallographic where
  exists_value r s := by
    obtain ⟨z, hz⟩ := hΦ.crystallographic s s.property r r.property
    refine ⟨z, ?_⟩
    rw [toRootPairing_pairing]
    simpa only [algebraMap_int_eq, Int.coe_castRingHom,
      real_inner_comm (s : V) (r : V)] using hz

/-- Steps `rpcdependence`--`rpcproportional` and `rpcreduced` of the bridge for
Definition 3.9 of [CGSS]. -/
instance toRootPairing_isReduced : hΦ.toRootPairing.IsReduced where
  eq_or_eq_neg r s h := by
    change ¬ LinearIndependent ℝ ![(r : V), (s : V)] at h
    rw [LinearIndependent.pair_iff' (hΦ.ne_zero r.property)] at h
    push Not at h
    obtain ⟨t, ht⟩ := h
    rcases hΦ.reduced r r.property t (ht.symm ▸ s.property) with h | h
    · left
      change (r : V) = (s : V)
      simpa only [h, one_smul] using ht
    · right
      change (r : V) = -(s : V)
      simpa only [h, neg_one_smul, neg_eq_iff_eq_neg] using ht

/-- Steps `rpcrootspan` and `rpccorootspan` of the bridge for Definition 3.9 of [CGSS]. -/
instance toRootPairing_isRootSystem : hΦ.toRootPairing.IsRootSystem where
  span_root_eq_top := by
    change span ℝ (Set.range (Subtype.val : Φ → V)) = ⊤
    simpa only [Subtype.range_coe] using hΦ.span_eq_top
  span_coroot_eq_top := by
    apply top_unique
    rw [← hΦ.span_eq_top]
    apply span_le.mpr
    intro r hr
    rw [← coroot_coroot r]
    exact smul_mem _ _ (subset_span ⟨⟨r, hr⟩, rfl⟩)

/-- Step `rpcreflectionmaps` of the bridge for Definition 3.9 of [CGSS]: Mathlib's
root reflection is the Euclidean reflection on every vector. -/
theorem toRootPairing_reflection (r : Φ) (x : V) :
    hΦ.toRootPairing.reflection r x = reflection (r : V) (hΦ.ne_zero r.property) x := by
  rw [RootPairing.reflection_apply, reflection_apply]
  change x - ⟪x, coroot (r : V)⟫ • (r : V) = _
  rw [coroot, real_inner_smul_right, real_inner_comm x]
  congr 2
  ring

/-- Step `rpcreflectionmaps` of the bridge for Definition 3.9 of [CGSS]: Mathlib's
coroot reflection is the same Euclidean reflection on every vector. -/
theorem toRootPairing_coreflection (r : Φ) (x : V) :
    hΦ.toRootPairing.coreflection r x = reflection (r : V) (hΦ.ne_zero r.property) x := by
  rw [RootPairing.coreflection_apply, reflection_apply]
  change x - ⟪(r : V), x⟫ • coroot (r : V) = _
  rw [coroot, smul_smul]
  congr 2
  ring

/-- The vanishing pairing criterion used in `rpcalternative` of the bridge for
Definition 3.9 of [CGSS]. -/
theorem toRootPairing_coroot'_eq_zero_iff (r : Φ) (x : V) :
    hΦ.toRootPairing.coroot' r x = 0 ↔ ⟪(r : V), x⟫ = 0 := by
  change ⟪x, coroot (r : V)⟫ = 0 ↔ _
  rw [coroot, real_inner_smul_right, real_inner_comm x]
  have hq : ⟪(r : V), (r : V)⟫ ≠ 0 := by simpa using hΦ.ne_zero r.property
  exact mul_eq_zero.trans (or_iff_right (div_ne_zero two_ne_zero hq))

end IsRootSet
