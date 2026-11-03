/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Basic
import LineGraphs.RootSetClassification.ClassicalCartan
import LineGraphs.RootSystems.Pairing
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# The prescribed root bases as Mathlib bases

Steps `rBmonoid`, `rBmodelbase`, and `rBcartan` of the indecomposable
classification in Remark 3.11 of [CGSS]. The support equivalence keeps the
prescribed indexing and the second-root denominator convention.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet.IsBase

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Φ : Set V} {hΦ : IsRootSet Φ} {α : I → V} (hα : hΦ.IsBase α)

include hα in
/-- Step `rBmonoid`: one-sign integer coefficients give a natural span or its negative. -/
theorem mem_nat_span_or_neg_mem {r : V} (hr : r ∈ Φ) :
    r ∈ span ℕ (Set.range α) ∨ -r ∈ span ℕ (Set.range α) := by
  obtain ⟨c, hc | hc, he⟩ := hα.coefficients r hr
  · left
    rw [he]
    apply sum_mem
    intro i _
    rw [← Int.toNat_of_nonneg (hc i), Int.cast_natCast, Nat.cast_smul_eq_nsmul]
    exact smul_mem _ _ (subset_span (Set.mem_range_self i))
  · right
    rw [he, ← Finset.sum_neg_distrib]
    apply sum_mem
    intro i _
    rw [← neg_smul, ← Int.cast_neg, ← Int.toNat_of_nonneg (neg_nonneg.mpr (hc i)),
      Int.cast_natCast, Nat.cast_smul_eq_nsmul]
    exact smul_mem _ _ (subset_span (Set.mem_range_self i))

/-- The simple-root indices inside the prescribed root set, in step `rBmodelbase`. -/
def rootIndex (i : I) : Φ := ⟨α i, hα.mem i⟩

/-- Independence makes the parametrization of the base support injective (`rBmodelbase`). -/
theorem rootIndex_injective : Function.Injective hα.rootIndex :=
  fun _ _ h ↦ hα.linearIndependent.injective (congrArg Subtype.val h)

/-- Step `rBmodelbase`: the displayed root base defines a Mathlib base of the
finite-root-set pairing, using `RootPairing.Base.mk'`. -/
noncomputable def toRootPairingBase : hΦ.toRootPairing.Base := by
  letI := hΦ.finite_root_index
  apply RootPairing.Base.mk' hΦ.toRootPairing (Set.range hα.rootIndex)
  · exact (linearIndepOn_range_iff hα.rootIndex_injective _).mpr hα.linearIndependent
  · intro r
    have he : hΦ.toRootPairing.root '' Set.range hα.rootIndex = Set.range α := by
      rw [← Set.range_comp]
      rfl
    rw [he, ← span_nat_eq_addSubmonoidClosure]
    exact hα.mem_nat_span_or_neg_mem r.property

/-- The support of the Mathlib base is precisely the prescribed family (`rBmodelbase`). -/
theorem mem_toRootPairingBase_support (r : Φ) :
    r ∈ hα.toRootPairingBase.support ↔ ∃ i, hα.rootIndex i = r := by
  simp [toRootPairingBase, RootPairing.Base.mk']

/-- The index bijection in step `rBcartan` of Remark 3.11. -/
noncomputable def baseIndexEquiv : I ≃ hα.toRootPairingBase.support :=
  Equiv.ofBijective
    (fun i ↦ ⟨hα.rootIndex i, (hα.mem_toRootPairingBase_support _).mpr ⟨i, rfl⟩⟩)
    ⟨fun _ _ h ↦ hα.rootIndex_injective (congrArg Subtype.val h), by
      intro r
      obtain ⟨i, hi⟩ := (hα.mem_toRootPairingBase_support r).mp r.property
      exact ⟨i, Subtype.ext hi⟩⟩

/-- Step `rBsimple`: the support equivalence retains the displayed simple roots. -/
@[simp] theorem root_baseIndexEquiv (i : I) :
    hΦ.toRootPairing.root (hα.baseIndexEquiv i) = α i := rfl

/-- Steps `rBrealcartan`, `rBcartan`: the Mathlib integer Cartan entries are exactly
the real coordinate pairings after casting. -/
theorem cartanMatrix_toRootPairingBase (i j : I) :
    (hα.toRootPairingBase.cartanMatrix (hα.baseIndexEquiv i) (hα.baseIndexEquiv j) : ℝ) =
      IsRootSet.cartanPairing α i j := by
  change algebraMap ℤ ℝ (hα.toRootPairingBase.cartanMatrixIn ℤ
    (hα.baseIndexEquiv i) (hα.baseIndexEquiv j)) = _
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply, hΦ.toRootPairing_pairing]
  rfl

end IsRootSet.IsBase
