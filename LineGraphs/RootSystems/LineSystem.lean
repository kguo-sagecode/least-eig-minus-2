/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.Irreducible
import LineGraphs.LineSystem.SpanTransport

/-!
# Root sets of squared norm two and star-closed line systems

The equivalence (i) ↔ (ii) in Theorem 3.10 of [CGSS], using Definition 3.9
(`def:roots`). The checked-out blueprint has the definition and RS1 bridge in
`sec3-remark311.tex`, but no statement or Lamport steps for Theorem 3.10. This file
follows its proof in [CGSS], J. Algebra 43 (1976), p. 314: integral inner products,
automatic reducedness, and the five reflection cases. The latter cases are already
proved by `LineSystem.rootReflection_mem_isometryGroup`.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {S : LineSystem V}

-- Theorem 3.10
/-- Theorem 3.10 of [CGSS], (ii) → (i): a spanning star-closed line system satisfies
Definition 3.9 (`def:roots`), including automatic reducedness at squared norm two. -/
theorem IsStarClosed.isRootSet (hS : S.IsStarClosed) (hspan : span ℝ S.Φ = ⊤) :
    IsRootSet S.Φ where
  finite := S.finite
  zero_notMem := by
    intro h
    have := S.inner_self 0 h
    simp at this
  span_eq_top := hspan
  crystallographic r hr s hs := by
    rw [S.inner_self r hr]
    have hc : 2 * ⟪r, s⟫ / 2 = ⟪r, s⟫ := by ring
    rw [hc]
    rcases S.inner_mem r hr s hs with h | h | h | h | h
    · exact ⟨-2, by simpa using h.symm⟩
    · exact ⟨-1, by simpa using h.symm⟩
    · exact ⟨0, by simpa using h.symm⟩
    · exact ⟨1, by simpa using h.symm⟩
    · exact ⟨2, by simpa using h.symm⟩
  reduced r hr t ht := by
    have he := S.inner_self (t • r) ht
    rw [real_inner_smul_left, real_inner_smul_right, S.inner_self r hr] at he
    have hf : (t - 1) * (t + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · left; linarith
    · right; linarith
  reflection_mem r hr s hs := by
    have h := (S.mem_isometryGroup_iff _).mp
      (rootReflection_mem_isometryGroup hS hr) s |>.mpr hs
    rw [rootReflection_apply] at h
    simpa only [S.inner_self r hr, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
      using h

-- Theorem 3.10
/-- Theorem 3.10 of [CGSS], (i) → (ii): reflection closure gives the third star root.
This uses condition (c) of Definition 3.9 (`def:roots`) at inner product minus one. -/
theorem isStarClosed_of_isRootSet (hΦ : IsRootSet S.Φ) : S.IsStarClosed := by
  intro r hr s hs hrs
  have h := hΦ.reflection_mem r hr s hs
  rw [S.inner_self r hr, hrs] at h
  norm_num at h
  simpa only [add_comm] using h

-- Theorem 3.10
/-- The first equivalence of Theorem 3.10 of [CGSS], on a spanning line system. -/
theorem isRootSet_iff_isStarClosed (S : LineSystem V) (hspan : span ℝ S.Φ = ⊤) :
    IsRootSet S.Φ ↔ S.IsStarClosed :=
  ⟨isStarClosed_of_isRootSet, fun h ↦ h.isRootSet hspan⟩

-- Theorem 3.10
/-- Definition 3.9 and Theorem 3.10 of [CGSS] on the span (`lem:sec3-restrict`): every
star-closed line system gives a root set in its own span. -/
theorem IsStarClosed.isRootSet_restrictSpan (hS : S.IsStarClosed) :
    IsRootSet S.restrictSpan.Φ :=
  ((Iso.restrictSpan S).isStarClosed_iff.mpr hS).isRootSet S.restrictSpan_span_eq_top

-- RS1, for Definition 3.9
/-- RS1, the Mathlib bridge for Definition 3.9 of [CGSS]: a star-closed line system
gives a finite real root pairing on its span, by the direct construction of
`lem:pairing-construction`. -/
noncomputable def IsStarClosed.toRootPairing (hS : S.IsStarClosed) :
    RootPairing S.restrictSpan.Φ ℝ (span ℝ S.Φ) (span ℝ S.Φ) :=
  hS.isRootSet_restrictSpan.toRootPairing

-- RS1, for Definition 3.9
/-- RS1 (`rpccrystal`), applied to the root sets of Definition 3.9 of [CGSS]. -/
instance IsStarClosed.toRootPairing_isCrystallographic (hS : S.IsStarClosed) :
    hS.toRootPairing.IsCrystallographic := inferInstanceAs
      hS.isRootSet_restrictSpan.toRootPairing.IsCrystallographic

-- RS1, for Definition 3.9
/-- RS1 (`rpcreduced`), applied to the root sets of Definition 3.9 of [CGSS]. -/
instance IsStarClosed.toRootPairing_isReduced (hS : S.IsStarClosed) :
    hS.toRootPairing.IsReduced := inferInstanceAs hS.isRootSet_restrictSpan.toRootPairing.IsReduced

-- RS1, for Definition 3.9
/-- RS1 (`rpcrootspan`, `rpccorootspan`), for Definition 3.9 of [CGSS]. -/
instance IsStarClosed.toRootPairing_isRootSystem (hS : S.IsStarClosed) :
    hS.toRootPairing.IsRootSystem := inferInstanceAs
      hS.isRootSet_restrictSpan.toRootPairing.IsRootSystem

-- RS1, for Definition 3.9
/-- RS1 (`rpcirreducible`, `rpcconverse`), for Definition 3.9 of [CGSS]: on a nonempty
star-closed line system, indecomposability agrees with Mathlib irreducibility. -/
theorem IsStarClosed.toRootPairing_isIrreducible_iff (hS : S.IsStarClosed)
    (hne : S.Φ.Nonempty) : hS.toRootPairing.IsIrreducible ↔ S.IsIndecomposable := by
  have hne' : S.restrictSpan.Φ.Nonempty := (Iso.restrictSpan S).nonempty_iff.mpr hne
  rw [show hS.toRootPairing = hS.isRootSet_restrictSpan.toRootPairing from rfl,
    hS.isRootSet_restrictSpan.isIrreducible_iff hne']
  exact (and_iff_right hne').trans (Iso.restrictSpan S).isIndecomposable_iff

end LineSystem

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Φ : Set V} (hΦ : IsRootSet Φ)

-- Theorem 3.10
/-- Theorem 3.10 of [CGSS], its integral-angle argument: roots of squared norm two
have inner products in `{-2, -1, 0, 1, 2}`. -/
theorem inner_mem_of_inner_self_eq_two (hΦ : IsRootSet Φ) (h₂ : ∀ r ∈ Φ, ⟪r, r⟫ = 2)
    {r s : V} (hr : r ∈ Φ) (hs : s ∈ Φ) :
    ⟪r, s⟫ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) := by
  obtain ⟨z, hz⟩ := hΦ.crystallographic r hr s hs
  rw [h₂ r hr] at hz
  have hz' : (z : ℝ) = ⟪r, s⟫ := by linarith [hz]
  have hm : 0 ≤ ⟪r - s, r - s⟫ := real_inner_self_nonneg
  have hp : 0 ≤ ⟪r + s, r + s⟫ := real_inner_self_nonneg
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    h₂ r hr, h₂ s hs, real_inner_comm r s] at hm hp
  have hbounds : (-2 : ℝ) ≤ (z : ℝ) ∧ (z : ℝ) ≤ 2 := by
    constructor <;> nlinarith
  have hbounds' : (-2 : ℤ) ≤ z ∧ z ≤ 2 := by exact_mod_cast hbounds
  obtain ⟨hl, hu⟩ := hbounds'
  rw [← hz']
  interval_cases z <;> norm_num

-- Theorem 3.10
/-- Theorem 3.10 of [CGSS], (i) → (ii), including the angle condition: a root set
of squared norm two gives a line system with the same roots. -/
def toLineSystem (h₂ : ∀ r ∈ Φ, ⟪r, r⟫ = 2) : LineSystem V where
  Φ := Φ
  finite := hΦ.finite
  inner_self := h₂
  neg_mem := fun _ hr ↦ hΦ.neg_mem hr
  inner_mem := fun _ hr _ hs ↦ hΦ.inner_mem_of_inner_self_eq_two h₂ hr hs

-- Theorem 3.10
/-- Theorem 3.10 of [CGSS], (i) → (ii), for the constructed line system. -/
theorem isStarClosed_toLineSystem (h₂ : ∀ r ∈ Φ, ⟪r, r⟫ = 2) :
    (hΦ.toLineSystem h₂).IsStarClosed := LineSystem.isStarClosed_of_isRootSet hΦ

end IsRootSet
