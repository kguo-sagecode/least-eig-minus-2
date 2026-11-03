/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Hyp24
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Reflections in roots and the transport of Hypothesis 2.4

A star-closed line system is preserved by the reflection in each of its vectors (the first step
of LN5 in `cgss/prerequisites.md`). An isometry that preserves `Φ` and carries one ordered star to
another carries `Γa`, `Δ` and the orthogonality graph of the first star to those of the second.
With a finite certificate that the reflections act transitively on ordered stars
(`Computations/C4E8Stars.lean` and its analogues), this gives the exceptional rows of
computation C4 for every ordered star.

## Main definitions

* `LineSystem.isometryGroup S`: the linear isometries `g` of `V` with `g x ∈ Φ ↔ x ∈ Φ`.
* `LineSystem.rootReflection v hv`: the reflection `x ↦ x - ⟪v, x⟫ • v` for `⟪v, v⟫ = 2`.
* `LineSystem.Hyp24.ΓaEquivOfIsometry`, `ΔEquivOfIsometry`, `orthGraphIsoOfIsometry`.

## Main statements

* `LineSystem.rootReflection_mem_isometryGroup`: reflections in roots of a star-closed system
  preserve it.
-/

open scoped RealInnerProductSpace

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The linear isometries of `V` that map `Φ` onto itself. -/
def isometryGroup (S : LineSystem V) : Subgroup (V ≃ₗᵢ[ℝ] V) where
  carrier := {g | ∀ x, g x ∈ S.Φ ↔ x ∈ S.Φ}
  mul_mem' {g h} hg hh x := by
    change g (h x) ∈ S.Φ ↔ x ∈ S.Φ
    rw [hg, hh]
  one_mem' x := Iff.rfl
  inv_mem' {g} hg x := by
    change g.symm x ∈ S.Φ ↔ x ∈ S.Φ
    rw [← hg (g.symm x), LinearIsometryEquiv.apply_symm_apply]

theorem mem_isometryGroup_iff (S : LineSystem V) (g : V ≃ₗᵢ[ℝ] V) :
    g ∈ S.isometryGroup ↔ ∀ x, g x ∈ S.Φ ↔ x ∈ S.Φ := Iff.rfl

/-- The linear map `x ↦ x - ⟪v, x⟫ • v`. -/
def rootReflectionMap (v : V) : V →ₗ[ℝ] V where
  toFun x := x - ⟪v, x⟫ • v
  map_add' x y := by rw [inner_add_right, add_smul]; abel
  map_smul' c x := by
    rw [real_inner_smul_right, smul_sub, mul_smul]
    rfl

theorem rootReflectionMap_involutive (v : V) (hv : ⟪v, v⟫ = 2) :
    Function.Involutive (rootReflectionMap v) := by
  intro x
  change (x - ⟪v, x⟫ • v) - ⟪v, x - ⟪v, x⟫ • v⟫ • v = x
  rw [inner_sub_right, real_inner_smul_right, hv]
  module

/-- The reflection in a vector `v` of squared norm 2: `x ↦ x - ⟪v, x⟫ • v`. -/
noncomputable def rootReflection (v : V) (hv : ⟪v, v⟫ = 2) : V ≃ₗᵢ[ℝ] V :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofInvolutive (rootReflectionMap v) (rootReflectionMap_involutive v hv))
    (by
      intro x y
      change ⟪x - ⟪v, x⟫ • v, y - ⟪v, y⟫ • v⟫ = ⟪x, y⟫
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        hv, real_inner_comm v x]
      ring)

@[simp] theorem rootReflection_apply (v : V) (hv : ⟪v, v⟫ = 2) (x : V) :
    rootReflection v hv x = x - ⟪v, x⟫ • v := rfl

/-- A reflection fixes the vectors orthogonal to its root. -/
theorem rootReflection_apply_of_inner_eq_zero (v : V) (hv : ⟪v, v⟫ = 2) {x : V}
    (hx : ⟪v, x⟫ = 0) : rootReflection v hv x = x := by
  simp [hx]

/-- LN5, first step: the reflection in a root of a star-closed line system preserves it. -/
theorem rootReflection_mem_isometryGroup {S : LineSystem V} (hS : S.IsStarClosed) {v : V}
    (hv : v ∈ S.Φ) : rootReflection v (S.inner_self v hv) ∈ S.isometryGroup := by
  have forward (x : V) (hx : x ∈ S.Φ) : rootReflection v (S.inner_self v hv) x ∈ S.Φ := by
    rw [rootReflection_apply]
    rcases S.inner_mem v hv x hx with h | h | h | h | h
    · rw [h, (S.inner_eq_neg_two_iff hv hx).mp h]
      convert S.neg_mem x hx using 1
      module
    · rw [h, neg_one_smul, sub_neg_eq_add]
      exact hS x hx v hv (by rw [real_inner_comm]; exact h)
    · rw [h, zero_smul, sub_zero]
      exact hx
    · rw [h, one_smul, sub_eq_add_neg]
      exact hS x hx (-v) (S.neg_mem v hv) (by rw [inner_neg_right, real_inner_comm, h])
    · rw [h, (S.inner_eq_two_iff hv hx).mp h]
      convert S.neg_mem x hx using 1
      module
  intro x
  refine ⟨fun h => ?_, forward x⟩
  have := forward _ h
  rwa [← LinearIsometryEquiv.trans_apply,
    show (rootReflection v (S.inner_self v hv)).trans (rootReflection v (S.inner_self v hv)) =
      LinearIsometryEquiv.refl ℝ V from
        LinearIsometryEquiv.ext (rootReflectionMap_involutive v (S.inner_self v hv))] at this

namespace Hyp24

variable (H H' : Hyp24 V) (g : V ≃ₗᵢ[ℝ] V) (hΦ : ∀ x, g x ∈ H'.S.Φ ↔ x ∈ H.S.Φ)
  (ha : g H.a = H'.a) (hb : g H.b = H'.b)

include ha hb in
theorem map_c_of_isometry : g H.c = H'.c := by
  simp only [Hyp24.c, map_sub, map_neg, ha, hb]

include hΦ ha hb in
theorem map_mem_Γa_iff_of_isometry (x : V) : g x ∈ H'.Γa ↔ x ∈ H.Γa := by
  simp only [Hyp24.mem_Γa_iff, hΦ, ← ha, ← hb, ← map_c_of_isometry H H' g ha hb,
    LinearIsometryEquiv.inner_map_map]

include hΦ ha hb in
theorem map_mem_Δ_iff_of_isometry (x : V) : g x ∈ H'.Δ ↔ x ∈ H.Δ := by
  simp only [Hyp24.mem_Δ_iff, hΦ, ← ha, ← hb, ← map_c_of_isometry H H' g ha hb,
    LinearIsometryEquiv.inner_map_map]

/-- An isometry carrying one ordered star to another identifies the two sets `Γa`. -/
def ΓaEquivOfIsometry : H.Γa ≃ H'.Γa where
  toFun x := ⟨g x, (map_mem_Γa_iff_of_isometry H H' g hΦ ha hb x).mpr x.2⟩
  invFun y := ⟨g.symm y, (map_mem_Γa_iff_of_isometry H H' g hΦ ha hb _).mp (by simp [y.2])⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-- An isometry carrying one ordered star to another identifies the two sets `Δ`. -/
def ΔEquivOfIsometry : H.Δ ≃ H'.Δ where
  toFun x := ⟨g x, (map_mem_Δ_iff_of_isometry H H' g hΦ ha hb x).mpr x.2⟩
  invFun y := ⟨g.symm y, (map_mem_Δ_iff_of_isometry H H' g hΦ ha hb _).mp (by simp [y.2])⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-- An isometry carrying one ordered star to another identifies the orthogonality graphs. -/
def orthGraphIsoOfIsometry : H.orthGraph ≃g H'.orthGraph where
  toEquiv := ΓaEquivOfIsometry H H' g hΦ ha hb
  map_rel_iff' {x y} := by
    change ⟪g x, g y⟫ = 0 ↔ ⟪(x : V), y⟫ = 0
    rw [LinearIsometryEquiv.inner_map_map]

include hΦ ha hb in
theorem ncard_Γa_eq_of_isometry : H'.Γa.ncard = H.Γa.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr (ΓaEquivOfIsometry H H' g hΦ ha hb)]

include hΦ ha hb in
theorem ncard_Δ_eq_of_isometry : H'.Δ.ncard = H.Δ.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr (ΔEquivOfIsometry H H' g hΦ ha hb)]

end Hyp24

end LineSystem
