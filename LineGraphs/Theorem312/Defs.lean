/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Log

/-!
# The line predicates for Theorem 3.12 of [CGSS]

Definitions `def:312-angles`, `def:312-root-lines`, `def:312-integral-roots` and
lemmas `lem:312-representatives`, `lem:312-squared-cosine`, `lem:312-coordinates`
of `blueprint/sec3-thm312.tex`. Lines are unbundled submodules: the Section 2
structure `LineSystem` does not permit angles of 45 degrees.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Theorem 3.12
/-- `def:312-angles` for Theorem 3.12 of [CGSS]: a division-free squared cosine. -/
def HasSquaredCosine (ℓ m : Submodule ℝ V) (a : ℝ) : Prop :=
  ∀ x ∈ ℓ, ∀ y ∈ m, ⟪x, y⟫ ^ 2 = a * ⟪x, x⟫ * ⟪y, y⟫

/-- `def:312-angles` for Theorem 3.12 of [CGSS]: angles 90, 60 or 45 degrees. -/
def HasAllowedAngles (S : Set (Submodule ℝ V)) : Prop :=
  ∀ ℓ ∈ S, ∀ m ∈ S, ℓ ≠ m →
    ∃ a ∈ ({0, 1 / 4, 1 / 2} : Set ℝ), HasSquaredCosine ℓ m a

/-- `def:312-angles` for Theorem 3.12 of [CGSS]. Either colour fibre may be empty
(Implicit hypothesis 8); the cross-part condition uses "or" (Error 13, item 3). -/
def HasBipartition (S : Set (Submodule ℝ V)) : Prop :=
  ∃ b : S → Bool, ∀ ℓ m : S, ℓ ≠ m →
    (b ℓ = b m → HasSquaredCosine ℓ.1 m.1 0 ∨ HasSquaredCosine ℓ.1 m.1 (1 / 4)) ∧
    (b ℓ ≠ b m → HasSquaredCosine ℓ.1 m.1 0 ∨ HasSquaredCosine ℓ.1 m.1 (1 / 2))

/-- `def:312-root-lines` for Theorem 3.12 of [CGSS]: the spans of the vectors in `T`. -/
def rootLines (T : Set V) : Set (Submodule ℝ V) :=
  {ℓ | ∃ r ∈ T, ℓ = span ℝ {r}}

/-- `def:312-integral-roots` for Theorem 3.12 of [CGSS]: the explicit set Ψ(T).
The long-root parity condition is against the entire fixed integer span. -/
def integralSpanRoots (T : Set V) : Set V :=
  {x | x ∈ span ℤ T ∧ (⟪x, x⟫ = 2 ∨
    (⟪x, x⟫ = 4 ∧ ∀ y ∈ span ℤ T, ∃ z : ℤ, ⟪x, y⟫ = 2 * z))}

/-- `t312repPositive`--`t312repNorm` of `lem:312-representatives`, Theorem 3.12
of [CGSS]: a nonzero vector on a line can be given any positive squared norm. -/
theorem exists_mem_line_sqNorm_eq {ℓ : Submodule ℝ V} {r : V}
    (hr : r ∈ ℓ) (hr0 : r ≠ 0) {h : ℝ} (hh : 0 < h) :
    ∃ t ∈ ℓ, ⟪t, t⟫ = h := by
  have hq : 0 < ⟪r, r⟫ := real_inner_self_pos.mpr hr0
  refine ⟨(Real.sqrt h / Real.sqrt ⟪r, r⟫) • r, ℓ.smul_mem _ hr, ?_⟩
  rw [real_inner_smul_left, real_inner_smul_right]
  have hs := Real.sq_sqrt hh.le
  have ht := Real.sq_sqrt hq.le
  have hn : Real.sqrt ⟪r, r⟫ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  field_simp
  nlinarith

/-- The nonzero-generator step of `lem:312-finite` and `lem:312-seeds`,
Theorem 3.12 of [CGSS]. -/
theorem exists_ne_zero_mem_line {ℓ : Submodule ℝ V} (hℓ : Module.finrank ℝ ℓ = 1) :
    ∃ r ∈ ℓ, r ≠ (0 : V) := by
  obtain ⟨r, hr, -⟩ := (finrank_eq_one_iff'.mp hℓ)
  exact ⟨r, r.property, fun h ↦ hr (Subtype.ext h)⟩

/-- `t312repForward` and `t312repReverse` of `lem:312-squared-cosine`,
Theorem 3.12 of [CGSS]: it suffices to check nonzero representatives. -/
theorem hasSquaredCosine_iff {ℓ m : Submodule ℝ V} {r s : V} {a : ℝ}
    (hℓ : Module.finrank ℝ ℓ = 1) (hm : Module.finrank ℝ m = 1)
    (hr : r ∈ ℓ) (hr0 : r ≠ 0) (hs : s ∈ m) (hs0 : s ≠ 0) :
    HasSquaredCosine ℓ m a ↔ ⟪r, s⟫ ^ 2 = a * ⟪r, r⟫ * ⟪s, s⟫ := by
  refine ⟨fun h ↦ h r hr s hs, ?_⟩
  intro h x hx y hy
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hℓ hr hr0] at hx
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hm hs hs0] at hy
  obtain ⟨u, rfl⟩ := mem_span_singleton.mp hx
  obtain ⟨v, rfl⟩ := mem_span_singleton.mp hy
  simp only [real_inner_smul_left, real_inner_smul_right]
  calc
    (v * (u * ⟪r, s⟫)) ^ 2 = u ^ 2 * v ^ 2 * ⟪r, s⟫ ^ 2 := by ring
    _ = a * (u * (u * ⟪r, r⟫)) * (v * (v * ⟪s, s⟫)) := by rw [h]; ring

/-- `t312repUnique` of `lem:312-squared-cosine`, Theorem 3.12 of [CGSS]. -/
theorem HasSquaredCosine.unique {ℓ m : Submodule ℝ V} {a a' : ℝ}
    (h : HasSquaredCosine ℓ m a) (h' : HasSquaredCosine ℓ m a')
    (hℓ : Module.finrank ℝ ℓ = 1) (hm : Module.finrank ℝ m = 1) : a = a' := by
  obtain ⟨r, hr, hr0⟩ := exists_ne_zero_mem_line hℓ
  obtain ⟨s, hs, hs0⟩ := exists_ne_zero_mem_line hm
  have hp := mul_pos (real_inner_self_pos.mpr hr0) (real_inner_self_pos.mpr hs0)
  have he := (h r hr s hs).symm.trans (h' r hr s hs)
  nlinarith

/-- `t312coordBasis`--`t312coordSelf` of `lem:312-coordinates`, Theorem 3.12
of [CGSS]: inner products with a spanning family determine a vector in its span. -/
theorem inner_coordinates_injective {I : Type*} (b : I → V)
    {W : Submodule ℝ V} (hb : span ℝ (Set.range b) = W) :
    Set.InjOn (fun x ↦ fun i ↦ ⟪x, b i⟫) W := by
  intro x hx y hy hxy
  have hz : ∀ z ∈ W, ⟪x - y, z⟫ = 0 := by
    rw [← hb]
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      simp only [inner_sub_left, congr_fun hxy i, sub_self]
    | zero => simp
    | add u v hu hv hu' hv' => simp [inner_add_right, hu', hv']
    | smul a u hu hu' => simp [real_inner_smul_right, hu']
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (hz (x - y) (W.sub_mem hx hy)))

/-- `t312seedsAllowed` of `lem:312-seeds`, Theorem 3.12 of [CGSS]. -/
theorem HasBipartition.hasAllowedAngles {S : Set (Submodule ℝ V)}
    (hS : HasBipartition S) : HasAllowedAngles S := by
  obtain ⟨b, hb⟩ := hS
  intro ℓ hℓ m hm hne
  have hp := hb ⟨ℓ, hℓ⟩ ⟨m, hm⟩ (fun h ↦ hne (congrArg Subtype.val h))
  by_cases he : b ⟨ℓ, hℓ⟩ = b ⟨m, hm⟩
  · rcases hp.1 he with h | h
    · exact ⟨0, by simp, h⟩
    · exact ⟨1 / 4, by simp, h⟩
  · rcases hp.2 he with h | h
    · exact ⟨0, by simp, h⟩
    · exact ⟨1 / 2, by simp, h⟩

end LineSystem
