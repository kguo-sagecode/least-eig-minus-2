/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Theorem312.Defs

/-!
# Finiteness of the lines in Theorem 3.12 of [CGSS]

The proof of `lem:312-finite` encodes unit representatives by their inner products
with a finite spanning family chosen from those representatives.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The finite-coordinate argument `t312finiteU` and `t312intFinite` for
Theorem 3.12 of [CGSS], using `lem:312-coordinates`. -/
theorem finite_of_inner_mem_finite {I : Type*} [Finite I] (b : I → V)
    {U : Set V} (hU : U ⊆ span ℝ (Set.range b)) {Θ : Set ℝ} (hΘ : Θ.Finite)
    (hp : ∀ x ∈ U, ∀ i, ⟪x, b i⟫ ∈ Θ) : U.Finite := by
  apply Set.Finite.of_injOn (f := fun x i ↦ ⟪x, b i⟫)
    (t := {a : I → ℝ | ∀ i, a i ∈ Θ})
  · exact hp
  · exact (inner_coordinates_injective b rfl).mono hU
  · exact Set.Finite.pi' (fun _ ↦ hΘ)

/-- `t312finiteSame` and `t312finiteDistinct` of `lem:312-finite`,
Theorem 3.12 of [CGSS]: the seven possible products of unit representatives. -/
private theorem inner_unit_mem_seven {S : Set (Submodule ℝ V)}
    (hline : ∀ ℓ ∈ S, Module.finrank ℝ ℓ = 1) (hangle : HasAllowedAngles S)
    {ℓ m : Submodule ℝ V} (hℓ : ℓ ∈ S) (hm : m ∈ S)
    {x y : V} (hx : x ∈ ℓ) (hy : y ∈ m) (hxx : ⟪x, x⟫ = 1)
    (hyy : ⟪y, y⟫ = 1) :
    ⟪x, y⟫ ∈ ({0, 1, -1, 1 / 2, -(1 / 2),
      Real.sqrt (1 / 2), -Real.sqrt (1 / 2)} : Set ℝ) := by
  have hsq : ⟪x, y⟫ ^ 2 = 1 ∨ ⟪x, y⟫ ^ 2 = 0 ∨
      ⟪x, y⟫ ^ 2 = 1 / 4 ∨ ⟪x, y⟫ ^ 2 = 1 / 2 := by
    by_cases he : ℓ = m
    · subst m
      have hx0 : x ≠ 0 := by intro h; simp [h] at hxx
      have hc : HasSquaredCosine ℓ ℓ 1 :=
        (hasSquaredCosine_iff (hline ℓ hℓ) (hline ℓ hℓ) hx hx0 hx hx0).mpr (by ring)
      exact Or.inl (by simpa only [hxx, hyy, mul_one] using hc x hx y hy)
    · obtain ⟨a, ha, hc⟩ := hangle ℓ hℓ m hm he
      have hc' : ⟪x, y⟫ ^ 2 = a := by
        simpa only [hxx, hyy, mul_one] using hc x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      exact Or.inr (hc' ▸ ha)
  have hsqrt : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  rcases hsq with h | h | h | h
  · have he : ⟪x, y⟫ = 1 ∨ ⟪x, y⟫ = -1 := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      simpa using h
    rcases he with he | he <;> simp [he]
  · have he : ⟪x, y⟫ = 0 := sq_eq_zero_iff.mp h
    simp [he]
  · have he : ⟪x, y⟫ = 1 / 2 ∨ ⟪x, y⟫ = -(1 / 2) := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      nlinarith
    rcases he with he | he <;> simp [he]
  · have he := sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans hsqrt.symm)
    rcases he with he | he <;> simp [he]

-- Theorem 3.12
/-- `lem:312-finite` for Theorem 3.12 of [CGSS]. Finiteness is derived from
finite dimension and the three allowed squared cosines; no spanning or
nonemptiness hypothesis is imposed. -/
theorem finite_of_hasAllowedAngles [FiniteDimensional ℝ V] {S : Set (Submodule ℝ V)}
    (hline : ∀ ℓ ∈ S, Module.finrank ℝ ℓ = 1) (hangle : HasAllowedAngles S) :
    S.Finite := by
  classical
  let U : Set V := {x | ∃ ℓ ∈ S, x ∈ ℓ ∧ ⟪x, x⟫ = 1}
  -- `t312finiteBasis`: the empty span is allowed.
  obtain ⟨B, hBU, hspan, hB⟩ := exists_linearIndependent ℝ U
  have : Finite B := hB.finite
  have hU : U.Finite := by
    refine finite_of_inner_mem_finite (fun b : B ↦ (b : V))
      (Θ := {0, 1, -1, 1 / 2, -(1 / 2), Real.sqrt (1 / 2), -Real.sqrt (1 / 2)})
      ?_ (Set.toFinite _) ?_
    · simpa only [Subtype.range_coe, hspan] using (subset_span : U ⊆ span ℝ U)
    · intro x hx b
      obtain ⟨ℓ, hℓ, hxℓ, hxx⟩ := hx
      obtain ⟨m, hm, hbm, hbb⟩ := hBU b.property
      exact inner_unit_mem_seven hline hangle hℓ hm hxℓ hbm hxx hbb
  -- `t312finiteImage` and `t312finiteSurj` identify the image with the original lines.
  have himage : (fun x : V ↦ span ℝ {x}) '' U = S := by
    ext ℓ
    constructor
    · rintro ⟨x, ⟨m, hm, hxm, hxx⟩, rfl⟩
      have hx0 : x ≠ 0 := by intro h; simp [h] at hxx
      change span ℝ {x} ∈ S
      rwa [← eq_span_singleton_of_mem_of_finrank_eq_one (hline m hm) hxm hx0]
    · intro hℓ
      obtain ⟨r, hr, hr0⟩ := exists_ne_zero_mem_line (hline ℓ hℓ)
      obtain ⟨x, hx, hxx⟩ := exists_mem_line_sqNorm_eq hr hr0 (by norm_num : (0 : ℝ) < 1)
      have hx0 : x ≠ 0 := by intro h; simp [h] at hxx
      exact ⟨x, ⟨ℓ, hℓ, hx, hxx⟩,
        (eq_span_singleton_of_mem_of_finrank_eq_one (hline ℓ hℓ) hx hx0).symm⟩
  rw [← himage]
  exact hU.image _

end LineSystem
