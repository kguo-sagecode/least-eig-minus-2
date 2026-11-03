/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.Defs
import Mathlib.LinearAlgebra.Trace

/-!
# Orthogonal line projectors

`lem:rem-projectors` of the blueprint for Remark 3.11 of [CGSS]. The
rank-one formula proves sign independence, symmetry, unit trace, and
conjugation by an orthogonal linear equivalence.
-/

open scoped RealInnerProductSpace

namespace IsRootSet

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The rank-one formula in `lem:rem-projectors` of Remark 3.11; for a unit vector
this is the orthogonal projection onto its line. -/
noncomputable def lineProjector (v : V) : Module.End ℝ V := (innerₗ V v).smulRight v

/-- The projector formula used in `rprsign`--`rprconjugate`. -/
@[simp] theorem lineProjector_apply (v x : V) : lineProjector v x = ⟪v, x⟫ • v := rfl

/-- Step `rprsign`: a sign change leaves the line projector unchanged. -/
@[simp] theorem lineProjector_neg (v : V) : lineProjector (-v) = lineProjector v := by
  ext x
  simp

/-- Step `rprsymmetry`: line projectors are symmetric. -/
theorem lineProjector_symmetric (v x y : V) :
    ⟪lineProjector v x, y⟫ = ⟪x, lineProjector v y⟫ := by
  simp only [lineProjector_apply, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x v]
  ring

/-- Step `rprtrace`: the trace of a rank-one projector is the squared norm. -/
theorem trace_lineProjector [FiniteDimensional ℝ V] (v : V) :
    LinearMap.trace ℝ V (lineProjector v) = ⟪v, v⟫ :=
  LinearMap.trace_smulRight _ _

/-- Step `rprconjugate`, evaluated on a vector. -/
theorem lineProjector_isometry (f : V ≃ₗᵢ[ℝ] W) (v x : V) :
    lineProjector (f v) (f x) = f (lineProjector v x) := by
  simp only [lineProjector_apply, LinearIsometryEquiv.inner_map_map, map_smul]

/-- Step `rprconjugate`: orthogonal conjugation sends a line projector to the
projector of the image line. -/
theorem lineProjector_conjugate (f : V ≃ₗᵢ[ℝ] W) (v : V) :
    f.toLinearMap ∘ₗ lineProjector v ∘ₗ f.symm.toLinearMap = lineProjector (f v) := by
  ext x
  simpa using (lineProjector_isometry f v (f.symm x)).symm

-- Remark 3.11, lem:rem-projectors
/-- The four identities in `lem:rem-projectors` of Remark 3.11 of [CGSS]. -/
theorem lineProjector_identities [FiniteDimensional ℝ V] {v : V} (hv : ‖v‖ = 1) :
    lineProjector (-v) = lineProjector v ∧
    (∀ x y, ⟪lineProjector v x, y⟫ = ⟪x, lineProjector v y⟫) ∧
    LinearMap.trace ℝ V (lineProjector v) = 1 ∧
    ∀ f : V ≃ₗᵢ[ℝ] V,
      f.toLinearMap ∘ₗ lineProjector v ∘ₗ f.symm.toLinearMap = lineProjector (f v) := by
  refine ⟨lineProjector_neg v, lineProjector_symmetric v, ?_, fun f ↦ lineProjector_conjugate f v⟩
  rw [trace_lineProjector, real_inner_self_eq_norm_sq, hv, one_pow]

/-- Normalization to unit length in step `rfrsign`, used for Theorem C of the blueprint for Remark
3.11 of [CGSS]. -/
noncomputable def normalizedRoot (r : V) : V := ‖r‖⁻¹ • r

/-- Nonzero roots normalize to unit vectors (`rfrsign`). -/
theorem norm_normalizedRoot {r : V} (hr : r ≠ 0) : ‖normalizedRoot r‖ = 1 := by
  simp [normalizedRoot, norm_smul, hr]

/-- Changing the sign of a root changes its normalized vector by the same sign (`rfrsign`). -/
@[simp] theorem normalizedRoot_neg (r : V) : normalizedRoot (-r) = -normalizedRoot r := by
  simp [normalizedRoot]

/-- Normalization commutes with orthogonal maps (`rfrpermute`). -/
theorem normalizedRoot_isometry (f : V ≃ₗᵢ[ℝ] W) (r : V) :
    normalizedRoot (f r) = f (normalizedRoot r) := by
  simp [normalizedRoot]

/-- A unit-trace projector defined from an arbitrary nonzero root (`rfrconjugation`). -/
noncomputable def rootProjector (r : V) : Module.End ℝ V := lineProjector (normalizedRoot r)

/-- Root projectors are independent of signs (`rfrsign`). -/
@[simp] theorem rootProjector_neg (r : V) : rootProjector (-r) = rootProjector r := by
  simp [rootProjector]

/-- Orthogonal maps transport root projectors (`rfrconjugation`). -/
theorem rootProjector_isometry (f : V ≃ₗᵢ[ℝ] W) (r x : V) :
    rootProjector (f r) (f x) = f (rootProjector r x) := by
  rw [rootProjector, rootProjector, normalizedRoot_isometry, lineProjector_isometry]

/-- Each root contributes trace one to the frame (`rfrtrace`). -/
theorem trace_rootProjector [FiniteDimensional ℝ V] {r : V} (hr : r ≠ 0) :
    LinearMap.trace ℝ V (rootProjector r) = 1 := by
  rw [rootProjector, trace_lineProjector, real_inner_self_eq_norm_sq, norm_normalizedRoot hr,
    one_pow]

end IsRootSet
