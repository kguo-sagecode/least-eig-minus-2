/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Projectors
import LineGraphs.RootSetClassification.Components

/-!
# The frame operator on all roots

Steps `rfrcommute`--`rfrvalue` of `lem:tight-frame` in Remark 3.11 of [CGSS].
The sum here contains both signs of every root. The line frame is half this
operator, proved by reindexing in `LineFrame`.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ : Set V}

/-- Step `rfrdimension`: an indecomposable root set has positive ambient dimension. -/
theorem finrank_pos_of_isIndecomposable (hΦ : IsRootSet Φ) (hI : hΦ.IsIndecomposable) :
    0 < Module.finrank ℝ V := by
  let := hΦ.finiteDimensional
  obtain ⟨r, hr⟩ := hI.1
  let : Nontrivial V := ⟨⟨r, 0, hΦ.ne_zero hr⟩⟩
  exact Module.finrank_pos

variable [Fintype Φ] (hΦ : IsRootSet Φ)

/-- The sum of unit projectors on all roots, used to prove `lem:tight-frame`. -/
noncomputable def rootFrame (_hΦ : IsRootSet Φ) : Module.End ℝ V :=
  ∑ r : Φ, rootProjector (r : V)

/-- Step `rfrsign`: the frame operator is symmetric. -/
theorem rootFrame_symmetric (x y : V) : ⟪hΦ.rootFrame x, y⟫ = ⟪x, hΦ.rootFrame y⟫ := by
  simp only [rootFrame, LinearMap.sum_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun r _ ↦ lineProjector_symmetric (normalizedRoot (r : V)) x y

/-- Steps `rfrpermute`, `rfrconjugation`: reindexing by a root reflection shows
that it commutes with the frame operator. -/
theorem rootFrame_reflection (r : Φ) (x : V) :
    hΦ.rootFrame (reflection (r : V) (hΦ.ne_zero r.property) x) =
      reflection (r : V) (hΦ.ne_zero r.property) (hΦ.rootFrame x) := by
  let f := reflection (r : V) (hΦ.ne_zero r.property)
  change (∑ s : Φ, rootProjector (s : V)) (f x) = f ((∑ s : Φ, rootProjector (s : V)) x)
  simp only [LinearMap.sum_apply]
  calc
    (∑ s : Φ, rootProjector (s : V) (f x)) =
        ∑ s : Φ, rootProjector ((hΦ.reflectionPerm r s : Φ) : V) (f x) :=
      ((hΦ.reflectionPerm r).sum_comp (fun s : Φ ↦ rootProjector (s : V) (f x))).symm
    _ = ∑ s : Φ, f (rootProjector (s : V) x) := by
      apply Finset.sum_congr rfl
      intro s _
      exact rootProjector_isometry f s x
    _ = _ := (map_sum f _ _).symm

/-- Steps `rfrminus`, `rfreigen`: each root is an eigenvector of the frame. -/
theorem rootFrame_root (r : Φ) :
    hΦ.rootFrame (r : V) =
      (⟪(r : V), hΦ.rootFrame (r : V)⟫ / ⟪(r : V), (r : V)⟫) • (r : V) := by
  have he := hΦ.rootFrame_reflection r (r : V)
  rw [reflection_self, map_neg, reflection_apply] at he
  apply sub_eq_zero.mp
  calc
    hΦ.rootFrame (r : V) -
        (⟪(r : V), hΦ.rootFrame (r : V)⟫ / ⟪(r : V), (r : V)⟫) • (r : V) =
      (1 / 2 : ℝ) • (hΦ.rootFrame (r : V) -
        (2 * ⟪(r : V), hΦ.rootFrame (r : V)⟫ / ⟪(r : V), (r : V)⟫) • (r : V)) +
        (1 / 2 : ℝ) • hΦ.rootFrame (r : V) := by module
    _ = 0 := by rw [← he]; module

/-- Steps `rfredge`--`rfrscalar`: symmetry and connectedness give one eigenvalue
on all roots, and spanning extends it to the entire ambient space. -/
theorem rootFrame_eq_scalar (hI : hΦ.IsIndecomposable) :
    ∃ c : ℝ, hΦ.rootFrame = c • LinearMap.id := by
  let μ : Φ → ℝ := fun r ↦ ⟪(r : V), hΦ.rootFrame (r : V)⟫ / ⟪(r : V), (r : V)⟫
  have he (r : Φ) : hΦ.rootFrame (r : V) = μ r • (r : V) := hΦ.rootFrame_root r
  have hedge : ∀ ⦃r s⦄, (rootGraph Φ).Adj r s → μ r = μ s := by
    intro r s hrs
    have h := hΦ.rootFrame_symmetric r s
    rw [he r, he s, real_inner_smul_left, real_inner_smul_right] at h
    exact mul_right_cancel₀ hrs.2 h
  obtain ⟨c, hc⟩ := (hΦ.isIndecomposable_iff_connected.mp hI).exists_constant_of_edge_eq hedge
  refine ⟨c, LinearMap.ext fun x ↦ ?_⟩
  change hΦ.rootFrame x = c • x
  have hx : x ∈ span ℝ Φ := hΦ.span_eq_top ▸ mem_top
  induction hx using span_induction with
  | mem x hx => simpa only [hc] using he ⟨x, hx⟩
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]
  | smul a x _ hx => simp only [map_smul, hx, smul_smul, mul_comm]

/-- Step `rfrtrace`: each oriented root contributes trace one. -/
theorem trace_rootFrame : LinearMap.trace ℝ V hΦ.rootFrame = Fintype.card Φ := by
  let := hΦ.finiteDimensional
  simp only [rootFrame, map_sum]
  simp only [trace_rootProjector (hΦ.ne_zero (Subtype.property _)), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Step `rfrvalue`: the trace identifies the scalar of the full root frame. -/
theorem rootFrame_eq_smul_id (hI : hΦ.IsIndecomposable) :
    hΦ.rootFrame = ((Fintype.card Φ : ℝ) / Module.finrank ℝ V) • LinearMap.id := by
  let := hΦ.finiteDimensional
  obtain ⟨c, hc⟩ := hΦ.rootFrame_eq_scalar hI
  have he := congrArg (LinearMap.trace ℝ V) hc
  rw [hΦ.trace_rootFrame, map_smul, LinearMap.trace_id, smul_eq_mul] at he
  have hn : (Module.finrank ℝ V : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hΦ.finrank_pos_of_isIndecomposable hI))
  have hval : c = (Fintype.card Φ : ℝ) / Module.finrank ℝ V :=
    (eq_div_iff hn).mpr he.symm
  rw [hc, hval]

end IsRootSet
