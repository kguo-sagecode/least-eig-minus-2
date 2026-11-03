/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.E8Criterion
import LineGraphs.Exceptional.ExtensionGraph
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Extending a representation by a vector of norm at most two

The geometric construction in the converse of `lem:extension` (Lemma 3.4) of [Exc].
-/

open Matrix Module Submodule
open scoped RealInnerProductSpace

namespace SimpleGraph

variable {V E : Type*} [Finite V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

open Classical in
-- Lemma 3.4 [Exc]
/-- The converse construction in `lem:extension` (Lemma 3.4) of [Exc]: add an
orthogonal coordinate if the prescribed vector has squared norm below two. At ambient
dimension eight, squared norm two is required. -/
theorem IsRepresentation.isRepresentedIn_adjoinVertex_of_norm_le
    (hx : X.IsRepresentation x) (hX : X.Connected) {N : Set V} (hN : N.Nonempty)
    (p : E) (hn : ∀ u, ⟪p, x u⟫ = if u ∈ N then 1 else 0)
    (hp : ⟪p, p⟫ ≤ 2) (hd : finrank ℝ E ≤ 8)
    (he : finrank ℝ E = 8 → ⟪p, p⟫ = 2) :
    (X.adjoinVertex N).IsRepresentedIn LineSystem.E₈ := by
  classical
  let := Fintype.ofFinite V
  apply (isRepresentedIn_E₈_iff_posSemidef_and_rank_le (hX.adjoinVertex X N hN)).mpr
  by_cases hr : finrank ℝ E = 8
  · have hy := hx.adjoinVertex X N p (he hr) hn
    refine ⟨hy.posSemidef _, ?_⟩
    rw [hy.rank_two_add_adjMatrix]
    exact (Submodule.finrank_le _).trans hd
  · let g : V → WithLp 2 (E × ℝ) := fun u => WithLp.toLp 2 (x u, 0)
    have hg : X.IsRepresentation g := by
      apply isRepresentation_iff.mpr
      intro u v
      change ⟪x u, x v⟫ + ⟪(0 : ℝ), 0⟫ = _
      simpa using isRepresentation_iff.mp hx u v
    let z : WithLp 2 (E × ℝ) := WithLp.toLp 2 (p, Real.sqrt (2 - ⟪p, p⟫))
    have hz : ⟪z, z⟫ = 2 := by
      change ⟪p, p⟫ + Real.sqrt (2 - ⟪p, p⟫) * Real.sqrt (2 - ⟪p, p⟫) = 2
      rw [Real.mul_self_sqrt (sub_nonneg.mpr hp)]
      ring
    have hzn : ∀ u, ⟪z, g u⟫ = if u ∈ N then 1 else 0 := by
      intro u
      change ⟪p, x u⟫ + (0 : ℝ) * Real.sqrt (2 - ⟪p, p⟫) = _
      simpa using hn u
    have hy := hg.adjoinVertex X N z hz hzn
    refine ⟨hy.posSemidef _, ?_⟩
    rw [hy.rank_two_add_adjMatrix]
    refine (Submodule.finrank_le _).trans ?_
    rw [(WithLp.linearEquiv 2 ℝ (E × ℝ)).finrank_eq, Module.finrank_prod,
      Module.finrank_self]
    omega

end SimpleGraph
