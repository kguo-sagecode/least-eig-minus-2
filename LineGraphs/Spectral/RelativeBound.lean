/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Basic
import LineGraphs.Computations.C20Classical
import LineGraphs.LineSystem.RootType
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The cone construction for EQ2

The cone and root-neighborhood counting steps of blueprint Lemma `lem:4-EQ2`, used in
Theorem 4.4 and its following remark in [CGSS]. The generic relative bound in `Frames`
does not imply EQ2. The remaining step `s4eq2type` requires the classification and
representation-transfer interface of `lem:4-rootsystem`.
-/

open Module Submodule
open scoped RealInnerProductSpace

namespace InnerProductSpace

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cone in step `s4eq2ip` of EQ2, for Theorem 4.4 of [CGSS]: `none` is its apex. -/
noncomputable def equiangularCone (v : ι → E) : Option ι → WithLp 2 (E × ℝ)
  | none => WithLp.toLp 2 (0, Real.sqrt 2)
  | some i => WithLp.toLp 2 (Real.sqrt (3 / 2) • v i, 1 / Real.sqrt 2)

/-- Step `s4eq2ip` of EQ2, for Theorem 4.4 of [CGSS]: the apex has squared norm two. -/
theorem inner_equiangularCone_none (v : ι → E) :
    ⟪equiangularCone v none, equiangularCone v none⟫ = 2 := by
  simp [equiangularCone]

/-- Step `s4eq2ip` of EQ2, for Theorem 4.4 of [CGSS]: each cone vector meets the apex
with inner product one. -/
theorem inner_equiangularCone_some_none (v : ι → E) (i : ι) :
    ⟪equiangularCone v (some i), equiangularCone v none⟫ = 1 := by
  simp [equiangularCone, Real.sqrt_ne_zero'.mpr (show (0 : ℝ) < 2 by norm_num)]

/-- Step `s4eq2ip` of EQ2, for Theorem 4.4 of [CGSS]: the cone changes inner products
by the affine function `t ↦ 3t/2 + 1/2`. -/
theorem inner_equiangularCone_some_some (v : ι → E) (i j : ι) :
    ⟪equiangularCone v (some i), equiangularCone v (some j)⟫ =
      (3 / 2 : ℝ) * ⟪v i, v j⟫ + 1 / 2 := by
  simp only [equiangularCone, WithLp.prod_inner_apply,
    real_inner_smul_left, real_inner_smul_right, RCLike.inner_apply, conj_trivial,
    div_mul_div_comm]
  rw [← mul_assoc, Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 / 2 by norm_num),
    Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num

/-- Step `s4eq2ip` of EQ2, for Theorem 4.4 of [CGSS]: unit vectors give roots of
squared norm two on the cone. -/
theorem inner_equiangularCone_self (v : ι → E) (hv : ∀ i, ‖v i‖ = 1) (a : Option ι) :
    ⟪equiangularCone v a, equiangularCone v a⟫ = 2 := by
  cases a with
  | none => exact inner_equiangularCone_none v
  | some i => rw [inner_equiangularCone_some_some, real_inner_self_eq_norm_sq, hv i]; norm_num

/-- Step `s4eq2rep` of EQ2, for Theorem 4.4 of [CGSS]: the cone spans the orthogonal
extension whenever the original family spans. -/
theorem span_range_equiangularCone (v : ι → E) (hv : span ℝ (Set.range v) = ⊤) :
    span ℝ (Set.range (equiangularCone v)) = ⊤ := by
  let S := span ℝ (Set.range (equiangularCone v))
  have htwo : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hthree : Real.sqrt (3 / 2) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hr : equiangularCone v none ∈ S := subset_span ⟨none, rfl⟩
  have he : WithLp.toLp 2 (0, (1 : ℝ)) ∈ S := by
    convert S.smul_mem (Real.sqrt 2)⁻¹ hr using 1
    apply (WithLp.equiv 2 (E × ℝ)).injective
    ext <;> simp [equiangularCone, htwo]
  have hi (i : ι) : WithLp.toLp 2 (v i, (0 : ℝ)) ∈ S := by
    have hu : equiangularCone v (some i) ∈ S := subset_span ⟨some i, rfl⟩
    convert S.smul_mem (Real.sqrt (3 / 2))⁻¹
      (S.sub_mem hu (S.smul_mem (1 / Real.sqrt 2) he)) using 1
    apply (WithLp.equiv 2 (E × ℝ)).injective
    apply Prod.ext
    · change v i = (Real.sqrt (3 / 2))⁻¹ •
        (Real.sqrt (3 / 2) • v i - (1 / Real.sqrt 2) • (0 : E))
      rw [smul_zero, sub_zero, inv_smul_smul₀ hthree]
    · change (0 : ℝ) = (Real.sqrt (3 / 2))⁻¹ *
        (1 / Real.sqrt 2 - (1 / Real.sqrt 2) * 1)
      ring
  have hx (x : E) : WithLp.toLp 2 (x, (0 : ℝ)) ∈ S := by
    have hx : x ∈ span ℝ (Set.range v) := by rw [hv]; exact mem_top
    induction hx using span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hi i
    | zero => exact S.zero_mem
    | add x y _ _ hx hy =>
      simpa only [← WithLp.toLp_add, Prod.mk_add_mk, add_zero] using S.add_mem hx hy
    | smul a x _ hx =>
      simpa only [← WithLp.toLp_smul, Prod.smul_mk, smul_zero] using S.smul_mem a hx
  apply eq_top_iff.mpr
  intro x _
  convert S.add_mem (hx (WithLp.ofLp x).1) (S.smul_mem (WithLp.ofLp x).2 he) using 1
  apply (WithLp.equiv 2 (E × ℝ)).injective
  ext <;> simp

/-- Step `s4eq2rep` of EQ2, for Theorem 4.4 of [CGSS]: a spanning family in dimension
eight gives a cone whose span has dimension nine. -/
theorem finrank_span_equiangularCone [FiniteDimensional ℝ E] (v : ι → E)
    (hv : span ℝ (Set.range v) = ⊤) (hdim : finrank ℝ E = 8) :
    finrank ℝ (span ℝ (Set.range (equiangularCone v))) = 9 := by
  rw [span_range_equiangularCone v hv, finrank_top,
    (WithLp.linearEquiv 2 ℝ (E × ℝ)).finrank_eq, Module.finrank_prod, hdim,
    Module.finrank_self]

end InnerProductSpace

namespace SimpleGraph

open InnerProductSpace

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The graph `X'` in step `s4eq2rep` of EQ2, for Theorem 4.4 of [CGSS]. -/
noncomputable def equiangularConeGraph (v : ι → E) : SimpleGraph (Option ι) where
  Adj a b := a ≠ b ∧ ⟪equiangularCone v a, equiangularCone v b⟫ = 1
  symm.symm := by
    intro a b h
    exact ⟨h.1.symm, (real_inner_comm _ _).trans h.2⟩
  loopless.irrefl := by intro a h; exact h.1 rfl

/-- Step `s4eq2rep` of EQ2, for Theorem 4.4 of [CGSS]: the cone apex is universal. -/
theorem equiangularConeGraph_isUniversal_none (v : ι → E) :
    (equiangularConeGraph v).IsUniversal none := by
  intro a ha
  cases a with
  | none => exact (ha rfl).elim
  | some i => exact ⟨by simp, (real_inner_comm _ _).trans
      (inner_equiangularCone_some_none v i)⟩

/-- Step `s4eq2rep` of EQ2, for Theorem 4.4 of [CGSS]: the cone graph is connected. -/
theorem equiangularConeGraph_connected (v : ι → E) :
    (equiangularConeGraph v).Connected :=
  Connected.of_isUniversal (equiangularConeGraph_isUniversal_none v)

noncomputable local instance (v : ι → E) : DecidableRel (equiangularConeGraph v).Adj :=
  Classical.decRel _

/-- The final counting step of EQ2, for Theorem 4.4 of [CGSS]: the apex has one
neighbour for each member of the original family. -/
theorem equiangularConeGraph_degree_none [Fintype ι] (v : ι → E) :
    (equiangularConeGraph v).degree none = Fintype.card ι := by
  simpa only [Fintype.card_option, Nat.add_sub_cancel] using
    ((equiangularConeGraph v).degree_eq_card_sub_one none).mpr
      (equiangularConeGraph_isUniversal_none v)

/-- Steps `s4eq2ip` and `s4eq2rep` of EQ2, for Theorem 4.4 of [CGSS]: the cone is a
representation with Gram matrix `2I + A`. -/
theorem isRepresentation_equiangularCone [DecidableEq ι] (v : ι → E)
    (hv : ∀ i, ‖v i‖ = 1)
    (hpair : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 1 / 3 ∨ ⟪v i, v j⟫ = -(1 / 3)) :
    (equiangularConeGraph v).IsRepresentation (equiangularCone v) := by
  ext a b
  simp only [Matrix.gram_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, adjMatrix_apply]
  by_cases hab : a = b
  · subst b
    rw [inner_equiangularCone_self v hv]
    simp
  · have hip : ⟪equiangularCone v a, equiangularCone v b⟫ = 0 ∨
        ⟪equiangularCone v a, equiangularCone v b⟫ = 1 := by
      cases a with
      | none =>
        cases b with
        | none => exact (hab rfl).elim
        | some j => exact Or.inr ((real_inner_comm _ _).trans
            (inner_equiangularCone_some_none v j))
      | some i =>
        cases b with
        | none => exact Or.inr (inner_equiangularCone_some_none v i)
        | some j =>
          rw [inner_equiangularCone_some_some]
          rcases hpair i j (fun h ↦ hab (congrArg some h)) with h | h <;>
            rw [h] <;> norm_num
    have hadj : (equiangularConeGraph v).Adj a b ↔
        ⟪equiangularCone v a, equiangularCone v b⟫ = 1 :=
      and_iff_right hab
    rcases hip with hip | hip <;>
      simp only [hab, hip, hadj, ite_false, mul_zero, zero_add] <;> norm_num

end SimpleGraph

namespace LineSystem

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pair-counting step of EQ2, for Theorem 4.4 of [CGSS]: distinct roots in `Nᵣ`
with nonnegative mutual products occupy distinct pairs `{u, r-u}`. -/
theorem IsStarClosed.two_mul_card_le_ncard_N {S : LineSystem E} (hS : S.IsStarClosed)
    {r : E} (hr : r ∈ S.Φ) (u : ι → S.N r) (hinj : Function.Injective u)
    (hinner : ∀ i j, 0 ≤ ⟪(u i : E), (u j : E)⟫) :
    2 * Fintype.card ι ≤ (S.N r).ncard := by
  let p := S.pairInv r hS hr
  have hdisj (i j : ι) : u i ≠ p (u j) := by
    intro h
    have he : (u i : E) = r - (u j : E) := congrArg Subtype.val h
    have hi := hinner i j
    rw [he, inner_sub_left, real_inner_comm _ r, (u j).property.2,
      S.inner_self _ (u j).property.1] at hi
    norm_num at hi
  let f : Bool × ι → S.N r := fun a ↦ if a.1 then p (u a.2) else u a.2
  have hf : Function.Injective f := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    cases a <;> cases b
    · exact Prod.ext rfl (hinj h)
    · exact (hdisj i j h).elim
    · exact (hdisj j i h.symm).elim
    · exact Prod.ext rfl (hinj (p.injective h))
  have : Finite (S.N r) := (S.finite_N r).to_subtype
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool,
    Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf

/-- The final step of EQ2, for Theorem 4.4 of [CGSS]: C20 bounds such a family in a
root model of rank nine by fourteen; the A-model gives the stronger bound eight. -/
theorem RootType.card_le_fourteen_of_rank_eq_nine (t : RootType) (ht : t.rank = 9)
    {r : EuclideanSpace ℝ (Fin t.dim)} (hr : r ∈ t.model.Φ) (u : ι → t.model.N r)
    (hinj : Function.Injective u)
    (hinner : ∀ i j, 0 ≤ ⟪(u i : EuclideanSpace ℝ (Fin t.dim)), (u j : _)⟫) :
    Fintype.card ι ≤ 14 := by
  cases t with
  | A n hn =>
    change n = 9 at ht
    subst n
    have h := (isStarClosed_An 9).two_mul_card_le_ncard_N hr u hinj hinner
    rw [An.card_N hr] at h
    omega
  | D n hn =>
    change n = 9 at ht
    subst n
    have h := (isStarClosed_Dn 9).two_mul_card_le_ncard_N hr u hinj hinner
    rw [Dn.card_N hr] at h
    omega
  | E₆ => norm_num [RootType.rank] at ht
  | E₇ => norm_num [RootType.rank] at ht
  | E₈ => norm_num [RootType.rank] at ht

end LineSystem

namespace SimpleGraph

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable local instance (v : ι → E) : DecidableRel (equiangularConeGraph v).Adj :=
  Classical.decRel _

/-- The final step of EQ2, for Theorem 4.4 of [CGSS]: a representation of the cone in
a rank-nine root model gives the bound fourteen. The root-model witness is the separate
classification step `s4eq2type`. -/
theorem IsRepresentedIn.card_le_fourteen_of_equiangularCone {v : ι → E}
    {t : LineSystem.RootType} (hX : (equiangularConeGraph v).IsRepresentedIn t.model)
    (ht : t.rank = 9) : Fintype.card ι ≤ 14 := by
  obtain ⟨x, hx, hm⟩ := hX
  let u : ι → t.model.N (x none) := fun i ↦
    ⟨x (some i), hm (some i), hx.inner_of_adj
      ((equiangularConeGraph_isUniversal_none v) (by simp)).symm⟩
  apply t.card_le_fourteen_of_rank_eq_nine ht (hm none) u
  · intro i j h
    exact Option.some.inj (hx.injective (congrArg Subtype.val h))
  · intro i j
    exact hx.inner_nonneg (some i) (some j)

end SimpleGraph
