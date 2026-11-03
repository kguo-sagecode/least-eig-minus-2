/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.TypeA
import LineGraphs.Representation.TypeDNormalForm
import LineGraphs.Graphs.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Choose.Cast

/-!
# Nonnegative subsets of the classical root models

The remarks after Theorems 4.1 and 4.2 of [CGSS], blueprint `rem:4-after41` and
`rem:4-after42`. Maximality means inclusion maximality among subsets of the given
root model with nonnegative mutual inner products.
-/

open EuclideanSpace SimpleGraph
open scoped RealInnerProductSpace

namespace LineSystem

/-- Classical adjacency decisions for graph representations of nonnegative subsets. -/
noncomputable local instance decidableAdjNonnegSubset {I : Type*} (Y : SimpleGraph I) :
    DecidableRel Y.Adj :=
  Classical.decRel _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Remarks after Theorems 4.1 and 4.2 of [CGSS]: a subset of roots with
nonnegative mutual inner products, including the diagonal. -/
def IsNonnegSubset (S : LineSystem E) (sigma : Set E) : Prop :=
  sigma ⊆ S.Φ ∧ ∀ x ∈ sigma, ∀ y ∈ sigma, 0 ≤ ⟪x, y⟫

/-- Step `s4rdrep`, remark after Theorem 4.2 of [CGSS]: the roots themselves
represent their inner-product graph. -/
theorem IsNonnegSubset.isRepresentation {S : LineSystem E} {sigma : Set E}
    (hsigma : S.IsNonnegSubset sigma) [DecidableEq sigma] :
    (representedGraph (fun x : sigma ↦ (x : E))).IsRepresentation (fun x : sigma ↦ (x : E)) := by
  apply isRepresentation_representedGraph
  · intro x
    exact S.inner_self _ (hsigma.1 x.property)
  · intro x y hxy
    have hn := hsigma.2 x x.property y y.property
    have hi := S.inner_mem _ (hsigma.1 x.property) _ (hsigma.1 y.property)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with hi | hi | hi | hi | hi
    · linarith
    · linarith
    · exact Or.inl hi
    · exact Or.inr hi
    · exact (hxy (Subtype.ext ((S.inner_eq_two_iff
        (hsigma.1 x.property) (hsigma.1 y.property)).mp hi))).elim

/-- The maximality step in the remarks after Theorems 4.1 and 4.2 of [CGSS]:
a root compatible with the entire subset already belongs to it. -/
theorem mem_of_maximal_nonnegSubset {S : LineSystem E} {sigma : Set E}
    (hsigma : Maximal S.IsNonnegSubset sigma) {z : E} (hz : z ∈ S.Φ)
    (hn : ∀ x ∈ sigma, 0 ≤ ⟪z, x⟫) : z ∈ sigma := by
  apply hsigma.2 (show S.IsNonnegSubset (insert z sigma) from ?_)
    (Set.subset_insert _ _) (Set.mem_insert _ _)
  refine ⟨Set.insert_subset hz hsigma.1.1, ?_⟩
  rintro x (rfl | hx) y (rfl | hy)
  · rw [S.inner_self _ hz]; norm_num
  · exact hn y hy
  · rw [real_inner_comm]; exact hn x hx
  · exact hsigma.1.2 x hx y hy

namespace An

/-- The set `sigma_P` in the remark after Theorem 4.1 of [CGSS]. -/
def sigmaP {n : ℕ} (P : Set (Fin (n + 1))) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | ∃ p ∈ P, ∃ q ∉ P, x = single p 1 - single q 1}

/-- Step `s4raip`, remark after Theorem 4.1 of [CGSS]: products between
oriented roots count their common positive and negative coordinates. -/
theorem inner_sigmaP {n : ℕ} {P : Set (Fin (n + 1))} {p p' q q' : Fin (n + 1)}
    (hp : p ∈ P) (hp' : p' ∈ P) (hq : q ∉ P) (hq' : q' ∉ P) :
    ⟪single p (1 : ℝ) - single q 1, single p' 1 - single q' 1⟫ =
      (if p = p' then 1 else 0) + (if q = q' then 1 else 0) := by
  rw [inner_sub_single_sub_single]
  have h₁ : p ≠ q' := fun h ↦ hq' (h ▸ hp)
  have h₂ : q ≠ p' := fun h ↦ hq (h ▸ hp')
  simp [h₁, h₂]

/-- Step `s4raip`, remark after Theorem 4.1 of [CGSS]: `sigma_P` is nonnegative. -/
theorem isNonnegSubset_sigmaP {n : ℕ} (P : Set (Fin (n + 1))) :
    (An n).IsNonnegSubset (sigmaP P) := by
  constructor
  · rintro x ⟨p, hp, q, hq, rfl⟩
    exact sub_single_mem_An p q (fun h ↦ hq (h ▸ hp))
  · rintro x ⟨p, hp, q, hq, rfl⟩ y ⟨p', hp', q', hq', rfl⟩
    rw [inner_sigmaP hp hp' hq hq']
    positivity

/-- Step `s4rasign`, remark after Theorem 4.1 of [CGSS]: each coordinate has
one sign throughout a nonnegative subset. -/
theorem exists_subset_sigmaP {n : ℕ} {sigma : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hsigma : (An n).IsNonnegSubset sigma) : ∃ P, sigma ⊆ sigmaP P := by
  classical
  have hroot (x : sigma) := mem_iff_exists_sub_single.mp (hsigma.1 x.property)
  choose p q hpq hform using hroot
  refine ⟨Set.range p, ?_⟩
  intro x hx
  refine ⟨p ⟨x, hx⟩, Set.mem_range_self _, q ⟨x, hx⟩, ?_, hform ⟨x, hx⟩⟩
  rintro ⟨y, hy⟩
  have hn := hsigma.2 y y.property x hx
  have hxform : x = single (p ⟨x, hx⟩) 1 - single (q ⟨x, hx⟩) 1 := hform ⟨x, hx⟩
  rw [hform y, hxform, inner_sub_single_sub_single] at hn
  have h₁ : p y ≠ p ⟨x, hx⟩ := fun h ↦ hpq ⟨x, hx⟩ (h.symm.trans hy)
  have h₂ : q y ≠ q ⟨x, hx⟩ := fun h ↦ hpq y (hy.trans h.symm)
  simp only [ite_eq_right h₁, ite_eq_left hy, ite_eq_right h₂] at hn
  split_ifs at hn <;> norm_num at hn

/-- Step `s4racard`, remark after Theorem 4.1 of [CGSS]: roots of `sigma_P` are
indexed injectively by a positive and a negative coordinate. -/
theorem sigmaP_injective {n : ℕ} (P : Set (Fin (n + 1))) :
    Function.Injective (fun a : P × ↥(Pᶜ) ↦ single a.1.val (1 : ℝ) - single a.2.val 1) := by
  intro a b hab
  dsimp only at hab
  have he := inner_sigmaP a.1.property b.1.property a.2.property b.2.property
  rw [hab, inner_sigmaP b.1.property b.1.property b.2.property b.2.property] at he
  simp only [ite_true] at he
  by_cases hp : a.1.val = b.1.val <;> by_cases hq : a.2.val = b.2.val
  · exact Prod.ext (Subtype.ext hp) (Subtype.ext hq)
  all_goals norm_num [hp, hq] at he

/-- Step `s4racard`, remark after Theorem 4.1 of [CGSS]. -/
theorem card_sigmaP {n : ℕ} (P : Set (Fin (n + 1))) :
    (sigmaP P).ncard = P.ncard * (n + 1 - P.ncard) := by
  classical
  have he : sigmaP P = Set.range
      (fun a : P × ↥(Pᶜ) ↦ single a.1.val (1 : ℝ) - single a.2.val 1) := by
    ext x
    constructor
    · rintro ⟨p, hp, q, hq, rfl⟩
      exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.1.property, a.2, a.2.property, rfl⟩
  rw [he, Set.ncard_range_of_injective (sigmaP_injective P), Nat.card_prod,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_compl]
  simp

/-- Step `s4rabound`, remark after Theorem 4.1 of [CGSS]: the sharp order bound. -/
theorem card_nonneg_subset_le {n : ℕ} {sigma : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hsigma : (An n).IsNonnegSubset sigma) : sigma.ncard ≤ (n + 1) ^ 2 / 4 := by
  obtain ⟨P, hP⟩ := exists_subset_sigmaP hsigma
  have hc := Set.ncard_le_ncard hP ((An n).finite.subset (isNonnegSubset_sigmaP P).1)
  rw [card_sigmaP] at hc
  have hm : P.ncard ≤ n + 1 := by simpa using Set.ncard_le_card P
  apply hc.trans
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  have hs := Nat.sub_add_cancel hm
  nlinarith [sq_nonneg ((n + 1 : ℤ) - 2 * P.ncard)]

/-- Step `s4raback`, remark after Theorem 4.1 of [CGSS]: every nontrivial
coordinate bipartition gives a maximal nonnegative subset. -/
theorem maximal_sigmaP {n : ℕ} {P : Set (Fin (n + 1))}
    (hp : P.Nonempty) (hq : Pᶜ.Nonempty) : Maximal (An n).IsNonnegSubset (sigmaP P) := by
  refine ⟨isNonnegSubset_sigmaP P, ?_⟩
  intro T hT hPT z hz
  obtain ⟨a, b, hab, rfl⟩ := mem_iff_exists_sub_single.mp (hT.1 hz)
  obtain ⟨p, hp⟩ := hp
  obtain ⟨q, hq⟩ := hq
  have hb : b ∉ P := by
    intro hb
    have hn := hT.2 _ hz _ (hPT ⟨b, hb, q, hq, rfl⟩)
    rw [inner_sub_single_sub_single] at hn
    have hbq : b ≠ q := fun h ↦ hq (h ▸ hb)
    simp only [hab, hbq, ite_false, ite_true] at hn
    split_ifs at hn <;> norm_num at hn
  have ha : a ∈ P := by
    by_contra ha
    have hn := hT.2 _ hz _ (hPT ⟨p, hp, a, ha, rfl⟩)
    rw [inner_sub_single_sub_single] at hn
    have hap : a ≠ p := fun h ↦ ha (h ▸ hp)
    simp only [hap, hab.symm, ite_false, ite_true] at hn
    split_ifs at hn <;> norm_num at hn
  exact ⟨a, ha, b, hb, rfl⟩

/-- Remark after Theorem 4.1 of [CGSS], blueprint assertion 1 (`rem:4-after41`):
the maximal nonnegative subsets are exactly the nontrivial `Σ_P`. -/
theorem nonneg_subset_maximal_iff {n : ℕ} (hn : 1 ≤ n)
    {sigma : Set (EuclideanSpace ℝ (Fin (n + 1)))} :
    Maximal (An n).IsNonnegSubset sigma ↔
      ∃ P : Set (Fin (n + 1)), 1 ≤ P.ncard ∧ P.ncard ≤ n ∧ sigma = sigmaP P := by
  constructor
  · intro hsigma
    obtain ⟨P, hP⟩ := exists_subset_sigmaP hsigma.1
    have he : sigma = sigmaP P :=
      Set.Subset.antisymm hP (hsigma.2 (isNonnegSubset_sigmaP P) hP)
    have hne : sigma.Nonempty := by
      by_contra hne
      let i : Fin (n + 1) := ⟨0, by omega⟩
      let j : Fin (n + 1) := ⟨1, by omega⟩
      have hz := mem_of_maximal_nonnegSubset hsigma
        (sub_single_mem_An i j (by simp [i, j]))
        (fun x hx ↦ (hne ⟨x, hx⟩).elim)
      exact hne ⟨_, hz⟩
    obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, q, hq, _⟩ := he ▸ hx
    have hpc : 0 < P.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨p, hp⟩
    have hqc : 0 < Pᶜ.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨q, hq⟩
    have hc := Set.ncard_add_ncard_compl P
    simp only [Nat.card_fin] at hc
    exact ⟨P, by omega, by omega, he⟩
  · rintro ⟨P, hp, hq, rfl⟩
    apply maximal_sigmaP ((Set.ncard_pos (Set.toFinite _)).mp hp)
    apply (Set.ncard_pos (Set.toFinite _)).mp
    rw [Set.ncard_compl]
    simp only [Nat.card_fin]
    omega

/-- Remark after Theorem 4.1 of [CGSS], blueprint assertion 3, steps `s4racard` and `s4raeq`: a
balanced bipartition, with `|P| = ⌊(n + 1) / 2⌋`, attains the integer bound. -/
theorem exists_nonneg_subset_card_eq (n : ℕ) :
    ∃ sigma : Set (EuclideanSpace ℝ (Fin (n + 1))),
      (An n).IsNonnegSubset sigma ∧ sigma.ncard = (n + 1) ^ 2 / 4 ∧
        ∃ P : Set (Fin (n + 1)), P.ncard = (n + 1) / 2 ∧ sigma = sigmaP P := by
  obtain ⟨P, _, hP⟩ := Set.exists_subset_card_eq
    (s := (Set.univ : Set (Fin (n + 1)))) (n := (n + 1) / 2)
    (by simpa using Nat.div_le_self (n + 1) 2)
  refine ⟨sigmaP P, isNonnegSubset_sigmaP P, ?_, P, hP, rfl⟩
  rw [card_sigmaP, hP]
  have hmod := Nat.mod_lt (n + 1) (by omega : 0 < 2)
  have hdiv := Nat.mod_add_div (n + 1) 2
  have hsub : n + 1 - (n + 1) / 2 = (n + 1) / 2 + (n + 1) % 2 := by omega
  rw [hsub]
  have hb : 4 * ((n + 1) / 2 * ((n + 1) / 2 + (n + 1) % 2)) ≤ (n + 1) ^ 2 ∧
      (n + 1) ^ 2 < 4 * ((n + 1) / 2 * ((n + 1) / 2 + (n + 1) % 2) + 1) := by
    rcases (show (n + 1) % 2 = 0 ∨ (n + 1) % 2 = 1 by omega) with he | he <;>
      simp only [he] at hdiv ⊢ <;> constructor <;> nlinarith
  omega

/-- Remark after Theorem 4.1 of [CGSS], step `s4rarep`: the vectors of `Σ_P`,
indexed by the edges of the complete bipartite graph, represent its line graph. -/
theorem isRepresentation_lineGraph_completeBipartite_sigmaP {n : ℕ}
    (P : Set (Fin (n + 1))) :
    (completeBipartiteGraph P ↥(Pᶜ)).lineGraph.IsRepresentation
      (fun e ↦ single ((completeBipartiteEdgeEquiv P ↥(Pᶜ)).symm e).1.val (1 : ℝ) -
        single ((completeBipartiteEdgeEquiv P ↥(Pᶜ)).symm e).2.val 1) := by
  classical
  let f := completeBipartiteEdgeEquiv P ↥(Pᶜ)
  apply isRepresentation_iff.mpr
  intro e e'
  obtain ⟨a, rfl⟩ := f.surjective e
  obtain ⟨b, rfl⟩ := f.surjective e'
  simp only [f, Equiv.symm_apply_apply]
  rw [inner_sigmaP a.1.property b.1.property a.2.property b.2.property]
  simp only [lineGraph_completeBipartiteGraph_adj, ← Subtype.ext_iff,
    (completeBipartiteEdgeEquiv P ↥(Pᶜ)).injective.eq_iff]
  by_cases hp : a.1 = b.1 <;> by_cases hq : a.2 = b.2
  · have hab : a = b := Prod.ext hp hq
    norm_num [hab]
  · have hab : a ≠ b := fun h ↦ hq (congrArg Prod.snd h)
    simp [hp, hq, hab]
  · have hab : a ≠ b := fun h ↦ hp (congrArg Prod.fst h)
    simp [hp, hq, hab]
  · have hab : a ≠ b := fun h ↦ hp (congrArg Prod.fst h)
    simp [hp, hq, hab]

end An

namespace Dn

/-- Step `s4rdaddnn`, remark after Theorem 4.2 of [CGSS]: every sum of two
centres is compatible with all vectors in the normal form. -/
private theorem inner_centers_nonneg {m : ℕ} (Y : SimpleGraph (Fin m)) (a : Fin m → ℕ)
    (i j : Fin m) (u : GeneralizedLineGraphVertex Y a) :
    0 ≤ ⟪single (generalizedLineGraphCenter a i) (1 : ℝ) +
      single (generalizedLineGraphCenter a j) 1, Y.generalizedLineGraphVector a u⟫ := by
  rcases u with ⟨⟨k, l⟩, hkl⟩ | ⟨k, p, b⟩
  · simp only [generalizedLineGraphVector, Sym2.lift_mk,
      inner_add_left, inner_add_right, inner_single_left, PiLp.single_apply,
      map_one, one_mul]
    positivity
  · simp only [generalizedLineGraphVector, inner_add_left, inner_add_right,
      inner_single_left, PiLp.single_apply, map_one, one_mul,
      generalizedLineGraphCenter_ne_petal, ite_false, add_zero]
    positivity

/-- Remark after Theorem 4.2 of [CGSS], blueprint assertion 1 (`rem:4-after42`): a
maximal nonnegative subset, suitably indexed, represents a generalized line
graph with complete underlying graph and exactly `n` centre and petal coordinates. -/
theorem exists_isRepresentation_generalizedLineGraph_top_of_maximal {n : ℕ} (hn : 1 ≤ n)
    {sigma : Set (EuclideanSpace ℝ (Fin n))}
    (hsigma : Maximal (Dn n).IsNonnegSubset sigma) :
    ∃ (m : ℕ) (a : Fin m → ℕ), 1 ≤ m ∧ (∑ i, (1 + a i)) = n ∧
      ∃ e : GeneralizedLineGraphVertex (⊤ : SimpleGraph (Fin m)) a ≃ sigma,
        (generalizedLineGraph (⊤ : SimpleGraph (Fin m)) a).IsRepresentation
          (fun u ↦ (e u : EuclideanSpace ℝ (Fin n))) := by
  classical
  have hx := hsigma.1.isRepresentation
  obtain ⟨m, a, q, b, Y, e, hform, _, _, _, _, hcount⟩ :=
    hx.exists_normal_form_Dn (fun x ↦ hsigma.1.1 x.property) hn
  let D := signChange b
  let R := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ q
  have hDD (z : EuclideanSpace ℝ (Fin n)) : D (D z) = z := by
    ext i
    simp only [D, signChange_apply]
    cases b i <;> simp
  have hDinv (z : EuclideanSpace ℝ (Fin n)) : D.symm z = D z := by
    apply D.injective
    rw [D.apply_symm_apply, hDD]
  have hcc := generalizedLineGraphCenter_injective a
  have hcomplete (i j : Fin m) (hij : i ≠ j) : Y.Adj i j := by
    let z₀ := single (generalizedLineGraphCenter a i) (1 : ℝ) +
      single (generalizedLineGraphCenter a j) 1
    let z := D.symm (R z₀)
    have hzroot : z ∈ (Dn n).Φ := by
      dsimp only [z]
      rw [hDinv]
      apply signChange_mem_Dn
      simp only [R, z₀, map_add, EuclideanSpace.piLpCongrLeft_single]
      exact add_single_mem_Dn _ _ (q.injective.ne (hcc.ne hij))
    have hznn (x : EuclideanSpace ℝ (Fin n)) (hxmem : x ∈ sigma) : 0 ≤ ⟪z, x⟫ := by
      rw [← D.inner_map_map]
      change 0 ≤ ⟪D (D.symm (R z₀)), D x⟫
      rw [D.apply_symm_apply]
      have hf : D x = R (Y.generalizedLineGraphVector a (e ⟨x, hxmem⟩)) :=
        hform ⟨x, hxmem⟩
      rw [hf, R.inner_map_map]
      exact inner_centers_nonneg Y a i j _
    have hz : z ∈ sigma := mem_of_maximal_nonnegSubset hsigma hzroot hznn
    have hf : z₀ = Y.generalizedLineGraphVector a (e ⟨z, hz⟩) := by
      apply R.injective
      exact (D.apply_symm_apply (R z₀)).symm.trans (hform ⟨z, hz⟩)
    rcases hv : e ⟨z, hz⟩ with ⟨⟨k, l⟩, hkl⟩ | ⟨k, p, s⟩
    · rw [hv] at hf
      have hf' :
          (⊤ : SimpleGraph (Fin m)).generalizedLineGraphVector a
              (.inl ⟨s(i, j), by simpa using hij⟩) =
            (⊤ : SimpleGraph (Fin m)).generalizedLineGraphVector a
              (.inl ⟨s(k, l), by simpa using (Y.mem_edgeSet.mp hkl).ne⟩) := hf
      have htop := (⊤ : SimpleGraph (Fin m)).generalizedLineGraph_isRepresentation a
      have heq := htop.injective hf'
      have hs : s(i, j) = s(k, l) := congrArg Subtype.val (Sum.inl.inj heq)
      apply Y.mem_edgeSet.mp
      rw [hs]
      exact hkl
    · rw [hv] at hf
      have hh := congrArg
        (fun w : EuclideanSpace ℝ ((i : Fin m) × Fin (a i + 1)) ↦
          w (generalizedLineGraphPetal a ⟨k, p⟩)) hf
      have hpi := (generalizedLineGraphCenter_ne_petal a i ⟨k, p⟩).symm
      have hpj := (generalizedLineGraphCenter_ne_petal a j ⟨k, p⟩).symm
      have hpk := (generalizedLineGraphCenter_ne_petal a k ⟨k, p⟩).symm
      cases s <;> simp [z₀, generalizedLineGraphVector, hpi, hpj, hpk] at hh
  have hY : Y = ⊤ := by
    ext i j
    simp only [top_adj]
    exact ⟨Adj.ne, hcomplete i j⟩
  subst Y
  have hm : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    subst m
    simp at hcount
    omega
  exact ⟨m, a, hm, hcount, e.symm.toEquiv, hx.comp_iso e.symm⟩

/-- Step `s4rdcount`, remark after Theorem 4.2 of [CGSS]: the normal form
counts edges and the two roots at each petal, including all unused coordinates. -/
theorem card_nonneg_subset_le {n : ℕ} (hn : 4 ≤ n)
    {sigma : Set (EuclideanSpace ℝ (Fin n))} (hsigma : (Dn n).IsNonnegSubset sigma) :
    sigma.ncard ≤ n * (n - 1) / 2 := by
  classical
  let := ((Dn n).finite.subset hsigma.1).fintype
  have hx := hsigma.isRepresentation
  obtain ⟨m, a, _, _, Y, e, _, _, _, _, _, hcount⟩ :=
    hx.exists_normal_form_Dn (fun x ↦ hsigma.1 x.property) (by omega)
  have hsum : m + ∑ i, a i = n := by
    simpa [Finset.sum_add_distrib] using hcount
  have hm : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    subst m
    simp at hsum
    omega
  have hmn : m ≤ n := by omega
  have hc := Fintype.card_congr e.toEquiv
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, ← Finset.sum_mul] at hc
  have he := Y.card_edgeFinset_le_card_choose_two
  rw [Y.edgeFinset_card, Fintype.card_fin] at he
  have hs : sigma.ncard ≤ m.choose 2 + 2 * (n - m) := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, hc]
    nlinarith [show ∑ i, a i = n - m by omega]
  rw [← Nat.choose_two_right]
  apply hs.trans
  have hineq : (m.choose 2 : ℚ) + 2 * (n - m : ℕ) ≤ n.choose 2 := by
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub hmn]
    have hn' : (4 : ℚ) ≤ n := by exact_mod_cast hn
    have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
    have hmn' : (m : ℚ) ≤ n := by exact_mod_cast hmn
    nlinarith [mul_nonneg (sub_nonneg.mpr hmn')
      (show (0 : ℚ) ≤ n + m - 5 by linarith)]
  exact_mod_cast hineq

/-- Remark after Theorem 4.2 of [CGSS], blueprint assertion 2, step `s4rdK`: the vectors
`e_i + e_j` of the edges of the complete graph attain the bound and represent its line graph. -/
theorem exists_nonneg_subset_card_eq (n : ℕ) :
    ∃ sigma : Set (EuclideanSpace ℝ (Fin n)),
      (Dn n).IsNonnegSubset sigma ∧ sigma.ncard = n * (n - 1) / 2 ∧
        sigma = Set.range (⊤ : SimpleGraph (Fin n)).lineGraphVector ∧
          (⊤ : SimpleGraph (Fin n)).lineGraph.IsRepresentation
            (⊤ : SimpleGraph (Fin n)).lineGraphVector := by
  classical
  let Y : SimpleGraph (Fin n) := ⊤
  refine ⟨Set.range Y.lineGraphVector, ⟨?_, ?_⟩, ?_, rfl, Y.lineGraph_isRepresentation⟩
  · rintro _ ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
    rw [Y.lineGraphVector_mk hij]
    exact add_single_mem_Dn i j (Y.mem_edgeSet.mp hij).ne
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact Y.lineGraph_isRepresentation.inner_nonneg u v
  · rw [Set.ncard_range_of_injective Y.lineGraph_isRepresentation.injective,
      Nat.card_eq_fintype_card, Y.card_edgeSet]
    simpa [Y, Nat.choose_two_right] using
      (card_edgeFinset_top_eq_card_choose_two (V := Fin n))

end Dn

end LineSystem
