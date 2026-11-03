/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.GeneralizedLineGraph

/-!
# The coordinate representation of a generalized line graph

Lemma `lem:4-glgrep` and assertion 2 of Theorem 4.2 of [CGSS]. Coordinates are indexed
by `Σ i, Fin (a i + 1)`, as in the paper's corrected formula.
-/

open scoped RealInnerProductSpace
open EuclideanSpace

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (Y : SimpleGraph V) (a : V → ℕ)

/-- Lemma `lem:4-glgrep`, Section 4 of [CGSS]: the centre coordinate at a vertex of `Y`. -/
def generalizedLineGraphCenter (i : V) : (j : V) × Fin (a j + 1) := ⟨i, 0⟩

/-- Lemma `lem:4-glgrep`, Section 4 of [CGSS]: the extra coordinate of a petal. -/
def generalizedLineGraphPetal (p : (i : V) × Fin (a i)) : (j : V) × Fin (a j + 1) :=
  ⟨p.1, p.2.succ⟩

omit [Fintype V] [DecidableEq V] in
/-- Lemma `lem:4-glgrep`, step `s4glgee`, Section 4 of [CGSS]: centres have distinct labels. -/
theorem generalizedLineGraphCenter_injective : Function.Injective (generalizedLineGraphCenter a) :=
  fun _ _ h ↦ congrArg Sigma.fst h

omit [Fintype V] [DecidableEq V] in
/-- Lemma `lem:4-glgrep`, step `s4glgce`, Section 4 of [CGSS]: extra coordinates are not centres. -/
theorem generalizedLineGraphCenter_ne_petal (i : V) (p : (j : V) × Fin (a j)) :
    generalizedLineGraphCenter a i ≠ generalizedLineGraphPetal a p := by
  rintro h
  obtain ⟨j, k⟩ := p
  have hij : i = j := congrArg Sigma.fst h
  subst j
  exact Fin.succ_ne_zero k (sigma_mk_injective h).symm

omit [Fintype V] [DecidableEq V] in
/-- Lemma `lem:4-glgrep`, step `s4glgcc`, Section 4 of [CGSS]: distinct petals have
distinct labels. -/
theorem generalizedLineGraphPetal_injective : Function.Injective (generalizedLineGraphPetal a) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst j
  change (⟨i, k.succ⟩ : (j : V) × Fin (a j + 1)) = ⟨i, l.succ⟩ at h
  have hsucc : k.succ = l.succ := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hkl : k = l := Fin.succ_inj.mp hsucc
  subst l
  rfl

/-- Lemma `lem:4-glgrep`, Section 4 of [CGSS]: edge sums and signed petal vectors. -/
noncomputable def generalizedLineGraphVector : GeneralizedLineGraphVertex Y a →
    EuclideanSpace ℝ ((i : V) × Fin (a i + 1))
  | .inl e => Sym2.lift
      ⟨fun i j ↦ single (generalizedLineGraphCenter a i) 1 +
        single (generalizedLineGraphCenter a j) 1, fun _ _ ↦ add_comm _ _⟩ e.val
  | .inr ⟨i, k, b⟩ => single (generalizedLineGraphCenter a i) 1 +
      single (generalizedLineGraphPetal a ⟨i, k⟩) (if b then -1 else 1)

/-- Lemma `lem:4-glgrep`, step `s4glgee`, Section 4 of [CGSS]: edge-edge products are unchanged. -/
theorem inner_generalizedLineGraphVector_edges (e f : Y.edgeSet) :
    ⟪Y.generalizedLineGraphVector a (.inl e), Y.generalizedLineGraphVector a (.inl f)⟫ =
      ⟪Y.lineGraphVector e, Y.lineGraphVector f⟫ := by
  rcases e with ⟨⟨i, j⟩, hij⟩
  rcases f with ⟨⟨k, l⟩, hkl⟩
  rw [Y.lineGraphVector_mk hij, Y.lineGraphVector_mk hkl]
  simp [generalizedLineGraphVector, inner_add_left, inner_add_right, inner_single_left,
    PiLp.single_apply, (generalizedLineGraphCenter_injective a).eq_iff]

/-- Lemma `lem:4-glgrep`, steps `s4glgee`--`s4glgcc`, Section 4 of [CGSS]: the explicit
vectors have Gram matrix `2I + A`. -/
theorem generalizedLineGraph_isRepresentation :
    (generalizedLineGraph Y a).IsRepresentation (Y.generalizedLineGraphVector a) := by
  classical
  have hcc (i j : V) : generalizedLineGraphCenter a i = generalizedLineGraphCenter a j ↔
      i = j := (generalizedLineGraphCenter_injective a).eq_iff
  have hpp (p q : (i : V) × Fin (a i)) :
      generalizedLineGraphPetal a p = generalizedLineGraphPetal a q ↔ p = q :=
    (generalizedLineGraphPetal_injective a).eq_iff
  have hcp := generalizedLineGraphCenter_ne_petal a
  apply isRepresentation_iff.mpr
  rintro (e | ⟨i, k, b⟩) (f | ⟨j, l, c⟩)
  · rw [Y.inner_generalizedLineGraphVector_edges]
    have h := isRepresentation_iff.mp Y.lineGraph_isRepresentation e f
    by_cases he : e = f <;> by_cases ha : Y.lineGraph.Adj e f <;>
      simpa [he, ha, generalizedLineGraph] using h
  · rcases e with ⟨⟨u, v⟩, huv⟩
    have hne : u ≠ v := huv.ne
    simp only [generalizedLineGraphVector, Sym2.lift_mk, inner_add_left, inner_add_right,
      inner_single_left, PiLp.single_apply, map_one, one_mul, hcc, hcp,
      ite_false, mul_zero, add_zero, Sum.inl_ne_inr, generalizedLineGraph, Sym2.mem_iff]
    by_cases hju : j = u <;> by_cases hjv : j = v <;> simp_all [eq_comm]
  · rw [real_inner_comm]
    rcases f with ⟨⟨u, v⟩, huv⟩
    have hne : u ≠ v := huv.ne
    simp only [generalizedLineGraphVector, Sym2.lift_mk, inner_add_left, inner_add_right,
      inner_single_left, PiLp.single_apply, map_one, one_mul, hcc, hcp,
      ite_false, mul_zero, add_zero, Sum.inr_ne_inl, generalizedLineGraph, Sym2.mem_iff]
    by_cases hiu : i = u <;> by_cases hiv : i = v <;> simp_all [eq_comm]
  · by_cases hij : i = j
    · subst j
      by_cases hkl : k = l
      · subst l
        cases b <;> cases c <;>
          simp only [generalizedLineGraphVector, generalizedLineGraph, inner_add_left,
            inner_add_right, inner_single_left, PiLp.single_apply, hcp,
            Ne.symm (hcp i ⟨i, k⟩)] <;> norm_num
      · have hval : k.val ≠ l.val := fun h ↦ hkl (Fin.ext h)
        cases b <;> cases c <;>
          simp [generalizedLineGraphVector, generalizedLineGraph, inner_add_left,
            inner_add_right, inner_single_left, hcp, hpp,
            Ne.symm (hcp i ⟨i, k⟩), hkl, hval]
    · have hpq : (⟨i, k⟩ : (i : V) × Fin (a i)) ≠ ⟨j, l⟩ :=
        fun h ↦ hij (congrArg Sigma.fst h)
      have hverts : (⟨i, k, b⟩ : (i : V) × (Fin (a i) × Bool)) ≠ ⟨j, l, c⟩ :=
        fun h ↦ hij (congrArg Sigma.fst h)
      simp [generalizedLineGraphVector, generalizedLineGraph, inner_add_left,
        inner_add_right, inner_single_left, hcc, hcp, hpp,
        Ne.symm (hcp j ⟨i, k⟩), hij, hpq, hverts]

-- Theorem 4.2, assertion 2
/-- Lemma `lem:4-glgrep` and Theorem 4.2, assertion 2, of [CGSS]: the generalized
line graph is represented in `Dₙ`, for `n = ∑ i, (1 + a i)`, including `n < 4`.
Renumbering the centre and petal coordinates gives the stipulated coordinate model. -/
theorem generalizedLineGraph_isRepresentedIn_Dn :
    (generalizedLineGraph Y a).IsRepresentedIn (LineSystem.Dn (∑ i, (1 + a i))) := by
  let e : ((i : V) × Fin (a i + 1)) ≃ Fin (∑ i, (1 + a i)) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_sigma, Nat.add_comm])
  let g := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  refine ⟨fun u ↦ g (Y.generalizedLineGraphVector a u), ?_, ?_⟩
  · apply isRepresentation_iff.mpr
    intro u v
    rw [g.inner_map_map]
    exact isRepresentation_iff.mp (Y.generalizedLineGraph_isRepresentation a) u v
  · rintro (⟨⟨i, j⟩, hij⟩ | ⟨i, k, b⟩)
    · change g (single (generalizedLineGraphCenter a i) 1 +
        single (generalizedLineGraphCenter a j) 1) ∈ _
      simp only [map_add, g, EuclideanSpace.piLpCongrLeft_single]
      exact LineSystem.add_single_mem_Dn _ _
        (e.injective.ne ((generalizedLineGraphCenter_injective a).ne hij.ne))
    · change g (single (generalizedLineGraphCenter a i) 1 +
        single (generalizedLineGraphPetal a ⟨i, k⟩) (if b then -1 else 1)) ∈ _
      simp only [map_add, g, EuclideanSpace.piLpCongrLeft_single]
      have hne := e.injective.ne (generalizedLineGraphCenter_ne_petal a i ⟨i, k⟩)
      cases b
      · exact LineSystem.add_single_mem_Dn _ _ hne
      · convert LineSystem.sub_single_mem_Dn _ _ hne using 1
        ext j
        simp [PiLp.single_apply]
        split_ifs <;> norm_num

omit [Fintype V] in
/-- Theorem 4.2, assertion 2, of [CGSS]: every generalized line graph is represented
in some coordinate model of type D. -/
theorem IsGeneralizedLineGraph.exists_isRepresentedIn_Dn {X : SimpleGraph V}
    [DecidableRel X.Adj] (hX : X.IsGeneralizedLineGraph) :
    ∃ n, X.IsRepresentedIn (LineSystem.Dn n) := by
  obtain ⟨m, Z, b, ⟨e⟩⟩ := hX
  exact ⟨_, (Z.generalizedLineGraph_isRepresentedIn_Dn b).comp_iso e⟩

end SimpleGraph
