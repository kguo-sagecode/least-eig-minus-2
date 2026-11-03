/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.EightRegular
import LineGraphs.Seidel.CubicCheck
import Mathlib.Logic.Equiv.Fintype

/-!
# The cubic case of SE4

Theorem `res:414-SE4`, used in Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

namespace CubicEight

/-- The root and its three neighbours can be given the fixed labels of the SE4 search. -/
theorem exists_iso_neighborFinset_zero (X : SimpleGraph (Fin 8)) [DecidableRel X.Adj]
    (hr : X.IsRegularOfDegree 3) :
    ∃ p : Equiv.Perm (Fin 8), (X.comap p).neighborFinset 0 = {1, 2, 3} := by
  classical
  let e : Fin 3 ≃ X.neighborSet 0 :=
    (Fintype.equivFinOfCardEq ((X.card_neighborSet_eq_degree 0).trans (hr 0))).symm
  let f : Fin 4 → Fin 8 := Fin.castAdd 4
  let g : Fin 4 → Fin 8 := Fin.cons 0 (fun i ↦ (e i).val)
  have hg : Function.Injective g := by
    apply Fin.cons_injective_iff.mpr
    refine ⟨?_, Subtype.val_injective.comp e.injective⟩
    rintro ⟨i, hi⟩
    exact (e i).property.ne hi.symm
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair f g (Fin.castAdd_injective 4 4) hg
  have hzero : p 0 = 0 := hp 0
  have hsucc (i : Fin 3) : p (f i.succ) = (e i).val := hp i.succ
  refine ⟨p, ?_⟩
  ext j
  simp only [mem_neighborFinset, comap_adj, hzero]
  constructor
  · intro hj
    obtain ⟨i, hi⟩ := e.surjective ⟨p j, hj⟩
    have he : j = f i.succ := p.injective ((congrArg Subtype.val hi).symm.trans
      (hsucc i).symm)
    rw [he]
    fin_cases i <;> decide
  · intro hj
    have hm : ∃ i : Fin 3, j = f i.succ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    obtain ⟨i, rfl⟩ := hm
    rw [hsucc]
    exact (e i).property

end CubicEight

-- Theorem SE4 (Remark 4.14), valency three
/-- The cubic case of `res:414-SE4`, Remark 4.14 of [CGSS]: every cubic graph on
eight vertices is isomorphic to one of the six models in `cgss/proofs/reg8/reg8.tex`.
The proof fixes a vertex and its neighbours and checks all degree-compatible completions. -/
theorem IsRegularOfDegree.nonempty_iso_of_three_of_card_eq_eight
    {V : Type*} [Fintype V] {X : SimpleGraph V} [DecidableRel X.Adj]
    (hr : X.IsRegularOfDegree 3) (hn : Fintype.card V = 8) :
    Nonempty (X ≃g twoK4) ∨ Nonempty (X ≃g cubeGraph) ∨
      Nonempty (X ≃g wagnerGraph) ∨ Nonempty (X ≃g truncatedK33Graph) ∨
      Nonempty (X ≃g twiceTruncatedK4Graph) ∨ Nonempty (X ≃g twoDiamondsGraph) := by
  classical
  let e := (Fintype.equivFinOfCardEq hn).symm
  let Y := X.comap e
  have hY : Y.IsRegularOfDegree 3 := fun i ↦ ((Iso.comap e X).degree_eq i).symm.trans (hr _)
  obtain ⟨p, hp⟩ := CubicEight.exists_iso_neighborFinset_zero Y hY
  have hZ : (Y.comap p).IsRegularOfDegree 3 :=
    fun i ↦ ((Iso.comap p Y).degree_eq i).symm.trans (hY _)
  obtain ⟨i, ⟨f⟩⟩ := CubicEight.nonempty_iso_of_neighborFinset_zero (Y.comap p) hZ hp
  have hh : Nonempty (X ≃g CubicEight.model i) :=
    ⟨(Iso.comap e X).symm.trans ((Iso.comap p Y).symm.trans f)⟩
  fin_cases i <;> simp [CubicEight.model] at hh <;> tauto

end SimpleGraph
