/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Isomorphisms
import LineGraphs.Computations.C9ModelIsos

/-!
# Uniqueness of the folded five-cube and the Clebsch graph

Lemmas `lem:414-foldiso` and `lem:414-SE2` of the blueprint for Remark 4.14
of [CGSS]. The vertices outside a fixed vertex and its neighbourhood are
labelled by pairs of neighbours, as in `cgss/proofs/clebsch/clebsch.tex`, Section 3.
-/

open scoped symmDiff

namespace SimpleGraph

variable {V : Type*} [Fintype V] {X : SimpleGraph V} [DecidableRel X.Adj]

-- Lemma (the folded five-cube from its parameters), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-foldiso`, Remark 4.14 of [CGSS]: a strongly regular graph
with parameters `(16,5,0,2)` is isomorphic to the even-subset folded five-cube. -/
theorem IsSRGWith.nonempty_iso_foldedFiveCube (h : X.IsSRGWith 16 5 0 2) :
    Nonempty (X ≃g foldedFiveCube) := by
  classical
  obtain ⟨u⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by rw [h.card]; omega)
  -- Step `s414foldcocl`: every neighbourhood is a coclique.
  have htf {x y z : V} (hxy : X.Adj x y) (hxz : X.Adj x z) (hyz : X.Adj y z) :
      False := by
    have hpos : 0 < Fintype.card (X.commonNeighbors x y) :=
      Fintype.card_pos_iff.mpr ⟨⟨z, hxz, hyz⟩⟩
    rw [h.of_adj x y hxy] at hpos
    omega
  let β : X.neighborSet u ≃ Fin 5 := Fintype.equivOfCardEq (by
    rw [card_neighborSet_eq_degree, h.regular u, Fintype.card_fin])
  let φ (v : V) : Finset (Fin 5) := Finset.univ.filter fun i ↦ X.Adj v (β.symm i)
  have hmem (v : V) (i : Fin 5) : i ∈ φ v ↔ X.Adj v (β.symm i) := by simp [φ]
  have hφcard (v : V) : (φ v).card = Fintype.card (X.commonNeighbors u v) := by
    rw [← Fintype.card_coe (φ v)]
    apply Fintype.card_congr
    refine
      { toFun := fun i ↦ ⟨β.symm i, (β.symm i).property, (hmem v i).mp i.property⟩
        invFun := fun w ↦ ⟨β ⟨w, w.property.1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [hmem]
      simpa only [Equiv.symm_apply_apply, mem_neighborSet] using w.property.2
    · intro i
      apply Subtype.ext
      exact β.apply_symm_apply i
    · intro w
      exact Subtype.ext (congrArg (fun z : X.neighborSet u ↦ (z : V))
        (β.symm_apply_apply ⟨w, w.property.1⟩))
  -- Step `s414foldphi`: an outside vertex has a pair as its label.
  have htwo (v : V) (hvu : v ≠ u) (huv : ¬ X.Adj u v) : (φ v).card = 2 := by
    rw [hφcard, h.of_not_adj hvu.symm huv]
  -- Step `s414foldbij`: two outside vertices cannot have the same pair.
  have hφinj (v w : V) (hvu : v ≠ u) (hwu : w ≠ u)
      (huv : ¬ X.Adj u v) (huw : ¬ X.Adj u w) (he : φ v = φ w) : v = w := by
    obtain ⟨i, j, hij, hp⟩ := Finset.card_eq_two.mp (htwo v hvu huv)
    have hiv : X.Adj v (β.symm i) := (hmem v i).mp (by simp [hp])
    have hjv : X.Adj v (β.symm j) := (hmem v j).mp (by simp [hp])
    have hiw : X.Adj w (β.symm i) := (hmem w i).mp (by rw [← he, hp]; simp)
    have hjw : X.Adj w (β.symm j) := (hmem w j).mp (by rw [← he, hp]; simp)
    have hne : (β.symm i : V) ≠ β.symm j := fun he ↦
      hij (β.symm.injective (Subtype.ext he))
    have hna : ¬ X.Adj (β.symm i) (β.symm j) := fun ha ↦
      htf ha (β.symm i).property.symm (β.symm j).property.symm
    by_contra hvw
    have hsub : {u, v, w} ⊆ (X.commonNeighbors (β.symm i) (β.symm j)).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Set.mem_toFinset.mpr ⟨(β.symm i).property.symm, (β.symm j).property.symm⟩
      · exact Set.mem_toFinset.mpr ⟨hiv.symm, hjv.symm⟩
      · exact Set.mem_toFinset.mpr ⟨hiw.symm, hjw.symm⟩
    have hh := Finset.card_le_card hsub
    rw [Set.toFinset_card, h.of_not_adj hne hna] at hh
    have hc : ({u, v, w} : Finset V).card = 3 := by simp [hvu.symm, hwu.symm, hvw]
    omega
  let label (v : V) : Finset (Fin 5) :=
    if v = u then ∅ else if huv : X.Adj u v then Finset.univ.erase (β ⟨v, huv⟩) else φ v
  have hzero : label u = ∅ := by simp [label]
  have hnear (v : V) (huv : X.Adj u v) :
      label v = Finset.univ.erase (β ⟨v, huv⟩) := by simp [label, huv.ne.symm, huv]
  have hfar (v : V) (hvu : v ≠ u) (huv : ¬ X.Adj u v) : label v = φ v := by
    simp [label, hvu, huv]
  have hsize (v : V) : (label v).card = if v = u then 0 else if X.Adj u v then 4 else 2 := by
    by_cases hvu : v = u
    · subst v; simp [hzero]
    by_cases huv : X.Adj u v
    · simp [hnear v huv, hvu, huv]
    · simp [hfar v hvu huv, hvu, huv, htwo v hvu huv]
  have heven (v : V) : Even (label v).card := by
    rw [hsize]
    split_ifs <;> norm_num
  -- Step `s414foldf`: the three label sizes separate the three parts.
  have hinj : Function.Injective label := by
    intro v w he
    have hs := congrArg Finset.card he
    rw [hsize, hsize] at hs
    by_cases hvu : v = u
    · subst v
      by_cases hwu : w = u
      · exact hwu.symm
      · by_cases huw : X.Adj u w <;> simp [hwu, huw] at hs
    by_cases hwu : w = u
    · subst w
      by_cases huv : X.Adj u v <;> simp [hvu, huv] at hs
    by_cases huv : X.Adj u v <;> by_cases huw : X.Adj u w
    · rw [hnear v huv, hnear w huw, ← Finset.compl_singleton,
        ← Finset.compl_singleton] at he
      have he' := compl_injective he
      have heβ : β ⟨v, huv⟩ = β ⟨w, huw⟩ := Finset.singleton_injective he'
      exact congrArg Subtype.val (β.injective heβ)
    · simp [hvu, hwu, huv, huw] at hs
    · simp [hvu, hwu, huv, huw] at hs
    · exact hφinj v w hvu hwu huv huw (by simpa only [hfar v hvu huv, hfar w hwu huw] using he)
  -- Step `s414foldsd`: the only mixed label calculation is on five points.
  have hmixed : ∀ (i : Fin 5) (s : Finset (Fin 5)), s.card = 2 → i ∈ s →
      ((Finset.univ.erase i) ∆ s).card = 4 := by decide +kernel
  have hmap {v w : V} (hvw : X.Adj v w) : (label v ∆ label w).card = 4 := by
    by_cases hvu : v = u
    · subst v
      simp [hzero, hnear w hvw, Finset.symmDiff_def]
    by_cases hwu : w = u
    · subst w
      simp [hzero, hnear v hvw.symm, Finset.symmDiff_def]
    by_cases huv : X.Adj u v <;> by_cases huw : X.Adj u w
    · exact (htf hvw huv.symm huw.symm).elim
    · rw [hnear v huv, hfar w hwu huw]
      apply hmixed _ _ (htwo w hwu huw)
      rw [hmem]
      simpa only [Equiv.symm_apply_apply] using hvw.symm
    · rw [symmDiff_comm, hnear w huw, hfar v hvu huv]
      apply hmixed _ _ (htwo v hvu huv)
      rw [hmem]
      simpa only [Equiv.symm_apply_apply] using hvw
    · rw [hfar v hvu huv, hfar w hwu huw]
      have hd : Disjoint (φ v) (φ w) := Finset.disjoint_left.mpr fun i hiv hiw ↦
        htf hvw ((hmem v i).mp hiv) ((hmem w i).mp hiw)
      rw [Finset.symmDiff_eq_union hd, Finset.card_union_of_disjoint hd,
        htwo v hvu huv, htwo w hwu huw]
  let f : X →g foldedFiveCube :=
    { toFun := fun v ↦ ⟨label v, heven v⟩
      map_rel' := fun {v w} hvw ↦ hmap hvw }
  have hf : Function.Injective f := fun v w he ↦ hinj (congrArg Subtype.val he)
  -- Steps `s414foldO` and `s414folddisj`: equal degrees exhaust the neighbours.
  exact h.regular.nonempty_iso_of_injective_hom foldedFiveCube_isSRGWith.regular f hf
    (h.card.trans foldedFiveCube_isSRGWith.card.symm)

-- Lemma (SE2: the Clebsch graph), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-SE2`, Remark 4.14 of [CGSS]: a strongly regular graph with
parameters `(16,10,6,6)` is isomorphic to the vector Clebsch graph of Example 4.8. -/
theorem IsSRGWith.nonempty_iso_clebsch (h : X.IsSRGWith 16 10 6 6) :
    Nonempty (X ≃g clebsch) := by
  classical
  have hc : Xᶜ.IsSRGWith 16 5 0 2 := by simpa using h.compl
  obtain ⟨e⟩ := hc.nonempty_iso_foldedFiveCube
  have he : X ≃g foldedFiveCubeᶜ := by simpa only [compl_compl] using e.compl
  exact ⟨he.trans clebsch.foldedFiveCubeComplIso.symm⟩

end SimpleGraph
