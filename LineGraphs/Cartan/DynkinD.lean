/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.DynkinSpectrum

/-!
# The finite D spectral certificate

The two short arms are the first pair of affine D leaves; the long arm is the
affine D spine. The unused pair of leaves makes containment proper.
-/

namespace SimpleGraph

private def finiteDVertex (c : ℕ) : ArmVertex ![1, 1, c] → Fin (c + 1) ⊕ Fin 4
  | none => Sum.inl 0
  | some ⟨r, i⟩ =>
    if hr : r = 0 then Sum.inr 0
    else if hr' : r = 1 then Sum.inr 1
    else Sum.inl ⟨i.val + 1, by
      have hr2 : r = 2 := by fin_cases r <;> simp_all
      have hi : i.val < c := by simpa [hr2] using i.isLt
      omega⟩

/-- Steps `rdDfour` and `rdDmany` of the weighted dichotomy, Remark 3.11 of [CGSS]:
the finite D arm tree embeds in affine D by adding two leaves at the far end. -/
def finiteDToAffineD (c : ℕ) : Copy (armTree ![1, 1, c]) (smithD (c + 4)) where
  toHom :=
    { toFun := finiteDVertex c
      map_rel' := by
        rintro (_ | ⟨r, i⟩) (_ | ⟨s, j⟩) h
        · exact h.elim
        · have hj : j.val = 0 := h
          fin_cases s <;>
            simp [finiteDVertex, smithD, WeightedGraph.affineD, WeightedGraph.attachLeaves,
              WeightedGraph.path, WeightedGraph.support, hj, Fin.ext_iff]
        · have hi : i.val = 0 := h
          fin_cases r <;>
            simp [finiteDVertex, smithD, WeightedGraph.affineD, WeightedGraph.attachLeaves,
              WeightedGraph.path, WeightedGraph.support, hi, Fin.ext_iff]
        · dsimp only [armTree] at h
          obtain ⟨hrs, hij⟩ := h
          subst s
          fin_cases r
          · have hi : i.val < 1 := i.isLt
            have hj : j.val < 1 := j.isLt
            omega
          · have hi : i.val < 1 := i.isLt
            have hj : j.val < 1 := j.isLt
            omega
          · dsimp only [finiteDVertex]
            dsimp only [smithD, WeightedGraph.affineD, WeightedGraph.attachLeaves,
              WeightedGraph.path, WeightedGraph.support]
            simp only [show (⟨2, by decide⟩ : Fin 3) ≠ 0 by decide,
              show (⟨2, by decide⟩ : Fin 3) ≠ 1 by decide, dite_false]
            split_ifs <;> norm_num
            all_goals omega }
  injective' := by
    rintro (_ | ⟨r, i⟩) (_ | ⟨s, j⟩) h
    · rfl
    · fin_cases s
      · simp [finiteDVertex] at h
      · simp [finiteDVertex] at h
      · dsimp only [finiteDVertex] at h
        have hh := congrArg Fin.val (Sum.inl.inj h)
        simp only [Fin.val_zero] at hh
        omega
    · fin_cases r
      · simp [finiteDVertex] at h
      · simp [finiteDVertex] at h
      · dsimp only [finiteDVertex] at h
        have hh := congrArg Fin.val (Sum.inl.inj h)
        simp only [Fin.val_zero] at hh
        omega
    · fin_cases r <;> fin_cases s
      · have hi : i.val < 1 := i.isLt
        have hj : j.val < 1 := j.isLt
        have hij : i = j := Fin.ext (by omega)
        subst j
        rfl
      · simp [finiteDVertex] at h
      · simp [finiteDVertex] at h
      · simp [finiteDVertex] at h
      · have hi : i.val < 1 := i.isLt
        have hj : j.val < 1 := j.isLt
        have hij : i = j := Fin.ext (by omega)
        subst j
        rfl
      · simp [finiteDVertex] at h
      · simp [finiteDVertex] at h
      · simp [finiteDVertex] at h
      · dsimp only [finiteDVertex] at h
        have hh := congrArg Fin.val (Sum.inl.inj h)
        have hij : i = j := Fin.ext (by dsimp only [Fin.val_mk] at hh; omega)
        subst j
        rfl

end SimpleGraph

namespace WeightedGraph

open Matrix SimpleGraph

/-- Every finite D arm tree has maximum Rayleigh value strictly less than two. -/
theorem finiteD_maxRayleigh_lt_two (c : ℕ) :
    maxRayleigh (unit (armTree ![1, 1, c])).isHermitian < 2 := by
  classical
  let e := finiteDToAffineD c
  have he : (affineD (c + 4)).Contains (unit (armTree ![1, 1, c])) e.toEmbedding := by
    rw [affineD_eq_unit]
    apply ((unit (smithD (c + 4))).unit_contains_iff_support_embedding _
      (armTree ![1, 1, c]) e.toEmbedding).mpr
    · intro i j hij
      rw [support_unit]
      exact e.toHom.map_adj hij
    · intro i j hij
      change 1 ≤ if (smithD (c + 4)).Adj i j then (1 : ℝ) else 0
      have h : (smithD (c + 4)).Adj i j := by simpa only [support_unit] using hij
      simp [h]
  apply maxRayleigh_lt_two_of_contains_affine
    (.d (c + 4) (by omega) (Equiv.refl _) rfl) he
  simp [ArmVertex, Fintype.card_sigma, Fin.sum_univ_succ]
  omega

/-- Every finite Dynkin weighted model is strictly below the affine spectral threshold. -/
theorem HasDynkinLabelling.maxRayleigh_lt_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {X : WeightedGraph ι} (hX : X.HasDynkinLabelling) :
    maxRayleigh X.isHermitian < 2 := by
  cases hX with
  | a n hn e h =>
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    subst X
    exact (Matrix.IsHermitian.maxRayleigh_reindex _ e).trans_lt (unit_path_maxRayleigh_lt_two n)
  | doublePath n k hk hp e h =>
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    subst X
    apply (Matrix.IsHermitian.maxRayleigh_reindex _ e).trans_lt
    rcases hp with hp | hp | ⟨rfl, rfl⟩
    · exact terminal_double_path_maxRayleigh_lt_two n k hk (Or.inl hp)
    · exact terminal_double_path_maxRayleigh_lt_two n k hk (Or.inr hp)
    · exact middle_double_path_maxRayleigh_lt_two
  | d c _ e h =>
    subst X
    exact (Matrix.IsHermitian.maxRayleigh_reindex _ e).trans_lt (finiteD_maxRayleigh_lt_two c)
  | e₆ e h =>
    subst X
    exact (Matrix.IsHermitian.maxRayleigh_reindex _ e).trans_lt finiteE_maxRayleigh_lt_two.1
  | e₇ e h =>
    subst X
    exact (Matrix.IsHermitian.maxRayleigh_reindex _ e).trans_lt finiteE_maxRayleigh_lt_two.2.1
  | e₈ e h =>
    subst X
    exact (Matrix.IsHermitian.maxRayleigh_reindex _ e).trans_lt finiteE_maxRayleigh_lt_two.2.2
  | g₂ e h =>
    subst X
    exact (Matrix.IsHermitian.maxRayleigh_reindex _ e).trans_lt tripleEdge_maxRayleigh_lt_two

/-- Among connected graphs with Cartan edge weights, the finite Dynkin weighted models
are exactly those whose maximum Rayleigh value is strictly less than two. -/
theorem hasDynkinLabelling_iff_maxRayleigh_lt_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {X : WeightedGraph ι} (hconn : X.support.Connected)
    (hweights : ∀ i j, X.support.Adj i j →
      X.weights i j = 1 ∨ X.weights i j = Real.sqrt 2 ∨ X.weights i j = Real.sqrt 3) :
    X.HasDynkinLabelling ↔ maxRayleigh X.isHermitian < 2 :=
  ⟨HasDynkinLabelling.maxRayleigh_lt_two,
    dynkin_labelling_of_maxRayleigh_lt_two hconn hweights⟩

/-- No finite Dynkin weighted model contains an affine obstruction. -/
theorem HasDynkinLabelling.not_contains_affine {ι κ : Type*}
    [Finite ι] [Nonempty ι] [Finite κ] [Nonempty κ]
    {X : WeightedGraph ι} (hX : X.HasDynkinLabelling)
    {Y : WeightedGraph κ} (hY : Y.IsAffineObstruction) (e : κ ↪ ι) : ¬ X.Contains Y e := by
  classical
  let _ := Fintype.ofFinite ι
  exact not_contains_affine_of_maxRayleigh_lt_two hX.maxRayleigh_lt_two hY e

/-- The weighted dichotomy of Remark 3.11: exactly one of affine containment and a
finite Dynkin weighted labelling holds. Every graph in the second alternative has
maximum Rayleigh value strictly below two. -/
theorem affine_or_dynkin {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : WeightedGraph ι} (hconn : X.support.Connected)
    (hweights : ∀ i j, X.support.Adj i j →
      X.weights i j = 1 ∨ X.weights i j = Real.sqrt 2 ∨ X.weights i j = Real.sqrt 3) :
    (X.ContainsAffineObstruction ∨ X.HasDynkinLabelling) ∧
      ¬ (X.ContainsAffineObstruction ∧ X.HasDynkinLabelling) ∧
      (X.HasDynkinLabelling → maxRayleigh X.isHermitian < 2) := by
  classical
  refine ⟨?_, ?_, HasDynkinLabelling.maxRayleigh_lt_two⟩
  · by_cases h : X.ContainsAffineObstruction
    · exact Or.inl h
    · exact Or.inr (dynkin_labelling_of_no_affine hconn hweights h)
  · rintro ⟨hcontains, hdynkin⟩
    exact not_containsAffineObstruction_of_maxRayleigh_lt_two
      hdynkin.maxRayleigh_lt_two hcontains

end WeightedGraph
