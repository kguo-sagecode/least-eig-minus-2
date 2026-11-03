/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4Classical

/-!
# The marked star in Aₙ

The vertices of Γa are precisely `eᵢ-e₂` with `3 ≤ i ≤ n`.
-/

open scoped RealInnerProductSpace

namespace LineSystem

/-- The first root of the classical A star. -/
def An.starA {n : ℕ} (hn : 2 ≤ n) : An.Index n :=
  ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩

/-- The second root of the classical A star. -/
def An.starB {n : ℕ} (hn : 2 ≤ n) : An.Index n :=
  ⟨(⟨1, by omega⟩, ⟨2, by omega⟩), by simp [Fin.ext_iff]⟩

/-- C4: Hypothesis 2.4 for the ordered star `(e₀-e₁, e₁-e₂, e₂-e₀)`. -/
noncomputable def An.hyp24 {n : ℕ} (hn : 2 ≤ n) :
    Hyp24 (EuclideanSpace ℝ (Fin (n + 1))) :=
  (An.integerModel n).hyp24 (isIndecomposable_An (by omega)) (isStarClosed_An n)
    (An.starA hn) (An.starB hn) (by
      change integerInner (anRoot (An.starA hn)) (anRoot (An.starB hn)) = -1
      simp [An.starA, An.starB, anRoot, pairVector, Fin.ext_iff])

/-- The first root of the A star is `e₀ - e₁` (the blueprint's `e₁ - e₂`). -/
theorem An.hyp24_a {n : ℕ} (hn : 2 ≤ n) : (An.hyp24 hn).a =
    EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) - EuclideanSpace.single ⟨1, by omega⟩ 1 := by
  change integerVector 1 (anRoot (An.starA hn)) = _
  ext k
  simp [anRoot, An.starA, pairVector, Pi.single_apply]
  split_ifs <;> norm_num

/-- The second root of the A star is `e₁ - e₂` (the blueprint's `e₂ - e₃`). -/
theorem An.hyp24_b {n : ℕ} (hn : 2 ≤ n) : (An.hyp24 hn).b =
    EuclideanSpace.single ⟨1, by omega⟩ (1 : ℝ) - EuclideanSpace.single ⟨2, by omega⟩ 1 := by
  change integerVector 1 (anRoot (An.starB hn)) = _
  ext k
  simp [anRoot, An.starB, pairVector, Pi.single_apply]
  split_ifs <;> norm_num

private theorem an_gamma_condition {m : ℕ} (z o t i j : Fin m)
    (hzo : z ≠ o) (hzt : z ≠ t) (hot : o ≠ t) (hij : i ≠ j) :
    (integerInner (pairVector i j 1 (-1)) (pairVector z o 1 (-1)) = 0 ∧
      integerInner (pairVector i j 1 (-1)) (pairVector o t 1 (-1)) = 1) ↔
      j = t ∧ i ≠ z ∧ i ≠ o ∧ i ≠ t := by
  rw [integerInner_pairVector, integerInner_pairVector]
  by_cases hi0 : i = z <;> by_cases hi1 : i = o <;> by_cases hi2 : i = t <;>
    by_cases hj0 : j = z <;> by_cases hj1 : j = o <;> by_cases hj2 : j = t <;>
    simp_all [pairVector]

/-- The Γa labels are the remaining coordinates, with a common negative coordinate 2. -/
def An.gammaLabel {n : ℕ} (hn : 2 ≤ n) (i : Fin (n - 2)) : An.Index n :=
  ⟨(⟨i.val + 3, by omega⟩, ⟨2, by omega⟩), by simp [Fin.ext_iff]⟩

/-- Exact coordinate characterization of the marked Γa. -/
theorem An.mem_Γa_iff {n : ℕ} (hn : 2 ≤ n) (p : An.Index n) :
    integerVector 1 (anRoot p) ∈ (An.hyp24 hn).Γa ↔ ∃ i, An.gammaLabel hn i = p := by
  change integerVector (An.integerModel n).c ((An.integerModel n).v p) ∈
    (An.hyp24 hn).Γa ↔ _
  rw [An.hyp24, (An.integerModel n).mem_Γa_iff]
  rcases p with ⟨⟨i, j⟩, hij⟩
  change (integerInner (pairVector i j 1 (-1))
    (pairVector ⟨0, by omega⟩ ⟨1, by omega⟩ 1 (-1)) = 0 ∧
    integerInner (pairVector i j 1 (-1))
      (pairVector ⟨1, by omega⟩ ⟨2, by omega⟩ 1 (-1)) = 1) ↔ _
  rw [an_gamma_condition _ _ _ _ _ (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) hij]
  constructor
  · rintro ⟨hj, hi0, hi1, hi2⟩
    have h0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    have h1 : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
    have h2 : i.val ≠ 2 := fun h => hi2 (Fin.ext h)
    refine ⟨⟨i.val - 3, by omega⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      dsimp [An.gammaLabel]
      omega
    · exact hj.symm
  · rintro ⟨k, hk⟩
    have he := congrArg Subtype.val hk
    have hi : i.val = k.val + 3 := (congrArg (fun p => p.1.val) he).symm
    have hj : j.val = 2 := (congrArg (fun p => p.2.val) he).symm
    refine ⟨Fin.ext hj, ?_, ?_, ?_⟩ <;> intro h <;>
      have hh := congrArg Fin.val h <;> dsimp at hh <;> omega

/-- The finite labels are in bijection with the real set Γa. -/
noncomputable def An.gammaEquiv {n : ℕ} (hn : 2 ≤ n) : Fin (n - 2) ≃ (An.hyp24 hn).Γa :=
  (An.integerModel n).subsetEquiv _ (An.hyp24 hn).Γa_subset_Φ (An.gammaLabel hn)
    (by
      intro i j h
      have he := congrArg (fun p : An.Index n => p.val.1.val) h
      apply Fin.ext
      dsimp [An.gammaLabel] at he
      omega) (An.mem_Γa_iff hn)

/-- C4: the graph on Γa in Aₙ is the void graph on `n - 2` vertices. -/
noncomputable def An.orthGraphIso {n : ℕ} (hn : 2 ≤ n) :
    (⊥ : SimpleGraph (Fin (n - 2))) ≃g (An.hyp24 hn).orthGraph where
  toEquiv := An.gammaEquiv hn
  map_rel_iff' := by
    intro i j
    change (⟪integerVector 1 (anRoot (An.gammaLabel hn i)),
      integerVector 1 (anRoot (An.gammaLabel hn j))⟫ = 0) ↔ False
    rw [inner_integerVector]
    simp only [one_mul, Int.cast_eq_zero, iff_false]
    simp [anRoot, An.gammaLabel, pairVector, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

/-- C4: the order of the marked orthogonality graph of Aₙ. -/
theorem An.card_Γa {n : ℕ} (hn : 2 ≤ n) : (An.hyp24 hn).Γa.ncard = n - 2 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (An.gammaEquiv hn), Nat.card_eq_fintype_card]
  exact Fintype.card_fin _

end LineSystem
