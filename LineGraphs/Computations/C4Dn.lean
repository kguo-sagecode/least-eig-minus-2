/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4Classical
import LineGraphs.Graphs.Basic

/-!
# The marked star in Dₙ

The star is `(e₁ - e₂, e₂ - e₃)` of the blueprint's C4 table, that is `(e₀ - e₁, e₁ - e₂)` in
`Fin n`. Its Γa consists of `e₀ + e₁` and `-e₂ ± eⱼ` for `j ≥ 3` (the blueprint's
`{e₁ + e₂} ∪ {-e₃ ± eⱼ : 4 ≤ j ≤ ℓ}`), and its graph is the friendship graph.
-/

open scoped RealInnerProductSpace

namespace LineSystem

/-- The first root `e₀ - e₁` of the D star. -/
def Dn.starA {n : ℕ} (hn : 4 ≤ n) : Dn.Index n :=
  (⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change (0 : ℕ) < 1; omega⟩, false, true)

/-- The second root `e₁ - e₂` of the D star. -/
def Dn.starB {n : ℕ} (hn : 4 ≤ n) : Dn.Index n :=
  (⟨(⟨1, by omega⟩, ⟨2, by omega⟩), by change (1 : ℕ) < 2; omega⟩, false, true)

/-- C4: Hypothesis 2.4 for `(e₀-e₁, e₁-e₂, -e₀+e₂)`, the blueprint's `(e₁-e₂, e₂-e₃)`. -/
noncomputable def Dn.hyp24 {n : ℕ} (hn : 4 ≤ n) :
    Hyp24 (EuclideanSpace ℝ (Fin n)) :=
  (Dn.integerModel n).hyp24 (isIndecomposable_Dn hn) (isStarClosed_Dn n)
    (Dn.starA hn) (Dn.starB hn) (by
      change integerInner (dnRoot (Dn.starA hn)) (dnRoot (Dn.starB hn)) = -1
      simp [Dn.starA, Dn.starB, dnRoot, pairVector, rootSign, Fin.ext_iff])

/-- The first root of the D star is `e₀ - e₁` (the blueprint's `e₁ - e₂`). -/
theorem Dn.hyp24_a {n : ℕ} (hn : 4 ≤ n) : (Dn.hyp24 hn).a =
    EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) - EuclideanSpace.single ⟨1, by omega⟩ 1 := by
  change integerVector 1 (dnRoot (Dn.starA hn)) = _
  ext k
  simp [dnRoot, Dn.starA, pairVector, rootSign, Pi.single_apply]
  split_ifs <;> norm_num

/-- The second root of the D star is `e₁ - e₂` (the blueprint's `e₂ - e₃`). -/
theorem Dn.hyp24_b {n : ℕ} (hn : 4 ≤ n) : (Dn.hyp24 hn).b =
    EuclideanSpace.single ⟨1, by omega⟩ (1 : ℝ) - EuclideanSpace.single ⟨2, by omega⟩ 1 := by
  change integerVector 1 (dnRoot (Dn.starB hn)) = _
  ext k
  simp [dnRoot, Dn.starB, pairVector, rootSign, Pi.single_apply]
  split_ifs <;> norm_num

/-- The common vertex `e₀ + e₁` and the two other vertices `-e₂ ± eᵢ₊₃` of each triangle. -/
def Dn.gammaLabel {n : ℕ} (hn : 4 ≤ n) : Option (Fin (n - 3) × Bool) → Dn.Index n
  | none => (⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change (0 : ℕ) < 1; omega⟩, false, false)
  | some (i, s) => (⟨(⟨2, by omega⟩, ⟨i.val + 3, by omega⟩), by
      change 2 < i.val + 3; omega⟩, true, s)

/-- Computation C4, step `s3c4Dvertices` of the Section 3 blueprint: classify the ordered
support of a root with the two marked inner products. -/
private theorem dn_gamma_condition {n : ℕ} (hn : 4 ≤ n)
    (i j : Fin n) (hij : i < j) (s t : Bool) :
    (integerInner (dnRoot (⟨(i, j), hij⟩, s, t)) (dnRoot (Dn.starA hn)) = 0 ∧
      integerInner (dnRoot (⟨(i, j), hij⟩, s, t)) (dnRoot (Dn.starB hn)) = 1) ↔
      (i.val = 0 ∧ j.val = 1 ∧ s = false ∧ t = false) ∨
      (i.val = 2 ∧ 3 ≤ j.val ∧ s = true) := by
  change i.val < j.val at hij
  have hj0 : j.val ≠ 0 := by omega
  simp only [Dn.starA, Dn.starB, dnRoot]
  rw [integerInner_pairVector, integerInner_pairVector]
  simp only [pairVector, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  by_cases hi0 : i.val = 0
  · by_cases hj1 : j.val = 1
    · cases s <;> cases t <;> norm_num [rootSign, hi0, hj1]
    · by_cases hj2 : j.val = 2
      · cases s <;> cases t <;> norm_num [rootSign, hi0, hj2]
      · cases s <;> cases t <;> norm_num [rootSign, hi0, hj0, hj1, hj2]
  · by_cases hi1 : i.val = 1
    · by_cases hj2 : j.val = 2
      · cases s <;> cases t <;> norm_num [rootSign, hi1, hj2]
      · have hj1 : j.val ≠ 1 := by omega
        cases s <;> cases t <;> norm_num [rootSign, hi1, hj0, hj1, hj2]
    · have hj1 : j.val ≠ 1 := by omega
      by_cases hi2 : i.val = 2
      · have hj2 : j.val ≠ 2 := by omega
        have hj3 : 3 ≤ j.val := by omega
        cases s <;> cases t <;> norm_num [rootSign, hi2, hj0, hj1, hj2, hj3]
      · have hj2 : j.val ≠ 2 := by omega
        cases s <;> cases t <;> norm_num [rootSign, hi0, hi1, hi2, hj0, hj1, hj2]

/-- Exact characterization of the roots in the marked Γa. -/
theorem Dn.mem_Γa_iff {n : ℕ} (hn : 4 ≤ n) (p : Dn.Index n) :
    integerVector 1 (dnRoot p) ∈ (Dn.hyp24 hn).Γa ↔ ∃ i, Dn.gammaLabel hn i = p := by
  change integerVector (Dn.integerModel n).c ((Dn.integerModel n).v p) ∈
    (Dn.hyp24 hn).Γa ↔ _
  rw [Dn.hyp24, (Dn.integerModel n).mem_Γa_iff]
  rcases p with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  change (integerInner (dnRoot (⟨(i, j), hij⟩, s, t)) (dnRoot (Dn.starA hn)) = 0 ∧
    integerInner (dnRoot (⟨(i, j), hij⟩, s, t)) (dnRoot (Dn.starB hn)) = 1) ↔ _
  rw [dn_gamma_condition hn]
  constructor
  · rintro (⟨hi, hj, rfl, rfl⟩ | ⟨hi, hj, rfl⟩)
    · refine ⟨none, ?_⟩
      simp [Dn.gammaLabel, Prod.ext_iff, Subtype.ext_iff, Fin.ext_iff, hi, hj]
    · refine ⟨some (⟨j.val - 3, by omega⟩, t), ?_⟩
      simp [Dn.gammaLabel, Prod.ext_iff, Subtype.ext_iff, Fin.ext_iff, hi, Nat.sub_add_cancel hj]
  · rintro ⟨x, hx⟩
    have hi := congrArg (fun p : Dn.Index n => p.1.val.1.val) hx
    have hj := congrArg (fun p : Dn.Index n => p.1.val.2.val) hx
    have hs := congrArg (fun p : Dn.Index n => p.2.1) hx
    have ht := congrArg (fun p : Dn.Index n => p.2.2) hx
    rcases x with _ | ⟨k, u⟩
    · exact Or.inl ⟨hi.symm, hj.symm, hs.symm, ht.symm⟩
    · dsimp [Dn.gammaLabel] at hj
      exact Or.inr ⟨hi.symm, by omega, hs.symm⟩

/-- The labels identify the friendship vertices with the real set Γa. -/
noncomputable def Dn.gammaEquiv {n : ℕ} (hn : 4 ≤ n) :
    Option (Fin (n - 3) × Bool) ≃ (Dn.hyp24 hn).Γa :=
  (Dn.integerModel n).subsetEquiv _ (Dn.hyp24 hn).Γa_subset_Φ (Dn.gammaLabel hn)
    (by
      rintro (_ | ⟨i, s⟩) (_ | ⟨j, t⟩) h
      · rfl
      · have he := congrArg (fun p : Dn.Index n => p.1.val.1.val) h
        simp [Dn.gammaLabel] at he
      · have he := congrArg (fun p : Dn.Index n => p.1.val.1.val) h
        simp [Dn.gammaLabel] at he
      · have he := congrArg (fun p : Dn.Index n => p.1.val.2.val) h
        have hs := congrArg (fun p : Dn.Index n => p.2.2) h
        have hij : i = j := by apply Fin.ext; dsimp [Dn.gammaLabel] at he; omega
        exact congrArg some (Prod.ext hij hs))
    (Dn.mem_Γa_iff hn)

/-- C4: the marked orthogonality graph is `n - 3` triangles sharing one vertex. -/
noncomputable def Dn.orthGraphIso {n : ℕ} (hn : 4 ≤ n) :
    SimpleGraph.friendship (n - 3) ≃g (Dn.hyp24 hn).orthGraph where
  toEquiv := Dn.gammaEquiv hn
  map_rel_iff' := by
    intro x y
    change (⟪integerVector 1 (dnRoot (Dn.gammaLabel hn x)),
      integerVector 1 (dnRoot (Dn.gammaLabel hn y))⟫ = 0) ↔ _
    rw [inner_integerVector]
    simp only [one_mul, Int.cast_eq_zero]
    rcases x with _ | ⟨i, s⟩ <;> rcases y with _ | ⟨j, t⟩
    · simp [Dn.gammaLabel, dnRoot, pairVector, rootSign, Fin.ext_iff, SimpleGraph.friendship]
    · cases t <;>
        simp [Dn.gammaLabel, dnRoot, pairVector, rootSign, Fin.ext_iff, SimpleGraph.friendship]
    · cases s <;>
        simp [Dn.gammaLabel, dnRoot, pairVector, rootSign, Fin.ext_iff, SimpleGraph.friendship]
    · cases s <;> cases t <;> by_cases he : i = j <;>
        simp_all [Dn.gammaLabel, dnRoot, pairVector, rootSign, Fin.ext_iff,
          SimpleGraph.friendship]

/-- C4: the order of the marked graph of Dₙ. -/
theorem Dn.card_Γa {n : ℕ} (hn : 4 ≤ n) : (Dn.hyp24 hn).Γa.ncard = 2 * (n - 3) + 1 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (Dn.gammaEquiv hn), Nat.card_eq_fintype_card]
  simp [Nat.mul_comm]

end LineSystem
