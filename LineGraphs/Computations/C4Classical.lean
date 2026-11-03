/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.StarCertificates
import LineGraphs.LineSystem.ClassicalModels

/-!
# Parametric computations for the classical families

Connectivity is proved uniformly in the rank, without a bounded search.
-/

open scoped RealInnerProductSpace

namespace LineSystem

/-- Two nonorthogonal steps to a fixed root exclude an orthogonal partition. -/
theorem IntegerModel.isIndecomposable_of_two_steps {d : ℕ}
    {S : LineSystem (EuclideanSpace ℝ (Fin d))} (M : IntegerModel S) (a : M.ι)
    (h : ∀ i, ∃ j, integerInner (M.v i) (M.v j) ≠ 0 ∧
      integerInner (M.v j) (M.v a) ≠ 0) : S.IsIndecomposable := by
  intro P Q hPQ ho
  have hn (i j : M.ι) (hij : integerInner (M.v i) (M.v j) ≠ 0) :
      ⟪integerVector M.c (M.v i), integerVector M.c (M.v j)⟫ ≠ 0 :=
    fun hz => hij ((M.inner_eq_zero_iff i j).mp hz)
  have empty (R T : Set (EuclideanSpace ℝ (Fin d))) (hRT : R ∪ T = S.Φ)
      (hort : ∀ r ∈ R, ∀ t ∈ T, ⟪r, t⟫ = 0)
      (ha : integerVector M.c (M.v a) ∈ R) : T = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxS : x ∈ S.Φ := hRT ▸ Or.inr hx
    rw [M.Φ_eq] at hxS
    obtain ⟨i, rfl⟩ := hxS
    obtain ⟨j, hij, hja⟩ := h i
    have hj : integerVector M.c (M.v j) ∈ R ∪ T := hRT ▸ M.root_mem j
    rcases hj with hj | hj
    · exact hn i j hij (by rw [real_inner_comm]; exact hort _ hj _ hx)
    · exact hn j a hja (by rw [real_inner_comm]; exact hort _ ha _ hj)
  have ha : integerVector M.c (M.v a) ∈ P ∪ Q := hPQ ▸ M.root_mem a
  rcases ha with ha | ha
  · exact Or.inr (empty P Q hPQ ho ha)
  · exact Or.inl (empty Q P (by rw [Set.union_comm, hPQ])
      (fun q hq p hp => by rw [real_inner_comm]; exact ho p hp q hq) ha)

/-- C4: Aₙ is indecomposable for every positive rank, including A₁. -/
theorem isIndecomposable_An {n : ℕ} (hn : 1 ≤ n) : (An n).IsIndecomposable := by
  let z : Fin (n + 1) := ⟨0, by omega⟩
  let o : Fin (n + 1) := ⟨1, by omega⟩
  have hzo : z ≠ o := by simp [z, o, Fin.ext_iff]
  let a : An.Index n := ⟨(z, o), hzo⟩
  apply (An.integerModel n).isIndecomposable_of_two_steps a
  rintro ⟨⟨i, j⟩, hij⟩
  change i ≠ j at hij
  change ∃ b : An.Index n, integerInner (anRoot ⟨(i, j), hij⟩) (anRoot b) ≠ 0 ∧
    integerInner (anRoot b) (anRoot a) ≠ 0
  have haa : integerInner (anRoot a) (anRoot a) ≠ 0 := by
    rw [integerInner_anRoot_self]; decide
  by_cases hi0 : i = z
  · refine ⟨a, ?_, haa⟩
    simp_all [anRoot, a, pairVector, Pi.single_apply]
    split_ifs <;> simp_all
  by_cases hj0 : j = z
  · refine ⟨a, ?_, haa⟩
    simp_all [anRoot, a, pairVector, Pi.single_apply]
    split_ifs <;> simp_all
  by_cases hi1 : i = o
  · refine ⟨a, ?_, haa⟩
    have hoj : o ≠ j := hi1 ▸ hij
    simp_all [anRoot, a, pairVector]
  by_cases hj1 : j = o
  · refine ⟨a, ?_, haa⟩
    simp_all [anRoot, a, pairVector]
  refine ⟨⟨(i, z), hi0⟩, ?_, ?_⟩
  · simp_all [anRoot, a, pairVector]
  · simp_all [anRoot, a, pairVector]

/-- C4: Dₙ is indecomposable throughout the stated range. -/
theorem isIndecomposable_Dn {n : ℕ} (hn : 4 ≤ n) : (Dn n).IsIndecomposable := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let t : Fin n := ⟨2, by omega⟩
  have hzo : z < o := by change (0 : ℕ) < 1; omega
  have hzno : z ≠ o := ne_of_lt hzo
  have hzt : z < t := by change (0 : ℕ) < 2; omega
  have htz : t ≠ z := ne_of_gt hzt
  have hot : o ≠ t := by simp [o, t, Fin.ext_iff]
  let a : Dn.Index n := (⟨(z, o), hzo⟩, false, false)
  apply (Dn.integerModel n).isIndecomposable_of_two_steps a
  rintro ⟨⟨⟨i, j⟩, hij⟩, s, u⟩
  change i < j at hij
  have hne : i ≠ j := ne_of_lt hij
  change ∃ b : Dn.Index n,
    integerInner (dnRoot (⟨(i, j), hij⟩, s, u)) (dnRoot b) ≠ 0 ∧
      integerInner (dnRoot b) (dnRoot a) ≠ 0
  have haa : integerInner (dnRoot a) (dnRoot a) ≠ 0 := by
    rw [integerInner_dnRoot_self]; decide
  have hj0 : j ≠ z := by
    intro he
    have hij' : i.val < j.val := hij
    rw [he] at hij'
    change i.val < 0 at hij'
    omega
  by_cases hi0 : i = z
  · by_cases hj1 : j = o
    · refine ⟨(⟨(z, t), hzt⟩, false, false), ?_, ?_⟩
      · simp_all [dnRoot, a, pairVector, rootSign]
        cases s <;> norm_num [z, o, t, Fin.ext_iff]
      · simp_all [dnRoot, a, pairVector, rootSign]
    · refine ⟨a, ?_, haa⟩
      simp_all [dnRoot, a, pairVector, rootSign]
      cases s <;> norm_num [z, o, t, Fin.ext_iff]
  by_cases hi1 : i = o
  · refine ⟨a, ?_, haa⟩
    simp_all [dnRoot, a, pairVector, rootSign]
    cases s <;> norm_num [z, o, t, Fin.ext_iff]
  by_cases hj1 : j = o
  · refine ⟨a, ?_, haa⟩
    simp_all [dnRoot, a, pairVector, rootSign]
    cases u <;> norm_num [z, o, t, Fin.ext_iff]
  obtain ⟨b, hb⟩ := exists_dnRoot_eq_pairVector i z hi0 false false
  refine ⟨b, ?_, ?_⟩
  · rw [hb]
    simp_all [dnRoot, a, pairVector, rootSign]
    cases s <;> norm_num [z, o, t, Fin.ext_iff]
  · rw [hb]
    simp_all [dnRoot, a, pairVector, rootSign]

end LineSystem
