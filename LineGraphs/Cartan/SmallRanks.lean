/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Models

/-!
# The Cartan matrices at small ranks

Remark (small ranks), `rem:small` of the Remark 3.11 blueprint: the coincidences among Mathlib's
generalized matrices `CartanMatrix.A`, `B`, `C`, `D`, `E` at small ranks, and the failure of
finite Cartan type for `E ℓ` with `ℓ ≥ 9`.

An old-index order `(i₀, …, iₙ₋₁)` is the reindexing `M.submatrix ![i₀, …, iₙ₋₁] ![i₀, …, iₙ₋₁]`,
whose index `k` is the old index `iₖ`. Each order below lists every old index exactly once.
-/

namespace CartanMatrix

open Matrix SimpleGraph WeightedGraph

/-- Step `rsmallElarge` of `rem:small`, Remark 3.11: for `ℓ ≥ 9`, the leading nine vertices of
the weighted support of `E ℓ` contain the affine `E₈` tree `T(1,2,5)`. The embedding is the arm
bijection `h_E` of `lem:rem-model-supports` on both short arms and on the first five positions of
the long arm. -/
theorem exists_weightedGraph_E_contains_smithE₈ {ℓ : ℕ} (hℓ : 9 ≤ ℓ) :
    ∃ e : ArmVertex ![1, 2, 5] ↪ Fin ℓ, (∀ i, (e i : ℕ) < 9) ∧
      (weightedGraph (E ℓ)).Contains (unit smithE₈) e := by
  obtain ⟨c, rfl⟩ : ∃ c, ℓ = c + 4 := ⟨ℓ - 4, by omega⟩
  have hab : ∀ r, (![1, 2, 5] : Fin 3 → ℕ) r ≤ ![1, 2, c] r := by
    intro r
    fin_cases r <;> simp [show 5 ≤ c by omega]
  let f := armTreeEmbedding hab
  refine ⟨f.toEmbedding.trans (eEquiv c).toEmbedding, ?_, ?_⟩
  · -- `h_E` sends the centre, the short arms and the first five long-arm positions below 9.
    have hlead (r : Fin 3) (s : Fin (![1, 2, c] r)) (hs : s.val < ![1, 2, 5] r) :
        (eVertex c (some ⟨r, s⟩)).val < 9 := by
      fin_cases r
      · exact (show (1 : ℕ) < 9 by norm_num)
      · change (if s.val = 0 then 2 else 0) < 9
        split_ifs <;> norm_num
      · change s.val < 5 at hs
        change s.val + 4 < 9
        omega
    rintro (_ | ⟨r, t⟩)
    · exact (show (3 : ℕ) < 9 by norm_num)
    · exact hlead r (Fin.castLE (hab r) t) t.isLt
  · rw [weightedGraph_E]
    intro i j
    change smithE₈.adjMatrix ℝ i j ≤ (armTree ![1, 2, c]).adjMatrix ℝ
      ((eEquiv c).symm (eEquiv c (f i))) ((eEquiv c).symm (eEquiv c (f j)))
    simp only [Equiv.symm_apply_apply, adjMatrix_apply]
    by_cases h : smithE₈.Adj i j
    · rw [ite_eq_left h, ite_eq_left (f.map_adj_iff.mpr h)]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

/-- Step `rsmallnotfinite` of `rem:small`, Remark 3.11: the matrices `E ℓ` with `ℓ ≥ 9` are not
finite Cartan. Their support is connected, so they are indecomposable; the affine `E₈` tree in
their support gives a maximum Rayleigh value of at least two, whereas symmetrization of a finite
Cartan matrix gives a value below two. -/
theorem not_isFiniteCartan_E {ℓ : ℕ} (hℓ : 9 ≤ ℓ) : ¬ (E ℓ).IsFiniteCartan := by
  intro hM
  obtain ⟨c, rfl⟩ : ∃ c, ℓ = c + 4 := ⟨ℓ - 4, by omega⟩
  have : Nonempty (Fin (c + 4)) := ⟨0⟩
  -- Step `rsmallconnected`, from `lem:rem-model-supports`.
  have hconn : (weightedGraph (E (c + 4))).support.Connected :=
    weightedGraph_E_support_connected c
  -- Step `rsmallindecomposable`, by `lem:connected`.
  have hind : (E (c + 4)).IsIndecomposable := by
    apply (isIndecomposable_iff_connected_support (E (c + 4)) hM.zero_comm).mpr
    rw [← hM.weightedGraph_support]
    exact hconn
  -- Step `rsmalllower`: `lem:affine` and `lem:monotonicity` applied to `rsmallElarge`.
  have hlower : 2 ≤ maxRayleigh hM.weightedGraph.isHermitian := by
    obtain ⟨e, -, he⟩ := exists_weightedGraph_E_contains_smithE₈ hℓ
    have hE₈ : (unit smithE₈).IsAffineObstruction := .e₈ (Equiv.refl _) rfl
    calc
      (2 : ℝ) = maxRayleigh (unit smithE₈).isHermitian := hE₈.maxRayleigh_eq_two.symm
      _ ≤ maxRayleigh hM.weightedGraph.isHermitian := maxRayleigh_mono he
  -- `lem:symmetrization` gives a maximum Rayleigh value below two.
  obtain ⟨d, hd, hH⟩ := hM.exists_posDef
  exact not_lt_of_ge hlower (hM.symmetrization hind hd hH).2.2.2.2

/-- Remark (small ranks), `rem:small` of the Remark 3.11 blueprint, for Mathlib's generalized
definitions at all natural ranks: `B₁ = C₁ = D₁ = A₁ = [2]` and `D₂ = 2I₂`; the old-index order
`(1,0)` sends `C₂` to `B₂`, and `(1,0,2)` sends `D₃` to `A₃`; `E₁ = A₁` and `E₂ = 2I₂`; the order
`(0,2,1)` sends `E₃` to `A₂ ⊕ A₁`, which is `fromBlocks (A 2) 0 0 (A 1)` on `Fin 2 ⊕ Fin 1`
carried to `Fin 3` by `finSumFinEquiv`; `(0,2,3,1)` sends `E₄` to `A₄`, and `(0,2,3,1,4)` sends
`E₅` to `D₅`. The matrices `E ℓ`, `ℓ ≥ 9`, are not finite Cartan. All five parameterized
definitions at rank 0 give the empty matrix. -/
theorem small_rank_identifications (ℓ : ℕ) :
    (B 1 = A 1 ∧ C 1 = A 1 ∧ D 1 = A 1 ∧ A 1 = !![2]) ∧
    D 2 = (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) ∧
    (C 2).submatrix ![1, 0] ![1, 0] = B 2 ∧
    (D 3).submatrix ![1, 0, 2] ![1, 0, 2] = A 3 ∧
    E 1 = A 1 ∧ E 2 = (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) ∧
    (E 3).submatrix ![0, 2, 1] ![0, 2, 1] =
      (fromBlocks (A 2) 0 0 (A 1)).reindex finSumFinEquiv finSumFinEquiv ∧
    (E 4).submatrix ![0, 2, 3, 1] ![0, 2, 3, 1] = A 4 ∧
    (E 5).submatrix ![0, 2, 3, 1, 4] ![0, 2, 3, 1, 4] = D 5 ∧
    (9 ≤ ℓ → ¬ (E ℓ).IsFiniteCartan) ∧
    (A 0 = !![] ∧ B 0 = !![] ∧ C 0 = !![] ∧ D 0 = !![] ∧ E 0 = !![]) := by
  refine ⟨⟨B_one, C_one, D_one, A_one⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, not_isFiniteCartan_E, ?_⟩
  -- Step `rsmallDtwo`.
  · rw [D_two]
    decide
  -- Step `rsmallBC`.
  · rw [B_two, C_two]
    decide
  -- Step `rsmallDthree`: `D_three'` transposes the indices 0 and 1, which is the order
  -- `(1,0,2)`.
  · rw [← D_three']
    decide
  -- Step `rsmallone` for `E`: the only index pair is diagonal.
  · decide
  -- Step `rsmallEtwo`: no off-diagonal edge clause of `E` has both indices below 2.
  · decide
  -- Step `rsmallEthree`: at rank 3 the sole edge is `{0,2}`.
  · decide
  -- Step `rsmallEfour`: at rank 4 the path order is `(0,2,3,1)`.
  · decide
  -- Step `rsmallEfive`: in the order `(0,2,3,1,4)` the edges are exactly the `D₅` edges.
  · decide
  -- Step `rsmallempty`: at rank 0 the index type has no elements.
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end CartanMatrix
