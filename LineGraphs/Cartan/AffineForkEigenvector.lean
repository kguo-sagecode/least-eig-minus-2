/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Affine

/-!
# The weighted-fork eigenvector

The vector is 2 along the path except at its final vertex, where it is √2;
both additional leaves have value 1. The proof includes the single-edge fork.
-/

namespace WeightedGraph

open Matrix

/-- The positive weighted-fork vector from the affine obstruction lemma. -/
noncomputable def forkEigenvector (k : ℕ) : Fin (k + 1) ⊕ Fin 2 → ℝ :=
  Sum.elim (fun i => if i.val = k then Real.sqrt 2 else 2) (fun _ => 1)

/-- The displayed weighted-fork vector is a positive 2-eigenvector for every `k ≥ 1`. -/
theorem fork_eigenvector (k : ℕ) (hk : 1 ≤ k) :
    (∀ i, 0 < forkEigenvector k i) ∧
    (fork k).weights *ᵥ forkEigenvector k = (2 : ℝ) • forkEigenvector k := by
  constructor
  · rintro (i | i)
    · dsimp [forkEigenvector]
      split_ifs <;> positivity
    · norm_num [forkEigenvector]
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    funext z
    rcases z with i | j
    · by_cases hi : i.val = 0
      · have hieq : i = 0 := Fin.ext hi
        subst i
        rw [fork, forkEigenvector, attachLeaves_mulVec_inl, path_mulVec_first n]
        by_cases hn : n = 0
        · subst n
          norm_num [Fin.sum_univ_two, ← pow_two]
        · have hn' : ¬ 0 = n := Ne.symm hn
          norm_num [Fin.sum_univ_two, hn, hn']
      · by_cases hi' : i.val = n + 1
        · have hieq : i = Fin.last (n + 1) := Fin.ext hi'
          subst i
          rw [fork, forkEigenvector, attachLeaves_mulVec_inl, path_mulVec_last n]
          norm_num [Fin.sum_univ_two, Fin.ext_iff]
          ring
        · have hile : i.val + 1 < n + 1 + 1 := by omega
          rw [fork, forkEigenvector, attachLeaves_mulVec_inl,
            path_mulVec_interior _ _ _ _ i (by omega) hile]
          have hp : i.val - 1 + 1 = i.val := by omega
          have hp' : ¬ i.val - 1 = n + 1 := by omega
          have hi0 : i ≠ 0 := by intro h; exact hi (congrArg Fin.val h)
          simp only [Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Fin.sum_univ_two,
            hp, hp', hi', hi0, ite_false, one_mul, add_zero]
          by_cases hn : i.val + 1 = n + 1
          · norm_num [hn, ← pow_two]
          · have hn' : i.val ≠ n := by omega
            norm_num [hn']
    · rw [fork, forkEigenvector, attachLeaves_mulVec_inr]
      norm_num

end WeightedGraph
