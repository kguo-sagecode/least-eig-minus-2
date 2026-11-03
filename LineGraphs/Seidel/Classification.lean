/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.ClassificationParameters
import LineGraphs.Seidel.LatticeIntegrality
import LineGraphs.Seidel.ExceptionalSwitching
import LineGraphs.Seidel.Seven
import LineGraphs.Seidel.Clebsch
import LineGraphs.Seidel.Schlafli

/-! # Remark 4.14: Seidel's seven graphs

The proof of `rem:414-proof`, using the lattice-root classification, C18 and C21,
the three switching classifications, and the two uniqueness theorems.
-/

open Submodule Module

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {X : SimpleGraph V} [DecidableRel X.Adj] {n k a c : ℕ}

/-- Steps `s414mE`--`s414mchang` of Remark 4.14: the parameter and lattice-type
reductions leave precisely the seven listed graphs. -/
theorem IsSRGWith.nonempty_iso_seidelSeven (h : X.IsSRGWith n k a c) (hc : X.Connected)
    (hleast : X.leastEigenvalue = -2) (hE : X.IsRepresentedIn LineSystem.E₈)
    (hex : ∀ m, ¬ Nonempty (X ≃g (⊤ : SimpleGraph (Fin m)).lineGraph) ∧
      ¬ Nonempty (X ≃g (completeBipartiteGraph (Fin m) (Fin m)).lineGraph) ∧
      ¬ Nonempty (X ≃g cocktailParty m)) :
    ∃ i : Fin 7, Nonempty (X ≃g (seidelSeven i).2) := by
  have hdet := (X.leastEigenvalue_eq_neg_two_iff.mp hleast).2
  have hp := h.parameters_mem_small_list hc hdet hE
  obtain ⟨x, hx, _⟩ := hE
  rcases hx.nonempty_iso_exceptional_of_latticeRoots h hc hdet hex with he | he | he
  · obtain ⟨e⟩ := he
    have hρ : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank = 6 := by
      rw [hx.rank_two_add_adjMatrix X, ← hx.span_latticeRoots, e.finrank_span_eq,
        LineSystem.finrank_span_E₆]
    norm_num [Computations.C18.parameters, hρ] at hp
    rcases hp with hpar | hpar | hpar | hpar
    · rcases hpar with ⟨hn, hk, ha, hcp⟩
      norm_cast at hn hk ha hcp
      subst n k a c
      exact ((hex 5).2.2 (h.regular.nonempty_iso_cocktailParty (by decide) h.card)).elim
    · rcases hpar with ⟨hn, hk, ha, hcp⟩
      norm_cast at hn hk ha hcp
      subst n k a c
      exact ⟨6, hx.nonempty_iso_petersen_of_latticeRoots h.regular h.card e⟩
    · rcases hpar with ⟨hn, hk, ha, hcp⟩
      norm_cast at hn hk ha hcp
      subst n k a c
      obtain ⟨z, hz⟩ := hx.three_mul_apex_mem_int_of_E₆ h.regular e
      rw [h.card] at hz
      norm_num at hz
      have hz' : 2 * z = 9 := by
        exact_mod_cast (show (2 : ℝ) * z = 9 by linarith)
      omega
    · rcases hpar with ⟨hn, hk, ha, hcp⟩
      norm_cast at hn hk ha hcp
      subst n k a c
      exact ⟨5, h.nonempty_iso_clebsch⟩
  · obtain ⟨e⟩ := he
    have hρ : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank = 7 := by
      rw [hx.rank_two_add_adjMatrix X, ← hx.span_latticeRoots, e.finrank_span_eq,
        LineSystem.finrank_span_E₇]
    norm_num [Computations.C18.parameters, hρ] at hp
    rcases hp with hpar | hpar | hpar | hpar
    · rcases hpar with ⟨hn, hk, ha, hcp⟩
      norm_cast at hn hk ha hcp
      subst n k a c
      exact ((hex 6).2.2 (h.regular.nonempty_iso_cocktailParty (by decide) h.card)).elim
    · rcases hpar with ⟨hn, hk, ha, hcp⟩
      norm_cast at hn hk ha hcp
      subst n k a c
      rcases hx.nonempty_iso_shrikhande_or_lattice_of_latticeRoots h.regular h.card e with
        hshr | hlat
      · exact ⟨4, hshr⟩
      · exact ((hex 4).2.1 hlat).elim
    · rcases hpar with ⟨hn, hk, ha, hcp⟩
      norm_cast at hn hk ha hcp
      subst n k a c
      obtain ⟨z, hz⟩ := hx.two_mul_apex_mem_int_of_E₇ h.regular e
      rw [h.card] at hz
      norm_num at hz
      have hz' : 2 * z = 7 := by
        exact_mod_cast (show (2 : ℝ) * z = 7 by linarith)
      omega
    · rcases hpar with ⟨hn, hk, ha, hcp⟩
      norm_cast at hn hk ha hcp
      subst n k a c
      exact ⟨3, h.nonempty_iso_schlafli⟩
  · obtain ⟨e⟩ := he
    have hρ : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank = 8 := by
      rw [hx.rank_two_add_adjMatrix X, ← hx.span_latticeRoots, e.finrank_span_eq,
        LineSystem.finrank_span_E₈]
    norm_num [Computations.C18.parameters, hρ] at hp
    rcases hp with hpar | hpar
    · rcases hpar with ⟨hn, hk, ha, hcp⟩
      norm_cast at hn hk ha hcp
      subst n k a c
      exact ((hex 7).2.2 (h.regular.nonempty_iso_cocktailParty (by decide) h.card)).elim
    · rcases hpar with ⟨hn, hk, ha, hcp⟩
      norm_cast at hn hk ha hcp
      subst n k a c
      rcases hx.nonempty_iso_triangular_or_chang_of_latticeRoots h.regular h.card e with
        ht | hI | hII | hIII
      · exact ((hex 8).1 ht).elim
      · exact ⟨0, hI⟩
      · exact ⟨1, hII⟩
      · exact ⟨2, hIII⟩

-- Remark 4.14, restated
/-- Remark 4.14 of [CGSS], `rem:414-proof`: a connected strongly regular graph of least
eigenvalue minus two, represented in `E₈` and outside the triangular, lattice and cocktail
party families, is isomorphic to exactly one of Seidel's seven graphs. -/
theorem seidel_seven_classification (h : X.IsSRGWith n k a c) (hc : X.Connected)
    (hleast : X.leastEigenvalue = -2) (hE : X.IsRepresentedIn LineSystem.E₈)
    (hex : ∀ m, ¬ Nonempty (X ≃g (⊤ : SimpleGraph (Fin m)).lineGraph) ∧
      ¬ Nonempty (X ≃g (completeBipartiteGraph (Fin m) (Fin m)).lineGraph) ∧
      ¬ Nonempty (X ≃g cocktailParty m)) :
    ∃! i : Fin 7, Nonempty (X ≃g (seidelSeven i).2) := by
  obtain ⟨i, hi⟩ := h.nonempty_iso_seidelSeven hc hleast hE hex
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  by_contra hji
  obtain ⟨f⟩ := hj
  obtain ⟨g⟩ := hi
  exact seidel_seven_pairwise_not_iso hji ⟨f.symm.trans g⟩

-- Remark 4.14
/-- Remark 4.14 of [CGSS], `rem:4.14`: the classification, pairwise non-isomorphism,
and the fact that all seven models satisfy the hypotheses. The last two conjuncts
are also unconditional theorems, `seidel_seven_pairwise_not_iso` and
`seidel_seven_properties`. The least-eigenvalue hypothesis agrees with the two
spectral hypotheses of `seidel` by `leastEigenvalue_eq_neg_two_iff` and
`neg_two_mem_spectrumMultiset_iff_det_eq_zero`. -/
theorem seidel_seven (h : X.IsSRGWith n k a c) (hc : X.Connected)
    (hleast : X.leastEigenvalue = -2) (hE : X.IsRepresentedIn LineSystem.E₈)
    (hex : ∀ m, ¬ Nonempty (X ≃g (⊤ : SimpleGraph (Fin m)).lineGraph) ∧
      ¬ Nonempty (X ≃g (completeBipartiteGraph (Fin m) (Fin m)).lineGraph) ∧
      ¬ Nonempty (X ≃g cocktailParty m)) :
    (∃! i : Fin 7, Nonempty (X ≃g (seidelSeven i).2)) ∧
      Pairwise (fun i j : Fin 7 ↦ ¬ Nonempty ((seidelSeven i).2 ≃g (seidelSeven j).2)) ∧
      ∀ i : Fin 7, (seidelSeven i).2.Connected ∧
        (seidelSeven i).2.IsSRGWith (seidelSeven i).1 (seidelSevenParameters i).1
          (seidelSevenParameters i).2.1 (seidelSevenParameters i).2.2 ∧
        (seidelSeven i).2.leastEigenvalue = -2 ∧
        (seidelSeven i).2.IsRepresentedIn LineSystem.E₈ ∧
        ∀ m, ¬ Nonempty ((seidelSeven i).2 ≃g (⊤ : SimpleGraph (Fin m)).lineGraph) ∧
          ¬ Nonempty ((seidelSeven i).2 ≃g
            (completeBipartiteGraph (Fin m) (Fin m)).lineGraph) ∧
          ¬ Nonempty ((seidelSeven i).2 ≃g cocktailParty m) :=
  ⟨seidel_seven_classification h hc hleast hE hex,
    seidel_seven_pairwise_not_iso, seidel_seven_properties⟩

end SimpleGraph
