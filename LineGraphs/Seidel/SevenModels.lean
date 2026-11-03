/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22
import LineGraphs.Computations.C9Schlafli
import LineGraphs.Computations.C9Clebsch

/-! # The seven models in Proposition `prop:414-seven` (Remark 4.14) -/

namespace SimpleGraph

/-- The seven graphs of Proposition `prop:414-seven`, in the order of Examples 4.5--4.9. -/
def seidelSeven : Fin 7 → Σ n : ℕ, SimpleGraph (Fin n) :=
  ![⟨28, changI⟩, ⟨28, changII⟩, ⟨28, changIII⟩, ⟨27, schlafli⟩,
    ⟨16, shrikhande⟩, ⟨16, clebsch⟩, ⟨10, petersen⟩]

/-- The strongly regular parameters in step `s414sevparams` of Proposition `prop:414-seven`. -/
def seidelSevenParameters : Fin 7 → ℕ × ℕ × ℕ :=
  ![(12, 6, 4), (12, 6, 4), (12, 6, 4), (16, 10, 8), (6, 2, 2), (10, 6, 6), (3, 0, 1)]

/-- The adjacency decisions of the seven explicit models in Proposition `prop:414-seven`. -/
instance seidelSevenDecidableAdj (i : Fin 7) : DecidableRel (seidelSeven i).2.Adj :=
  match i with
  | 0 => inferInstanceAs (DecidableRel changI.Adj)
  | 1 => inferInstanceAs (DecidableRel changII.Adj)
  | 2 => inferInstanceAs (DecidableRel changIII.Adj)
  | 3 => inferInstanceAs (DecidableRel schlafli.Adj)
  | 4 => inferInstanceAs (DecidableRel shrikhande.Adj)
  | 5 => inferInstanceAs (DecidableRel clebsch.Adj)
  | 6 => inferInstanceAs (DecidableRel petersen.Adj)

/-- Every graph of `prop:414-seven` has a vertex. -/
instance seidelSevenNonempty (i : Fin 7) : Nonempty (Fin (seidelSeven i).1) := by
  exact ⟨⟨0, by fin_cases i <;> decide⟩⟩

/-- Step `s414sevparams` of Proposition `prop:414-seven`: the parameters from C9. -/
theorem seidelSeven_isSRGWith (i : Fin 7) :
    (seidelSeven i).2.IsSRGWith (seidelSeven i).1 (seidelSevenParameters i).1
      (seidelSevenParameters i).2.1 (seidelSevenParameters i).2.2 := by
  fin_cases i
  · exact changI_isSRGWith
  · exact changII_isSRGWith
  · exact changIII_isSRGWith
  · exact schlafli_isSRGWith
  · exact shrikhande_isSRGWith
  · exact clebsch_isSRGWith
  · exact petersen_isSRGWith

/-- Step `s414sevparams` of Proposition `prop:414-seven`: the representations from C9. -/
theorem seidelSeven_isRepresentedIn_E₈ (i : Fin 7) :
    (seidelSeven i).2.IsRepresentedIn LineSystem.E₈ := by
  fin_cases i
  · exact changI_isRepresentedIn_E₈
  · exact changII_isRepresentedIn_E₈
  · exact changIII_isRepresentedIn_E₈
  · exact schlafli_isRepresentedIn_E₈
  · exact shrikhande_isRepresentedIn_E₈
  · exact clebsch_isRepresentedIn_E₈
  · exact petersen_isRepresentedIn_E₈

/-- The common-neighbour argument in step `s414sevconn` of Proposition `prop:414-seven`. -/
theorem IsSRGWith.connected_of_pos {V : Type*} [Fintype V] [Nonempty V]
    {X : SimpleGraph V} [DecidableRel X.Adj] {n k a c : ℕ}
    (h : X.IsSRGWith n k a c) (hc : 0 < c) : X.Connected := by
  refine { preconnected := fun u v ↦ ?_, nonempty := inferInstance }
  by_cases huv : u = v
  · subst v
    exact Reachable.refl u
  by_cases hadj : X.Adj u v
  · exact hadj.reachable
  have hpos : 0 < Fintype.card (X.commonNeighbors u v) := by
    rw [h.of_not_adj huv hadj]
    exact hc
  obtain ⟨⟨w, huw, hvw⟩⟩ := Fintype.card_pos_iff.mp hpos
  exact huw.reachable.trans hvw.symm.reachable

/-- Step `s414sevconn` of Proposition `prop:414-seven`: all seven graphs are connected. -/
theorem seidelSeven_connected (i : Fin 7) : (seidelSeven i).2.Connected :=
  (seidelSeven_isSRGWith i).connected_of_pos (by fin_cases i <;> decide)

/-- Step `s414sevlmin` of Proposition `prop:414-seven`: dimension eight is smaller than
the order, so the least eigenvalue is exactly minus two. -/
theorem seidelSeven_leastEigenvalue (i : Fin 7) :
    (seidelSeven i).2.leastEigenvalue = -2 := by
  obtain ⟨x, hx, _⟩ := seidelSeven_isRepresentedIn_E₈ i
  apply hx.leastEigenvalue_eq_neg_two_of_finrank_lt
  have hn : 8 < (seidelSeven i).1 := by fin_cases i <;> decide
  simpa using hn

end SimpleGraph
