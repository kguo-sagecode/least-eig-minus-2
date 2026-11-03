/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.LineGraphRecovery

/-! # The line-graph spectrum from the signless spectrum -/

open Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (X : SimpleGraph V) [DecidableRel X.Adj]

attribute [local instance] Classical.propDecidable

-- Remark 5.12
/-- The incidence-matrix spectral identity used in [CGSS], Remark 5.12:
when there are at least as many edges as vertices, subtract two from the signless
spectrum and adjoin one `-2` for each excess edge. -/
theorem spectrumMultiset_lineGraph_of_card_le (h : Fintype.card V ≤ X.edgeFinset.card) :
    X.lineGraph.spectrumMultiset =
      (X.signlessLapMatrix ℝ).spectrumMultiset.map (fun μ => μ - 2) +
        Multiset.replicate (X.edgeFinset.card - Fintype.card V) (-2) := by
  have he := Matrix.spectrumMultiset_mul_comm_add_zeros (X.edgeIncMatrix ℝ)
    (X.edgeIncMatrix ℝ)ᵀ
  rw [X.edgeIncMatrix_mul_transpose, X.transpose_edgeIncMatrix_mul, X.card_edgeSet] at he
  have hs := (X.lineGraph.isHermitian_adjMatrix ℝ).spectrumMultiset_smul_one_add_smul 2 1
  simp only [one_smul, one_mul] at hs
  rw [hs] at he
  have he' := congrArg (Multiset.map (fun μ : ℝ => μ - 2)) he
  simp only [Multiset.map_add, Multiset.map_replicate, Multiset.map_map,
    Function.comp_def, add_sub_cancel_left, Multiset.map_id', zero_sub] at he'
  apply add_left_cancel (a := Multiset.replicate (Fintype.card V) (-2 : ℝ))
  calc
    _ = Multiset.replicate X.edgeFinset.card (-2 : ℝ) +
        (X.signlessLapMatrix ℝ).spectrumMultiset.map (fun μ => μ - 2) := he'.symm
    _ = _ := by
      have hm : X.edgeFinset.card =
          Fintype.card V + (X.edgeFinset.card - Fintype.card V) := (Nat.add_sub_of_le h).symm
      conv_lhs => rw [hm]
      rw [Multiset.replicate_add]
      abel

end SimpleGraph
