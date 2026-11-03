/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Orientation

/-!
# Recognition of the named Cartan matrices

The orientation and reindexing part of Theorem A, Remark 3.11.
-/

namespace WeightedGraph

/-- Change between two index orders of a common model (Theorem A, Remark 3.11). -/
theorem reindex_change {ι κ ν : Type*} (X : WeightedGraph ι) (f : ι ≃ κ) (e : ι ≃ ν) :
    (X.reindex f).reindex (f.symm.trans e) = X.reindex e := by
  rw [reindex_trans]
  congr 1
  ext i
  simp

end WeightedGraph

namespace Matrix.IsFiniteCartan

open Matrix CartanMatrix WeightedGraph SimpleGraph

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {M : Matrix ι ι ℤ}

/-- Pulling back along a weighted labelling recovers its weights
(Theorem A, Remark 3.11). -/
theorem weightedGraph_eq_of_labelling (hM : M.IsFiniteCartan) (e : κ ≃ ι)
    {X : WeightedGraph κ} (hw : hM.weightedGraph = X.reindex e) :
    (hM.submatrix e).weightedGraph = X := by
  rw [weightedGraph_submatrix hM e, hw, reindex_symm_cancel]

/-- Terminal double paths have a canonical B or C orientation, including B₂
(Theorem A, Remark 3.11). -/
theorem exists_model_of_terminal_double_path {n : ℕ} (hn : 2 ≤ n)
    {N : Matrix (Fin n) (Fin n) ℤ} (hN : N.IsFiniteCartan)
    (hw : hN.weightedGraph = singleDoublePath n (n - 2)) :
    ∃ e : Fin n ≃ Fin n, IsFiniteTypeModel (N.submatrix e e) := by
  rw [← CartanMatrix.weightedGraph_B] at hw
  rcases hN.eq_B_or_C_of_weightedGraph_eq hn hw with h | h
  · exact ⟨Equiv.refl _, .intro (.b n hn) h.symm⟩
  · by_cases hn' : 3 ≤ n
    · exact ⟨Equiv.refl _, .intro (.c n hn') h.symm⟩
    · have hn2 : n = 2 := by omega
      subst n
      refine ⟨Fin.revPerm, .intro (.b 2 (by omega)) ?_⟩
      rw [h, C_two_submatrix_rev]
      rfl

/-- The middle double path has the canonical F orientation
(Theorem A, Remark 3.11). -/
theorem exists_model_of_middle_double_path {N : Matrix (Fin 4) (Fin 4) ℤ}
    (hN : N.IsFiniteCartan) (hw : hN.weightedGraph = singleDoublePath 4 1) :
    ∃ e : Fin 4 ≃ Fin 4, IsFiniteTypeModel (N.submatrix e e) := by
  rw [← CartanMatrix.weightedGraph_F₄] at hw
  rcases hN.eq_F₄_or_transpose_of_weightedGraph_eq hw with h | h
  · exact ⟨Equiv.refl _, .intro .f₄ h.symm⟩
  · refine ⟨Fin.revPerm, .intro .f₄ ?_⟩
    rw [h, F₄_transpose_submatrix_rev]
    rfl

/-- The triple edge has the canonical G orientation (Theorem A, Remark 3.11). -/
theorem exists_model_of_triple_edge {N : Matrix (Fin 2) (Fin 2) ℤ}
    (hN : N.IsFiniteCartan) (hw : hN.weightedGraph = tripleEdge) :
    ∃ e : Fin 2 ≃ Fin 2, IsFiniteTypeModel (N.submatrix e e) := by
  rw [← CartanMatrix.weightedGraph_G₂] at hw
  rcases hN.eq_G₂_or_transpose_of_weightedGraph_eq hw with h | h
  · exact ⟨Equiv.refl _, .intro .g₂ h.symm⟩
  · refine ⟨Fin.revPerm, .intro .g₂ ?_⟩
    rw [h, G₂_transpose_submatrix_rev]
    rfl

/-- A weighted Dynkin labelling determines a named integer Cartan model
(the recognition part of Theorem A, Remark 3.11). -/
theorem exists_model_of_dynkin_labelling (hM : M.IsFiniteCartan)
    (hX : hM.weightedGraph.HasDynkinLabelling) :
    ∃ n : ℕ, ∃ e : Fin n ≃ ι, IsFiniteTypeModel (M.submatrix e e) := by
  have hunit {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
      (t : FiniteType n) (X : WeightedGraph α) (f : α ≃ Fin n) (e : α ≃ ι)
      (hmodel : CartanMatrix.weightedGraph (modelEntries t) = X.reindex f)
      (hX : hM.weightedGraph = X.reindex e)
      (hsym : (modelEntries t).IsSymm) (hsimple : (modelEntries t).IsSimplyLaced) :
      ∃ n : ℕ, ∃ e : Fin n ≃ ι, IsFiniteTypeModel (M.submatrix e e) := by
    let g := f.symm.trans e
    have hg : hM.weightedGraph = (CartanMatrix.weightedGraph (modelEntries t)).reindex g := by
      rw [hmodel, reindex_change]
      exact hX
    have heq := (hM.submatrix g).eq_of_weightedGraph_eq_of_isSimplyLaced
      (model_diag t) hsym hsimple (hM.weightedGraph_eq_of_labelling g hg)
    exact ⟨n, g, t, heq.symm⟩
  cases hX with
  | a n hn e h =>
    exact hunit (.a n hn) (path n (fun _ ↦ 1) (by intros; norm_num))
      (Equiv.refl _) e (weightedGraph_A n) h
      (A_isSymm n) (isSimplyLaced_A n)
  | doublePath n k hk hp e h =>
    have hw := hM.weightedGraph_eq_of_labelling e h
    rcases hp with rfl | ht | ⟨rfl, rfl⟩
    · have hrev : ((hM.submatrix e).submatrix Fin.revPerm).weightedGraph =
          singleDoublePath n (n - 2) := by
        rw [weightedGraph_submatrix (hM.submatrix e) Fin.revPerm, hw,
          Fin.revPerm_symm, singleDoublePath_reindex_rev]
        · simp
        · exact hk
      obtain ⟨f, hf⟩ := exists_model_of_terminal_double_path (by omega)
        ((hM.submatrix e).submatrix Fin.revPerm) hrev
      exact ⟨n, (f.trans Fin.revPerm).trans e, hf⟩
    · have hk' : k = n - 2 := by omega
      subst k
      obtain ⟨f, hf⟩ := (hM.submatrix e).exists_model_of_terminal_double_path (by omega) hw
      exact ⟨n, f.trans e, hf⟩
    · obtain ⟨f, hf⟩ := (hM.submatrix e).exists_model_of_middle_double_path hw
      exact ⟨4, f.trans e, hf⟩
  | d c hc e h =>
    have ht : 4 ≤ c + 3 := by omega
    exact hunit (.d (c + 3) ht) (unit (armTree ![1, 1, c]))
      (dEquiv c) e (by simpa only [modelEntries] using weightedGraph_D c hc) h
      (D_isSymm _) (isSimplyLaced_D _)
  | e₆ e h =>
    exact hunit .e₆ _ (eEquiv 2) e (weightedGraph_E 2) h
      (E_isSymm _) (isSimplyLaced_E _)
  | e₇ e h =>
    exact hunit .e₇ _ (eEquiv 3) e (weightedGraph_E 3) h
      (E_isSymm _) (isSimplyLaced_E _)
  | e₈ e h =>
    exact hunit .e₈ _ (eEquiv 4) e (weightedGraph_E 4) h
      (E_isSymm _) (isSimplyLaced_E _)
  | g₂ e h =>
    obtain ⟨f, hf⟩ := (hM.submatrix e).exists_model_of_triple_edge
      (hM.weightedGraph_eq_of_labelling e h)
    exact ⟨2, f.trans e, hf⟩

end Matrix.IsFiniteCartan
