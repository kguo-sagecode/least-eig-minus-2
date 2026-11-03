/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.DynkinD

/-!
# The named finite Cartan matrices

The canonical rank ranges and indexed matrices in `def:rem-bases` and
`def:rem-matrices` of the Remark 3.11 blueprint. The dependent index records the rank,
so the exceptional cases use Mathlib's matrices without an arbitrary reindexing.
The E arm bijections and support identities hold at every rank `c + 4`, including
all ranks at least five in `lem:rem-model-supports`, independently of finite Cartan type.
-/

namespace CartanMatrix

open Matrix SimpleGraph

/-- The permitted type and rank choices in Theorem A of Remark 3.11. -/
inductive FiniteType : ℕ → Type
  | a (n : ℕ) (hn : 1 ≤ n) : FiniteType n
  | b (n : ℕ) (hn : 2 ≤ n) : FiniteType n
  | c (n : ℕ) (hn : 3 ≤ n) : FiniteType n
  | d (n : ℕ) (hn : 4 ≤ n) : FiniteType n
  | e₆ : FiniteType 6
  | e₇ : FiniteType 7
  | e₈ : FiniteType 8
  | f₄ : FiniteType 4
  | g₂ : FiniteType 2
  deriving DecidableEq

/-- The actual Mathlib matrices in `def:rem-matrices`, Remark 3.11. -/
def modelEntries {n : ℕ} : FiniteType n → Matrix (Fin n) (Fin n) ℤ
  | .a n _ => A n
  | .b n _ => B n
  | .c n _ => C n
  | .d n _ => D n
  | .e₆ => E 6
  | .e₇ => E 7
  | .e₈ => E 8
  | .f₄ => F₄
  | .g₂ => G₂

/-- Membership in the canonical list of Theorem A, Remark 3.11: A starts at rank 1,
B at 2, C at 3, and D at 4. Exceptional matrices keep their Mathlib index order. -/
def IsFiniteTypeModel {n : ℕ} (N : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ t : FiniteType n, modelEntries t = N

/-- Every type in the list of Theorem A has positive rank. -/
theorem FiniteType.rank_pos {n : ℕ} (t : FiniteType n) : 0 < n := by
  cases t <;> omega

/-- The named matrices in Theorem A belong to the canonical list. -/
theorem modelEntries_isFiniteTypeModel {n : ℕ} (t : FiniteType n) :
    IsFiniteTypeModel (modelEntries t) := ⟨t, rfl⟩

/-- The disjunction of `sec:shapes` in the ordinary proof of Remark 3.11: membership in the
canonical list of Theorem A is one of the equalities of `eq:list`, with its rank restriction;
the exceptional clauses transport indices along the rank equality. -/
theorem isFiniteTypeModel_iff {l : ℕ} {N : Matrix (Fin l) (Fin l) ℤ} :
    IsFiniteTypeModel N ↔
      (1 ≤ l ∧ N = A l) ∨ (2 ≤ l ∧ N = B l) ∨ (3 ≤ l ∧ N = C l) ∨ (4 ≤ l ∧ N = D l) ∨
      (∃ h : l = 6, N = (E 6).submatrix (finCongr h) (finCongr h)) ∨
      (∃ h : l = 7, N = (E 7).submatrix (finCongr h) (finCongr h)) ∨
      (∃ h : l = 8, N = (E 8).submatrix (finCongr h) (finCongr h)) ∨
      (∃ h : l = 4, N = F₄.submatrix (finCongr h) (finCongr h)) ∨
      (∃ h : l = 2, N = G₂.submatrix (finCongr h) (finCongr h)) := by
  constructor
  · rintro ⟨t, rfl⟩
    cases t with
    | a n hn => exact Or.inl ⟨hn, rfl⟩
    | b n hn => exact Or.inr (Or.inl ⟨hn, rfl⟩)
    | c n hn => exact Or.inr (Or.inr (Or.inl ⟨hn, rfl⟩))
    | d n hn => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hn, rfl⟩)))
    | e₆ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    | e₇ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    | e₈ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
    | f₄ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨rfl, rfl⟩)))))))
    | g₂ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨rfl, rfl⟩)))))))
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    exacts [⟨.a l h, rfl⟩, ⟨.b l h, rfl⟩, ⟨.c l h, rfl⟩, ⟨.d l h, rfl⟩, ⟨.e₆, rfl⟩, ⟨.e₇, rfl⟩,
      ⟨.e₈, rfl⟩, ⟨.f₄, rfl⟩, ⟨.g₂, rfl⟩]

/-- The independent weighted matrix in `lem:rem-model-supports`, Remark 3.11.
Its definition does not assume the finite-Cartan converse. -/
noncomputable def weightedGraph {ι : Type*} [DecidableEq ι]
    (N : Matrix ι ι ℤ) : WeightedGraph ι where
  weights i j := if i = j then 0 else Real.sqrt ((N i j * N j i : ℤ) : ℝ)
  symmetric := by
    apply IsSymm.ext
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · simp [h, Ne.symm h, mul_comm]
  nonneg i j := by split_ifs <;> positivity
  diag i := by simp

/-- The independent model weights agree with the symmetrization weights
(`lem:rem-model-supports` of Remark 3.11). -/
theorem weightedGraph_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : Matrix ι ι ℤ} (hN : N.IsFiniteCartan) : weightedGraph N = hN.weightedGraph := rfl

/-- Transposition preserves the model weights (`lem:rem-model-supports`, Remark 3.11). -/
theorem weightedGraph_transpose {ι : Type*} [DecidableEq ι] (N : Matrix ι ι ℤ) :
    weightedGraph N.transpose = weightedGraph N := by
  apply WeightedGraph.ext
  funext i j
  simp [weightedGraph, mul_comm]

/-- The A matrices have the unit path labelling in `lem:rem-model-supports`, Remark 3.11. -/
theorem weightedGraph_A (n : ℕ) :
    weightedGraph (A n) = WeightedGraph.path n (fun _ ↦ 1) (by intro _; norm_num) := by
  apply WeightedGraph.ext
  funext i j
  simp only [weightedGraph, A, Matrix.of_apply, WeightedGraph.path]
  split_ifs <;> simp_all

/-- The B matrices have their double edge at the end of the path
(`lem:rem-model-supports`, Remark 3.11). -/
theorem weightedGraph_B (n : ℕ) :
    weightedGraph (B n) = WeightedGraph.singleDoublePath n (n - 2) := by
  apply WeightedGraph.ext
  funext i j
  simp only [weightedGraph, B, Matrix.of_apply, WeightedGraph.singleDoublePath,
    WeightedGraph.path]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> norm_num at * <;> omega

/-- The C matrices have the same weighted path as B
(`lem:rem-model-supports`, Remark 3.11). -/
theorem weightedGraph_C (n : ℕ) :
    weightedGraph (C n) = WeightedGraph.singleDoublePath n (n - 2) := by
  rw [← B_transpose, weightedGraph_transpose, weightedGraph_B]

/-- The arm order for D in `lem:rem-model-supports`, Remark 3.11. -/
def dVertex (c : ℕ) : ArmVertex ![1, 1, c] → Fin (c + 3)
  | none => ⟨c, by omega⟩
  | some ⟨r, i⟩ => ⟨if r = 0 then c + 1 else if r = 1 then c + 2 else c - 1 - i.val,
      by split_ifs <;> omega⟩

/-- The D arm order is bijective (`lem:rem-model-supports`, Remark 3.11). -/
theorem dVertex_bijective (c : ℕ) : Function.Bijective (dVertex c) := by
  constructor
  · rintro (_ | ⟨r, i⟩) (_ | ⟨s, j⟩) h
    · rfl
    · have hv := congrArg Fin.val h
      have hj := j.isLt
      clear h
      fin_cases s <;> simp [dVertex] at hv
      simp at hj
      omega
    · have hv := congrArg Fin.val h
      have hi := i.isLt
      clear h
      fin_cases r <;> simp [dVertex] at hv
      simp at hi
      omega
    · have hv := congrArg Fin.val h
      have hi := i.isLt
      have hj := j.isLt
      fin_cases r <;> fin_cases s <;> simp only [dVertex] at hv <;> simp at hv hi hj <;>
        first | omega | (congr 2; apply Fin.ext; omega)
  · intro j
    by_cases hj : j.val < c
    · refine ⟨some ⟨2, ⟨c - 1 - j.val, by simpa using (show c - 1 - j.val < c by omega)⟩⟩,
        Fin.ext ?_⟩
      simp only [dVertex, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        ite_false]
      omega
    · by_cases he : j.val = c
      · exact ⟨none, Fin.ext he.symm⟩
      · by_cases he' : j.val = c + 1
        · exact ⟨some ⟨0, ⟨0, by simp⟩⟩,
            Fin.ext (by simpa [dVertex] using he'.symm)⟩
        · exact ⟨some ⟨1, ⟨0, by simp⟩⟩, Fin.ext (by simp [dVertex]; omega)⟩

/-- The bijection displayed for D in `lem:rem-model-supports`, Remark 3.11. -/
noncomputable def dEquiv (c : ℕ) : ArmVertex ![1, 1, c] ≃ Fin (c + 3) :=
  Equiv.ofBijective (dVertex c) (dVertex_bijective c)

/-- The D entries in the displayed arm order of `lem:rem-model-supports`, Remark 3.11. -/
theorem D_dVertex_apply (c : ℕ) (_hc : 0 < c) (i j : ArmVertex ![1, 1, c]) :
    D (c + 3) (dVertex c i) (dVertex c j) =
      if i = j then 2 else if (armTree ![1, 1, c]).Adj i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j; simp [D]
  have hdij : dVertex c i ≠ dVertex c j := (dVertex_bijective c).injective.ne hij
  rw [ite_eq_right hij]
  simp only [D, Matrix.of_apply, ite_eq_right hdij]
  rcases i with _ | ⟨r, i⟩ <;> rcases j with _ | ⟨s, j⟩
  · exact (hij rfl).elim
  · have hj := j.isLt
    fin_cases s <;> simp [dVertex, armTree, Fin.ext_iff] at hdij hj ⊢ <;> omega
  · have hi := i.isLt
    fin_cases r <;> simp [dVertex, armTree, Fin.ext_iff] at hdij hi ⊢ <;> omega
  · have hi := i.isLt
    have hj := j.isLt
    fin_cases r <;> fin_cases s <;>
      simp [dVertex, armTree, Fin.ext_iff] at hdij hi hj ⊢ <;> omega

/-- An entry labelling gives the unit-weight labelling
(`lem:rem-model-supports`, Remark 3.11). -/
theorem weightedGraph_eq_unit_reindex {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (N : Matrix ι ι ℤ) (G : SimpleGraph κ) [DecidableRel G.Adj] (e : κ ≃ ι)
    (h : ∀ i j, N (e i) (e j) = if i = j then 2 else if G.Adj i j then -1 else 0) :
    weightedGraph N = (WeightedGraph.unit G).reindex e := by
  apply WeightedGraph.ext
  funext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp only [weightedGraph, WeightedGraph.reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, WeightedGraph.unit, SimpleGraph.adjMatrix_apply,
    e.injective.eq_iff, h]
  by_cases hij : i = j
  · subst j; simp
  · simp only [hij, Ne.symm hij, ite_false, G.adj_comm j i]
    split_ifs <;> norm_num

/-- The D weighted support has exactly the arm labelling of
`lem:rem-model-supports`, Remark 3.11. -/
theorem weightedGraph_D (c : ℕ) (hc : 0 < c) :
    weightedGraph (D (c + 3)) = (WeightedGraph.unit (armTree ![1, 1, c])).reindex
      (dEquiv c) :=
  weightedGraph_eq_unit_reindex _ _ _ (D_dVertex_apply c hc)

/-- The E arm order at rank `c + 4` in `lem:rem-model-supports`, Remark 3.11. -/
def eVertex (c : ℕ) : ArmVertex ![1, 2, c] → Fin (c + 4)
  | none => ⟨3, by omega⟩
  | some ⟨r, i⟩ =>
      ⟨if r = 0 then 1 else if r = 1 then (if i.val = 0 then 2 else 0) else i.val + 4,
        by
          have hi := i.isLt
          split_ifs <;> fin_cases r <;> simp_all⟩

/-- The E arm orders are bijective (`lem:rem-model-supports`, Remark 3.11). -/
theorem eVertex_bijective (c : ℕ) : Function.Bijective (eVertex c) := by
  constructor
  · rintro (_ | ⟨r, i⟩) (_ | ⟨s, j⟩) h
    · rfl
    · have hv := congrArg Fin.val h
      fin_cases s <;> simp [eVertex] at hv
      split_ifs at hv; omega
    · have hv := congrArg Fin.val h
      fin_cases r <;> simp [eVertex] at hv
      split_ifs at hv; omega
    · have hv := congrArg Fin.val h
      have hi := i.isLt
      have hj := j.isLt
      fin_cases r <;> fin_cases s <;>
        simp only [eVertex, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq,
          Fin.isValue, ite_true, ite_false, cons_val_zero, cons_val_one, cons_val] at hv hi hj <;>
        (try split_ifs at hv) <;> norm_num at hv <;>
        first | omega | (congr 2; apply Fin.ext; omega)
  · intro j
    by_cases hj : j.val < 4
    · interval_cases h : j.val
      · exact ⟨some ⟨1, ⟨1, by simp⟩⟩, Fin.ext (by simpa [eVertex] using h.symm)⟩
      · exact ⟨some ⟨0, ⟨0, by simp⟩⟩, Fin.ext (by simpa [eVertex] using h.symm)⟩
      · exact ⟨some ⟨1, ⟨0, by simp⟩⟩, Fin.ext (by simpa [eVertex] using h.symm)⟩
      · exact ⟨none, Fin.ext h.symm⟩
    · refine ⟨some ⟨2, ⟨j.val - 4, by simpa using (show j.val - 4 < c by omega)⟩⟩,
        Fin.ext ?_⟩
      simp only [eVertex, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        ite_false]
      omega

/-- The E bijections at every rank `c + 4` in `lem:rem-model-supports`, Remark 3.11. -/
noncomputable def eEquiv (c : ℕ) : ArmVertex ![1, 2, c] ≃ Fin (c + 4) :=
  Equiv.ofBijective (eVertex c) (eVertex_bijective c)

/-- The E entries in the displayed arm order of `lem:rem-model-supports`, Remark 3.11. -/
theorem E_eVertex_apply (c : ℕ) (i j : ArmVertex ![1, 2, c]) :
    E (c + 4) (eVertex c i) (eVertex c j) =
      if i = j then 2 else if (armTree ![1, 2, c]).Adj i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j; simp only [E_diag, ite_true]
  have heij : eVertex c i ≠ eVertex c j := (eVertex_bijective c).injective.ne hij
  simp only [E, Matrix.of_apply, ite_eq_right heij, ite_eq_right hij]
  congr 1
  apply propext
  rcases i with _ | ⟨r, i⟩ <;> rcases j with _ | ⟨s, j⟩
  · exact (hij rfl).elim
  · have hj := j.isLt
    fin_cases s <;> simp only [eVertex, armTree] at hj ⊢ <;> (try split_ifs) <;>
      simp_all [eVertex]
  · have hi := i.isLt
    fin_cases r <;> simp only [eVertex, armTree] at hi ⊢ <;> (try split_ifs) <;>
      simp_all [eVertex]
  · have hi := i.isLt
    have hj := j.isLt
    fin_cases r <;> fin_cases s <;> simp only [eVertex, armTree] at hi hj ⊢ <;>
      (try split_ifs) <;> simp_all [eVertex] <;> omega

/-- The E weighted supports in `lem:rem-model-supports`, Remark 3.11. -/
theorem weightedGraph_E (c : ℕ) :
    weightedGraph (E (c + 4)) = (WeightedGraph.unit (armTree ![1, 2, c])).reindex
      (eEquiv c) :=
  weightedGraph_eq_unit_reindex _ _ _ (E_eVertex_apply c)

/-- Every E support at rank `c + 4` is connected (`lem:rem-model-supports`, Remark 3.11). -/
theorem weightedGraph_E_support_connected (c : ℕ) :
    (weightedGraph (E (c + 4))).support.Connected := by
  rw [weightedGraph_E]
  apply WeightedGraph.connected_reindex
  rw [WeightedGraph.support_unit]
  exact armTree_connected _

/-- The F weighted path in `lem:rem-model-supports`, Remark 3.11. -/
theorem weightedGraph_F₄ : weightedGraph F₄ = WeightedGraph.singleDoublePath 4 1 := by
  apply WeightedGraph.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [weightedGraph, F₄, WeightedGraph.singleDoublePath, WeightedGraph.path]

/-- The G weighted edge in `lem:rem-model-supports`, Remark 3.11. -/
theorem weightedGraph_G₂ : weightedGraph G₂ = WeightedGraph.tripleEdge := by
  apply WeightedGraph.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [weightedGraph, G₂, WeightedGraph.tripleEdge, WeightedGraph.path]

/-- The weight-preserving named-model labellings of `lem:rem-model-supports`, Remark 3.11. -/
theorem model_support_labelling {n : ℕ} (t : FiniteType n) :
    (weightedGraph (modelEntries t)).HasDynkinLabelling := by
  cases t with
  | a n hn => exact .a n hn (Equiv.refl _) (weightedGraph_A n)
  | b n hn =>
    exact .doublePath n (n - 2) (by omega) (Or.inr (Or.inl (by omega)))
      (Equiv.refl _) (weightedGraph_B n)
  | c n hn =>
    exact .doublePath n (n - 2) (by omega) (Or.inr (Or.inl (by omega)))
      (Equiv.refl _) (weightedGraph_C n)
  | d n hn =>
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ n by omega)
    exact .d c (by omega) (dEquiv c) (weightedGraph_D c (by omega))
  | e₆ => exact .e₆ (eEquiv 2) (weightedGraph_E 2)
  | e₇ => exact .e₇ (eEquiv 3) (weightedGraph_E 3)
  | e₈ => exact .e₈ (eEquiv 4) (weightedGraph_E 4)
  | f₄ => exact .doublePath 4 1 (by omega) (by simp) (Equiv.refl _) weightedGraph_F₄
  | g₂ => exact .g₂ (Equiv.refl _) weightedGraph_G₂

end CartanMatrix

namespace WeightedGraph

open SimpleGraph

/-- Dynkin labellings have connected support (`lem:rem-labelled-connected`, Remark 3.11). -/
theorem HasDynkinLabelling.connected {ι : Type*} {X : WeightedGraph ι}
    (hX : X.HasDynkinLabelling) : X.support.Connected := by
  cases hX with
  | a n hn e h =>
    subst X
    apply connected_reindex
    rw [support_path _ _ _ (by intros; norm_num)]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact pathGraph_connected n
  | doublePath n k hk _ e h =>
    subst X
    apply connected_reindex
    rw [singleDoublePath, support_path _ _ _ (by intros; split_ifs <;> positivity)]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact pathGraph_connected n
  | d c _ e h | e₆ e h | e₇ e h | e₈ e h =>
    subst X
    apply connected_reindex
    rw [support_unit]
    exact armTree_connected _
  | g₂ e h =>
    subst X
    apply connected_reindex
    rw [tripleEdge, support_path _ _ _ (by intros; positivity)]
    exact pathGraph_connected 1

end WeightedGraph

namespace CartanMatrix

/-- The diagonal entries of the models in `def:rem-matrices`, Remark 3.11. -/
theorem model_diag {n : ℕ} (t : FiniteType n) (i : Fin n) : modelEntries t i i = 2 := by
  cases t <;> simp [modelEntries, A]

/-- The off-diagonal signs of the models in `def:rem-matrices`, Remark 3.11. -/
theorem model_offDiag_nonpos {n : ℕ} (t : FiniteType n) (i j : Fin n) (hij : i ≠ j) :
    modelEntries t i j ≤ 0 := by
  cases t with
  | a n _ => exact A_apply_le_zero_of_ne n i j hij
  | b n _ => exact B_off_diag_nonpos n i j hij
  | c n _ => exact C_off_diag_nonpos n i j hij
  | d n _ => exact D_off_diag_nonpos n i j hij
  | e₆ | e₇ | e₈ => exact E_off_diag_nonpos _ i j hij
  | f₄ => exact F₄_off_diag_nonpos i j hij
  | g₂ => exact G₂_off_diag_nonpos i j hij

/-- The B and C paths have symmetric zero relations (`def:rem-matrices`, Remark 3.11). -/
theorem B_zero_comm (n : ℕ) (i j : Fin n) : B n i j = 0 ↔ B n j i = 0 := by
  simp only [B, Matrix.of_apply]
  split_ifs <;> simp_all

/-- The symmetric zero relations in `def:rem-matrices`, Remark 3.11. -/
theorem model_zero_comm {n : ℕ} (t : FiniteType n) (i j : Fin n) :
    modelEntries t i j = 0 ↔ modelEntries t j i = 0 := by
  cases t with
  | a n _ => rw [modelEntries, (A_isSymm n).apply i j]
  | b n _ => exact B_zero_comm n i j
  | c n _ =>
    simpa only [modelEntries, ← B_transpose, Matrix.transpose_apply] using B_zero_comm n j i
  | d n _ => rw [modelEntries, (D_isSymm n).apply i j]
  | e₆ | e₇ | e₈ => rw [modelEntries, (E_isSymm _).apply i j]
  | f₄ => fin_cases i <;> fin_cases j <;> norm_num [modelEntries, F₄]
  | g₂ => fin_cases i <;> fin_cases j <;> norm_num [modelEntries, G₂]

/-- Connectedness of the named-model supports (`lem:rem-model-supports`, Remark 3.11). -/
theorem model_support_connected {n : ℕ} (t : FiniteType n) :
    (weightedGraph (modelEntries t)).support.Connected :=
  (model_support_labelling t).connected

end CartanMatrix
