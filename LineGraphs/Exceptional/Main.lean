/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.Types
import LineGraphs.Exceptional.Growth
import LineGraphs.Exceptional.Maximal

/-! # The mathematical classification of the exceptional-graph lists

Theorem `thm:main` (Theorem C.1) and the paragraph after Proposition `prop:maximal`
(Proposition 3.7) of [Exc]. The lists are sets selected from the abstract growth, for
every valid certificate choice and canonical form. Positive semidefiniteness together
with failure of positive definiteness expresses `λ_min = -2`; positive definiteness
expresses `λ_min > -2`.

The statement about the database files, the correctness of the program, and the
correctness of `labelg` are not formalized.
-/

namespace Matrix

-- Theorem C.1 [Exc]
/-- The rank test in `thm:main` (Theorem C.1) of [Exc]: a positive semidefinite real
matrix is positive definite exactly when it has full rank. -/
theorem PosSemidef.posDef_iff_rank_eq {V : Type*} [Fintype V]
    {M : Matrix V V ℝ} (hM : M.PosSemidef) : M.PosDef ↔ M.rank = Fintype.card V := by
  classical
  constructor
  · exact fun h => rank_of_isUnit _ h.isUnit
  · intro hr
    apply hM.posDef_iff_isUnit.mpr
    apply mulVec_surjective_iff_isUnit.mp
    change Function.Surjective M.mulVecLin
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    simpa only [rank, Module.finrank_pi] using hr

end Matrix

namespace SimpleGraph

-- Theorem C.1 [Exc]
/-- The rank and lattice determinant pairs in `thm:main` (Theorem C.1) of [Exc],
as characterized by `prop:types` (Proposition 2.6). -/
def exceptionalRankDetPairs : Set (ℕ × ℕ) := {(6, 3), (7, 2), (8, 1)}

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {X : SimpleGraph V} {Z : SimpleGraph W} [DecidableRel X.Adj] [DecidableRel Z.Adj]

-- Theorem C.1 [Exc]
omit [Fintype V] [Fintype W] in
/-- The spectral split in `thm:main` (Theorem C.1) of [Exc] is invariant under graph
isomorphism. This is the positive-definite formulation of `λ_min > -2`. -/
theorem Iso.posDef_two_add_adjMatrix_iff [Finite V] [Finite W] (e : X ≃g Z) :
    ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosDef ↔
      ((2 : ℝ) • (1 : Matrix W W ℝ) + Z.adjMatrix ℝ).PosDef := by
  let := Fintype.ofFinite V
  let := Fintype.ofFinite W
  constructor
  · intro h
    convert h.submatrix e.symm.injective using 1
    ext u v
    simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, adjMatrix_apply, e.symm.injective.eq_iff, e.symm.map_rel_iff]
  · intro h
    convert h.submatrix e.injective using 1
    ext u v
    simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, adjMatrix_apply, e.injective.eq_iff, e.map_rel_iff]

-- Theorem C.1 [Exc]
/-- The rank bounds used in `thm:main` (Theorem C.1) of [Exc]: exceptional graphs
have Gram rank six, seven or eight. -/
theorem IsExceptional.rank_mem (hX : X.IsExceptional) :
    ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank ∈ ({6, 7, 8} : Set ℕ) := by
  have h := (X.isExceptional_iff_rank_latticeDet hX.1 hX.2.1).mp hX
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
    h.elim (fun h => Or.inl (congrArg Prod.fst h))
      (fun h => h.elim (fun h => Or.inr (Or.inl (congrArg Prod.fst h)))
        (fun h => Or.inr (Or.inr (congrArg Prod.fst h))))

-- Theorem C.1 [Exc]
/-- The order bounds in `thm:main` (Theorem C.1) of [Exc]: an exceptional graph has
between six and thirty-six vertices. -/
theorem IsExceptional.card_bounds (hX : X.IsExceptional) :
    6 ≤ Fintype.card V ∧ Fintype.card V ≤ 36 := by
  have hr := hX.rank_mem
  have hle := Matrix.rank_le_card_width ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  exact ⟨by omega, hX.isRepresentedIn_E₈.card_le_36⟩

-- Theorem C.1 [Exc]
/-- The order restriction for list (B) in `thm:main` (Theorem C.1) of [Exc]: a
positive-definite exceptional graph has six, seven or eight vertices. -/
theorem IsExceptional.card_mem_of_posDef (hX : X.IsExceptional)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosDef) :
    Fintype.card V ∈ ({6, 7, 8} : Set ℕ) := by
  simpa only [Matrix.rank_of_isUnit _ hp.isUnit] using hX.rank_mem

-- Theorem C.1 [Exc]
open Classical in
/-- The classification step in `thm:main` (Theorem C.1) of [Exc]: exceptional
graphs are exactly the graphs in a level with one of the three exceptional pairs.
This statement uses classical adjacency decidability, consistently with `levels` and `growth`. -/
theorem isExceptional_iff_mem_levels_rank_latticeDet {n : ℕ} (X : SimpleGraph (Fin n)) :
    X.IsExceptional ↔ X ∈ levels n ∧
      (((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) + X.adjMatrix ℝ).rank,
        X.latticeDet) ∈ exceptionalRankDetPairs := by
  constructor
  · intro hX
    refine ⟨⟨hX.1, hX.isRepresentedIn_E₈⟩, ?_⟩
    exact (X.isExceptional_iff_rank_latticeDet hX.1 hX.2.1).mp hX
  · rintro ⟨hX, hr⟩
    exact (X.isExceptional_iff_rank_latticeDet hX.1
      hX.2.posSemidef_two_add_adjMatrix_and_rank_le_eight.1).mpr hr

-- Theorem C.1 [Exc]
open Classical in
/-- The mathematical classification of list (A) in `thm:main` (Theorem C.1) of
[Exc]. The statement about files, the program and `labelg` is not formalized.
This statement uses classical adjacency decidability, consistently with `levels` and `growth`. -/
theorem isExceptional_and_not_posDef_iff {n : ℕ} (X : SimpleGraph (Fin n)) :
    (X.IsExceptional ∧ ¬ ((2 : ℝ) • 1 + X.adjMatrix ℝ).PosDef) ↔
      X ∈ levels n ∧ ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) + X.adjMatrix ℝ).rank < n ∧
        (((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) + X.adjMatrix ℝ).rank,
          X.latticeDet) ∈ exceptionalRankDetPairs := by
  constructor
  · rintro ⟨hX, hpd⟩
    obtain ⟨hL, ht⟩ := (isExceptional_iff_mem_levels_rank_latticeDet X).mp hX
    have hr := Matrix.rank_le_card_width ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      X.adjMatrix ℝ)
    have hn := hX.2.1.posDef_iff_rank_eq.not.mp hpd
    simp only [Fintype.card_fin] at hr hn
    exact ⟨hL, by omega, ht⟩
  · rintro ⟨hL, hr, ht⟩
    have hX := (isExceptional_iff_mem_levels_rank_latticeDet X).mpr ⟨hL, ht⟩
    refine ⟨hX, ?_⟩
    intro hp
    have := hX.2.1.posDef_iff_rank_eq.mp hp
    simp only [Fintype.card_fin] at this
    omega

-- Theorem C.1 [Exc]
open Classical in
/-- The mathematical classification of list (B) in `thm:main` (Theorem C.1) of
[Exc]. The statement about files, the program and `labelg` is not formalized.
This statement uses classical adjacency decidability, consistently with `levels` and `growth`. -/
theorem isExceptional_and_posDef_iff {n : ℕ} (X : SimpleGraph (Fin n)) :
    (X.IsExceptional ∧ ((2 : ℝ) • 1 + X.adjMatrix ℝ).PosDef) ↔
      X ∈ levels n ∧ ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) + X.adjMatrix ℝ).rank = n ∧
        (((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) + X.adjMatrix ℝ).rank,
          X.latticeDet) ∈ exceptionalRankDetPairs := by
  constructor
  · rintro ⟨hX, hp⟩
    obtain ⟨hL, ht⟩ := (isExceptional_iff_mem_levels_rank_latticeDet X).mp hX
    exact ⟨hL, by simpa using hX.2.1.posDef_iff_rank_eq.mp hp, ht⟩
  · rintro ⟨hL, hr, ht⟩
    have hX := (isExceptional_iff_mem_levels_rank_latticeDet X).mpr ⟨hL, ht⟩
    exact ⟨hX, hX.2.1.posDef_iff_rank_eq.mpr (by simpa using hr)⟩

end SimpleGraph

namespace SimpleGraph

-- Theorem C.1 [Exc]
/-- The mathematical list (A) in `thm:main` (Theorem C.1) of [Exc], as a set:
keep growth graphs of rank less than their order with an exceptional rank and determinant.
The statement about files and the correctness of the program and of `labelg` are not formalized. -/
noncomputable def singularExceptionalGrowth (c : CertificateChoice) (q : CanonicalForm) (n : ℕ) :
    Set (SimpleGraph (Fin n)) := by
  classical
  exact {X | X ∈ growth c q n ∧ ((2 : ℝ) • 1 + X.adjMatrix ℝ).rank < n ∧
    (((2 : ℝ) • 1 + X.adjMatrix ℝ).rank, X.latticeDet) ∈ exceptionalRankDetPairs}

-- Theorem C.1 [Exc]
/-- The mathematical list (B) in `thm:main` (Theorem C.1) of [Exc], as a set:
keep growth graphs of full rank with an exceptional rank and determinant.
The statement about files and the correctness of the program and of `labelg` are not formalized. -/
noncomputable def definiteExceptionalGrowth (c : CertificateChoice) (q : CanonicalForm) (n : ℕ) :
    Set (SimpleGraph (Fin n)) := by
  classical
  exact {X | X ∈ growth c q n ∧ ((2 : ℝ) • 1 + X.adjMatrix ℝ).rank = n ∧
    (((2 : ℝ) • 1 + X.adjMatrix ℝ).rank, X.latticeDet) ∈ exceptionalRankDetPairs}

-- Proposition 3.7 [Exc]
/-- The mathematical maximal list in the paragraph after `prop:maximal`
(Proposition 3.7) of [Exc]: graphs of either list with no nonzero admissible vector
for the chosen certificate. The statement about files and the correctness of the program
and of `labelg` are not formalized. -/
noncomputable def maximalExceptionalGrowth (c : CertificateChoice) (q : CanonicalForm) (n : ℕ) :
    Set (SimpleGraph (Fin n)) := by
  classical
  exact {X | X ∈ singularExceptionalGrowth c q n ∪ definiteExceptionalGrowth c q n ∧
    ∀ s : c.indices X → ℤ, s ≠ 0 → ¬ X.integralGramMatrix.IsAdmissible (c.indices X) s}

-- Theorem C.1 [Exc]
open Classical in
/-- The rank filter defining list (A) in `thm:main` (Theorem C.1) of [Exc] selects
exactly the exceptional growth graphs with `λ_min = -2`.
This statement uses classical adjacency decidability, consistently with `levels` and `growth`. -/
theorem mem_singularExceptionalGrowth_iff (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} (X : SimpleGraph (Fin n)) :
    X ∈ singularExceptionalGrowth c q n ↔ X ∈ growth c q n ∧ X.IsExceptional ∧
      ¬ ((2 : ℝ) • 1 + X.adjMatrix ℝ).PosDef := by
  classical
  change (X ∈ growth c q n ∧ _ ∧ _) ↔ _
  rw [isExceptional_and_not_posDef_iff X]
  have hL := growth_subset_levels c q n (a := X)
  tauto

-- Theorem C.1 [Exc]
open Classical in
/-- The rank filter defining list (B) in `thm:main` (Theorem C.1) of [Exc] selects
exactly the exceptional growth graphs with `λ_min > -2`.
This statement uses classical adjacency decidability, consistently with `levels` and `growth`. -/
theorem mem_definiteExceptionalGrowth_iff (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} (X : SimpleGraph (Fin n)) :
    X ∈ definiteExceptionalGrowth c q n ↔ X ∈ growth c q n ∧ X.IsExceptional ∧
      ((2 : ℝ) • 1 + X.adjMatrix ℝ).PosDef := by
  classical
  change (X ∈ growth c q n ∧ _ ∧ _) ↔ _
  rw [isExceptional_and_posDef_iff X]
  have hL := growth_subset_levels c q n (a := X)
  tauto

-- Proposition 3.7 [Exc]
open Classical in
/-- The two rank filters and the admissibility filter select exactly the maximal
exceptional growth graphs, as stated after `prop:maximal` (Proposition 3.7) of [Exc].
This statement uses classical adjacency decidability, consistently with `levels` and `growth`. -/
theorem mem_maximalExceptionalGrowth_iff (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} (X : SimpleGraph (Fin n)) :
    X ∈ maximalExceptionalGrowth c q n ↔ X ∈ growth c q n ∧ X.IsMaximalExceptional := by
  classical
  change ((X ∈ singularExceptionalGrowth c q n ∨ X ∈ definiteExceptionalGrowth c q n) ∧
    ∀ s, s ≠ 0 → ¬ X.integralGramMatrix.IsAdmissible (c.indices X) s) ↔ _
  rw [mem_singularExceptionalGrowth_iff, mem_definiteExceptionalGrowth_iff]
  constructor
  · rintro ⟨h, hs⟩
    have hX : X.IsExceptional := h.elim (fun h => h.2.1) (fun h => h.2.1)
    exact ⟨h.elim And.left And.left,
      (hX.isMaximalExceptional_iff_no_admissible (c.valid X hX.2.1)).mpr hs⟩
  · rintro ⟨hg, hm⟩
    refine ⟨?_, (hm.1.isMaximalExceptional_iff_no_admissible (c.valid X hm.1.2.1)).mp hm⟩
    by_cases hp : ((2 : ℝ) • 1 + X.adjMatrix ℝ).PosDef
    · exact Or.inr ⟨hg, hm.1, hp⟩
    · exact Or.inl ⟨hg, hm.1, hp⟩

-- Theorem C.1 [Exc]
/-- List (A) of `thm:main` (Theorem C.1) of [Exc], as a set: for every certificate
choice and canonical form and every positive order, all selected graphs are exceptional
with `λ_min = -2`, and each such isomorphism class occurs exactly once.
The statement about files and the correctness of the program and of `labelg` are not formalized. -/
theorem singularExceptionalGrowth_represents (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} (hn : 1 ≤ n) :
    (∀ X ∈ singularExceptionalGrowth c q n,
      letI := Classical.decRel X.Adj
      X.IsExceptional ∧ ¬ ((2 : ℝ) • 1 + X.adjMatrix ℝ).PosDef) ∧
    (∀ Z : SimpleGraph (Fin n),
      letI := Classical.decRel Z.Adj
      Z.IsExceptional ∧ ¬ ((2 : ℝ) • 1 + Z.adjMatrix ℝ).PosDef →
        ∃! X, X ∈ singularExceptionalGrowth c q n ∧ Nonempty (X ≃g Z)) := by
  classical
  constructor
  · intro X hX
    exact ((mem_singularExceptionalGrowth_iff c q X).mp hX).2
  · intro Z hZ
    obtain ⟨X, ⟨hX, ⟨e⟩⟩, hu⟩ := existsUnique_mem_growth_iso c q hn
      ((isExceptional_iff_mem_levels_rank_latticeDet Z).mp hZ.1).1
    refine ⟨X, ⟨?_, ⟨e⟩⟩, ?_⟩
    · exact (mem_singularExceptionalGrowth_iff c q X).mpr
        ⟨hX, e.isExceptional_iff.mpr hZ.1, e.posDef_two_add_adjMatrix_iff.not.mpr hZ.2⟩
    · intro Y hY
      exact hu Y ⟨((mem_singularExceptionalGrowth_iff c q Y).mp hY.1).1, hY.2⟩

-- Theorem C.1 [Exc]
/-- List (B) of `thm:main` (Theorem C.1) of [Exc], as a set: for every certificate
choice and canonical form and every positive order, all selected graphs are exceptional
with `λ_min > -2`, and each such isomorphism class occurs exactly once.
The statement about files and the correctness of the program and of `labelg` are not formalized. -/
theorem definiteExceptionalGrowth_represents (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} (hn : 1 ≤ n) :
    (∀ X ∈ definiteExceptionalGrowth c q n,
      letI := Classical.decRel X.Adj
      X.IsExceptional ∧ ((2 : ℝ) • 1 + X.adjMatrix ℝ).PosDef) ∧
    (∀ Z : SimpleGraph (Fin n),
      letI := Classical.decRel Z.Adj
      Z.IsExceptional ∧ ((2 : ℝ) • 1 + Z.adjMatrix ℝ).PosDef →
        ∃! X, X ∈ definiteExceptionalGrowth c q n ∧ Nonempty (X ≃g Z)) := by
  classical
  constructor
  · intro X hX
    exact ((mem_definiteExceptionalGrowth_iff c q X).mp hX).2
  · intro Z hZ
    obtain ⟨X, ⟨hX, ⟨e⟩⟩, hu⟩ := existsUnique_mem_growth_iso c q hn
      ((isExceptional_iff_mem_levels_rank_latticeDet Z).mp hZ.1).1
    refine ⟨X, ⟨?_, ⟨e⟩⟩, ?_⟩
    · exact (mem_definiteExceptionalGrowth_iff c q X).mpr
        ⟨hX, e.isExceptional_iff.mpr hZ.1, e.posDef_two_add_adjMatrix_iff.mpr hZ.2⟩
    · intro Y hY
      exact hu Y ⟨((mem_definiteExceptionalGrowth_iff c q Y).mp hY.1).1, hY.2⟩

-- Proposition 3.7 [Exc]
/-- The paragraph after `prop:maximal` (Proposition 3.7) of [Exc], as a set: for
every certificate choice and canonical form, the filtered graphs are maximal exceptional
graphs, exactly one per isomorphism class at each positive order. The statement about files
and the correctness of the program and of `labelg` are not formalized. -/
theorem maximalExceptionalGrowth_represents (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} (hn : 1 ≤ n) :
    (∀ X ∈ maximalExceptionalGrowth c q n,
      letI := Classical.decRel X.Adj
      X.IsMaximalExceptional) ∧
    (∀ Z : SimpleGraph (Fin n),
      letI := Classical.decRel Z.Adj
      Z.IsMaximalExceptional →
        ∃! X, X ∈ maximalExceptionalGrowth c q n ∧ Nonempty (X ≃g Z)) := by
  classical
  constructor
  · intro X hX
    exact ((mem_maximalExceptionalGrowth_iff c q X).mp hX).2
  · intro Z hZ
    obtain ⟨X, ⟨hX, ⟨e⟩⟩, hu⟩ := existsUnique_mem_growth_iso c q hn
      ((isExceptional_iff_mem_levels_rank_latticeDet Z).mp hZ.1).1
    refine ⟨X, ⟨?_, ⟨e⟩⟩, ?_⟩
    · exact (mem_maximalExceptionalGrowth_iff c q X).mpr
        ⟨hX, e.isMaximalExceptional_iff.mpr hZ⟩
    · intro Y hY
      exact hu Y ⟨((mem_maximalExceptionalGrowth_iff c q Y).mp hY.1).1, hY.2⟩

end SimpleGraph
