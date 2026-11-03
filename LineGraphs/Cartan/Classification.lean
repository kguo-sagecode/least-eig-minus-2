/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Invariants

/-!
# Theorem A of Remark 3.11

`thm:A` of the Remark 3.11 blueprint: a nonempty indecomposable finite Cartan matrix
is, after a simultaneous reindexing by `Fin ℓ`, one of the named matrices in the canonical
list, with a unique type and rank. The converse is
`CartanMatrix.IsFiniteTypeModel.isFiniteCartan` and `.isIndecomposable` (`Converse.lean`),
and uniqueness is `CartanMatrix.IsFiniteTypeModel.type_eq_of_reindex_eq` (`Invariants.lean`).
-/

namespace Matrix.IsFiniteCartan

open CartanMatrix

/-- Theorem A of Remark 3.11 (`thm:A`), the existence part: an indecomposable finite Cartan
matrix on a nonempty finite index type is a named matrix of the canonical list after a
simultaneous reindexing by `Fin ℓ`. The steps `rAsupport` (the weighted classification) and
`rAentries`, `rABCorient`, `rAForient`, `rAGorient` (the orientations) of the blueprint. -/
theorem classification {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {M : Matrix I I ℤ} (hM : M.IsFiniteCartan) (hI : M.IsIndecomposable) :
    ∃ l : ℕ, ∃ e : Fin l ≃ I, IsFiniteTypeModel (M.submatrix e e) :=
  hM.exists_model_of_dynkin_labelling (hM.weighted_classification hI)

/-- The uniqueness clause of Theorem A of Remark 3.11 (`thm:A`, step `rAunique`), for one
matrix: two reindexings of `M` onto named matrices give the same type and rank. The
reindexings themselves need not agree. -/
theorem classification_type_unique {I : Type*} {M : Matrix I I ℤ} {m n : ℕ}
    (s : FiniteType m) (t : FiniteType n) (e : Fin m ≃ I) (f : Fin n ≃ I)
    (hs : M.submatrix e e = modelEntries s) (ht : M.submatrix f f = modelEntries t) :
    (⟨m, s⟩ : (n : ℕ) × FiniteType n) = ⟨n, t⟩ := by
  apply IsFiniteTypeModel.type_eq_of_reindex_eq s t (f.trans e.symm)
  rw [← hs, ← ht, submatrix_submatrix]
  congr 1 <;> ext i <;> simp

end Matrix.IsFiniteCartan
