/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Connected matrix supports

The connected-support and edge-constancy lemmas in the Remark 3.11 blueprint.
The index type must be nonempty in the equivalence with matrix indecomposability:
Mathlib's matrix predicate also holds on an empty index type.
-/

namespace SimpleGraph

variable {ι S : Type*} {X : SimpleGraph ι}

/-- A function agreeing across every edge of a connected graph is constant
(`lem:rem-edge-constant` in the Remark 3.11 blueprint). -/
theorem Connected.constant_of_edge_eq (hX : X.Connected) {f : ι → S}
    (hf : ∀ ⦃u v⦄, X.Adj u v → f u = f v) (u v : ι) : f u = f v := by
  obtain ⟨p⟩ := hX u v
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hf h).trans ih

/-- The common value in the edge-constancy lemma exists, since a connected graph is nonempty. -/
theorem Connected.exists_constant_of_edge_eq (hX : X.Connected) {f : ι → S}
    (hf : ∀ ⦃u v⦄, X.Adj u v → f u = f v) : ∃ c, ∀ u, f u = c := by
  obtain ⟨u⟩ := hX.nonempty
  exact ⟨f u, fun v => hX.constant_of_edge_eq hf v u⟩

end SimpleGraph

namespace Matrix

variable {ι R : Type*} [Zero R]

/-- The off-diagonal nonzero support of a matrix whose zero entries are symmetric. -/
def supportGraph (M : Matrix ι ι R) (hzero : ∀ i j, M i j = 0 ↔ M j i = 0) :
    SimpleGraph ι where
  Adj i j := i ≠ j ∧ M i j ≠ 0
  symm := ⟨fun i j hij => ⟨hij.1.symm, fun h => hij.2 ((hzero i j).mpr h)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- On a finite nonempty index type, a matrix with symmetric zeros is indecomposable
exactly when its off-diagonal support is connected (`lem:connected` of Remark 3.11). -/
theorem isIndecomposable_iff_connected_support [Finite ι] [Nonempty ι]
    (M : Matrix ι ι R) (hzero : ∀ i j, M i j = 0 ↔ M j i = 0) :
    M.IsIndecomposable ↔ (M.supportGraph hzero).Connected := by
  classical
  rw [isIndecomposable_iff_blockTriangular_const (α := ℕ)]
  constructor
  · intro hM
    refine ⟨?_⟩
    intro u v
    let b : ι → ℕ := fun i => if (M.supportGraph hzero).Reachable u i then 0 else 1
    have hb : M.BlockTriangular b := by
      intro i j hij
      have hj : (M.supportGraph hzero).Reachable u j := by
        by_contra hn
        simp only [b, ite_eq_right hn] at hij
        split_ifs at hij <;> omega
      have hi : ¬ (M.supportGraph hzero).Reachable u i := by
        intro hi
        simp only [b, ite_eq_left hi, not_lt_zero] at hij
      by_contra hne
      have hji : (M.supportGraph hzero).Adj j i :=
        ⟨fun h => hi (h ▸ hj), fun h => hne ((hzero i j).mpr h)⟩
      exact hi (hj.trans hji.reachable)
    obtain ⟨c, hc⟩ := hM b hb
    have hbu : b u = 0 := by simp [b]
    have hbv : b v = 0 := by rw [hc] at hbu ⊢; exact hbu
    simpa only [b, ite_eq_left_iff, one_ne_zero, imp_false, not_not] using hbv
  · intro hX b hb
    obtain ⟨c, hc⟩ := hX.exists_constant_of_edge_eq (f := b) (fun {i j} hij => by
      apply le_antisymm
      · by_contra h
        exact hij.2 (hb (lt_of_not_ge h))
      · by_contra h
        exact hij.2 ((hzero i j).mpr (hb (lt_of_not_ge h))))
    exact ⟨c, funext hc⟩

end Matrix
