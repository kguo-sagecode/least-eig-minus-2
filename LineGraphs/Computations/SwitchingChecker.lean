/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.GraphCertificates
import LineGraphs.Spectral.Switching

/-!
# Checked sign and permutation witnesses for Seidel switching

Both signs and bijectivity are checked before the matrix identity is interpreted.
-/

namespace Computations

/-- Check simultaneous permutation and conjugation by a diagonal sign matrix. -/
def checkSwitching (n : ℕ) (S T : IntMatrix) (d : IntVector) (p : List ℕ) : Bool :=
  checkShape n S && checkShape n T && (d.length == n) &&
  d.all (fun x => x == 1 || x == -1) && checkPermutation n p &&
  (List.range n).all (fun i => (List.range n).all (fun j =>
    entry S i j == d[i]?.getD 0 * d[j]?.getD 0 *
      entry T (p[i]?.getD n) (p[j]?.getD n)))

/-- The sign and permutation certificate gives genuine real switching equivalence. -/
theorem checkSwitching_sound {n : ℕ} {S T : IntMatrix} {d : IntVector} {p : List ℕ}
    (h : checkSwitching n S T d p = true) :
    (toMatrix (R := ℝ) n S).IsSwitchingEquivalent (toMatrix n T) := by
  obtain ⟨⟨⟨⟨⟨_, _⟩, hl⟩, hd⟩, hp⟩, he⟩ := by
    simpa only [checkSwitching, Bool.and_eq_true_iff, beq_iff_eq] using h
  obtain ⟨e, heq⟩ := checkPermutation_sound hp
  refine ⟨e, fun i => (d[i.val]?.getD 0 : ℝ), ?_, ?_⟩
  · intro i
    have hi : i.val < d.length := hl ▸ i.isLt
    have hs := List.all_eq_true.mp hd d[i.val] (List.getElem_mem hi)
    simp only [Bool.or_eq_true_iff, beq_iff_eq] at hs
    rcases hs with hs | hs <;> simp [List.getElem?_eq_getElem hi, hs]
  · intro i j
    have hij : entry S i j = d[i.val]?.getD 0 * d[j.val]?.getD 0 * entry T (e i) (e j) := by
      simpa [heq] using List.all_eq_true.mp
        (List.all_eq_true.mp he i.val (List.mem_range.mpr i.isLt)) j.val
        (List.mem_range.mpr j.isLt)
    change (entry S i j : ℝ) = (d[i.val]?.getD 0 : ℝ) * (d[j.val]?.getD 0 : ℝ) *
      (entry T (e i) (e j) : ℝ)
    exact_mod_cast hij

/-- The integer Seidel matrix of a zero-one adjacency table. -/
def seidelData (n : ℕ) (A : IntMatrix) : IntMatrix :=
  tabulate n fun i j => (if i = j then 0 else 1) - 2 * entry A i j

theorem seidelMatrix_graphOfMatrix {n : ℕ} {A : IntMatrix}
    (h : checkAdjacency n A = true) :
    (graphOfMatrix h).seidelMatrix = toMatrix n (seidelData n A) := by
  rw [SimpleGraph.seidelMatrix, adjMatrix_graphOfMatrix, seidelData, toMatrix_tabulate]
  ext i j
  by_cases hij : i = j <;> simp [hij, toMatrix]

/-- Graph guards followed by a switching certificate for the two Seidel matrices. -/
def checkSeidelSwitching (n : ℕ) (A B : IntMatrix) (d : IntVector) (p : List ℕ) : Bool :=
  checkAdjacency n A && checkAdjacency n B &&
    checkSwitching n (seidelData n A) (seidelData n B) d p

theorem checkSeidelSwitching_sound {n : ℕ} {A B : IntMatrix} {d : IntVector} {p : List ℕ}
    (hA : checkAdjacency n A = true) (hB : checkAdjacency n B = true)
    (h : checkSeidelSwitching n A B d p = true) :
    (graphOfMatrix hA).IsSwitchingEquivalent (graphOfMatrix hB) := by
  simpa only [SimpleGraph.IsSwitchingEquivalent, seidelMatrix_graphOfMatrix] using
    checkSwitching_sound (Bool.and_eq_true_iff.mp h).2

end Computations
