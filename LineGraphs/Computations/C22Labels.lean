/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.SwitchingModels
import LineGraphs.Computations.GraphCertificates

/-! # Edge labels and semantic soundness for `comp:C22` (Remark 4.14) -/

namespace Computations.C22

open SimpleGraph

/-- Increasing endpoint pairs used to label the triangular graphs in C22. -/
abbrev Pair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Two distinct increasing pairs share an endpoint, as in the source graphs of C22. -/
def pairAdj {n : ℕ} (p q : Pair n) : Prop :=
  p ≠ q ∧ (p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨ p.1.2 = q.1.2)

instance {n : ℕ} (p q : Pair n) : Decidable (pairAdj p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The finite formula for a switched triangular graph in C22. -/
def pairSwitchAdj {n : ℕ} (Z : SimpleGraph (Fin n)) (p q : Pair n) : Prop :=
  p ≠ q ∧ (pairAdj p q ↔ (Z.Adj p.1.1 p.1.2 ↔ Z.Adj q.1.1 q.1.2))

instance {n : ℕ} (Z : SimpleGraph (Fin n)) [DecidableRel Z.Adj] (p q : Pair n) :
    Decidable (pairSwitchAdj Z p q) := inferInstanceAs (Decidable (_ ∧ _))

/-- Lexicographic edge labels for `K5` in `comp:C22`. -/
def edgePairs5 : Fin 10 → Pair 5 :=
  ![⟨(0, 1), by decide⟩,
    ⟨(0, 2), by decide⟩,
    ⟨(0, 3), by decide⟩,
    ⟨(0, 4), by decide⟩,
    ⟨(1, 2), by decide⟩,
    ⟨(1, 3), by decide⟩,
    ⟨(1, 4), by decide⟩,
    ⟨(2, 3), by decide⟩,
    ⟨(2, 4), by decide⟩,
    ⟨(3, 4), by decide⟩]

/-- The lexicographic labels cover all increasing pairs in the `K5` case of C22. -/
theorem edgePairs5_bijective : Function.Bijective edgePairs5 := by decide +kernel

/-- The C22 labels interpreted as actual edges of `K5`. -/
noncomputable def edgeLabel5 : Fin 10 ≃ (⊤ : SimpleGraph (Fin 5)).edgeSet :=
  (Equiv.ofBijective edgePairs5 edgePairs5_bijective).trans
    (completeGraphEdgeEquiv (Fin 5))

/-- Lexicographic edge labels for `K6` in `comp:C22`. -/
def edgePairs6 : Fin 15 → Pair 6 :=
  ![⟨(0, 1), by decide⟩,
    ⟨(0, 2), by decide⟩,
    ⟨(0, 3), by decide⟩,
    ⟨(0, 4), by decide⟩,
    ⟨(0, 5), by decide⟩,
    ⟨(1, 2), by decide⟩,
    ⟨(1, 3), by decide⟩,
    ⟨(1, 4), by decide⟩,
    ⟨(1, 5), by decide⟩,
    ⟨(2, 3), by decide⟩,
    ⟨(2, 4), by decide⟩,
    ⟨(2, 5), by decide⟩,
    ⟨(3, 4), by decide⟩,
    ⟨(3, 5), by decide⟩,
    ⟨(4, 5), by decide⟩]

/-- The lexicographic labels cover all increasing pairs in the `K6` case of C22. -/
theorem edgePairs6_bijective : Function.Bijective edgePairs6 := by decide +kernel

/-- The C22 labels interpreted as actual edges of `K6`. -/
noncomputable def edgeLabel6 : Fin 15 ≃ (⊤ : SimpleGraph (Fin 6)).edgeSet :=
  (Equiv.ofBijective edgePairs6 edgePairs6_bijective).trans
    (completeGraphEdgeEquiv (Fin 6))

/-- Lexicographic edge labels for `K8` in `comp:C22`. -/
def edgePairs8 : Fin 28 → Pair 8 :=
  ![⟨(0, 1), by decide⟩,
    ⟨(0, 2), by decide⟩,
    ⟨(0, 3), by decide⟩,
    ⟨(0, 4), by decide⟩,
    ⟨(0, 5), by decide⟩,
    ⟨(0, 6), by decide⟩,
    ⟨(0, 7), by decide⟩,
    ⟨(1, 2), by decide⟩,
    ⟨(1, 3), by decide⟩,
    ⟨(1, 4), by decide⟩,
    ⟨(1, 5), by decide⟩,
    ⟨(1, 6), by decide⟩,
    ⟨(1, 7), by decide⟩,
    ⟨(2, 3), by decide⟩,
    ⟨(2, 4), by decide⟩,
    ⟨(2, 5), by decide⟩,
    ⟨(2, 6), by decide⟩,
    ⟨(2, 7), by decide⟩,
    ⟨(3, 4), by decide⟩,
    ⟨(3, 5), by decide⟩,
    ⟨(3, 6), by decide⟩,
    ⟨(3, 7), by decide⟩,
    ⟨(4, 5), by decide⟩,
    ⟨(4, 6), by decide⟩,
    ⟨(4, 7), by decide⟩,
    ⟨(5, 6), by decide⟩,
    ⟨(5, 7), by decide⟩,
    ⟨(6, 7), by decide⟩]

/-- The lexicographic labels cover all increasing pairs in the `K8` case of C22. -/
theorem edgePairs8_bijective : Function.Bijective edgePairs8 := by decide +kernel

/-- The C22 labels interpreted as actual edges of `K8`. -/
noncomputable def edgeLabel8 : Fin 28 ≃ (⊤ : SimpleGraph (Fin 8)).edgeSet :=
  (Equiv.ofBijective edgePairs8 edgePairs8_bijective).trans
    (completeGraphEdgeEquiv (Fin 8))

/-- C22's matrix checker produces an isomorphism of the actual switched line graph. -/
theorem nonempty_iso_switchTriangular_of_check {n m : ℕ}
    (Z : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (pairs : Fin m → Pair n) (hp : Function.Bijective pairs)
    (A B : IntMatrix) (perm : List ℕ)
    (hA : ∀ i j, pairSwitchAdj Z (pairs i) (pairs j) ↔ entry A i j = 1)
    (hB : ∀ i j, H.Adj i j ↔ entry B i j = 1)
    (hc : checkGraphIso m A B perm = true) :
    Nonempty (switchTriangular Z ≃g H) := by
  let e := (Equiv.ofBijective pairs hp).trans (completeGraphEdgeEquiv (Fin n))
  apply nonempty_iso_of_checkGraphIso' _ H e (Equiv.refl _) _ hB hc
  intro i j
  exact (switchTriangular_adj Z (pairs i) (pairs j)).trans (hA i j)

/-- C22's unswitched triangular graph has the expected adjacency table. -/
theorem edgeLabel8_adj (i j : Fin 28) :
    (⊤ : SimpleGraph (Fin 8)).lineGraph.Adj (edgeLabel8 i) (edgeLabel8 j) ↔
      pairAdj (edgePairs8 i) (edgePairs8 j) :=
  lineGraph_completeGraph_adj _ _

/-- The pair adjacency for the triangular graph with one extra isolated vertex (C22). -/
def sumPairAdj {n : ℕ} : (Pair n ⊕ Fin 1) → (Pair n ⊕ Fin 1) → Prop
  | .inl p, .inl q => pairAdj p q
  | _, _ => False

/-- The switching set excludes the extra vertex in assertion 2 of C22. -/
def sumMarked {n : ℕ} (Z : SimpleGraph (Fin n)) : (Pair n ⊕ Fin 1) → Prop
  | .inl p => Z.Adj p.1.1 p.1.2
  | .inr _ => False

instance {n : ℕ} (p q : Pair n ⊕ Fin 1) : Decidable (sumPairAdj p q) := by
  cases p <;> cases q <;> dsimp [sumPairAdj] <;> infer_instance

instance {n : ℕ} (Z : SimpleGraph (Fin n)) [DecidableRel Z.Adj] (p : Pair n ⊕ Fin 1) :
    Decidable (sumMarked Z p) := by
  cases p <;> dsimp [sumMarked] <;> infer_instance

/-- The finite adjacency formula for assertion 2 of C22. -/
def sumSwitchAdj {n : ℕ} (Z : SimpleGraph (Fin n)) (p q : Pair n ⊕ Fin 1) : Prop :=
  p ≠ q ∧ (sumPairAdj p q ↔ (sumMarked Z p ↔ sumMarked Z q))

instance {n : ℕ} (Z : SimpleGraph (Fin n)) [DecidableRel Z.Adj] (p q : Pair n ⊕ Fin 1) :
    Decidable (sumSwitchAdj Z p q) := inferInstanceAs (Decidable (_ ∧ _))

/-- The first fifteen vertices are edges of `K₆`; the last is the extra vertex (C22). -/
def sumPairs6 (i : Fin 16) : Pair 6 ⊕ Fin 1 :=
  Sum.map edgePairs6 id (finSumFinEquiv.symm i)

/-- The actual graph vertices corresponding to `sumPairs6` in assertion 2 of C22. -/
noncomputable def sumLabel6 : Fin 16 ≃ (⊤ : SimpleGraph (Fin 6)).edgeSet ⊕ Fin 1 :=
  (finSumFinEquiv : Fin 15 ⊕ Fin 1 ≃ Fin 16).symm.trans
    (edgeLabel6.sumCongr (Equiv.refl _))

/-- The actual C22 sum labels are obtained by interpreting their ordered pairs as edges. -/
theorem sumLabel6_apply (i : Fin 16) : sumLabel6 i =
    ((completeGraphEdgeEquiv (Fin 6)).sumCongr (Equiv.refl (Fin 1))) (sumPairs6 i) := by
  dsimp [sumLabel6, sumPairs6]
  cases (finSumFinEquiv.symm i : Fin 15 ⊕ Fin 1) <;> rfl

/-- The sum-pair formula is the actual switching adjacency in assertion 2 of C22. -/
theorem sumPair_switch_adj {n : ℕ} (Z : SimpleGraph (Fin n)) (p q : Pair n ⊕ Fin 1) :
    (switchTriangularAddOne Z).Adj
        (((completeGraphEdgeEquiv (Fin n)).sumCongr (Equiv.refl (Fin 1))) p)
        (((completeGraphEdgeEquiv (Fin n)).sumCongr (Equiv.refl (Fin 1))) q) ↔
      sumSwitchAdj Z p q := by
  cases p <;> cases q <;>
    simp [switchTriangularAddOne, triangularAddOne, switch_adj, SimpleGraph.sum,
      sumSwitchAdj, sumPairAdj, sumMarked, pairAdj, lineGraph_completeGraph_adj,
      (completeGraphEdgeEquiv (Fin n)).injective.eq_iff]

/-- The C22 sum labels turn the checked matrix into the actual switched graph. -/
theorem nonempty_iso_switchTriangularAddOne_of_check
    (Z : SimpleGraph (Fin 6)) (H : SimpleGraph (Fin 16))
    (A B : IntMatrix) (perm : List ℕ)
    (hA : ∀ i j, sumSwitchAdj Z (sumPairs6 i) (sumPairs6 j) ↔ entry A i j = 1)
    (hB : ∀ i j, H.Adj i j ↔ entry B i j = 1)
    (hc : checkGraphIso 16 A B perm = true) :
    Nonempty (switchTriangularAddOne Z ≃g H) := by
  apply nonempty_iso_of_checkGraphIso' _ H sumLabel6 (Equiv.refl _) _ hB hc
  intro i j
  rw [sumLabel6_apply, sumLabel6_apply]
  exact (sumPair_switch_adj Z (sumPairs6 i) (sumPairs6 j)).trans (hA i j)

end Computations.C22
