/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Monotonicity
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Labelled paths and arm trees

Support and containment interfaces for the explicit graphs in the Remark 3.11 proof.
Arm positions are zero based: position 0 is adjacent to the centre.
-/

namespace WeightedGraph

variable {ι κ : Type*}

/-- Give every edge of a simple graph weight one. -/
def unit (X : SimpleGraph ι) [DecidableRel X.Adj] : WeightedGraph ι where
  weights := X.adjMatrix ℝ
  symmetric := Matrix.isHermitian_iff_isSymm.mp (X.isHermitian_adjMatrix ℝ)
  nonneg i j := by simp only [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num
  diag i := by simp

/-- `def:rem-weighted`, Remark 3.11 of [CGSS]: assigning unit edge weights
recovers the original simple graph as the support. -/
@[simp]
theorem support_unit (X : SimpleGraph ι) [DecidableRel X.Adj] : (unit X).support = X := by
  ext i j
  change (0 < X.adjMatrix ℝ i j) ↔ X.Adj i j
  simp only [SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp_all

/-- Transport all weights along a vertex equivalence. -/
def reindex (X : WeightedGraph ι) (e : ι ≃ κ) : WeightedGraph κ where
  weights := Matrix.reindex e e X.weights
  symmetric := Matrix.isHermitian_iff_isSymm.mp (X.isHermitian.reindex e)
  nonneg i j := X.nonneg (e.symm i) (e.symm j)
  diag i := X.diag (e.symm i)

/-- Unit containment is equivalent to preservation of support edges, with the same embedding. -/
theorem unit_contains_iff_support_embedding (X : WeightedGraph ι)
    (hweights : ∀ i j, X.support.Adj i j → 1 ≤ X.weights i j)
    (Y : SimpleGraph κ) [DecidableRel Y.Adj] (e : κ ↪ ι) :
    X.Contains (unit Y) e ↔ ∀ i j, Y.Adj i j → X.support.Adj (e i) (e j) := by
  constructor
  · intro h i j hij
    have hle := h i j
    change (if Y.Adj i j then (1 : ℝ) else 0) ≤ X.weights (e i) (e j) at hle
    rw [ite_eq_left hij] at hle
    exact lt_of_lt_of_le zero_lt_one hle
  · intro h i j
    change (if Y.Adj i j then (1 : ℝ) else 0) ≤ X.weights (e i) (e j)
    split_ifs with hij
    · exact hweights _ _ (h i j hij)
    · exact X.nonneg _ _

/-- A weighted path on `Fin n`; `w i` is the edge from `i` to `i+1`. -/
def path (n : ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) : WeightedGraph (Fin n) where
  weights i j := if i.val + 1 = j.val then w i.val
    else if j.val + 1 = i.val then w j.val else 0
  symmetric := by
    apply Matrix.IsSymm.ext
    intro i j
    split_ifs <;> first | omega | rfl
  nonneg i j := by split_ifs <;> first | exact hw _ | exact le_rfl
  diag i := by simp

/-- Positive path weights have exactly the usual path support. -/
theorem support_path (n : ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hpos : ∀ i, i + 1 < n → 0 < w i) : (path n w hw).support = SimpleGraph.pathGraph n := by
  ext i j
  change (0 < if i.val + 1 = j.val then w i.val
    else if j.val + 1 = i.val then w j.val else 0) ↔ _
  rw [SimpleGraph.pathGraph_adj]
  split_ifs with hij hji
  · simp [hij, hpos i.val (hij ▸ j.isLt)]
  · simp [hji, hpos j.val (hji ▸ i.isLt)]
  · simp_all

end WeightedGraph

namespace SimpleGraph

/-- The centre and the zero-based positions on three arms. -/
abbrev ArmVertex (a : Fin 3 → ℕ) := Option ((r : Fin 3) × Fin (a r))

/-- A three-arm tree, with no edges except centre-to-first-position and consecutive arm edges. -/
def armTree (a : Fin 3 → ℕ) : SimpleGraph (ArmVertex a) where
  Adj
    | none, none => False
    | none, some j => j.2.val = 0
    | some i, none => i.2.val = 0
    | some i, some j => i.1 = j.1 ∧ (i.2.val + 1 = j.2.val ∨ j.2.val + 1 = i.2.val)
  symm := ⟨by rintro (_ | i) (_ | j) <;> simp_all [eq_comm, or_comm]⟩
  loopless := ⟨by rintro (_ | i) <;> simp⟩

instance instDecidableRelArmTree (a : Fin 3 → ℕ) : DecidableRel (armTree a).Adj := by
  rintro (_ | i) (_ | j) <;> dsimp [armTree] <;> infer_instance

/-- Each arm vertex reaches the centre by decreasing its position. -/
theorem armTree_connected (a : Fin 3 → ℕ) : (armTree a).Connected := by
  apply (connected_iff_exists_forall_reachable (armTree a)).mpr
  refine ⟨none, ?_⟩
  rintro (_ | ⟨r, ⟨t, ht⟩⟩)
  · exact .refl _
  · induction t with
    | zero => exact (show (armTree a).Adj none (some ⟨r, ⟨0, ht⟩⟩) from rfl).reachable
    | succ t ih =>
      have hprev := ih (by omega)
      apply hprev.trans
      apply Adj.reachable
      exact ⟨rfl, Or.inl rfl⟩

/-- The affine A graph at parameter `ℓ` is a cycle on `ℓ+1` vertices. -/
def smithA (ℓ : ℕ) : SimpleGraph (Fin (ℓ + 1)) := cycleGraph (ℓ + 1)

instance instDecidableRelSmithA (ℓ : ℕ) : DecidableRel (smithA ℓ).Adj := inferInstanceAs
  (DecidableRel (cycleGraph (ℓ + 1)).Adj)

/-- The affine E₆ graph is the unit three-arm tree with arm lengths 2, 2, 2. -/
def smithE₆ : SimpleGraph (ArmVertex ![2, 2, 2]) := armTree ![2, 2, 2]

/-- The affine E₇ graph is the unit three-arm tree with arm lengths 1, 3, 3. -/
def smithE₇ : SimpleGraph (ArmVertex ![1, 3, 3]) := armTree ![1, 3, 3]

/-- The affine E₈ graph is the unit three-arm tree with arm lengths 1, 2, 5. -/
def smithE₈ : SimpleGraph (ArmVertex ![1, 2, 5]) := armTree ![1, 2, 5]

instance instDecidableRelSmithE₆ : DecidableRel smithE₆.Adj :=
  inferInstanceAs (DecidableRel (armTree ![2, 2, 2]).Adj)
instance instDecidableRelSmithE₇ : DecidableRel smithE₇.Adj :=
  inferInstanceAs (DecidableRel (armTree ![1, 3, 3]).Adj)
instance instDecidableRelSmithE₈ : DecidableRel smithE₈.Adj :=
  inferInstanceAs (DecidableRel (armTree ![1, 2, 5]).Adj)

end SimpleGraph

namespace WeightedGraph

variable {ι : Type*}

/-- A support with a path or three-arm labelling is connected. -/
theorem connected_of_path_or_arm (X : WeightedGraph ι)
    (h : (∃ n : ℕ, Nonempty (SimpleGraph.pathGraph (n + 1) ≃g X.support)) ∨
      ∃ a : Fin 3 → ℕ, Nonempty (SimpleGraph.armTree a ≃g X.support)) :
    X.support.Connected := by
  rcases h with ⟨n, ⟨e⟩⟩ | ⟨a, ⟨e⟩⟩
  · exact e.connected_iff.mp (SimpleGraph.pathGraph_connected n)
  · exact e.connected_iff.mp (SimpleGraph.armTree_connected a)

end WeightedGraph
