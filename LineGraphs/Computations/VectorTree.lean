/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ListData

/-!
# VectorTree

A compact membership certificate. Tree ordering and key injectivity are unnecessary for
soundness: a successful lookup always compares the complete vector at a stored node. -/

namespace Computations

/-- A binary search tree whose successful lookups verify complete integer vectors. -/
inductive VectorTree where
  | nil
  | node (key : ℤ) (value : IntVector) (left right : VectorTree)
  deriving Repr

/-- Read every stored vector in left-to-right order. -/
def VectorTree.vectors : VectorTree → List IntVector
  | .nil => []
  | .node _ v l r => l.vectors ++ v :: r.vectors

/-- A supplied search key chooses a branch; equality of full vectors certifies membership. -/
def VectorTree.lookup (key : ℤ) (v : IntVector) : VectorTree → Bool
  | .nil => false
  | .node k w l r =>
    if key < k then l.lookup key v else if k < key then r.lookup key v else v == w

theorem VectorTree.lookup_sound {t : VectorTree} {key : ℤ} {v : IntVector}
    (h : t.lookup key v = true) : v ∈ t.vectors := by
  induction t with
  | nil => simp [lookup] at h
  | node k w l r hl hr =>
    simp only [lookup] at h
    split_ifs at h with hk hk'
    · exact List.mem_append_left _ (hl h)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (hr h))
    · have hv : v = w := by simpa using h
      subst w
      simp [vectors]

/-- Base-five code for the E₈ demo. Soundness does not assume a coordinate bound. -/
def vectorKey (v : IntVector) : ℤ := v.foldl (fun k x => 5 * k + (x + 2)) 0

/-- Search for a vector using its base-five key. -/
def VectorTree.contains (t : VectorTree) (v : IntVector) : Bool := t.lookup (vectorKey v) v

theorem VectorTree.contains_sound {t : VectorTree} {v : IntVector}
    (h : t.contains v = true) : v ∈ t.vectors := t.lookup_sound h

end Computations
