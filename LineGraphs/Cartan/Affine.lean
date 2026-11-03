/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Attachments
import LineGraphs.Cartan.PathMatrix
import LineGraphs.Cartan.Cycle

/-!
# Affine obstructions

The seven families in `def:affine` of the Remark 3.11 blueprint, with specified
reindexings. The shortest D graph is a four-leaf star; both edges of `endPath 3`
have weight √2; the weighted edge of `fork 1` meets the branch vertex.
-/

namespace WeightedGraph

/-- The unit affine D graph: a path with two leaves attached at each endpoint. -/
def affineD (ℓ : ℕ) : WeightedGraph (Fin (ℓ - 4 + 1) ⊕ Fin 4) :=
  (path (ℓ - 4 + 1) (fun _ => 1) (by intro _; norm_num)).attachLeaves
    (fun j => if j.val < 2 then 0 else Fin.last (ℓ - 4))
    (fun _ => 1) (by intro _; norm_num)

/-- A path with first and last weights √2 and all other weights 1. -/
noncomputable def endPath (m : ℕ) : WeightedGraph (Fin m) :=
  path m (fun i => if i = 0 ∨ i + 2 = m then Real.sqrt 2 else 1)
    (by intro i; split_ifs <;> positivity)

/-- A path of `k` edges, its last edge of weight √2, with two unit leaves at its start. -/
noncomputable def fork (k : ℕ) : WeightedGraph (Fin (k + 1) ⊕ Fin 2) :=
  (path (k + 1) (fun i => if i + 1 = k then Real.sqrt 2 else 1)
    (by intro i; split_ifs <;> positivity)).attachLeaves
      (fun _ => 0) (fun _ => 1) (by intro _; norm_num)

/-- The five-vertex path with weights 1, 1, √2, 1. -/
noncomputable def middlePath : WeightedGraph (Fin 5) :=
  path 5 (fun i => if i = 2 then Real.sqrt 2 else 1)
    (by intro i; split_ifs <;> positivity)

/-- The three-vertex path with weights √3, 1. -/
noncomputable def triplePath : WeightedGraph (Fin 3) :=
  path 3 (fun i => if i = 0 then Real.sqrt 3 else 1)
    (by intro i; split_ifs <;> positivity)

end WeightedGraph

namespace SimpleGraph

/-- The affine D support; for `ℓ ≥ 4` it has `ℓ+1` vertices. For `ℓ ≤ 4` it is `K₁,₄`,
since natural-number subtraction truncates at zero. -/
def smithD (ℓ : ℕ) : SimpleGraph (Fin (ℓ - 4 + 1) ⊕ Fin 4) :=
  (WeightedGraph.affineD ℓ).support

end SimpleGraph

namespace WeightedGraph

variable {ι : Type*}

/-- The seven affine-obstruction families, up to a specified equivalence of vertex types. -/
inductive IsAffineObstruction (X : WeightedGraph ι) : Prop
  | cycle (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (e : Fin (ℓ + 1) ≃ ι)
      (h : X = (unit (SimpleGraph.smithA ℓ)).reindex e) : IsAffineObstruction X
  | d (ℓ : ℕ) (hℓ : 4 ≤ ℓ) (e : (Fin (ℓ - 4 + 1) ⊕ Fin 4) ≃ ι)
      (h : X = (affineD ℓ).reindex e) : IsAffineObstruction X
  | e₆ (e : SimpleGraph.ArmVertex ![2, 2, 2] ≃ ι)
      (h : X = (unit SimpleGraph.smithE₆).reindex e) : IsAffineObstruction X
  | e₇ (e : SimpleGraph.ArmVertex ![1, 3, 3] ≃ ι)
      (h : X = (unit SimpleGraph.smithE₇).reindex e) : IsAffineObstruction X
  | e₈ (e : SimpleGraph.ArmVertex ![1, 2, 5] ≃ ι)
      (h : X = (unit SimpleGraph.smithE₈).reindex e) : IsAffineObstruction X
  | ends (m : ℕ) (hm : 3 ≤ m) (e : Fin m ≃ ι)
      (h : X = (endPath m).reindex e) : IsAffineObstruction X
  | fork (k : ℕ) (hk : 1 ≤ k) (e : (Fin (k + 1) ⊕ Fin 2) ≃ ι)
      (h : X = (WeightedGraph.fork k).reindex e) : IsAffineObstruction X
  | middle (e : Fin 5 ≃ ι) (h : X = middlePath.reindex e) : IsAffineObstruction X
  | triple (e : Fin 3 ≃ ι) (h : X = triplePath.reindex e) : IsAffineObstruction X

/-- Reindexing transports connectedness of weighted support. -/
theorem connected_reindex (X : WeightedGraph ι) {κ : Type*} (e : ι ≃ κ)
    (hX : X.support.Connected) : (X.reindex e).support.Connected := by
  let f : X.support ≃g (X.reindex e).support :=
    { e with map_rel_iff' := by intro i j; simp [support, reindex, Matrix.reindex_apply] }
  exact f.connected_iff.mp hX

/-- Every affine D support is connected, including the four-leaf star. -/
theorem affineD_connected (ℓ : ℕ) : (affineD ℓ).support.Connected := by
  apply attachLeaves_connected
  · rw [support_path _ _ _ (by intro _ _; norm_num)]
    exact SimpleGraph.pathGraph_connected _
  · intro _; norm_num

/-- A nonempty endpoint-weighted affine path is connected. -/
theorem endPath_connected (m : ℕ) (hm : 0 < m) : (endPath m).support.Connected := by
  rw [endPath, support_path _ _ _ (by intro i _; split_ifs <;> positivity)]
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact ⟨SimpleGraph.pathGraph_preconnected _⟩

/-- Every weighted-fork support is connected. -/
theorem fork_connected (k : ℕ) : (fork k).support.Connected := by
  apply attachLeaves_connected
  · rw [support_path _ _ _ (by intro i _; split_ifs <;> positivity)]
    exact SimpleGraph.pathGraph_connected _
  · intro _; norm_num

/-- Every listed affine obstruction has connected support. -/
theorem IsAffineObstruction.connected {X : WeightedGraph ι} (hX : X.IsAffineObstruction) :
    X.support.Connected := by
  cases hX with
  | cycle ℓ _ e h =>
    subst X
    apply connected_reindex
    rw [support_unit]
    exact SimpleGraph.smithA_connected ℓ
  | d ℓ _ e h => subst X; exact connected_reindex _ e (affineD_connected ℓ)
  | e₆ e h =>
    subst X
    apply connected_reindex
    rw [support_unit]
    exact SimpleGraph.armTree_connected _
  | e₇ e h =>
    subst X
    apply connected_reindex
    rw [support_unit]
    exact SimpleGraph.armTree_connected _
  | e₈ e h =>
    subst X
    apply connected_reindex
    rw [support_unit]
    exact SimpleGraph.armTree_connected _
  | ends m hm e h => subst X; exact connected_reindex _ e (endPath_connected m (by omega))
  | fork k _ e h => subst X; exact connected_reindex _ e (fork_connected k)
  | middle e h =>
    subst X
    apply connected_reindex
    rw [middlePath, support_path _ _ _ (by intro i _; split_ifs <;> positivity)]
    exact SimpleGraph.pathGraph_connected _
  | triple e h =>
    subst X
    apply connected_reindex
    rw [triplePath, support_path _ _ _ (by intro i _; split_ifs <;> positivity)]
    exact SimpleGraph.pathGraph_connected _

end WeightedGraph
