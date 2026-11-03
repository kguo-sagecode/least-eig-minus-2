/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.LabelledGraphs

/-!
# Cycle obstructions

A cycle walk gives an injective support-edge map, and unit cycles have maximum
Rayleigh value 2, as required in the Remark 3.11 obstruction argument.
-/

namespace SimpleGraph

/-- The cycle edges in zero-based natural coordinates, including the closing edge. -/
theorem cycleGraph_adj_iff_consecutive {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    (cycleGraph n).Adj i j ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (i.val + 1 = n ∧ j.val = 0) ∨ (j.val + 1 = n ∧ i.val = 0) := by
  have hsub (u v : Fin n) : (u - v).val =
      if v.val ≤ u.val then u.val - v.val else n - v.val + u.val := by
    split_ifs with h
    · exact Fin.sub_val_of_le h
    · rw [Fin.val_sub, Nat.mod_eq_of_lt (by omega)]
  rw [cycleGraph_adj', hsub i j, hsub j i]
  split_ifs <;> omega

/-- A cycle walk has length at least three and supplies an injection of its cycle graph
into the ambient graph (`lem:rem-cycle-embedding` of Remark 3.11). -/
theorem Walk.IsCycle.exists_cycle_embedding {V : Type*} {X : SimpleGraph V}
    {u : V} {p : X.Walk u u} (hp : p.IsCycle) :
    3 ≤ p.length ∧ ∃ e : Fin p.length ↪ V,
      ∀ i j, (cycleGraph p.length).Adj i j → X.Adj (e i) (e j) := by
  refine ⟨hp.three_le_length, ⟨fun i => p.getVert i.val, ?_⟩, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) hij
  · intro i j hij
    change X.Adj (p.getVert i.val) (p.getVert j.val)
    rcases (cycleGraph_adj_iff_consecutive hp.three_le_length i j).mp hij with
      h | h | ⟨hi, hj⟩ | ⟨hj, hi⟩
    · simpa only [h] using p.adj_getVert_succ i.isLt
    · simpa only [h] using (p.adj_getVert_succ j.isLt).symm
    · have h := p.adj_getVert_succ i.isLt
      simpa only [hi, hj, p.getVert_length, p.getVert_zero] using h
    · have h := (p.adj_getVert_succ j.isLt).symm
      simpa only [hi, hj, p.getVert_length, p.getVert_zero] using h

/-- Every affine A support is connected. -/
theorem smithA_connected (ℓ : ℕ) : (smithA ℓ).Connected := cycleGraph_connected

open Matrix in
/-- The all-ones vector is a positive 2-eigenvector on each affine A graph. -/
theorem smithA_mulVec_one (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (WeightedGraph.unit (smithA ℓ)).weights *ᵥ (1 : Fin (ℓ + 1) → ℝ) =
      (2 : ℝ) • (1 : Fin (ℓ + 1) → ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 2 := ⟨ℓ - 2, by omega⟩
  have hregular : (smithA (k + 2)).IsRegularOfDegree 2 := fun _ => cycleGraph_degree_three_le
  ext i
  change ((smithA (k + 2)).adjMatrix ℝ *ᵥ Function.const _ 1) i = _
  rw [adjMatrix_mulVec_const_apply_of_regular hregular]
  simp

end SimpleGraph
