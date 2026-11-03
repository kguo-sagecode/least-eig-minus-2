/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.StarCertificates
import LineGraphs.Computations.NeighborData

/-!
# Root neighborhoods and their pairs

The notation `S.N r` and `S.pairInv r` follows the paper's notation table.
-/

open scoped RealInnerProductSpace
open Computations

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The roots with inner product one against the specified root. -/
def N (S : LineSystem V) (r : V) : Set V := {x ∈ S.Φ | ⟪x, r⟫ = 1}

theorem finite_N (S : LineSystem V) (r : V) : (S.N r).Finite :=
  S.finite.subset (fun _ h => h.1)

private theorem sub_mem_N (S : LineSystem V) (r : V) (hS : S.IsStarClosed)
    (hr : r ∈ S.Φ) {x : V} (hx : x ∈ S.N r) : r - x ∈ S.N r := by
  refine ⟨?_, ?_⟩
  · simpa only [sub_eq_add_neg] using hS r hr (-x) (S.neg_mem x hx.1)
      (by rw [inner_neg_right, real_inner_comm]; simp [hx.2])
  · rw [inner_sub_left, S.inner_self r hr, hx.2]
    norm_num

/-- The involution pairing `x` with `r-x` in `Nᵣ`. -/
def pairInv (S : LineSystem V) (r : V) (hS : S.IsStarClosed) (hr : r ∈ S.Φ) :
    S.N r ≃ S.N r where
  toFun x := ⟨r - x, sub_mem_N S r hS hr x.property⟩
  invFun x := ⟨r - x, sub_mem_N S r hS hr x.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem pairInv_add (S : LineSystem V) (r : V) (hS : S.IsStarClosed) (hr : r ∈ S.Φ)
    (x : S.N r) : (x : V) + S.pairInv r hS hr x = r := by
  change (x : V) + (r - x) = r
  abel

theorem pairInv_ne (S : LineSystem V) (r : V) (hS : S.IsStarClosed) (hr : r ∈ S.Φ)
    (x : S.N r) : S.pairInv r hS hr x ≠ x := by
  intro he
  have hv : r - (x : V) = x := congrArg Subtype.val he
  have hd := congrArg (fun y => ⟪(x : V), y⟫) hv
  rw [inner_sub_right, x.property.2, S.inner_self x x.property.1] at hd
  norm_num at hd

namespace IntegerModel

variable {d : ℕ} {S : LineSystem (EuclideanSpace ℝ (Fin d))} (M : IntegerModel S)

/-- Integer indices for the actual neighborhood, with no repeated real roots. -/
noncomputable def neighborEquiv (a : M.ι) :
    {i : M.ι // integerInner (M.v i) (M.v a) = M.q} ≃
      S.N (integerVector M.c (M.v a)) :=
  M.subsetEquiv _ (fun _ h => h.1) Subtype.val Subtype.val_injective (by
    intro i
    change (_ ∧ _) ↔ _
    rw [and_iff_right (M.root_mem i), M.inner_eq_one_iff]
    exact ⟨fun h => ⟨⟨i, h⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.property⟩)

/-- Transfer a list count to the cardinality of a neighborhood of real roots. -/
theorem card_N_eq_filter {n : ℕ} (e : Fin n ≃ M.ι) (table : List IntVector)
    (ht : table = List.ofFn (fun i => List.ofFn (M.v (e i)))) (a : M.ι) :
    (S.N (integerVector M.c (M.v a))).ncard =
      (table.filter (fun w => dot w (List.ofFn (M.v a)) == M.q)).length := by
  classical
  let f := (e.subtypeEquiv (fun _ => Iff.rfl)).trans (M.neighborEquiv a)
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr f, Nat.card_eq_fintype_card,
    card_subtype_fin_eq, ht,
    List.ofFn_eq_map (f := fun i : Fin n => List.ofFn (M.v (e i))),
    List.filter_map, List.length_map]
  congr 2
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [dot_ofFn, integerInner]

/-- A complete successful sweep counts the neighborhood of every real root. -/
theorem card_N_of_check {n k : ℕ} (e : Fin n ≃ M.ι) (table : List IntVector)
    (ht : table = List.ofFn (fun i => List.ofFn (M.v (e i))))
    (checked : table.all (checkNeighborCount M.q k table) = true)
    {r : EuclideanSpace ℝ (Fin d)} (hr : r ∈ S.Φ) : (S.N r).ncard = k := by
  rw [M.Φ_eq] at hr
  obtain ⟨a, rfl⟩ := hr
  change (S.N (integerVector M.c (M.v a))).ncard = k
  rw [M.card_N_eq_filter e table ht a]
  have hm : List.ofFn (M.v a) ∈ table := by
    rw [ht]
    exact List.mem_ofFn.mpr ⟨e.symm a, by simp⟩
  simpa only [checkNeighborCount, beq_iff_eq] using List.all_eq_true.mp checked _ hm

end IntegerModel
end LineSystem
