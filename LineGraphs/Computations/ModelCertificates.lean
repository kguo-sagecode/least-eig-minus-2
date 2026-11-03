/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ModelTables
import LineGraphs.Computations.RootMapData
import LineGraphs.LineSystem.Hyp24
import Mathlib.Data.List.NodupEquivFin

/-!
# Finite presentations for model certificates

Materialized tables are related to the original root sets before any finite check is used.
-/

open Computations

namespace LineSystem.IntegerModel

variable {d : ℕ} {S : LineSystem (EuclideanSpace ℝ (Fin d))}

/-- Reconstruct a row from its coordinate lookups. -/
theorem ofFn_entry {table : List IntVector} {n : ℕ} (hlen : table.length = n)
    (hd : ∀ w ∈ table, w.length = d) (i : Fin n) :
    List.ofFn (fun j : Fin d => entry table i j) = table[i.val]'(by omega) := by
  have hi : i.val < table.length := by omega
  have hw := hd _ (List.getElem_mem hi)
  apply List.ext_getElem
  · simpa using hw.symm
  · intro j hj hk
    simp [entry, hi, hw]

/-- Use positions in a complete, duplicate-free root table as the integer indices. -/
@[instance_reducible] noncomputable def ofTable (M : IntegerModel S)
    (table : List IntVector) (n : ℕ)
    (hlen : table.length = n) (hn : table.Nodup)
    (ht : ∀ w, w ∈ table ↔ ∃ a, List.ofFn (M.v a) = w) : IntegerModel S where
  ι := Fin n
  fintype := inferInstance
  v i j := entry table i j
  q := M.q
  c := M.c
  hc := M.hc
  inj := by
    have hd : ∀ w ∈ table, w.length = d := by
      intro w hw
      obtain ⟨a, rfl⟩ := (ht w).mp hw
      simp
    intro i j hij
    have he := congrArg List.ofFn hij
    rw [ofFn_entry hlen hd, ofFn_entry hlen hd] at he
    have := hn.injective_get (show table.get ⟨i.val, by omega⟩ =
      table.get ⟨j.val, by omega⟩ from he)
    exact Fin.ext (congrArg (fun k : Fin table.length => k.val) this)
  Φ_eq := by
    have hd : ∀ w ∈ table, w.length = d := by
      intro w hw
      obtain ⟨a, rfl⟩ := (ht w).mp hw
      simp
    rw [M.Φ_eq]
    apply Set.ext
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ((ht _).mpr ⟨a, rfl⟩)
      refine ⟨⟨i, by omega⟩, ?_⟩
      have hv : (fun j : Fin d => entry table i j) = M.v a := by
        apply List.ofFn_inj.mp
        exact (ofFn_entry hlen hd ⟨i, by omega⟩).trans he
      simp only [Function.comp_apply, hv]
    · rintro ⟨i, rfl⟩
      obtain ⟨a, ha⟩ := (ht _).mp (List.getElem_mem (show i.val < table.length by omega))
      refine ⟨a, ?_⟩
      have hv : M.v a = (fun j : Fin d => entry table i j) := by
        apply List.ofFn_inj.mp
        exact ha.trans (ofFn_entry hlen hd i).symm
      simp only [Function.comp_apply, hv]

end LineSystem.IntegerModel

namespace Computations

/-- Soundness of the scaled Gram comparison. -/
theorem checkScaledGram_sound {ds dt n : ℕ} {qs qt : ℤ} {s t : List IntVector}
    (hs : s.length = n) (ht : t.length = n)
    (hds : ∀ w ∈ s, w.length = ds) (hdt : ∀ w ∈ t, w.length = dt)
    (h : (List.range n).all (checkScaledGramRow qs qt s t) = true) (i j : Fin n) :
    qt * (fun k : Fin ds => entry s i k) ⬝ᵥ (fun k => entry s j k) =
      qs * (fun k : Fin dt => entry t i k) ⬝ᵥ (fun k => entry t j k) := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have hij := List.all_eq_true.mp hi j.val (List.mem_range.mpr (by omega))
  have es (a : Fin n) : s[a.val]?.getD [] = List.ofFn (fun k : Fin ds => entry s a k) := by
    rw [LineSystem.IntegerModel.ofFn_entry hs hds a]
    simp [show a.val < s.length by omega]
  have et (a : Fin n) : t[a.val]?.getD [] = List.ofFn (fun k : Fin dt => entry t a k) := by
    rw [LineSystem.IntegerModel.ofFn_entry ht hdt a]
    simp [show a.val < t.length by omega]
  simpa only [beq_iff_eq, es i, es j, et i, et j, dot_ofFn] using hij

/-- Equal finite sets give the same root membership specification. -/
theorem mem_iff_of_toFinset_eq {s t : List IntVector} (h : s.toFinset = t.toFinset)
    (w : IntVector) : w ∈ s ↔ w ∈ t := by
  rw [← List.mem_toFinset, h, List.mem_toFinset]

end Computations
