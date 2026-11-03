/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ExceptionalTables
import LineGraphs.Computations.E8Model

/-!
# Tables and integer decoders for all seven models

The fixed exceptional tables import no real arithmetic in their sweep modules. The public
membership lemmas accept arbitrary integer vectors, so explicit Section 4 vectors do not
need to expose a structured root index. The E₈ decoder uses a balanced lookup tree; E₇ and
E₆ add their coordinate constraints. The seven-sign structured index is retained for counting,
while the vector-table interface also accommodates arbitrary coordinate permutations.
-/

open scoped RealInnerProductSpace
open Computations

namespace LineSystem

/-- Executable enumeration of the ordered distinct pairs for Aₙ. -/
def An.indices (n : ℕ) : List (An.Index n) :=
  (List.finRange (n + 1)).flatMap fun i ↦ (List.finRange (n + 1)).flatMap fun j ↦
    if h : i ≠ j then [⟨(i, j), h⟩] else []

theorem An.mem_indices {n : ℕ} (a : An.Index n) : a ∈ An.indices n := by
  rcases a with ⟨⟨i, j⟩, hij⟩
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, List.mem_flatMap.mpr ⟨j, List.mem_finRange j, ?_⟩⟩
  simp [hij]

/-- Executable enumeration of the signed increasing pairs for Dₙ. -/
def Dn.indices (n : ℕ) : List (Dn.Index n) :=
  (List.finRange n).flatMap fun i ↦ (List.finRange n).flatMap fun j ↦
    if h : i < j then [(⟨(i, j), h⟩, false, false), (⟨(i, j), h⟩, false, true),
      (⟨(i, j), h⟩, true, false), (⟨(i, j), h⟩, true, true)] else []

theorem Dn.mem_indices {n : ℕ} (a : Dn.Index n) : a ∈ Dn.indices n := by
  rcases a with ⟨⟨⟨i, j⟩, hij⟩, a, b⟩
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, List.mem_flatMap.mpr ⟨j, List.mem_finRange j, ?_⟩⟩
  simp only [dite_eq_left hij]
  cases a <;> cases b <;> simp

/-- The computable integer root table for this model. -/
def An.rootList (n : ℕ) : List IntVector := indexedRootTable (An.indices n) anRoot

/-- The computable integer root table for this model. -/
def Dn.rootList (n : ℕ) : List IntVector := indexedRootTable (Dn.indices n) dnRoot

/-- The computable integer root table for this model. -/
def E₈viaD₈.rootList : List IntVector := Computations.E₈Data.e₈Roots

/-- The computable integer root table for this model. -/
def E₈viaA₈.rootList : List IntVector := e₈ARoots

/-- The computable integer root table for this model. -/
def E₈viaSteiner.rootList : List IntVector := e₈SteinerRoots

/-- The computable integer root table for this model. -/
def E₇.rootList : List IntVector := E₈viaD₈.rootList.filter
  (fun w ↦ decide (w[6]?.getD 0 = w[7]?.getD 0))

/-- The computable integer root table for this model. -/
def E₆.rootList : List IntVector := E₈viaD₈.rootList.filter
  (fun w ↦ decide (w[6]?.getD 0 = w[7]?.getD 0 ∧ w[5]?.getD 0 = w[6]?.getD 0))

/-- The complete executable enumeration of the structured root indices. -/
abbrev E₈viaD₈.indices := Computations.E₈Data.e₈Indices
/-- The complete executable enumeration of the structured root indices. -/
abbrev E₈viaA₈.indices := Computations.e₈AIndices
/-- The complete executable enumeration of the structured root indices. -/
abbrev E₈viaSteiner.indices := Computations.e₈SteinerIndices

theorem E₈viaD₈.mem_indices (a : E₈viaD₈.Index) : a ∈ E₈viaD₈.indices :=
  Computations.E₈Data.mem_e₈Indices a

theorem E₈viaA₈.mem_indices (a : E₈viaA₈.Index) : a ∈ E₈viaA₈.indices := mem_e₈AIndices a

theorem E₈viaSteiner.mem_indices (a : E₈viaSteiner.Index) : a ∈ E₈viaSteiner.indices :=
  mem_e₈SteinerIndices a

theorem An.rootList_eq_map (n : ℕ) :
    An.rootList n = (An.indices n).map (fun a ↦ List.ofFn (An.root a)) := rfl

theorem Dn.rootList_eq_map (n : ℕ) :
    Dn.rootList n = (Dn.indices n).map (fun a ↦ List.ofFn (Dn.root a)) := rfl

theorem E₈viaA₈.rootList_eq_map :
    E₈viaA₈.rootList = E₈viaA₈.indices.map (fun a ↦ List.ofFn (E₈viaA₈.root a)) :=
  e₈ARoots_eq_map

theorem E₈viaSteiner.rootList_eq_map : E₈viaSteiner.rootList =
    E₈viaSteiner.indices.map (fun a ↦ List.ofFn (E₈viaSteiner.root a)) := e₈SteinerRoots_eq_map

theorem E₇.rootList_length : E₇.rootList.length = 126 := by decide +kernel

theorem E₆.rootList_length : E₆.rootList.length = 72 := by decide +kernel

theorem An.mem_rootList (n : ℕ) (w : IntVector) :
    w ∈ An.rootList n ↔ ∃ a : An.Index n, List.ofFn (An.root a) = w :=
  mem_indexedRootTable _ An.mem_indices _ _

theorem Dn.mem_rootList (n : ℕ) (w : IntVector) :
    w ∈ Dn.rootList n ↔ ∃ a : Dn.Index n, List.ofFn (Dn.root a) = w :=
  mem_indexedRootTable _ Dn.mem_indices _ _

theorem E₈viaD₈.mem_rootList (w : IntVector) :
    w ∈ E₈viaD₈.rootList ↔ ∃ a, List.ofFn (E₈viaD₈.root a) = w := by
  constructor
  · exact Computations.E₈Data.e₈Roots_sound
  · rintro ⟨a, rfl⟩
    exact Computations.E₈Data.ofFn_e₈Root_mem a

theorem E₈viaA₈.mem_rootList (w : IntVector) :
    w ∈ E₈viaA₈.rootList ↔ ∃ a, List.ofFn (E₈viaA₈.root a) = w := mem_e₈ARoots w

theorem E₈viaSteiner.mem_rootList (w : IntVector) :
    w ∈ E₈viaSteiner.rootList ↔ ∃ a, List.ofFn (E₈viaSteiner.root a) = w :=
  mem_e₈SteinerRoots w

theorem E₇.mem_rootList (w : IntVector) :
    w ∈ E₇.rootList ↔ ∃ a, List.ofFn (E₇.root a) = w := by
  simp only [E₇.rootList, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, he⟩
    obtain ⟨a, rfl⟩ := E₈viaD₈.mem_rootList w |>.mp hw
    exact ⟨⟨a, by simpa using he⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Computations.E₈Data.ofFn_e₈Root_mem a.val, by simpa using a.property⟩

theorem E₆.mem_rootList (w : IntVector) :
    w ∈ E₆.rootList ↔ ∃ a, List.ofFn (E₆.root a) = w := by
  simp only [E₆.rootList, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, he⟩
    obtain ⟨a, rfl⟩ := E₈viaD₈.mem_rootList w |>.mp hw
    exact ⟨⟨a, by simpa using he⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Computations.E₈Data.ofFn_e₈Root_mem a.val, by simpa using a.property⟩

/-- An executable root decoder for the corresponding integer model. -/
def isAnRoot {n : ℕ} (w : Fin (n + 1) → ℤ) : Bool := decodeRoot (An.rootList n) w

/-- An executable root decoder for the corresponding integer model. -/
def isDnRoot {n : ℕ} (w : Fin n → ℤ) : Bool := decodeRoot (Dn.rootList n) w

/-- An executable root decoder for the corresponding integer model. -/
def isE₈Root (w : Fin 8 → ℤ) : Bool := Computations.E₈Data.e₈Tree.contains (List.ofFn w)

/-- An executable root decoder for the corresponding integer model. -/
def isE₈viaA₈Root (w : Fin 9 → ℤ) : Bool := e₈ADecode (List.ofFn w)

/-- An executable root decoder for the corresponding integer model. -/
def isE₈viaSteinerRoot (w : Fin 8 → ℤ) : Bool := e₈SteinerDecode (List.ofFn w)

/-- An executable root decoder for the corresponding integer model. -/
def isE₇Root (w : Fin 8 → ℤ) : Bool := isE₈Root w && decide (w 6 = w 7)

/-- An executable root decoder for the corresponding integer model. -/
def isE₆Root (w : Fin 8 → ℤ) : Bool := isE₇Root w && decide (w 5 = w 6)

theorem integerVector_mem_An_iff {n : ℕ} (w : Fin (n + 1) → ℤ) :
    integerVector 1 w ∈ (An n).Φ ↔ isAnRoot w = true :=
  (An.integerModel n).mem_iff_table (An.mem_rootList n) w

theorem integerVector_mem_Dn_iff {n : ℕ} (w : Fin n → ℤ) :
    integerVector 1 w ∈ (Dn n).Φ ↔ isDnRoot w = true :=
  (Dn.integerModel n).mem_iff_table (Dn.mem_rootList n) w

theorem integerVector_mem_E₈_iff (w : Fin 8 → ℤ) :
    integerVector (1 / 2) w ∈ E₈.Φ ↔ isE₈Root w = true := by
  refine (E₈viaD₈.integerModel.mem_iff w).trans ?_
  change (∃ a : E₈Index, e₈Root a = w) ↔ _
  constructor
  · rintro ⟨a, rfl⟩
    exact List.all_eq_true.mp Computations.E₈Data.e₈_coverage_checked a
      (Computations.E₈Data.mem_e₈Indices a)
  · intro h
    obtain ⟨a, ha⟩ := Computations.E₈Data.e₈Roots_sound (VectorTree.contains_sound h)
    exact ⟨a, List.ofFn_inj.mp ha⟩

theorem integerVector_mem_E₈viaA₈_iff (w : Fin 9 → ℤ) :
    integerVector (1 / 3) w ∈ E₈viaA₈.Φ ↔ isE₈viaA₈Root w = true := by
  refine (E₈viaA₈.integerModel.mem_iff w).trans ?_
  change (∃ a : E₈AIndex, e₈ARoot a = w) ↔ _
  simp only [isE₈viaA₈Root, e₈ADecode_iff, mem_e₈ARoots, List.ofFn_inj]

theorem integerVector_mem_E₈viaSteiner_iff (w : Fin 8 → ℤ) :
    integerVector (Real.sqrt 2)⁻¹ w ∈ E₈viaSteiner.Φ ↔ isE₈viaSteinerRoot w = true := by
  refine (E₈viaSteiner.integerModel.mem_iff w).trans ?_
  change (∃ a : E₈SteinerIndex, e₈SteinerRoot a = w) ↔ _
  simp only [isE₈viaSteinerRoot, e₈SteinerDecode_iff, mem_e₈SteinerRoots, List.ofFn_inj]

theorem integerVector_mem_E₇_iff (w : Fin 8 → ℤ) :
    integerVector (1 / 2) w ∈ E₇.Φ ↔ isE₇Root w = true := by
  change (integerVector (1 / 2) w ∈ E₈.Φ ∧
    ⟪integerVector (1 / 2) w, e₇Normal⟫ = 0) ↔ _
  rw [e₇Normal, integerVector_mem_E₈_iff,
    integerVector_inner_sub_single_eq_zero w (by norm_num) 6 7]
  simp [isE₇Root]

theorem integerVector_mem_E₆_iff (w : Fin 8 → ℤ) :
    integerVector (1 / 2) w ∈ E₆.Φ ↔ isE₆Root w = true := by
  change (integerVector (1 / 2) w ∈ E₇.Φ ∧
    ⟪integerVector (1 / 2) w, e₆Normal⟫ = 0) ↔ _
  rw [e₆Normal, integerVector_mem_E₇_iff,
    integerVector_inner_sub_single_eq_zero w (by norm_num) 5 6]
  simp [isE₆Root]

end LineSystem
