/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C20

/-!
# C20 in the form of LN6: the pairs of `N_c`

LN6 of `cgss/prerequisites.md` takes model (ii) of E₈, with `E₇ = E₈ ∩ (e₇ - e₈)^⊥` and
`E₆ = E₇ ∩ (e₆ - e₇)^⊥` (1-based, as in `LineSystem.E₇`, `LineSystem.E₆`), and the root
`c = ½ ∑ᵢ eᵢ`, which lies in all three. The root used is `c` (not `e₇ - e₈`): it is the apex
`neighborApex` of the Sage pairs of `C20E6.lean`, `C20E7.lean` and `C20E8.lean` (table roots
63, 115 and 225, the vector `(1, …, 1)` in doubled coordinates), by `neighborApex_eq_c`. Then
`N_c` consists of the pairs `{eᵢ + eⱼ, c - eᵢ - eⱼ}`, where `{i, j}` runs over the edges of

* `K₈` for E₈ (28 pairs, 56 roots),
* `K₆` together with `{7, 8}` for E₇ (16 pairs, 32 roots),
* `K₅` for E₆ (10 pairs, 20 roots).

In `Fin 8` these are the pairs `i < j` with no condition, with `j < 6` or `(i, j) = (6, 7)`, and
with `j < 5`. The two roots of a pair are exchanged by `pairInv c`.

## Main statements

* `E₈.c`, `E₈.c_mem`, `E₇.c_mem`, `E₆.c_mem`, and `neighborApex_eq_c` for each model.
* `E₈.cPairs`, `E₇.cPairs`, `E₆.cPairs`: the edges, with a sign, enumerate `N_c`;
  `cPairs_false`, `cPairs_true` give the two roots; `pairInv_cPairs` exchanges them.
* `E₈.N_c`, `E₇.N_c`, `E₆.N_c`: `N_c` as an explicit set; `card_N_c`: 56, 32 and 20.
-/

open Computations
open scoped RealInnerProductSpace

namespace LineSystem

/-- LN6: the root `c = ½ ∑ᵢ eᵢ` of model (ii) of E₈; it also lies in E₇ and E₆. -/
noncomputable def E₈.c : EuclideanSpace ℝ (Fin 8) :=
  (1 / 2 : ℝ) • ∑ i, EuclideanSpace.single i 1

theorem E₈.c_eq_integerVector : E₈.c = integerVector (1 / 2) (fun _ => 1) := by
  ext k
  simp [E₈.c]

/-- The doubled coordinates of `eᵢ + eⱼ`. -/
theorem integerVector_half_pairVector (i j : Fin 8) (hij : i ≠ j) :
    integerVector (1 / 2) (pairVector i j 2 2) =
      EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j 1 := by
  ext k
  simp only [integerVector_apply, pairVector, Pi.add_apply, Pi.single_apply, PiLp.add_apply,
    PiLp.single_apply]
  split_ifs <;> simp_all

/-! ### E₈ -/

/-- LN6: `neighborApex` of C20 for E₈ is `c = ½ ∑ᵢ eᵢ`. -/
theorem E₈.neighborApex_eq_c : E₈.neighborApex = E₈.c := by
  change integerVector (1 / 2) (E₈.tableModel.v (225 : Fin 240)) = _
  rw [E₈.c_eq_integerVector]
  congr 1
  decide +kernel

/-- LN6: `c ∈ E₈`. -/
theorem E₈.c_mem : E₈.c ∈ E₈.Φ :=
  E₈.neighborApex_eq_c ▸ E₈.tableModel.root_mem (225 : Fin 240)

/-- The pairs `i < j` of `Fin 8` indexing N_c in E₈: the edges of K₈. -/
abbrev E₈.CEdge := {p : Fin 8 × Fin 8 // p.1 < p.2}

/-- The position in `C20.e8Pairs` of an edge, in lexicographic order. -/
def E₈.edgeLabel (p : E₈.CEdge) : Fin 28 :=
  ⟨[0, 0, 1, 2, 3, 4, 5, 6, 0, 0, 7, 8, 9, 10, 11, 12, 0, 0, 0, 13, 14, 15, 16, 17,
    0, 0, 0, 0, 18, 19, 20, 21, 0, 0, 0, 0, 0, 22, 23, 24, 0, 0, 0, 0, 0, 0, 25,
    26, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0][8 * p.1.1.val + p.1.2.val]?.getD 0 % 28,
    Nat.mod_lt _ (by decide)⟩

/-- The edge labels are a bijection. -/
noncomputable def E₈.edgeEquiv : E₈.CEdge ≃ Fin 28 :=
  Equiv.ofBijective E₈.edgeLabel (by decide +kernel)

theorem E₈.card_CEdge : Fintype.card E₈.CEdge = 28 := by
  rw [Fintype.card_congr E₈.edgeEquiv, Fintype.card_fin]

-- LN6 / computation C20
/-- LN6: the edges of K₈, with a sign, enumerate `N_c` in E₈; see `cPairs_false` and
`cPairs_true` for the two roots of each pair. -/
noncomputable def E₈.cPairs : E₈.CEdge × Bool ≃ E₈.N E₈.c :=
  ((E₈.edgeEquiv.prodCongr (Equiv.refl Bool)).trans E₈.neighborPairs).trans
    (Set.equivOfEq (by rw [E₈.neighborApex_eq_c]))

theorem E₈.coe_cPairs (p : E₈.CEdge) (s : Bool) :
    (E₈.cPairs (p, s) : EuclideanSpace ℝ (Fin 8)) = E₈.neighborPairs (E₈.edgeLabel p, s) :=
  rfl

-- LN6 / computation C20
/-- LN6: the first root of the pair at the edge `{i, j}` is `eᵢ + eⱼ`. -/
theorem E₈.cPairs_false (p : E₈.CEdge) :
    (E₈.cPairs (p, false) : EuclideanSpace ℝ (Fin 8)) =
      EuclideanSpace.single p.1.1 (1 : ℝ) + EuclideanSpace.single p.1.2 1 := by
  rw [E₈.coe_cPairs, ← integerVector_half_pairVector _ _ (p.2).ne]
  change integerVector (1 / 2) (E₈.tableModel.v (E₈.neighborPairLabel (E₈.edgeLabel p, false)))
    = _
  congr 1
  exact (by decide +kernel : ∀ p : E₈.CEdge,
    E₈.tableModel.v (E₈.neighborPairLabel (E₈.edgeLabel p, false)) =
      pairVector p.1.1 p.1.2 2 2) p

-- LN6 / computation C20
/-- LN6: the second root of the pair at the edge `{i, j}` is `c - eᵢ - eⱼ`. -/
theorem E₈.cPairs_true (p : E₈.CEdge) :
    (E₈.cPairs (p, true) : EuclideanSpace ℝ (Fin 8)) =
      E₈.c - EuclideanSpace.single p.1.1 (1 : ℝ) - EuclideanSpace.single p.1.2 1 := by
  have h := E₈.neighborPairs_add (E₈.edgeLabel p)
  rw [← E₈.coe_cPairs, ← E₈.coe_cPairs, E₈.cPairs_false, E₈.neighborApex_eq_c] at h
  generalize (E₈.cPairs (p, true) : EuclideanSpace ℝ (Fin 8)) = y at h ⊢
  rw [← h]
  abel

-- LN6 / computation C20
/-- LN6: the involution `x ↦ c - x` of `N_c` exchanges the two roots of each pair. -/
theorem E₈.pairInv_cPairs (p : E₈.CEdge) :
    E₈.pairInv E₈.c isStarClosed_E₈ E₈.c_mem (E₈.cPairs (p, false)) = E₈.cPairs (p, true) := by
  apply Subtype.ext
  change E₈.c - (E₈.cPairs (p, false) : EuclideanSpace ℝ (Fin 8)) = _
  rw [E₈.cPairs_false, E₈.cPairs_true]
  abel

-- LN6 / computation C20
/-- LN6: `N_c` in E₈ is `{eᵢ + eⱼ, c - eᵢ - eⱼ}` over the edges `{i, j}` of K₈. -/
theorem E₈.N_c : E₈.N E₈.c = {x | ∃ p : Fin 8 × Fin 8,
    (p.1 < p.2) ∧
      (x = EuclideanSpace.single p.1 1 + EuclideanSpace.single p.2 1 ∨
        x = E₈.c - EuclideanSpace.single p.1 1 - EuclideanSpace.single p.2 1)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨p, s⟩, hp⟩ := E₈.cPairs.surjective ⟨x, hx⟩
    have hx' : x = E₈.cPairs (p, s) := (congrArg Subtype.val hp).symm
    refine ⟨p.1, p.2, ?_⟩
    cases s
    · exact Or.inl (hx'.trans (E₈.cPairs_false p))
    · exact Or.inr (hx'.trans (E₈.cPairs_true p))
  · rintro ⟨p, hp, h | h⟩ <;> subst h
    · rw [← E₈.cPairs_false ⟨p, hp⟩]
      exact Subtype.mem _
    · rw [← E₈.cPairs_true ⟨p, hp⟩]
      exact Subtype.mem _

/-- C20 at `c`: `|N_c| = 56` in E₈, that is, 28 pairs. -/
theorem E₈.card_N_c : (E₈.N E₈.c).ncard = 56 := E₈.card_N E₈.c_mem

/-! ### E₇ -/

/-- LN6: `neighborApex` of C20 for E₇ is `c = ½ ∑ᵢ eᵢ`. -/
theorem E₇.neighborApex_eq_c : E₇.neighborApex = E₈.c := by
  change integerVector (1 / 2) (E₇.tableModel.v (115 : Fin 126)) = _
  rw [E₈.c_eq_integerVector]
  congr 1
  decide +kernel

/-- LN6: `c ∈ E₇`. -/
theorem E₇.c_mem : E₈.c ∈ E₇.Φ :=
  E₇.neighborApex_eq_c ▸ E₇.tableModel.root_mem (115 : Fin 126)

/-- The pairs `i < j` of `Fin 8` indexing N_c in E₇: the edges of K₆ and {7, 8}. -/
abbrev E₇.CEdge := {p : Fin 8 × Fin 8 // p.1 < p.2 ∧ (p.2.val < 6 ∨ (p.1.val = 6 ∧ p.2.val = 7))}

/-- The position in `C20.e7Pairs` of an edge, in lexicographic order. -/
def E₇.edgeLabel (p : E₇.CEdge) : Fin 16 :=
  ⟨[0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 0, 9, 10, 11, 0, 0, 0, 0,
    0, 0, 12, 13, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0][8 * p.1.1.val + p.1.2.val]?.getD 0 % 16,
    Nat.mod_lt _ (by decide)⟩

/-- The edge labels are a bijection. -/
noncomputable def E₇.edgeEquiv : E₇.CEdge ≃ Fin 16 :=
  Equiv.ofBijective E₇.edgeLabel (by decide +kernel)

theorem E₇.card_CEdge : Fintype.card E₇.CEdge = 16 := by
  rw [Fintype.card_congr E₇.edgeEquiv, Fintype.card_fin]

-- LN6 / computation C20
/-- LN6: the edges of K₆ and {7, 8}, with a sign, enumerate `N_c` in E₇; see `cPairs_false` and
`cPairs_true` for the two roots of each pair. -/
noncomputable def E₇.cPairs : E₇.CEdge × Bool ≃ E₇.N E₈.c :=
  ((E₇.edgeEquiv.prodCongr (Equiv.refl Bool)).trans E₇.neighborPairs).trans
    (Set.equivOfEq (by rw [E₇.neighborApex_eq_c]))

theorem E₇.coe_cPairs (p : E₇.CEdge) (s : Bool) :
    (E₇.cPairs (p, s) : EuclideanSpace ℝ (Fin 8)) = E₇.neighborPairs (E₇.edgeLabel p, s) :=
  rfl

-- LN6 / computation C20
/-- LN6: the first root of the pair at the edge `{i, j}` is `eᵢ + eⱼ`. -/
theorem E₇.cPairs_false (p : E₇.CEdge) :
    (E₇.cPairs (p, false) : EuclideanSpace ℝ (Fin 8)) =
      EuclideanSpace.single p.1.1 (1 : ℝ) + EuclideanSpace.single p.1.2 1 := by
  rw [E₇.coe_cPairs, ← integerVector_half_pairVector _ _ (p.2.1).ne]
  change integerVector (1 / 2) (E₇.tableModel.v (E₇.neighborPairLabel (E₇.edgeLabel p, false)))
    = _
  congr 1
  exact (by decide +kernel : ∀ p : E₇.CEdge,
    E₇.tableModel.v (E₇.neighborPairLabel (E₇.edgeLabel p, false)) =
      pairVector p.1.1 p.1.2 2 2) p

-- LN6 / computation C20
/-- LN6: the second root of the pair at the edge `{i, j}` is `c - eᵢ - eⱼ`. -/
theorem E₇.cPairs_true (p : E₇.CEdge) :
    (E₇.cPairs (p, true) : EuclideanSpace ℝ (Fin 8)) =
      E₈.c - EuclideanSpace.single p.1.1 (1 : ℝ) - EuclideanSpace.single p.1.2 1 := by
  have h := E₇.neighborPairs_add (E₇.edgeLabel p)
  rw [← E₇.coe_cPairs, ← E₇.coe_cPairs, E₇.cPairs_false, E₇.neighborApex_eq_c] at h
  generalize (E₇.cPairs (p, true) : EuclideanSpace ℝ (Fin 8)) = y at h ⊢
  rw [← h]
  abel

-- LN6 / computation C20
/-- LN6: the involution `x ↦ c - x` of `N_c` exchanges the two roots of each pair. -/
theorem E₇.pairInv_cPairs (p : E₇.CEdge) :
    E₇.pairInv E₈.c isStarClosed_E₇ E₇.c_mem (E₇.cPairs (p, false)) = E₇.cPairs (p, true) := by
  apply Subtype.ext
  change E₈.c - (E₇.cPairs (p, false) : EuclideanSpace ℝ (Fin 8)) = _
  rw [E₇.cPairs_false, E₇.cPairs_true]
  abel

-- LN6 / computation C20
/-- LN6: `N_c` in E₇ is `{eᵢ + eⱼ, c - eᵢ - eⱼ}` over the edges `{i, j}` of K₆ and {7, 8}. -/
theorem E₇.N_c : E₇.N E₈.c = {x | ∃ p : Fin 8 × Fin 8,
    (p.1 < p.2 ∧ (p.2.val < 6 ∨ (p.1.val = 6 ∧ p.2.val = 7))) ∧
      (x = EuclideanSpace.single p.1 1 + EuclideanSpace.single p.2 1 ∨
        x = E₈.c - EuclideanSpace.single p.1 1 - EuclideanSpace.single p.2 1)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨p, s⟩, hp⟩ := E₇.cPairs.surjective ⟨x, hx⟩
    have hx' : x = E₇.cPairs (p, s) := (congrArg Subtype.val hp).symm
    refine ⟨p.1, p.2, ?_⟩
    cases s
    · exact Or.inl (hx'.trans (E₇.cPairs_false p))
    · exact Or.inr (hx'.trans (E₇.cPairs_true p))
  · rintro ⟨p, hp, h | h⟩ <;> subst h
    · rw [← E₇.cPairs_false ⟨p, hp⟩]
      exact Subtype.mem _
    · rw [← E₇.cPairs_true ⟨p, hp⟩]
      exact Subtype.mem _

/-- C20 at `c`: `|N_c| = 32` in E₇, that is, 16 pairs. -/
theorem E₇.card_N_c : (E₇.N E₈.c).ncard = 32 := E₇.card_N E₇.c_mem

/-! ### E₆ -/

/-- LN6: `neighborApex` of C20 for E₆ is `c = ½ ∑ᵢ eᵢ`. -/
theorem E₆.neighborApex_eq_c : E₆.neighborApex = E₈.c := by
  change integerVector (1 / 2) (E₆.tableModel.v (63 : Fin 72)) = _
  rw [E₈.c_eq_integerVector]
  congr 1
  decide +kernel

/-- LN6: `c ∈ E₆`. -/
theorem E₆.c_mem : E₈.c ∈ E₆.Φ :=
  E₆.neighborApex_eq_c ▸ E₆.tableModel.root_mem (63 : Fin 72)

/-- The pairs `i < j` of `Fin 8` indexing N_c in E₆: the edges of K₅. -/
abbrev E₆.CEdge := {p : Fin 8 × Fin 8 // p.1 < p.2 ∧ p.2.val < 5}

/-- The position in `C20.e6Pairs` of an edge, in lexicographic order. -/
def E₆.edgeLabel (p : E₆.CEdge) : Fin 10 :=
  ⟨[0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 4, 5, 6, 0, 0, 0, 0, 0, 0, 7, 8, 0, 0, 0, 0, 0,
    0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0][8 * p.1.1.val + p.1.2.val]?.getD 0 % 10,
    Nat.mod_lt _ (by decide)⟩

/-- The edge labels are a bijection. -/
noncomputable def E₆.edgeEquiv : E₆.CEdge ≃ Fin 10 :=
  Equiv.ofBijective E₆.edgeLabel (by decide +kernel)

theorem E₆.card_CEdge : Fintype.card E₆.CEdge = 10 := by
  rw [Fintype.card_congr E₆.edgeEquiv, Fintype.card_fin]

-- LN6 / computation C20
/-- LN6: the edges of K₅, with a sign, enumerate `N_c` in E₆; see `cPairs_false` and
`cPairs_true` for the two roots of each pair. -/
noncomputable def E₆.cPairs : E₆.CEdge × Bool ≃ E₆.N E₈.c :=
  ((E₆.edgeEquiv.prodCongr (Equiv.refl Bool)).trans E₆.neighborPairs).trans
    (Set.equivOfEq (by rw [E₆.neighborApex_eq_c]))

theorem E₆.coe_cPairs (p : E₆.CEdge) (s : Bool) :
    (E₆.cPairs (p, s) : EuclideanSpace ℝ (Fin 8)) = E₆.neighborPairs (E₆.edgeLabel p, s) :=
  rfl

-- LN6 / computation C20
/-- LN6: the first root of the pair at the edge `{i, j}` is `eᵢ + eⱼ`. -/
theorem E₆.cPairs_false (p : E₆.CEdge) :
    (E₆.cPairs (p, false) : EuclideanSpace ℝ (Fin 8)) =
      EuclideanSpace.single p.1.1 (1 : ℝ) + EuclideanSpace.single p.1.2 1 := by
  rw [E₆.coe_cPairs, ← integerVector_half_pairVector _ _ (p.2.1).ne]
  change integerVector (1 / 2) (E₆.tableModel.v (E₆.neighborPairLabel (E₆.edgeLabel p, false)))
    = _
  congr 1
  exact (by decide +kernel : ∀ p : E₆.CEdge,
    E₆.tableModel.v (E₆.neighborPairLabel (E₆.edgeLabel p, false)) =
      pairVector p.1.1 p.1.2 2 2) p

-- LN6 / computation C20
/-- LN6: the second root of the pair at the edge `{i, j}` is `c - eᵢ - eⱼ`. -/
theorem E₆.cPairs_true (p : E₆.CEdge) :
    (E₆.cPairs (p, true) : EuclideanSpace ℝ (Fin 8)) =
      E₈.c - EuclideanSpace.single p.1.1 (1 : ℝ) - EuclideanSpace.single p.1.2 1 := by
  have h := E₆.neighborPairs_add (E₆.edgeLabel p)
  rw [← E₆.coe_cPairs, ← E₆.coe_cPairs, E₆.cPairs_false, E₆.neighborApex_eq_c] at h
  generalize (E₆.cPairs (p, true) : EuclideanSpace ℝ (Fin 8)) = y at h ⊢
  rw [← h]
  abel

-- LN6 / computation C20
/-- LN6: the involution `x ↦ c - x` of `N_c` exchanges the two roots of each pair. -/
theorem E₆.pairInv_cPairs (p : E₆.CEdge) :
    E₆.pairInv E₈.c isStarClosed_E₆ E₆.c_mem (E₆.cPairs (p, false)) = E₆.cPairs (p, true) := by
  apply Subtype.ext
  change E₈.c - (E₆.cPairs (p, false) : EuclideanSpace ℝ (Fin 8)) = _
  rw [E₆.cPairs_false, E₆.cPairs_true]
  abel

-- LN6 / computation C20
/-- LN6: `N_c` in E₆ is `{eᵢ + eⱼ, c - eᵢ - eⱼ}` over the edges `{i, j}` of K₅. -/
theorem E₆.N_c : E₆.N E₈.c = {x | ∃ p : Fin 8 × Fin 8,
    (p.1 < p.2 ∧ p.2.val < 5) ∧
      (x = EuclideanSpace.single p.1 1 + EuclideanSpace.single p.2 1 ∨
        x = E₈.c - EuclideanSpace.single p.1 1 - EuclideanSpace.single p.2 1)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨p, s⟩, hp⟩ := E₆.cPairs.surjective ⟨x, hx⟩
    have hx' : x = E₆.cPairs (p, s) := (congrArg Subtype.val hp).symm
    refine ⟨p.1, p.2, ?_⟩
    cases s
    · exact Or.inl (hx'.trans (E₆.cPairs_false p))
    · exact Or.inr (hx'.trans (E₆.cPairs_true p))
  · rintro ⟨p, hp, h | h⟩ <;> subst h
    · rw [← E₆.cPairs_false ⟨p, hp⟩]
      exact Subtype.mem _
    · rw [← E₆.cPairs_true ⟨p, hp⟩]
      exact Subtype.mem _

/-- C20 at `c`: `|N_c| = 20` in E₆, that is, 10 pairs. -/
theorem E₆.card_N_c : (E₆.N E₈.c).ncard = 20 := E₆.card_N E₆.c_mem

end LineSystem
