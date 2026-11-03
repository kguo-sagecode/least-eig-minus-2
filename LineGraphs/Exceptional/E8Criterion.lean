/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C5Inclusions
import LineGraphs.Exceptional.RootLattice
import LineGraphs.Representation.Theorem44

/-! # The rank criterion for representation in E₈

Assertion (3) of Proposition `prop:types` (Proposition 2.6) of [Exc].
-/

open Matrix Module Submodule
open scoped RealInnerProductSpace

namespace LineSystem

-- Proposition 2.6 [Exc]
/-- The inclusions used in `prop:types` (Proposition 2.6(3)) of [Exc]: restrict the
existing `A₈` coordinate construction to obtain every `Aₙ`, `n ≤ 8`. -/
noncomputable def An.inclusionE₈OfLE {n : ℕ} (hn : n ≤ 8) :
    IsometricInclusion (An n) E₈ := by
  let h : n + 1 ≤ 9 := by omega
  let e := Fin.castLE h
  refine IsometricInclusion.ofRows (fun i => a₈Rows (e i))
    (fun i => if e i = 0 then -2 else 2) ?_ ?_
  · intro i j
    simpa only [e, (Fin.castLE_injective h).eq_iff] using
      Computations.C5.a₈_rows_gram (e i) (e j)
  · intro i j hij
    exact (integerVector_mem_E₈_iff _).mpr
      (Computations.C5.a₈_rows_mem (e i) (e j) (fun he => hij (Fin.castLE_injective h he)))

-- Proposition 2.6 [Exc]
/-- Coordinate padding gives the inclusions `Dₙ ⊆ Dₘ` used in `prop:types`
(Proposition 2.6(3)) of [Exc]. The construction works in every dimension. -/
noncomputable def Dn.inclusionOfLE {n m : ℕ} (hn : n ≤ m) :
    IsometricInclusion (Dn n) (Dn m) := by
  let e := Fin.castLE hn
  let A : Fin n → Fin m → ℤ := fun i => Pi.single (e i) 1
  refine IsometricInclusion.ofLinearMap (intLin 1 A) ?_ ?_
  · intro x _ y _
    have hG (i j : Fin n) : integerInner (A i) (A j) = if i = j then 1 else 0 := by
      simp [A, integerInner, Pi.single_apply, e,
        (Fin.castLE_injective hn).eq_iff, eq_comm]
    rw [inner_intLin]
    simp only [hG]
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  · rintro _ ⟨p, rfl⟩
    let q : DnIndex m := ⟨⟨(e p.1.val.1, e p.1.val.2), p.1.property⟩, p.2⟩
    refine ⟨q, ?_⟩
    rw [intLin_integerVector, one_mul]
    change integerVector 1 (dnRoot q) = integerVector 1 _
    apply congrArg (integerVector 1)
    funext k
    change dnRoot q k =
      (Pi.single p.1.val.1 (rootSign p.2.1) + Pi.single p.1.val.2 (rootSign p.2.2)) ⬝ᵥ
        (fun i => A i k)
    rw [add_dotProduct, single_dotProduct, single_dotProduct]
    simp [q, dnRoot, pairVector, A, Pi.single_apply]

-- Proposition 2.6 [Exc]
/-- The `Dₙ` inclusions in `prop:types` (Proposition 2.6(3)) of [Exc]. -/
noncomputable def Dn.inclusionE₈OfLE {n : ℕ} (hn : n ≤ 8) :
    IsometricInclusion (Dn n) E₈ :=
  (Dn.inclusionOfLE hn).trans Dn.inclusionE₈

-- Proposition 2.6 [Exc]
/-- The `E₆` inclusion in `prop:types` (Proposition 2.6(3)) of [Exc]. -/
noncomputable def E₆.inclusionE₈ : IsometricInclusion E₆ E₈ :=
  IsometricInclusion.ofSubset (E₆_Φ_subset_E₇.trans E₇_Φ_subset_E₈)

-- Proposition 2.6 [Exc]
/-- The `E₇` inclusion in `prop:types` (Proposition 2.6(3)) of [Exc]. -/
noncomputable def E₇.inclusionE₈ : IsometricInclusion E₇ E₈ :=
  IsometricInclusion.ofSubset E₇_Φ_subset_E₈

-- Proposition 2.6 [Exc]
/-- Every root type of rank at most eight embeds in `E₈`, as used in `prop:types`
(Proposition 2.6(3)) of [Exc]. -/
noncomputable def RootType.inclusionE₈ (t : RootType) (ht : t.rank ≤ 8) :
    IsometricInclusion t.model LineSystem.E₈ := by
  cases t with
  | A n _ => exact An.inclusionE₈OfLE ht
  | D n _ => exact Dn.inclusionE₈OfLE ht
  | E₆ => exact E₆.inclusionE₈
  | E₇ => exact E₇.inclusionE₈
  | E₈ => exact IsometricInclusion.ofSubset Set.Subset.rfl

end LineSystem

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {X : SimpleGraph V} [DecidableRel X.Adj]

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6(3)) of [Exc]: a connected graph is
represented in `E₈` exactly when `2I+A` is positive semidefinite of rank at most eight. -/
theorem isRepresentedIn_E₈_iff_posSemidef_and_rank_le (hX : X.Connected) :
    X.IsRepresentedIn LineSystem.E₈ ↔
      ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef ∧
      ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank ≤ 8 := by
  refine ⟨fun h => h.posSemidef_two_add_adjMatrix_and_rank_le_eight, ?_⟩
  rintro ⟨hp, hr⟩
  obtain ⟨x, hx⟩ := X.exists_representation_iff_posSemidef.mpr hp
  obtain ⟨t, ⟨⟨e⟩, ht, -, -, -⟩, -⟩ := hx.exists_unique_root_lattice hX
  have htr : t.rank ≤ 8 := by
    rw [ht, ← hx.rank_two_add_adjMatrix X]
    exact hr
  exact (hx.isRepresentedIn_latticeRoots.of_iso e).of_isometricInclusion (t.inclusionE₈ htr)

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6(3)) of [Exc], under its standing
positive semidefiniteness hypothesis. -/
theorem isRepresentedIn_E₈_iff_rank_le (hX : X.Connected)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef) :
    X.IsRepresentedIn LineSystem.E₈ ↔
      ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank ≤ 8 := by
  rw [isRepresentedIn_E₈_iff_posSemidef_and_rank_le hX, and_iff_right hp]

end SimpleGraph
