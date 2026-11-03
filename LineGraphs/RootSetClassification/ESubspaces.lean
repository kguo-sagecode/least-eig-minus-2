/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.ERealization

/-!
# The E₆ and E₇ subspaces and integer bases

Steps `rEseven`, `rEsix`, and `rEsubspaces` of `lem:E` in the blueprint
for Remark 3.11 of [CGSS]. Restrict the explicit E₈ inverse to its first
six or seven coordinates.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

/-- Step `rEseven`: the E₇ subspace equation is vanishing of coefficient 7. -/
theorem mem_e₇Space_iff_coefficient (x : EuclideanSpace ℝ (Fin 8)) :
    x ∈ e₇Space ↔ eCoefficients x 7 = 0 := by
  rw [mem_e₇Space]
  rfl

/-- Step `rEsix`: the E₆ equations are vanishing of coefficients 6 and 7. -/
theorem mem_e₆Space_iff_coefficients (x : EuclideanSpace ℝ (Fin 8)) :
    x ∈ e₆Space ↔ eCoefficients x 6 = 0 ∧ eCoefficients x 7 = 0 := by
  rw [mem_e₆Space]
  change (x 5 = x 6 ∧ x 6 = -x 7) ↔ x 5 + x 6 + 2 * x 7 = 0 ∧ x 6 + x 7 = 0
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Step `rEsubspaces`: the first seven prescribed roots lie in the E₇ space. -/
theorem E₈.simpleRoot_mem_e₇Space (i : Fin 7) : E₈.simpleRoot i.castSucc ∈ e₇Space := by
  rw [mem_e₇Space]
  have h : ∀ i : Fin 7, eSimpleEntries i.castSucc 6 + eSimpleEntries i.castSucc 7 = 0 :=
    by decide +kernel
  have hr := congrArg (Int.cast : ℤ → ℝ) (h i)
  push_cast at hr
  change (1 / 2 : ℝ) * (eSimpleEntries i.castSucc 6 : ℝ) +
    (1 / 2 : ℝ) * (eSimpleEntries i.castSucc 7 : ℝ) = 0
  linarith

/-- Step `rEsubspaces`: the first six prescribed roots lie in the E₆ space. -/
theorem E₈.simpleRoot_mem_e₆Space (i : Fin 6) :
    E₈.simpleRoot i.castSucc.castSucc ∈ e₆Space := by
  rw [mem_e₆Space]
  have h : ∀ i : Fin 6,
      eSimpleEntries i.castSucc.castSucc 5 = eSimpleEntries i.castSucc.castSucc 6 ∧
      eSimpleEntries i.castSucc.castSucc 6 = -eSimpleEntries i.castSucc.castSucc 7 :=
    by decide +kernel
  change (1 / 2 : ℝ) * (eSimpleEntries i.castSucc.castSucc 5 : ℝ) =
      (1 / 2 : ℝ) * (eSimpleEntries i.castSucc.castSucc 6 : ℝ) ∧
    (1 / 2 : ℝ) * (eSimpleEntries i.castSucc.castSucc 6 : ℝ) =
      -((1 / 2 : ℝ) * (eSimpleEntries i.castSucc.castSucc 7 : ℝ))
  rw [(h i).1, (h i).2]
  push_cast
  constructor <;> ring

/-- The E₇ simple roots of `eq:E-base`, in their prescribed space. -/
noncomputable def E₇.simpleRoot (i : Fin 7) : e₇Space :=
  ⟨E₈.simpleRoot i.castSucc, E₈.simpleRoot_mem_e₇Space i⟩

/-- The E₆ simple roots of `eq:E-base`, in their prescribed space. -/
noncomputable def E₆.simpleRoot (i : Fin 6) : e₆Space :=
  ⟨E₈.simpleRoot i.castSucc.castSucc, E₈.simpleRoot_mem_e₆Space i⟩

/-- Step `rEsubspaces`: the first seven coefficients reconstruct the E₇ subspace. -/
theorem E₇.sum_eCoefficients (x : e₇Space) :
    ∑ i : Fin 7, eCoefficients x i.castSucc • E₇.simpleRoot i = x := by
  apply Subtype.ext
  have he := sum_eCoefficients_simpleRoot (x : EuclideanSpace ℝ (Fin 8))
  have h₇ := (mem_e₇Space_iff_coefficient x).mp x.property
  rw [Fin.sum_univ_castSucc, show Fin.last 7 = (7 : Fin 8) from rfl,
    h₇, zero_smul, add_zero] at he
  simpa [E₇.simpleRoot] using he

/-- Step `rEsubspaces`: the first six coefficients reconstruct the E₆ subspace. -/
theorem E₆.sum_eCoefficients (x : e₆Space) :
    ∑ i : Fin 6, eCoefficients x i.castSucc.castSucc • E₆.simpleRoot i = x := by
  apply Subtype.ext
  have he := sum_eCoefficients_simpleRoot (x : EuclideanSpace ℝ (Fin 8))
  obtain ⟨h₆, h₇⟩ := (mem_e₆Space_iff_coefficients x).mp x.property
  rw [Fin.sum_univ_castSucc, show Fin.last 7 = (7 : Fin 8) from rfl,
    h₇, zero_smul, add_zero, Fin.sum_univ_castSucc,
    show (Fin.last 6).castSucc = (6 : Fin 8) from rfl, h₆, zero_smul, add_zero] at he
  simpa [E₆.simpleRoot] using he

/-- The E₇ independence assertion of `rEsubspaces`. -/
theorem E₇.simpleRoot_linearIndependent : LinearIndependent ℝ E₇.simpleRoot :=
  LinearIndependent.of_comp e₇Space.subtype
    (E₈.simpleRoot_linearIndependent.comp _ (Fin.castSucc_injective 7))

/-- The E₆ independence assertion of `rEsubspaces`. -/
theorem E₆.simpleRoot_linearIndependent : LinearIndependent ℝ E₆.simpleRoot :=
  LinearIndependent.of_comp e₆Space.subtype (E₈.simpleRoot_linearIndependent.comp _
    ((Fin.castSucc_injective 7).comp (Fin.castSucc_injective 6)))

/-- The E₇ spanning assertion of `rEsubspaces`. -/
theorem span_E₇_simpleRoot : span ℝ (Set.range E₇.simpleRoot) = ⊤ := by
  apply top_unique
  intro x _
  rw [← E₇.sum_eCoefficients x]
  exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span (Set.mem_range_self i))

/-- The E₆ spanning assertion of `rEsubspaces`. -/
theorem span_E₆_simpleRoot : span ℝ (Set.range E₆.simpleRoot) = ⊤ := by
  apply top_unique
  intro x _
  rw [← E₆.sum_eCoefficients x]
  exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span (Set.mem_range_self i))

/-- The real E₇ basis in `rEsubspaces` of Remark 3.11. -/
noncomputable def E₇.simpleBasis : Module.Basis (Fin 7) ℝ e₇Space :=
  Module.Basis.mk E₇.simpleRoot_linearIndependent span_E₇_simpleRoot.ge

/-- The real E₆ basis in `rEsubspaces` of Remark 3.11. -/
noncomputable def E₆.simpleBasis : Module.Basis (Fin 6) ℝ e₆Space :=
  Module.Basis.mk E₆.simpleRoot_linearIndependent span_E₆_simpleRoot.ge

/-- The E₇ basis retains the vectors of `eq:E-base`. -/
@[simp] theorem E₇.simpleBasis_apply (i : Fin 7) : E₇.simpleBasis i = E₇.simpleRoot i :=
  Module.Basis.mk_apply _ _ _

/-- The E₆ basis retains the vectors of `eq:E-base`. -/
@[simp] theorem E₆.simpleBasis_apply (i : Fin 6) : E₆.simpleBasis i = E₆.simpleRoot i :=
  Module.Basis.mk_apply _ _ _

/-- The dimension assertion in `lem:E` of Remark 3.11 for E₇. -/
theorem finrank_e₇Space : Module.finrank ℝ e₇Space = 7 := by
  simpa using Module.finrank_eq_card_basis E₇.simpleBasis

/-- The dimension assertion in `lem:E` of Remark 3.11 for E₆. -/
theorem finrank_e₆Space : Module.finrank ℝ e₆Space = 6 := by
  simpa using Module.finrank_eq_card_basis E₆.simpleBasis

/-- The lattice intersection in the E₇ part of `rEsubspaces`. -/
noncomputable def e₇Lattice : AddSubgroup e₇Space :=
  e₈Lattice.comap e₇Space.subtype.toAddMonoidHom

/-- The lattice intersection in the E₆ part of `rEsubspaces`. -/
noncomputable def e₆Lattice : AddSubgroup e₆Space :=
  e₈Lattice.comap e₆Space.subtype.toAddMonoidHom

/-- Step `rEsubspaces`: the first seven roots generate the E₇ lattice over the integers. -/
theorem mem_e₇Lattice_iff_exists_coefficients (x : e₇Space) :
    x ∈ e₇Lattice ↔ ∃ c : Fin 7 → ℤ, x = ∑ i, (c i : ℝ) • E₇.simpleBasis i := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := exists_integer_eCoefficients (x := (x : EuclideanSpace ℝ (Fin 8))) hx
    refine ⟨fun i ↦ c i.castSucc, ?_⟩
    simpa only [E₇.simpleBasis_apply, hc] using (E₇.sum_eCoefficients x).symm
  · rintro ⟨c, rfl⟩
    apply e₇Lattice.sum_mem
    intro i _
    rw [E₇.simpleBasis_apply, Int.cast_smul_eq_zsmul ℝ]
    exact e₇Lattice.zsmul_mem (E₈_subset_e₈Lattice (E₈.simpleRoot_mem i.castSucc)) _

/-- Step `rEsubspaces`: the first six roots generate the E₆ lattice over the integers. -/
theorem mem_e₆Lattice_iff_exists_coefficients (x : e₆Space) :
    x ∈ e₆Lattice ↔ ∃ c : Fin 6 → ℤ, x = ∑ i, (c i : ℝ) • E₆.simpleBasis i := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := exists_integer_eCoefficients (x := (x : EuclideanSpace ℝ (Fin 8))) hx
    refine ⟨fun i ↦ c i.castSucc.castSucc, ?_⟩
    simpa only [E₆.simpleBasis_apply, hc] using (E₆.sum_eCoefficients x).symm
  · rintro ⟨c, rfl⟩
    apply e₆Lattice.sum_mem
    intro i _
    rw [E₆.simpleBasis_apply, Int.cast_smul_eq_zsmul ℝ]
    exact e₆Lattice.zsmul_mem
      (E₈_subset_e₈Lattice (E₈.simpleRoot_mem i.castSucc.castSucc)) _

end RootSetModel
