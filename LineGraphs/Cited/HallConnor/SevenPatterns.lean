/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.LocalCounts

/-!
# Excluding positive defects

The seven-block arguments `hcLocalNotOne` and `hcLocalNotTwo` in `hc:lem:split` of the
Hall–Connor blueprint ([CGSS], Remark 5.12 and Example 5.13).
-/

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable (D : Design P B 15 5 21 7 2)

set_option maxHeartbeats 1500000 in
-- The seven-label injection and all 49 matrix entries are checked by finite case analysis.
/-- Defect one is excluded by `Q1`, `hcLocalNotOne`
([CGSS], Remark 5.12). -/
theorem localDefect_ne_one {X Y Z₁ : B} (hXY : D.Z.Adj X Y)
    (hZ : Z₁ ∈ D.neighborFiber X Y true true)
    (htwo : 2 ≤ ((D.neighborFiber X Y true false).filter (D.Z.Adj Z₁)).card) :
    D.localDefect X Y Z₁ ≠ 1 := by
  intro hj
  let U₀ := (D.neighborFiber X Y true false).filter (fun T ↦ ¬ D.Z.Adj Z₁ T)
  let V₁ := (D.neighborFiber X Y false true).filter (D.Z.Adj Z₁)
  have hUcard : U₀.card = 1 := hj
  have hVcard : V₁.card = 3 := by
    simpa [V₁, hj] using (D.local_counts hXY hZ htwo).2.2
  have hz : Z₁ ≠ Y ∧ Z₁ ≠ X ∧ D.Z.Adj X Z₁ ∧ D.Z.Adj Y Z₁ := by
    simpa [neighborFiber, and_assoc] using hZ
  have hU (T : B) (hT : T ∈ U₀) :
      T ≠ X ∧ T ≠ Y ∧ T ≠ Z₁ ∧ D.Z.Adj X T ∧ ¬ D.Z.Adj Y T ∧ ¬ D.Z.Adj Z₁ T := by
    obtain ⟨hT, hn⟩ := Finset.mem_filter.mp hT
    have ht : T ≠ Y ∧ T ≠ X ∧ D.Z.Adj X T ∧ ¬ D.Z.Adj Y T := by
      simpa [neighborFiber, and_assoc] using hT
    have hTZ : T ≠ Z₁ := by rintro rfl; exact ht.2.2.2 hz.2.2.2
    exact ⟨ht.2.1, ht.1, hTZ, ht.2.2.1, ht.2.2.2, hn⟩
  have hV (T : B) (hT : T ∈ V₁) :
      T ≠ X ∧ T ≠ Y ∧ T ≠ Z₁ ∧ ¬ D.Z.Adj X T ∧ D.Z.Adj Y T ∧ D.Z.Adj Z₁ T := by
    obtain ⟨hT, ha⟩ := Finset.mem_filter.mp hT
    have ht : T ≠ Y ∧ T ≠ X ∧ ¬ D.Z.Adj X T ∧ D.Z.Adj Y T := by
      simpa [neighborFiber, and_assoc] using hT
    exact ⟨ht.2.1, ht.1, ha.ne.symm, ht.2.2.1, ht.2.2.2, ha⟩
  have hVclique : D.Z.IsClique (D.neighborFiber X Y false true : Set B) := by
    rw [← D.neighborFiber_swap X Y false true]
    exact D.isClique_neighborFiber_true_false hXY.symm
  obtain ⟨A₁, hUA⟩ := Finset.card_eq_one.mp hUcard
  obtain ⟨B₁, B₂, B₃, hB12, hB13, hB23, hVB⟩ := Finset.card_eq_three.mp hVcard
  have hA1 : A₁ ∈ U₀ := by rw [hUA]; simp
  have ha1 := hU A₁ hA1
  have hB1 : B₁ ∈ V₁ := by rw [hVB]; simp
  have hb1 := hV B₁ hB1
  have hB2 : B₂ ∈ V₁ := by rw [hVB]; simp
  have hb2 := hV B₂ hB2
  have hB3 : B₃ ∈ V₁ := by rw [hVB]; simp
  have hb3 := hV B₃ hB3
  have hA1B1 : A₁ ≠ B₁ := by
    rintro rfl; exact hb1.2.2.2.1 ha1.2.2.2.1
  have hA1B2 : A₁ ≠ B₂ := by
    rintro rfl; exact hb2.2.2.2.1 ha1.2.2.2.1
  have hA1B3 : A₁ ≠ B₃ := by
    rintro rfl; exact hb3.2.2.2.1 ha1.2.2.2.1
  have hi : Function.Injective (![X, Y, Z₁, A₁, B₁, B₂, B₃] : Fin 7 → B) := by
    have hXY' := hXY.ne
    intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all
  let e : Fin 7 ↪ B := ⟨![X, Y, Z₁, A₁, B₁, B₂, B₃], hi⟩
  have h01 : D.Z.Adj X Y := hXY
  have h10 : D.Z.Adj Y X := h01.symm
  have h02 : D.Z.Adj X Z₁ := hz.2.2.1
  have h20 : D.Z.Adj Z₁ X := h02.symm
  have h03 : D.Z.Adj X A₁ := ha1.2.2.2.1
  have h30 : D.Z.Adj A₁ X := h03.symm
  have h04 : ¬ D.Z.Adj X B₁ := hb1.2.2.2.1
  have h40 : ¬ D.Z.Adj B₁ X := fun h ↦ h04 h.symm
  have h05 : ¬ D.Z.Adj X B₂ := hb2.2.2.2.1
  have h50 : ¬ D.Z.Adj B₂ X := fun h ↦ h05 h.symm
  have h06 : ¬ D.Z.Adj X B₃ := hb3.2.2.2.1
  have h60 : ¬ D.Z.Adj B₃ X := fun h ↦ h06 h.symm
  have h12 : D.Z.Adj Y Z₁ := hz.2.2.2
  have h21 : D.Z.Adj Z₁ Y := h12.symm
  have h13 : ¬ D.Z.Adj Y A₁ := ha1.2.2.2.2.1
  have h31 : ¬ D.Z.Adj A₁ Y := fun h ↦ h13 h.symm
  have h14 : D.Z.Adj Y B₁ := hb1.2.2.2.2.1
  have h41 : D.Z.Adj B₁ Y := h14.symm
  have h15 : D.Z.Adj Y B₂ := hb2.2.2.2.2.1
  have h51 : D.Z.Adj B₂ Y := h15.symm
  have h16 : D.Z.Adj Y B₃ := hb3.2.2.2.2.1
  have h61 : D.Z.Adj B₃ Y := h16.symm
  have h23 : ¬ D.Z.Adj Z₁ A₁ := ha1.2.2.2.2.2
  have h32 : ¬ D.Z.Adj A₁ Z₁ := fun h ↦ h23 h.symm
  have h24 : D.Z.Adj Z₁ B₁ := hb1.2.2.2.2.2
  have h42 : D.Z.Adj B₁ Z₁ := h24.symm
  have h25 : D.Z.Adj Z₁ B₂ := hb2.2.2.2.2.2
  have h52 : D.Z.Adj B₂ Z₁ := h25.symm
  have h26 : D.Z.Adj Z₁ B₃ := hb3.2.2.2.2.2
  have h62 : D.Z.Adj B₃ Z₁ := h26.symm
  have h34 : ¬ D.Z.Adj A₁ B₁ := D.not_adj_local_parts hXY hZ
      (Finset.mem_filter.mp hA1).1 (Finset.mem_filter.mp hA1).2
      (Finset.mem_filter.mp hB1).1 (Finset.mem_filter.mp hB1).2
  have h43 : ¬ D.Z.Adj B₁ A₁ := fun h ↦ h34 h.symm
  have h35 : ¬ D.Z.Adj A₁ B₂ := D.not_adj_local_parts hXY hZ
      (Finset.mem_filter.mp hA1).1 (Finset.mem_filter.mp hA1).2
      (Finset.mem_filter.mp hB2).1 (Finset.mem_filter.mp hB2).2
  have h53 : ¬ D.Z.Adj B₂ A₁ := fun h ↦ h35 h.symm
  have h36 : ¬ D.Z.Adj A₁ B₃ := D.not_adj_local_parts hXY hZ
      (Finset.mem_filter.mp hA1).1 (Finset.mem_filter.mp hA1).2
      (Finset.mem_filter.mp hB3).1 (Finset.mem_filter.mp hB3).2
  have h63 : ¬ D.Z.Adj B₃ A₁ := fun h ↦ h36 h.symm
  have h45 : D.Z.Adj B₁ B₂ := hVclique
      (Finset.mem_filter.mp hB1).1 (Finset.mem_filter.mp hB2).1 hB12
  have h54 : D.Z.Adj B₂ B₁ := h45.symm
  have h46 : D.Z.Adj B₁ B₃ := hVclique
      (Finset.mem_filter.mp hB1).1 (Finset.mem_filter.mp hB3).1 hB13
  have h64 : D.Z.Adj B₃ B₁ := h46.symm
  have h56 : D.Z.Adj B₂ B₃ := hVclique
      (Finset.mem_filter.mp hB2).1 (Finset.mem_filter.mp hB3).1 hB23
  have h65 : D.Z.Adj B₃ B₂ := h56.symm
  have hmatrix : D.C.submatrix e e = Computations.C19.Q1.map (Int.castRingHom ℚ) := by
    ext i k
    simp only [Matrix.submatrix_apply, D.C_apply, e.injective.eq_iff]
    fin_cases i <;> fin_cases k <;>
      norm_num [e, Computations.C19.Q1, Computations.toMatrix, Computations.entry,
        h01, h10, h02, h20, h03, h30, h04, h40, h05, h50, h06, h60,
        h12, h21, h13, h31, h14, h41, h15, h51, h16, h61, h23, h32,
        h24, h42, h25, h52, h26, h62, h34, h43, h35, h53, h36, h63,
        h45, h54, h46, h64, h56, h65]
  apply Computations.C19.det_Q1_ne_zero
  rw [← hmatrix]
  exact D.det_C_submatrix_eq_zero e (by decide)

set_option maxHeartbeats 1500000 in
-- The seven-label injection and all 49 matrix entries are checked by finite case analysis.
/-- Defect two is excluded by `Q2`, `hcLocalNotTwo`
([CGSS], Remark 5.12). -/
theorem localDefect_ne_two {X Y Z₁ : B} (hXY : D.Z.Adj X Y)
    (hZ : Z₁ ∈ D.neighborFiber X Y true true)
    (htwo : 2 ≤ ((D.neighborFiber X Y true false).filter (D.Z.Adj Z₁)).card) :
    D.localDefect X Y Z₁ ≠ 2 := by
  intro hj
  let U₀ := (D.neighborFiber X Y true false).filter (fun T ↦ ¬ D.Z.Adj Z₁ T)
  let V₁ := (D.neighborFiber X Y false true).filter (D.Z.Adj Z₁)
  have hUcard : U₀.card = 2 := hj
  have hVcard : V₁.card = 2 := by
    simpa [V₁, hj] using (D.local_counts hXY hZ htwo).2.2
  have hz : Z₁ ≠ Y ∧ Z₁ ≠ X ∧ D.Z.Adj X Z₁ ∧ D.Z.Adj Y Z₁ := by
    simpa [neighborFiber, and_assoc] using hZ
  have hU (T : B) (hT : T ∈ U₀) :
      T ≠ X ∧ T ≠ Y ∧ T ≠ Z₁ ∧ D.Z.Adj X T ∧ ¬ D.Z.Adj Y T ∧ ¬ D.Z.Adj Z₁ T := by
    obtain ⟨hT, hn⟩ := Finset.mem_filter.mp hT
    have ht : T ≠ Y ∧ T ≠ X ∧ D.Z.Adj X T ∧ ¬ D.Z.Adj Y T := by
      simpa [neighborFiber, and_assoc] using hT
    have hTZ : T ≠ Z₁ := by rintro rfl; exact ht.2.2.2 hz.2.2.2
    exact ⟨ht.2.1, ht.1, hTZ, ht.2.2.1, ht.2.2.2, hn⟩
  have hV (T : B) (hT : T ∈ V₁) :
      T ≠ X ∧ T ≠ Y ∧ T ≠ Z₁ ∧ ¬ D.Z.Adj X T ∧ D.Z.Adj Y T ∧ D.Z.Adj Z₁ T := by
    obtain ⟨hT, ha⟩ := Finset.mem_filter.mp hT
    have ht : T ≠ Y ∧ T ≠ X ∧ ¬ D.Z.Adj X T ∧ D.Z.Adj Y T := by
      simpa [neighborFiber, and_assoc] using hT
    exact ⟨ht.2.1, ht.1, ha.ne.symm, ht.2.2.1, ht.2.2.2, ha⟩
  have hVclique : D.Z.IsClique (D.neighborFiber X Y false true : Set B) := by
    rw [← D.neighborFiber_swap X Y false true]
    exact D.isClique_neighborFiber_true_false hXY.symm
  obtain ⟨A₁, A₂, hA12, hUA⟩ := Finset.card_eq_two.mp hUcard
  obtain ⟨B₁, B₂, hB12, hVB⟩ := Finset.card_eq_two.mp hVcard
  have hA1 : A₁ ∈ U₀ := by rw [hUA]; simp
  have ha1 := hU A₁ hA1
  have hA2 : A₂ ∈ U₀ := by rw [hUA]; simp
  have ha2 := hU A₂ hA2
  have hB1 : B₁ ∈ V₁ := by rw [hVB]; simp
  have hb1 := hV B₁ hB1
  have hB2 : B₂ ∈ V₁ := by rw [hVB]; simp
  have hb2 := hV B₂ hB2
  have hA1B1 : A₁ ≠ B₁ := by
    rintro rfl; exact hb1.2.2.2.1 ha1.2.2.2.1
  have hA1B2 : A₁ ≠ B₂ := by
    rintro rfl; exact hb2.2.2.2.1 ha1.2.2.2.1
  have hA2B1 : A₂ ≠ B₁ := by
    rintro rfl; exact hb1.2.2.2.1 ha2.2.2.2.1
  have hA2B2 : A₂ ≠ B₂ := by
    rintro rfl; exact hb2.2.2.2.1 ha2.2.2.2.1
  have hi : Function.Injective (![X, Y, Z₁, A₁, A₂, B₁, B₂] : Fin 7 → B) := by
    have hXY' := hXY.ne
    intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all
  let e : Fin 7 ↪ B := ⟨![X, Y, Z₁, A₁, A₂, B₁, B₂], hi⟩
  have h01 : D.Z.Adj X Y := hXY
  have h10 : D.Z.Adj Y X := h01.symm
  have h02 : D.Z.Adj X Z₁ := hz.2.2.1
  have h20 : D.Z.Adj Z₁ X := h02.symm
  have h03 : D.Z.Adj X A₁ := ha1.2.2.2.1
  have h30 : D.Z.Adj A₁ X := h03.symm
  have h04 : D.Z.Adj X A₂ := ha2.2.2.2.1
  have h40 : D.Z.Adj A₂ X := h04.symm
  have h05 : ¬ D.Z.Adj X B₁ := hb1.2.2.2.1
  have h50 : ¬ D.Z.Adj B₁ X := fun h ↦ h05 h.symm
  have h06 : ¬ D.Z.Adj X B₂ := hb2.2.2.2.1
  have h60 : ¬ D.Z.Adj B₂ X := fun h ↦ h06 h.symm
  have h12 : D.Z.Adj Y Z₁ := hz.2.2.2
  have h21 : D.Z.Adj Z₁ Y := h12.symm
  have h13 : ¬ D.Z.Adj Y A₁ := ha1.2.2.2.2.1
  have h31 : ¬ D.Z.Adj A₁ Y := fun h ↦ h13 h.symm
  have h14 : ¬ D.Z.Adj Y A₂ := ha2.2.2.2.2.1
  have h41 : ¬ D.Z.Adj A₂ Y := fun h ↦ h14 h.symm
  have h15 : D.Z.Adj Y B₁ := hb1.2.2.2.2.1
  have h51 : D.Z.Adj B₁ Y := h15.symm
  have h16 : D.Z.Adj Y B₂ := hb2.2.2.2.2.1
  have h61 : D.Z.Adj B₂ Y := h16.symm
  have h23 : ¬ D.Z.Adj Z₁ A₁ := ha1.2.2.2.2.2
  have h32 : ¬ D.Z.Adj A₁ Z₁ := fun h ↦ h23 h.symm
  have h24 : ¬ D.Z.Adj Z₁ A₂ := ha2.2.2.2.2.2
  have h42 : ¬ D.Z.Adj A₂ Z₁ := fun h ↦ h24 h.symm
  have h25 : D.Z.Adj Z₁ B₁ := hb1.2.2.2.2.2
  have h52 : D.Z.Adj B₁ Z₁ := h25.symm
  have h26 : D.Z.Adj Z₁ B₂ := hb2.2.2.2.2.2
  have h62 : D.Z.Adj B₂ Z₁ := h26.symm
  have h34 : D.Z.Adj A₁ A₂ := D.isClique_neighborFiber_true_false hXY
      (Finset.mem_filter.mp hA1).1 (Finset.mem_filter.mp hA2).1 hA12
  have h43 : D.Z.Adj A₂ A₁ := h34.symm
  have h35 : ¬ D.Z.Adj A₁ B₁ := D.not_adj_local_parts hXY hZ
      (Finset.mem_filter.mp hA1).1 (Finset.mem_filter.mp hA1).2
      (Finset.mem_filter.mp hB1).1 (Finset.mem_filter.mp hB1).2
  have h53 : ¬ D.Z.Adj B₁ A₁ := fun h ↦ h35 h.symm
  have h36 : ¬ D.Z.Adj A₁ B₂ := D.not_adj_local_parts hXY hZ
      (Finset.mem_filter.mp hA1).1 (Finset.mem_filter.mp hA1).2
      (Finset.mem_filter.mp hB2).1 (Finset.mem_filter.mp hB2).2
  have h63 : ¬ D.Z.Adj B₂ A₁ := fun h ↦ h36 h.symm
  have h45 : ¬ D.Z.Adj A₂ B₁ := D.not_adj_local_parts hXY hZ
      (Finset.mem_filter.mp hA2).1 (Finset.mem_filter.mp hA2).2
      (Finset.mem_filter.mp hB1).1 (Finset.mem_filter.mp hB1).2
  have h54 : ¬ D.Z.Adj B₁ A₂ := fun h ↦ h45 h.symm
  have h46 : ¬ D.Z.Adj A₂ B₂ := D.not_adj_local_parts hXY hZ
      (Finset.mem_filter.mp hA2).1 (Finset.mem_filter.mp hA2).2
      (Finset.mem_filter.mp hB2).1 (Finset.mem_filter.mp hB2).2
  have h64 : ¬ D.Z.Adj B₂ A₂ := fun h ↦ h46 h.symm
  have h56 : D.Z.Adj B₁ B₂ := hVclique
      (Finset.mem_filter.mp hB1).1 (Finset.mem_filter.mp hB2).1 hB12
  have h65 : D.Z.Adj B₂ B₁ := h56.symm
  have hmatrix : D.C.submatrix e e = Computations.C19.Q2.map (Int.castRingHom ℚ) := by
    ext i k
    simp only [Matrix.submatrix_apply, D.C_apply, e.injective.eq_iff]
    fin_cases i <;> fin_cases k <;>
      norm_num [e, Computations.C19.Q2, Computations.toMatrix, Computations.entry,
        h01, h10, h02, h20, h03, h30, h04, h40, h05, h50, h06, h60,
        h12, h21, h13, h31, h14, h41, h15, h51, h16, h61, h23, h32,
        h24, h42, h25, h52, h26, h62, h34, h43, h35, h53, h36, h63,
        h45, h54, h46, h64, h56, h65]
  apply Computations.C19.det_Q2_ne_zero
  rw [← hmatrix]
  exact D.det_C_submatrix_eq_zero e (by decide)

/-- The selected third block has zero defect, `hcLocalZero` ([CGSS], Remark 5.12). -/
theorem localDefect_eq_zero {X Y Z₁ : B} (hXY : D.Z.Adj X Y)
    (hZ : Z₁ ∈ D.neighborFiber X Y true true)
    (htwo : 2 ≤ ((D.neighborFiber X Y true false).filter (D.Z.Adj Z₁)).card) :
    D.localDefect X Y Z₁ = 0 := by
  have hle := (D.local_counts hXY hZ htwo).1
  have hne1 := D.localDefect_ne_one hXY hZ htwo
  have hne2 := D.localDefect_ne_two hXY hZ htwo
  omega

end Design
