/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4Dn
import LineGraphs.Computations.StarOrbits

/-!
# C4 for every ordered star of Dₙ

Step `s3c5Dtransitive` of computation C5 (`blueprint/sec3-rootsystems.tex`): the signed
permutations of the coordinates preserve `Dₙ` and act transitively on its ordered stars. Two roots
of `Dₙ` with product `-1` share exactly one coordinate, with opposite signs there; a signed
permutation sends the unshared coordinate of the first to `e₀`, the shared one to `e₁` and the
unshared one of the second to `e₂`. Hence the marked graph of every ordered star of `Dₙ` is the
friendship graph with `n - 3` triangles (`Hyp24.nonempty_orthGraph_iso_of_S_eq_Dn`).
-/

open scoped RealInnerProductSpace

namespace LineSystem

theorem rootSign_mul_self (b : Bool) : rootSign b * rootSign b = 1 := by
  cases b <;> rfl

theorem rootSign_not (b : Bool) : rootSign (!b) = -rootSign b := by
  cases b <;> rfl

private theorem eq_not_of_rootSign_mul {x y : Bool} (h : rootSign x * rootSign y = -1) :
    y = !x := by
  cases x <;> cases y <;> simp_all [rootSign]

/-- A signed permutation of integer coordinates: `eᵢ ↦ ±e_{π i}`. -/
def signedPermVec {n : ℕ} (π : Equiv.Perm (Fin n)) (ε : Fin n → Bool) (w : Fin n → ℤ) :
    Fin n → ℤ :=
  fun k => rootSign (ε (π.symm k)) * w (π.symm k)

/-- The signed permutation `eᵢ ↦ ε(i) e_{π i}` as a linear isometry of `ℝⁿ`. -/
noncomputable def signedPerm {n : ℕ} (π : Equiv.Perm (Fin n)) (ε : Fin n → Bool) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearEquiv.isometryOfInner
    { toFun := fun x => WithLp.toLp 2 fun k => (rootSign (ε (π.symm k)) : ℝ) * x (π.symm k)
      invFun := fun y => WithLp.toLp 2 fun i => (rootSign (ε i) : ℝ) * y (π i)
      map_add' := fun x y => by
        ext k
        simp [mul_add]
      map_smul' := fun c x => by
        ext k
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
      left_inv := fun x => by
        ext i
        simp only [Equiv.symm_apply_apply, ← mul_assoc]
        rw [← Int.cast_mul, rootSign_mul_self, Int.cast_one, one_mul]
      right_inv := fun y => by
        ext k
        simp only [Equiv.apply_symm_apply, ← mul_assoc]
        rw [← Int.cast_mul, rootSign_mul_self, Int.cast_one, one_mul] }
    (by
      intro x y
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial]
      conv_rhs => rw [← Equiv.sum_comp π.symm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := rootSign_mul_self (ε (π.symm i))
      have h' : (rootSign (ε (π.symm i)) : ℝ) * rootSign (ε (π.symm i)) = 1 := by exact_mod_cast h
      linear_combination (y (π.symm i) * x (π.symm i)) * h')

theorem signedPerm_apply {n : ℕ} (π : Equiv.Perm (Fin n)) (ε : Fin n → Bool)
    (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    signedPerm π ε x k = (rootSign (ε (π.symm k)) : ℝ) * x (π.symm k) := rfl

theorem signedPerm_integerVector {n : ℕ} (π : Equiv.Perm (Fin n)) (ε : Fin n → Bool)
    (w : Fin n → ℤ) :
    signedPerm π ε (integerVector 1 w) = integerVector 1 (signedPermVec π ε w) := by
  ext k
  simp [signedPerm_apply, signedPermVec]

theorem signedPermVec_pairVector {n : ℕ} (π : Equiv.Perm (Fin n)) (ε : Fin n → Bool)
    (i j : Fin n) (x y : ℤ) :
    signedPermVec π ε (pairVector i j x y) =
      pairVector (π i) (π j) (rootSign (ε i) * x) (rootSign (ε j) * y) := by
  funext k
  simp only [signedPermVec, pairVector, Pi.add_apply, Pi.single_apply, Equiv.symm_apply_eq]
  split_ifs <;> subst_vars <;> simp_all [mul_add]

/-- The roots of `Dₙ` are the integer vectors of squared norm 2. -/
theorem Dn.mem_Φ_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ (Dn n).Φ ↔ (∀ k, ∃ z : ℤ, x k = z) ∧ ⟪x, x⟫ = 2 := by
  constructor
  · intro hx
    refine ⟨?_, (Dn n).inner_self x hx⟩
    obtain ⟨a, rfl⟩ := hx
    exact fun k => ⟨dnRoot a k, by simp [integerVector]⟩
  · rintro ⟨hz, hn⟩
    choose w hw using hz
    have hx : x = integerVector 1 w := by
      ext k
      simp [hw k]
    rw [hx, inner_integerVector] at hn
    have hw2 : integerInner w w = 2 := by
      have : ((integerInner w w : ℤ) : ℝ) = 2 := by linarith
      exact_mod_cast this
    obtain ⟨a, ha⟩ := exists_dnRoot_of_inner_self w hw2
    exact ⟨a, by rw [hx]; exact congrArg (integerVector 1) ha⟩

/-- Signed permutations preserve `Dₙ`. -/
theorem signedPerm_mem_isometryGroup {n : ℕ} (π : Equiv.Perm (Fin n)) (ε : Fin n → Bool) :
    signedPerm π ε ∈ (Dn n).isometryGroup := by
  intro x
  rw [Dn.mem_Φ_iff, Dn.mem_Φ_iff, LinearIsometryEquiv.inner_map_map]
  refine and_congr_left fun _ => ⟨fun h i => ?_, fun h k => ?_⟩
  · obtain ⟨z, hz⟩ := h (π i)
    rw [signedPerm_apply, Equiv.symm_apply_apply] at hz
    refine ⟨rootSign (ε i) * z, ?_⟩
    have h1 : (rootSign (ε i) : ℝ) * rootSign (ε i) = 1 := by
      exact_mod_cast rootSign_mul_self (ε i)
    push_cast
    rw [← hz, ← mul_assoc, h1, one_mul]
  · obtain ⟨z, hz⟩ := h (π.symm k)
    exact ⟨rootSign (ε (π.symm k)) * z, by rw [signedPerm_apply, hz]; push_cast; rfl⟩

end LineSystem

namespace Computations.C5

/-- Computation C5, step `s3c5Dtransitive` of the Section 3 blueprint: a permutation of
`Fin n` with prescribed values at three distinct points. -/
theorem exists_perm_three {n : ℕ} {i₀ i₁ i₂ u w z : Fin n} (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂)
    (h12 : i₁ ≠ i₂) (huw : u ≠ w) (huz : u ≠ z) (hwz : w ≠ z) :
    ∃ π : Equiv.Perm (Fin n), π i₀ = u ∧ π i₁ = w ∧ π i₂ = z := by
  set τ₁ := Equiv.swap i₀ u
  have h₁ : τ₁ i₀ = u := Equiv.swap_apply_left _ _
  set w' := τ₁.symm w
  have hw' : w' ≠ i₀ := by
    intro h
    apply huw
    rw [← h₁, ← h, Equiv.apply_symm_apply]
  set τ₂ := Equiv.swap i₁ w'
  set π₂ := τ₁ * τ₂
  have hπ₀ : π₂ i₀ = u := by
    change τ₁ (τ₂ i₀) = u
    rw [Equiv.swap_apply_of_ne_of_ne h01 hw'.symm, h₁]
  have hπ₁ : π₂ i₁ = w := by
    change τ₁ (τ₂ i₁) = w
    rw [Equiv.swap_apply_left, Equiv.apply_symm_apply]
  set z' := π₂.symm z
  have hz₀ : z' ≠ i₀ := by
    intro h
    apply huz
    rw [← hπ₀, ← h, Equiv.apply_symm_apply]
  have hz₁ : z' ≠ i₁ := by
    intro h
    apply hwz
    rw [← hπ₁, ← h, Equiv.apply_symm_apply]
  refine ⟨π₂ * Equiv.swap i₂ z', ?_, ?_, ?_⟩
  · change π₂ (Equiv.swap i₂ z' i₀) = u
    rw [Equiv.swap_apply_of_ne_of_ne h02 hz₀.symm, hπ₀]
  · change π₂ (Equiv.swap i₂ z' i₁) = w
    rw [Equiv.swap_apply_of_ne_of_ne h12 hz₁.symm, hπ₁]
  · change π₂ (Equiv.swap i₂ z' i₂) = z
    rw [Equiv.swap_apply_left, Equiv.apply_symm_apply]

end Computations.C5

namespace LineSystem

-- Computation C5, step s3c5Dsupport
/-- Two roots of `Dₙ` with product `-1` share exactly one coordinate, with opposite signs:
they are `α e_u - β e_w` and `β e_w - γ e_z` for distinct `u, w, z`. -/
theorem Dn.exists_pair_of_inner_eq_neg_one {n : ℕ} (p q : Dn.Index n)
    (h : integerInner (dnRoot p) (dnRoot q) = -1) :
    ∃ u w z : Fin n, u ≠ w ∧ u ≠ z ∧ w ≠ z ∧ ∃ α β γ : Bool,
      dnRoot p = pairVector u w (rootSign α) (rootSign (!β)) ∧
      dnRoot q = pairVector w z (rootSign β) (rootSign (!γ)) := by
  rcases p with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  rcases q with ⟨⟨⟨k, m⟩, hkm⟩, s', t'⟩
  change i < j at hij
  change k < m at hkm
  change integerInner (pairVector i j (rootSign s) (rootSign t))
    (pairVector k m (rootSign s') (rootSign t')) = -1 at h
  rw [integerInner_pairVector] at h
  simp only [pairVector, Pi.add_apply, Pi.single_apply] at h
  change ∃ u w z : Fin n, u ≠ w ∧ u ≠ z ∧ w ≠ z ∧ ∃ α β γ : Bool,
      pairVector i j (rootSign s) (rootSign t) = pairVector u w (rootSign α) (rootSign (!β)) ∧
      pairVector k m (rootSign s') (rootSign t') = pairVector w z (rootSign β) (rootSign (!γ))
  have hsw : ∀ (a b : Fin n) (x y : ℤ), pairVector a b x y = pairVector b a y x :=
    fun _ _ _ _ => add_comm _ _
  by_cases hik : i = k
  · subst hik
    have hjk : ¬ j = i := hij.ne'
    by_cases hjm : j = m
    · subst hjm
      simp only [ite_true, hjk, ite_false, hij.ne, add_zero, zero_add] at h
      cases s <;> cases t <;> cases s' <;> cases t' <;> simp [rootSign] at h
    · simp only [ite_true, hjk, ite_false, hkm.ne, hjm, add_zero, mul_zero] at h
      have hs := eq_not_of_rootSign_mul h
      refine ⟨j, i, m, hij.ne', hjm, hkm.ne, t, s', !t', ?_, ?_⟩
      · rw [hsw, hs, Bool.not_not]
      · rw [Bool.not_not]
  · by_cases him : i = m
    · subst him
      have hjk : ¬ j = k := (hkm.trans hij).ne'
      have hjm : ¬ j = i := hij.ne'
      simp only [hik, ite_false, ite_true, hjk, hjm, zero_add, add_zero, mul_zero] at h
      have hs := eq_not_of_rootSign_mul h
      refine ⟨j, i, k, hij.ne', (hkm.trans hij).ne', hkm.ne', t, t', !s', ?_, ?_⟩
      · rw [hsw, hs, Bool.not_not]
      · rw [hsw, Bool.not_not]
    · by_cases hjk : j = k
      · subst hjk
        have hjm : ¬ j = m := hkm.ne
        simp only [hik, him, ite_false, ite_true, hjm, zero_add, add_zero, mul_zero] at h
        have hs := eq_not_of_rootSign_mul h
        refine ⟨i, j, m, hij.ne, (hij.trans hkm).ne, hkm.ne, s, s', !t', ?_, ?_⟩
        · rw [hs, Bool.not_not]
        · rw [Bool.not_not]
      · by_cases hjm : j = m
        · subst hjm
          simp only [hik, him, hjk, ite_false, ite_true, zero_add, add_zero, mul_zero] at h
          have hs := eq_not_of_rootSign_mul h
          refine ⟨i, j, k, hij.ne, hik, hkm.ne', s, t', !s', ?_, ?_⟩
          · rw [hs, Bool.not_not]
          · rw [hsw, Bool.not_not]
        · simp only [hik, him, hjk, hjm, ite_false, add_zero, mul_zero] at h
          norm_num at h

-- Computation C5, step s3c5Dtransitive
/-- C5, step `s3c5Dtransitive`: the signed permutations, which preserve `Dₙ`, act transitively on
its ordered stars; each is the image of the marked star `(e₀ - e₁, e₁ - e₂)`. -/
theorem Dn.exists_isometry_star {n : ℕ} (hn : 4 ≤ n) {a b : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ (Dn n).Φ) (hb : b ∈ (Dn n).Φ) (hab : ⟪a, b⟫ = -1) :
    ∃ g ∈ (Dn n).isometryGroup, g (Dn.hyp24 hn).a = a ∧ g (Dn.hyp24 hn).b = b := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  have hpq : integerInner (dnRoot p) (dnRoot q) = -1 := by
    rw [inner_integerVector] at hab
    have : ((integerInner (dnRoot p) (dnRoot q) : ℤ) : ℝ) = -1 := by linarith
    exact_mod_cast this
  obtain ⟨u, w, z, huw, huz, hwz, α, β, γ, hp, hq⟩ := Dn.exists_pair_of_inner_eq_neg_one p q hpq
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨π, hπ0, hπ1, hπ2⟩ := Computations.C5.exists_perm_three h01 h02 h12 huw huz hwz
  let ε : Fin n → Bool := fun i =>
    if i = ⟨0, by omega⟩ then α else if i = ⟨1, by omega⟩ then β else γ
  refine ⟨signedPerm π ε, signedPerm_mem_isometryGroup π ε, ?_, ?_⟩
  · change signedPerm π ε (integerVector 1 (dnRoot (Dn.starA hn))) = integerVector 1 (dnRoot p)
    rw [signedPerm_integerVector, hp]
    change integerVector 1 (signedPermVec π ε (pairVector ⟨0, by omega⟩ ⟨1, by omega⟩
      (rootSign false) (rootSign true))) = _
    rw [signedPermVec_pairVector, hπ0, hπ1]
    simp only [ε, ite_true, h01.symm, ite_false]
    congr 2
    · simp [rootSign]
    · cases β <;> cases γ <;> rfl
  · change signedPerm π ε (integerVector 1 (dnRoot (Dn.starB hn))) = integerVector 1 (dnRoot q)
    rw [signedPerm_integerVector, hq]
    change integerVector 1 (signedPermVec π ε (pairVector ⟨1, by omega⟩ ⟨2, by omega⟩
      (rootSign false) (rootSign true))) = _
    rw [signedPermVec_pairVector, hπ1, hπ2]
    simp only [ε, ite_true, h01.symm, h02.symm, h12.symm, ite_false]
    congr 2
    · simp [rootSign]
    · cases β <;> cases γ <;> rfl

namespace Hyp24

-- Computation C4
/-- C4 for every ordered star of `Dₙ`: its orthogonality graph is the friendship graph with
`n - 3` triangles. -/
theorem nonempty_orthGraph_iso_of_S_eq_Dn {n : ℕ} (hn : 4 ≤ n)
    (H : Hyp24 (EuclideanSpace ℝ (Fin n))) (hS : H.S = Dn n) :
    Nonempty (SimpleGraph.friendship (n - 3) ≃g H.orthGraph) := by
  obtain ⟨g, hΦ, ha, hb⟩ := exists_isometry_of_S_eq (Dn.hyp24 hn) H rfl hS
    (fun _ _ => Dn.exists_isometry_star hn)
  exact ⟨(Dn.orthGraphIso hn).trans (orthGraphIsoOfIsometry _ _ g hΦ ha hb)⟩

-- Computation C4
/-- C4 for every ordered star of `Dₙ`: `|Γa| = 2(n - 3) + 1`. -/
theorem card_Γa_of_S_eq_Dn {n : ℕ} (hn : 4 ≤ n) (H : Hyp24 (EuclideanSpace ℝ (Fin n)))
    (hS : H.S = Dn n) : H.Γa.ncard = 2 * (n - 3) + 1 := by
  obtain ⟨g, hΦ, ha, hb⟩ := exists_isometry_of_S_eq (Dn.hyp24 hn) H rfl hS
    (fun _ _ => Dn.exists_isometry_star hn)
  rw [ncard_Γa_eq_of_isometry _ _ g hΦ ha hb, Dn.card_Γa]

end Hyp24

end LineSystem
