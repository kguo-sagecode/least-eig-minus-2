/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.Pairing

/-!
# Indecomposability and Mathlib irreducibility

The two directions of `lem:pairing-construction` (`rpcirreducible`, `rpcconverse`) in
`blueprint/sec3-remark311.tex`, for Definition 3.9 of [CGSS]. A reflection-invariant
subspace separates roots into those it contains and those orthogonal to it. Conversely,
an orthogonal partition gives a proper invariant span.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Φ : Set V} (hΦ : IsRootSet Φ)

/-- Steps `rpcnontrivial`--`rpcallperp` of `lem:pairing-construction`, for Definition
3.9 of [CGSS]: indecomposability makes the associated pairing irreducible. -/
theorem isIrreducible_of_isIndecomposable (hI : hΦ.IsIndecomposable) :
    hΦ.toRootPairing.IsIrreducible := by
  obtain ⟨r, hr⟩ := hI.1
  let : Nontrivial V := ⟨⟨r, 0, hΦ.ne_zero hr⟩⟩
  apply RootPairing.IsIrreducible.mk'
  intro q hq hne
  let Q : hΦ.toRootPairing.invtRootSubmodule :=
    ⟨q, hΦ.toRootPairing.mem_invtRootSubmodule_iff.mpr hq⟩
  let A : Set V := {x | x ∈ Φ ∧ x ∈ q}
  let B : Set V := {x | x ∈ Φ ∧ x ∉ q}
  have hab : A ∪ B = Φ := by ext x; simp [A, B, ← and_or_left, em]
  have horth : ∀ a ∈ A, ∀ b ∈ B, ⟪a, b⟫ = 0 := by
    intro a ha b hb
    have hk := RootPairing.invtRootSubmodule.le_ker_coroot' Q
      (k := ⟨b, hb.1⟩) hb.2 ha.2
    rw [real_inner_comm]
    exact (hΦ.toRootPairing_coroot'_eq_zero_iff ⟨b, hb.1⟩ a).mp hk
  rcases hI.2 A B hab horth with hA | hB
  · exfalso
    apply hne
    have he := RootPairing.invtRootSubmodule.eq_span_root Q
    change q = span ℝ (hΦ.toRootPairing.root ''
      {i | hΦ.toRootPairing.root i ∈ q}) at he
    have hz : hΦ.toRootPairing.root '' {i | hΦ.toRootPairing.root i ∈ q} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨i, hi, rfl⟩
      have : (i : V) ∈ A := ⟨i.property, hi⟩
      simp only [hA, Set.mem_empty_iff_false] at this
    simpa only [hz, span_empty] using he
  · apply top_unique
    rw [← hΦ.span_eq_top]
    apply span_le.mpr
    intro x hx
    by_contra hn
    have : x ∈ B := ⟨hx, hn⟩
    simp only [hB, Set.mem_empty_iff_false] at this

/-- Steps `rpcWnonzero`--`rpcWB` of `lem:pairing-construction`, for Definition 3.9
of [CGSS]: an irreducible pairing precludes an orthogonal partition of the roots. -/
theorem isIndecomposable_of_isIrreducible (hne : Φ.Nonempty)
    (hI : hΦ.toRootPairing.IsIrreducible) : hΦ.IsIndecomposable := by
  let := hI
  refine ⟨hne, ?_⟩
  intro A B hab horth
  by_cases hA : A = ∅
  · exact Or.inl hA
  right
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hbΦ : b ∈ Φ := hab ▸ Or.inr hb
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hA
  have haΦ : a ∈ Φ := hab ▸ Or.inl ha
  have horth_span (c : V) (hc : c ∈ B) :
      span ℝ A ≤ LinearMap.ker (innerₗ V c) := by
    apply span_le.mpr
    intro x hx
    change ⟪c, x⟫ = 0
    rw [real_inner_comm]
    exact horth x hx c hc
  have hq : ∀ i : Φ, span ℝ A ∈
      Module.End.invtSubmodule (hΦ.toRootPairing.reflection i) := by
    intro i
    apply (Module.End.mem_invtSubmodule _).mpr
    intro x hx
    change hΦ.toRootPairing.reflection i x ∈ span ℝ A
    rw [hΦ.toRootPairing_reflection, reflection_apply]
    have hi : (i : V) ∈ A ∪ B := hab ▸ i.property
    rcases hi with hi | hi
    · exact (span ℝ A).sub_mem hx ((span ℝ A).smul_mem _ (subset_span hi))
    · have hz : ⟪(i : V), x⟫ = 0 := horth_span i hi hx
      simpa only [hz, mul_zero, zero_div, zero_smul, sub_zero] using hx
  have hbot : span ℝ A ≠ ⊥ := by
    intro hz
    have : a ∈ span ℝ A := subset_span ha
    rw [hz, mem_bot] at this
    exact hΦ.ne_zero haΦ this
  have htop := RootPairing.IsIrreducible.eq_top_of_invtSubmodule_reflection
    (P := hΦ.toRootPairing) (span ℝ A) hq hbot
  have hz : ⟪b, b⟫ = 0 := horth_span b hb (htop ▸ mem_top)
  exact hΦ.ne_zero hbΦ (inner_self_eq_zero.mp hz)

/-- `lem:pairing-construction`, steps `rpcirreducible` and `rpcconverse`, for
Definition 3.9 of [CGSS]: on a nonempty root set, Euclidean indecomposability is exactly
Mathlib's irreducibility. Nonemptiness is explicit, as in the blueprint. -/
theorem isIrreducible_iff (hne : Φ.Nonempty) :
    hΦ.toRootPairing.IsIrreducible ↔ hΦ.IsIndecomposable :=
  ⟨hΦ.isIndecomposable_of_isIrreducible hne, hΦ.isIrreducible_of_isIndecomposable⟩

end IsRootSet
