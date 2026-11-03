/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Hyp24

/-!
# Transport of model properties through root isomorphisms

Only preservation of Gram matrices is needed; the ambient dimensions may differ.
-/

open scoped RealInnerProductSpace

namespace LineSystem.Iso

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {S : LineSystem V} {T : LineSystem W} (e : S.Iso T)

include e

/-- Indecomposability is invariant under a root isomorphism. -/
theorem isIndecomposable (hT : T.IsIndecomposable) : S.IsIndecomposable := by
  intro P Q hPQ ho
  let R : Set W := {y | ∃ r : S.Φ, (r : V) ∈ P ∧ (e.toEquiv r : W) = y}
  let U : Set W := {y | ∃ r : S.Φ, (r : V) ∈ Q ∧ (e.toEquiv r : W) = y}
  have hRU : R ∪ U = T.Φ := by
    ext y
    constructor
    · rintro (⟨r, _, rfl⟩ | ⟨r, _, rfl⟩) <;> exact (e.toEquiv r).property
    · intro hy
      obtain ⟨r, hr⟩ := e.toEquiv.surjective ⟨y, hy⟩
      have hm : (r : V) ∈ P ∪ Q := by rw [hPQ]; exact r.property
      rcases hm with hp | hq
      · exact Or.inl ⟨r, hp, congrArg Subtype.val hr⟩
      · exact Or.inr ⟨r, hq, congrArg Subtype.val hr⟩
  have horth : ∀ r ∈ R, ∀ u ∈ U, ⟪r, u⟫ = 0 := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    rw [e.inner_map]
    exact ho r hr s hs
  rcases hT R U hRU horth with hR | hU
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hm : r ∈ S.Φ := hPQ ▸ Or.inl hr
    have he : (e.toEquiv ⟨r, hm⟩ : W) ∈ R := ⟨⟨r, hm⟩, hr, rfl⟩
    simp [hR] at he
  · right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hm : r ∈ S.Φ := hPQ ▸ Or.inr hr
    have he : (e.toEquiv ⟨r, hm⟩ : W) ∈ U := ⟨⟨r, hm⟩, hr, rfl⟩
    simp [hU] at he

/-- Star-closure is invariant under a Gram-preserving root bijection. -/
theorem isStarClosed (hT : T.IsStarClosed) : S.IsStarClosed := by
  intro r hr s hs hrs
  let r' : S.Φ := ⟨r, hr⟩
  let s' : S.Φ := ⟨s, hs⟩
  have ht : (e.toEquiv r' : W) + e.toEquiv s' ∈ T.Φ :=
    hT _ (e.toEquiv r').property _ (e.toEquiv s').property
      ((e.inner_map r' s').trans hrs)
  let d : S.Φ := e.toEquiv.symm ⟨_, ht⟩
  have he : (e.toEquiv d : W) = (e.toEquiv r' : W) + e.toEquiv s' :=
    congrArg Subtype.val (e.toEquiv.apply_symm_apply ⟨_, ht⟩)
  have hdr : ⟪(d : V), r⟫ = 1 := by
    change ⟪(d : V), (r' : V)⟫ = 1
    rw [← e.inner_map, he, inner_add_left, T.inner_self _ (e.toEquiv r').property,
      e.inner_map s' r']
    change 2 + ⟪s, r⟫ = 1
    rw [real_inner_comm]
    linarith
  have hds : ⟪(d : V), s⟫ = 1 := by
    change ⟪(d : V), (s' : V)⟫ = 1
    rw [← e.inner_map, he, inner_add_left, e.inner_map,
      T.inner_self _ (e.toEquiv s').property]
    change ⟪r, s⟫ + 2 = 1
    linarith
  have hz : ⟪(d : V) - (r + s), (d : V) - (r + s)⟫ = 0 := by
    have hrd : ⟪r, (d : V)⟫ = 1 := by rw [real_inner_comm]; exact hdr
    have hsd : ⟪s, (d : V)⟫ = 1 := by rw [real_inner_comm]; exact hds
    have hsr : ⟪s, r⟫ = -1 := by rw [real_inner_comm]; exact hrs
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      S.inner_self _ d.property, S.inner_self r hr, S.inner_self s hs, hdr, hds,
      hrd, hsd, hsr, hrs]
    norm_num
  have hd : (d : V) = r + s := sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  exact hd ▸ d.property

end LineSystem.Iso
