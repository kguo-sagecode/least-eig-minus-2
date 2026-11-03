/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.TypeDPairs
import LineGraphs.Representation.GeneralizedRepresentation

/-!
# The normal form for representations in type D

Lemma `lem:4-Dnform` and the recognition direction of Theorem 4.2 of [CGSS].
-/

open scoped RealInnerProductSpace
open EuclideanSpace

namespace EuclideanSpace

/-- Lemma `lem:4-Dnform`, step `s42flip`, for Theorem 4.2 of [CGSS]: change
the signs of the chosen coordinates. -/
noncomputable def signChange {ι : Type*} [Fintype ι] (b : ι → Bool) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i ↦
    if b i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

/-- Lemma `lem:4-Dnform`, step `s42flip`, for Theorem 4.2 of [CGSS]: the
coordinate formula for the diagonal sign change. -/
theorem signChange_apply {ι : Type*} [Fintype ι] (b : ι → Bool)
    (z : EuclideanSpace ℝ ι) (i : ι) :
    signChange b z i = if b i then -z i else z i := by
  change (if b i then LinearIsometryEquiv.neg ℝ else
    LinearIsometryEquiv.refl ℝ ℝ) (z i) = _
  split_ifs <;> rfl

/-- Lemma `lem:4-Dnform`, step `s42flip`, for Theorem 4.2 of [CGSS]: sign
changes preserve the coordinate root model, including dimensions below four. -/
theorem signChange_mem_Dn {n : ℕ} (b : Fin n → Bool) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ (LineSystem.Dn n).Φ) : signChange b z ∈ (LineSystem.Dn n).Φ := by
  obtain ⟨i, j, s, t, hij, rfl⟩ := LineSystem.Dn.mem_iff_exists_signed_single.mp hz
  refine LineSystem.Dn.mem_iff_exists_signed_single.mpr
    ⟨i, j, xor (b i) s, xor (b j) t, hij, ?_⟩
  ext k
  rw [signChange_apply]
  by_cases hki : k = i
  · subst k
    cases b i <;> cases s <;> simp [LineSystem.rootSign, hij]
  · by_cases hkj : k = j
    · subst k
      cases b j <;> cases t <;> simp [LineSystem.rootSign, hij.symm]
    · simp [hki, hkj]

end EuclideanSpace

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {X : SimpleGraph V} [DecidableRel X.Adj]
  {n : ℕ} {x : V → EuclideanSpace ℝ (Fin n)}

/-- Lemma `lem:4-Dnform`, step `s42onesign`, for Theorem 4.2 of [CGSS]: the
petals are exactly the coordinates occurring with both signs. -/
def representationPetals (x : V → EuclideanSpace ℝ (Fin n)) : Set (Fin n) :=
  {p | (∃ u, x u p = 1) ∧ ∃ v, x v p = -1}

/-- Lemma `lem:4-Dnform`, step `s42centre`, for Theorem 4.2 of [CGSS]:
the common coordinate of an opposite-sign pair is not a petal. -/
theorem IsRepresentation.not_mem_representationPetals_of_pair (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) {u v : V} {c p : Fin n} {b : Bool}
    (hcp : c ≠ p)
    (hu : x u = single c (LineSystem.rootSign b : ℝ) + single p 1)
    (hv : x v = single c (LineSystem.rootSign b : ℝ) - single p 1) :
    c ∉ representationPetals x := by
  have huv : u ≠ v := by
    intro h
    have he := congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ z p) (hu.symm.trans (h ▸ hv))
    norm_num [hcp.symm] at he
  have huc : x u c = (LineSystem.rootSign b : ℝ) := by simp [hu, hcp]
  have hvc : x v c = (LineSystem.rootSign b : ℝ) := by simp [hv, hcp]
  rintro ⟨⟨w, hw⟩, ⟨z, hz⟩⟩
  cases b with
  | false =>
    norm_num [LineSystem.rootSign] at huc hvc
    obtain ⟨d, s, _, huf, hzf⟩ := hx.exists_pair_of_opposite_coordinates hm huc hz
    have hvne : x v c ≠ 0 := by rw [hvc]; norm_num
    rcases hx.eq_or_eq_of_petal_ne_zero hm huf hzf (Or.inl rfl) hvne with h | h
    · exact huv h.symm
    · rw [h, hz] at hvc
      norm_num at hvc
  | true =>
    norm_num [LineSystem.rootSign] at huc hvc
    obtain ⟨d, s, _, hwf, huf⟩ := hx.exists_pair_of_opposite_coordinates hm hw huc
    have hvne : x v c ≠ 0 := by rw [hvc]; norm_num
    rcases hx.eq_or_eq_of_petal_ne_zero hm hwf huf (Or.inl rfl) hvne with h | h
    · rw [h, hw] at hvc
      norm_num at hvc
    · exact huv h.symm

/-- Lemma `lem:4-Dnform`, steps `s42onesign`--`s42flip`, for Theorem 4.2 of
[CGSS]: a diagonal sign change makes every non-petal coefficient nonnegative,
and leaves every petal coordinate fixed. -/
theorem IsRepresentation.exists_signChange_nonneg (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) :
    ∃ b : Fin n → Bool,
      (∀ p ∈ representationPetals x, b p = false) ∧
      (∀ u i, i ∉ representationPetals x → 0 ≤ signChange b (x u) i) ∧
      X.IsRepresentation (fun u ↦ signChange b (x u)) ∧
      (∀ u, signChange b (x u) ∈ (LineSystem.Dn n).Φ) := by
  classical
  let b : Fin n → Bool := fun i ↦ decide (i ∉ representationPetals x ∧ ∃ u, x u i = -1)
  refine ⟨b, ?_, ?_, ?_, fun u ↦ signChange_mem_Dn b (hm u)⟩
  · intro p hp
    simp [b, hp]
  · intro u i hi
    rw [signChange_apply]
    rcases LineSystem.Dn.apply_eq_zero_or_one_or_neg_one (hm u) i with h | h | h
    · simp [h]
    · have hn : ¬ ∃ v, x v i = -1 := fun hv ↦ hi ⟨⟨u, h⟩, hv⟩
      simp [b, hn, h]
    · have hn : ∃ v, x v i = -1 := ⟨u, h⟩
      simp [b, hi, hn, h]
  · apply isRepresentation_iff.mpr
    intro u v
    rw [(signChange b).inner_map_map]
    exact isRepresentation_iff.mp hx u v

omit [DecidableEq V] in
/-- Lemma `lem:4-Dnform`, step `s42flip`, for Theorem 4.2 of [CGSS]:
the normalization leaves the set of petal coordinates unchanged. -/
theorem representationPetals_signChange {b : Fin n → Bool}
    (hb : ∀ p ∈ representationPetals x, b p = false)
    (hn : ∀ u i, i ∉ representationPetals x → 0 ≤ signChange b (x u) i) :
    representationPetals (fun u ↦ signChange b (x u)) = representationPetals x := by
  ext p
  by_cases hp : p ∈ representationPetals x
  · obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hp
    simp only [representationPetals, Set.mem_ofPred_eq]
    exact ⟨fun _ ↦ ⟨⟨u, hu⟩, v, hv⟩,
      fun _ ↦ ⟨⟨u, by simp [signChange_apply, hb p ⟨⟨u, hu⟩, v, hv⟩, hu]⟩,
        v, by simp [signChange_apply, hb p ⟨⟨u, hu⟩, v, hv⟩, hv]⟩⟩
  · constructor
    · rintro ⟨_, v, hv⟩
      have := hn v p hp
      linarith
    · exact fun h ↦ (hp h).elim

/-- Lemma `lem:4-Dnform`, steps `s42centre`--`s42two`, for Theorem 4.2 of
[CGSS]: after normalization each petal has a centre outside the petal set, both
signs occur, and every remaining root joins two centres. -/
theorem IsRepresentation.exists_center_map (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ)
    (hn : ∀ u i, i ∉ representationPetals x → 0 ≤ x u i) :
    ∃ c : representationPetals x → ↥((representationPetals x)ᶜ),
      (∀ p, ∀ b : Bool, ∃ u,
        x u = single (c p).val 1 + single p.val (LineSystem.rootSign b : ℝ)) ∧
      (∀ u, (∃ i j : ↥((representationPetals x)ᶜ), i ≠ j ∧
        x u = single i.val 1 + single j.val 1) ∨
        ∃ (p : representationPetals x) (b : Bool),
          x u = single (c p).val 1 + single p.val (LineSystem.rootSign b : ℝ)) := by
  classical
  have hc (p : representationPetals x) : ∃ c : ↥((representationPetals x)ᶜ),
      ∀ b : Bool, ∃ u,
        x u = single c.val 1 + single p.val (LineSystem.rootSign b : ℝ) := by
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := p.property
    obtain ⟨c, b, hcp, huf, hvf⟩ := hx.exists_pair_of_opposite_coordinates hm hu hv
    have hc := hx.not_mem_representationPetals_of_pair hm hcp huf hvf
    have hb : b = false := by
      cases b
      · rfl
      · have h := hn u c hc
        norm_num [huf, LineSystem.rootSign, hcp] at h
    subst b
    refine ⟨⟨c, hc⟩, ?_⟩
    intro b
    cases b
    · exact ⟨u, by simpa [LineSystem.rootSign] using huf⟩
    · refine ⟨v, ?_⟩
      simpa [LineSystem.rootSign, sub_eq_add_neg, ← PiLp.single_neg] using hvf
  choose c hc using hc
  refine ⟨c, hc, ?_⟩
  intro u
  by_cases hp : ∃ p : representationPetals x, x u p.val ≠ 0
  · obtain ⟨p, hp⟩ := hp
    obtain ⟨v, hv⟩ := hc p false
    obtain ⟨w, hw⟩ := hc p true
    have hw' : x w = single (c p).val 1 - single p.val 1 := by
      simpa [LineSystem.rootSign, sub_eq_add_neg, ← PiLp.single_neg] using hw
    have hv' : x v = single (c p).val 1 + single p.val 1 := by
      simpa [LineSystem.rootSign] using hv
    rcases hx.eq_or_eq_of_petal_ne_zero hm hv' hw' (Or.inl rfl) hp with rfl | rfl
    · exact Or.inr ⟨p, false, hv⟩
    · exact Or.inr ⟨p, true, hw⟩
  · obtain ⟨i, j, b, d, hij, hform⟩ := LineSystem.Dn.mem_iff_exists_signed_single.mp (hm u)
    have hi : i ∉ representationPetals x := by
      intro hi
      apply hp
      refine ⟨⟨i, hi⟩, ?_⟩
      cases b <;> simp [hform, LineSystem.rootSign, hij]
    have hj : j ∉ representationPetals x := by
      intro hj
      apply hp
      refine ⟨⟨j, hj⟩, ?_⟩
      cases d <;> simp [hform, LineSystem.rootSign, hij.symm]
    have hb : b = false := by
      cases b
      · rfl
      · have h := hn u i hi
        norm_num [hform, LineSystem.rootSign, hij] at h
    have hd : d = false := by
      cases d
      · rfl
      · have h := hn u j hj
        norm_num [hform, LineSystem.rootSign, hij.symm] at h
    exact Or.inl ⟨⟨i, hi⟩, ⟨j, hj⟩, fun h ↦ hij (congrArg Subtype.val h),
      by simpa [hb, hd, LineSystem.rootSign] using hform⟩

/-- Lemma `lem:4-Dnform`, step `s42petals`, for Theorem 4.2 of [CGSS]: split
the coordinate labels into centres and petals. -/
def generalizedLineGraphCoordinateEquiv {I : Type*} (a : I → ℕ) :
    ((i : I) × Fin (a i + 1)) ≃ I ⊕ ((i : I) × Fin (a i)) where
  toFun z := (finSuccEquiv (a z.1) z.2).elim (.inl z.1) (fun k ↦ .inr ⟨z.1, k⟩)
  invFun
    | .inl i => ⟨i, 0⟩
    | .inr ⟨i, k⟩ => ⟨i, k.succ⟩
  left_inv := by
    rintro ⟨i, k⟩
    refine Fin.cases ?_ (fun k ↦ ?_) k <;> simp
  right_inv := by
    rintro (i | ⟨i, k⟩) <;> simp

/-- Lemma `lem:4-Dnform`, step `s42petals`, for Theorem 4.2 of [CGSS]:
enumerate the fibres of the petal-to-centre map, keeping all unused coordinates
as centres. The resulting equivalence is the partition of all `n` coordinates. -/
theorem exists_coordinate_partition {n : ℕ} (P : Set (Fin n))
    (c : P → ↥(Pᶜ)) :
    ∃ (m : ℕ) (a : Fin m → ℕ) (eC : Fin m ≃ ↥(Pᶜ))
      (eP : ((i : Fin m) × Fin (a i)) ≃ P)
      (q : ((i : Fin m) × Fin (a i + 1)) ≃ Fin n),
      (∀ i, q ⟨i, 0⟩ = (eC i).val) ∧
      (∀ p, q ⟨p.1, p.2.succ⟩ = (eP p).val) ∧
      (∀ p, c (eP p) = eC p.1) := by
  classical
  let m := Fintype.card ↥(Pᶜ)
  let eC : Fin m ≃ ↥(Pᶜ) := (Fintype.equivFin _).symm
  let f : P → Fin m := fun p ↦ eC.symm (c p)
  let a : Fin m → ℕ := fun i ↦ Fintype.card {p // f p = i}
  let eP : ((i : Fin m) × Fin (a i)) ≃ P :=
    (Equiv.sigmaCongrRight fun i ↦ (Fintype.equivFin {p // f p = i}).symm).trans
      (Equiv.sigmaFiberEquiv f)
  let q : ((i : Fin m) × Fin (a i + 1)) ≃ Fin n :=
    (generalizedLineGraphCoordinateEquiv a).trans
      ((Equiv.sumCongr eC eP).trans ((Equiv.sumComm _ _).trans (Equiv.Set.sumCompl P)))
  refine ⟨m, a, eC, eP, q, ?_, ?_, ?_⟩
  · intro i
    simp [q, generalizedLineGraphCoordinateEquiv]
  · rintro ⟨i, k⟩
    simp [q, generalizedLineGraphCoordinateEquiv]
  · rintro ⟨i, k⟩
    have h := ((Fintype.equivFin {p // f p = i}).symm k).property
    exact eC.symm.injective (by simpa [eP, f] using h)

section RangeIso

variable {W E : Type*} [DecidableEq W] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Y : SimpleGraph W} [DecidableRel Y.Adj] {r : V → E} {s : W → E}

/-- Lemma `lem:4-Dnform`, step `s42three`, for Theorem 4.2 of [CGSS]: two
representations with the same vectors induce an isomorphism matching the vectors. -/
theorem IsRepresentation.exists_iso_of_range_eq (hr : X.IsRepresentation r)
    (hs : Y.IsRepresentation s) (h : Set.range r = Set.range s) :
    ∃ e : X ≃g Y, ∀ u, s (e u) = r u := by
  classical
  have hf (u : V) : ∃ v, s v = r u := by
    change r u ∈ Set.range s
    rw [← h]
    exact Set.mem_range_self u
  choose f hf using hf
  have hi : Function.Injective f := by
    intro u v huv
    apply hr.injective
    rw [← hf u, ← hf v, huv]
  have ho : Function.Surjective f := by
    intro v
    have hv : s v ∈ Set.range r := by rw [h]; exact Set.mem_range_self v
    obtain ⟨u, hu⟩ := hv
    exact ⟨u, hs.injective ((hf u).trans hu)⟩
  refine ⟨{ toEquiv := Equiv.ofBijective f ⟨hi, ho⟩, map_rel_iff' := ?_ }, hf⟩
  intro u v
  change Y.Adj (f u) (f v) ↔ X.Adj u v
  rw [hs.adj_iff, hr.adj_iff, hf u, hf v]

end RangeIso

/-- Lemma `lem:4-Dnform`, steps `s42petals`--`s42three`, for Theorem 4.2 of
[CGSS]: enumerate the normalized roots as the canonical representation of a
generalized line graph, retaining the bijection of all coordinate labels. -/
theorem IsRepresentation.exists_generalizedLineGraph_normal_form
    (hx : X.IsRepresentation x) (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ)
    (hn : ∀ u i, i ∉ representationPetals x → 0 ≤ x u i) :
    ∃ (m : ℕ) (a : Fin m → ℕ)
      (q : ((i : Fin m) × Fin (a i + 1)) ≃ Fin n)
      (Y : SimpleGraph (Fin m)) (e : X ≃g generalizedLineGraph Y a),
      (∀ u, x u = LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ q
        (Y.generalizedLineGraphVector a (e u))) ∧
      Set.range (fun i ↦ q ⟨i, 0⟩) = (representationPetals x)ᶜ := by
  classical
  obtain ⟨c, hc, hform⟩ := hx.exists_center_map hm hn
  obtain ⟨m, a, eC, eP, q, hqC, hqP, hcP⟩ :=
    exists_coordinate_partition (representationPetals x) c
  let Y : SimpleGraph (Fin m) :=
    { Adj i j := i ≠ j ∧ ∃ u, x u = single (eC i).val 1 + single (eC j).val 1
      symm.symm := by
        rintro i j ⟨hij, u, hu⟩
        exact ⟨hij.symm, u, hu.trans (add_comm _ _)⟩
      loopless.irrefl := fun _ h ↦ h.1 rfl }
  let g := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ q
  let z := fun v ↦ g (Y.generalizedLineGraphVector a v)
  have hz : (generalizedLineGraph Y a).IsRepresentation z := by
    apply isRepresentation_iff.mpr
    intro u v
    rw [g.inner_map_map]
    exact isRepresentation_iff.mp (Y.generalizedLineGraph_isRepresentation a) u v
  have hzE (i j : Fin m) (hij : Y.Adj i j) :
      z (.inl ⟨s(i, j), hij⟩) = single (eC i).val 1 + single (eC j).val 1 := by
    change g (single ⟨i, 0⟩ 1 + single ⟨j, 0⟩ 1) = _
    simp only [map_add, g, EuclideanSpace.piLpCongrLeft_single, hqC]
  have hzP (p : (i : Fin m) × Fin (a i)) (b : Bool) :
      z (.inr ⟨p.1, p.2, b⟩) =
        single (eC p.1).val 1 + single (eP p).val (LineSystem.rootSign b : ℝ) := by
    change g (single ⟨p.1, 0⟩ 1 + single ⟨p.1, p.2.succ⟩ (if b then -1 else 1)) = _
    simp only [map_add, g, EuclideanSpace.piLpCongrLeft_single, hqC, hqP]
    cases b <;> simp [LineSystem.rootSign]
  have hrange : Set.range x = Set.range z := by
    apply Set.Subset.antisymm
    · rintro _ ⟨u, rfl⟩
      rcases hform u with ⟨i, j, hij, hu⟩ | ⟨p, b, hu⟩
      · let i' := eC.symm i
        let j' := eC.symm j
        have h' : Y.Adj i' j' := by
          refine ⟨eC.symm.injective.ne hij, u, ?_⟩
          simpa [i', j'] using hu
        refine ⟨.inl ⟨s(i', j'), h'⟩, ?_⟩
        simpa [i', j', hu] using hzE i' j' h'
      · let p' := eP.symm p
        refine ⟨.inr ⟨p'.1, p'.2, b⟩, ?_⟩
        rw [hzP, ← hcP, eP.apply_symm_apply, hu]
    · rintro _ ⟨v, rfl⟩
      rcases v with ⟨⟨i, j⟩, hij⟩ | ⟨i, k, b⟩
      · obtain ⟨u, hu⟩ := hij.2
        exact ⟨u, hu.trans (hzE i j hij).symm⟩
      · obtain ⟨u, hu⟩ := hc (eP ⟨i, k⟩) b
        refine ⟨u, ?_⟩
        rw [hzP ⟨i, k⟩ b, hu, hcP]
  obtain ⟨e, he⟩ := hx.exists_iso_of_range_eq hz hrange
  refine ⟨m, a, q, Y, e, fun u ↦ (he u).symm, ?_⟩
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    change q ⟨j, 0⟩ ∈ (representationPetals x)ᶜ
    rw [hqC]
    exact (eC j).property
  · intro hi
    exact ⟨eC.symm ⟨i, hi⟩, by simp [hqC]⟩

/-- Lemma `lem:4-Dnform`, used in Theorem 4.2 of [CGSS]: a sign change and
a partition of all coordinates identify the given family with the canonical
generalized-line-graph representation. The centres are exactly the non-petals;
successor labels enumerate their petals. This includes the coordinate count. -/
theorem IsRepresentation.exists_normal_form_Dn (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) (_hn : 1 ≤ n) :
    ∃ (m : ℕ) (a : Fin m → ℕ)
      (q : ((i : Fin m) × Fin (a i + 1)) ≃ Fin n) (b : Fin n → Bool)
      (Y : SimpleGraph (Fin m)) (e : X ≃g generalizedLineGraph Y a),
      (∀ u, signChange b (x u) = LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ q
        (Y.generalizedLineGraphVector a (e u))) ∧
      Set.range (fun i ↦ q ⟨i, 0⟩) = (representationPetals x)ᶜ ∧
      (∀ p ∈ representationPetals x, b p = false) ∧
      X.IsRepresentation (fun u ↦ signChange b (x u)) ∧
      (∀ u, signChange b (x u) ∈ (LineSystem.Dn n).Φ) ∧
      (∑ i, (1 + a i)) = n := by
  obtain ⟨b, hb, hn, hy, hm'⟩ := hx.exists_signChange_nonneg hm
  have hP := representationPetals_signChange hb hn
  obtain ⟨m, a, q, Y, e, he, hC⟩ := hy.exists_generalizedLineGraph_normal_form hm'
    (fun u i hi ↦ hn u i (by rwa [hP] at hi))
  refine ⟨m, a, q, b, Y, e, he, hC.trans (congrArg Compl.compl hP), hb, hy, hm', ?_⟩
  have hcard := Fintype.card_congr q
  simpa [Fintype.card_sigma, Nat.add_comm] using hcard

/-- Theorem 4.2 of [CGSS], with `n ≥ 1` as in the blueprint: a graph is
represented in `Dₙ` exactly when it is a generalized line graph whose centre
and petal coordinates total `n`. The dimension equality retains the information
from `lem:4-Dnform`; unused coordinates are isolated centres with no petals. -/
theorem isRepresentedIn_Dn_iff (n : ℕ) (hn : 1 ≤ n) :
    X.IsRepresentedIn (LineSystem.Dn n) ↔
      ∃ (m : ℕ) (Y : SimpleGraph (Fin m)) (a : Fin m → ℕ),
        (∑ i, (1 + a i)) = n ∧ Nonempty (X ≃g generalizedLineGraph Y a) := by
  constructor
  · rintro ⟨x, hx, hm⟩
    obtain ⟨m, a, _, _, Y, e, _, _, _, _, _, hcard⟩ := hx.exists_normal_form_Dn hm hn
    exact ⟨m, Y, a, hcard, ⟨e⟩⟩
  · rintro ⟨m, Y, a, hcard, ⟨e⟩⟩
    subst n
    exact (Y.generalizedLineGraph_isRepresentedIn_Dn a).comp_iso e

/-- Theorem 4.2, assertion 1, of [CGSS]: the recognition implication after
forgetting the coordinate count. -/
theorem IsRepresentedIn.isGeneralizedLineGraph_of_Dn (hX : X.IsRepresentedIn (LineSystem.Dn n))
    (hn : 1 ≤ n) : X.IsGeneralizedLineGraph := by
  obtain ⟨m, Y, a, _, he⟩ := (isRepresentedIn_Dn_iff n hn).mp hX
  exact ⟨m, Y, a, he⟩

end SimpleGraph
