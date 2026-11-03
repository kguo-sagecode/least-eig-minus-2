/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Graphs.TriangleProperty

/-! # Isomorphism from the order in Section 2 of [CGSS] -/

namespace SimpleGraph

/-- The six parts in `lem:triangle-iso`, used in [CGSS, Lemma 2.10]. -/
inductive TriangleVertex (K N : Type*)
  | first
  | second
  | common (x : K)
  | left (x : K)
  | right (x : K)
  | remainder (w : N)
  deriving DecidableEq

/-- The edge rules of step 210preserve of `lem:triangle-iso` ([CGSS, Lemma 2.10]),
with a missed-set predicate on `N × K` and an adjacency relation on `N`. -/
def triangleRelation {K N : Type*} (A : N → K → Prop) (R : N → N → Prop) :
    TriangleVertex K N → TriangleVertex K N → Prop
  | .first, .common _ | .common _, .first | .first, .left _ | .left _, .first => True
  | .second, .common _ | .common _, .second | .second, .right _ | .right _, .second => True
  | .common x, .left y | .left x, .common y
  | .common x, .right y | .right x, .common y => x = y
  | .left x, .right y | .right x, .left y => x ≠ y
  | .common x, .remainder w | .remainder w, .common x => ¬A w x
  | .left x, .remainder w | .remainder w, .left x
  | .right x, .remainder w | .remainder w, .right x => A w x
  | .remainder w, .remainder z => R w z
  | _, _ => False

/-- Decidable edge rules for the coordinates in `lem:triangle-iso` ([CGSS, Lemma 2.10]). -/
instance decidableTriangleRelation {K N : Type*} [DecidableEq K]
    (A : N → K → Prop) (R : N → N → Prop) [∀ w x, Decidable (A w x)]
    [DecidableRel R] : DecidableRel (triangleRelation A R) := by
  intro p q
  cases p <;> cases q <;> dsimp only [triangleRelation] <;> infer_instance

/-- The six-part bijection of step 210extend of `lem:triangle-iso`
([CGSS, Lemma 2.10]), induced by the core and remainder label bijections. -/
def TriangleVertex.congr {K N K' N' : Type*} (b : K ≃ K') (c : N ≃ N') :
    TriangleVertex K N ≃ TriangleVertex K' N' where
  toFun
    | .first => .first
    | .second => .second
    | .common x => .common (b x)
    | .left x => .left (b x)
    | .right x => .right (b x)
    | .remainder w => .remainder (c w)
  invFun
    | .first => .first
    | .second => .second
    | .common x => .common (b.symm x)
    | .left x => .left (b.symm x)
    | .right x => .right (b.symm x)
    | .remainder w => .remainder (c.symm w)
  left_inv p := by cases p <;> simp
  right_inv p := by cases p <;> simp

/-- Step 210preserve of `lem:triangle-iso` ([CGSS, Lemma 2.10]): matching missed sets
and internal remainder edges preserves all six-part edge rules. -/
theorem TriangleVertex.congr_relation {K N K' N' : Type*} (b : K ≃ K') (c : N ≃ N')
    {A : N → K → Prop} {A' : N' → K' → Prop} {R : N → N → Prop} {R' : N' → N' → Prop}
    (hA : ∀ w x, A' (c w) (b x) ↔ A w x) (hR : ∀ w z, R' (c w) (c z) ↔ R w z)
    (p q : TriangleVertex K N) :
    triangleRelation A' R' (congr b c p) (congr b c q) ↔ triangleRelation A R p q := by
  cases p <;> cases q <;> simp [congr, triangleRelation, hA, hR]

namespace HasTriangleProperty


variable {U : Type*} {X : SimpleGraph U} (hX : X.HasTriangleProperty)
include hX

/-- The `M` label bijection with its domain ordered as `K`, for step 210extendcore
of `lem:triangle-iso` ([CGSS, Lemma 2.10]). -/
noncomputable def rightCommonNeighborsEquiv {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    X.commonNeighbors u v ≃ ↥(X.neighborSet v \ X.neighborSet u) :=
  (Equiv.subtypeEquivRight (fun _ ↦ and_comm)).trans
    (hX.commonNeighborsEquiv v u huv.symm (fun h ↦ hnav h.symm))

/-- The coordinate equivalence in step 210extendcore of `lem:triangle-iso`
([CGSS, Lemma 2.10]): the two endpoints, three labelled core parts, and `N`. -/
noncomputable def triangleVertexEquiv {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    TriangleVertex (X.commonNeighbors u v) (Xᶜ.commonNeighbors u v) ≃ U := by
  classical
  let l := hX.commonNeighborsEquiv u v huv hnav
  let m := hX.rightCommonNeighborsEquiv huv hnav
  -- 210coresamePart: the three labelled parts are independent.
  let f : TriangleVertex (X.commonNeighbors u v) (Xᶜ.commonNeighbors u v) → U
    | .first => u
    | .second => v
    | .common x => x
    | .left x => l x
    | .right x => m x
    | .remainder w => w
  let g (w : U) : TriangleVertex (X.commonNeighbors u v) (Xᶜ.commonNeighbors u v) :=
    if hwu : w = u then .first
    else if hwv : w = v then .second
    else if huw : X.Adj u w then
      if hvw : X.Adj v w then .common ⟨w, huw, hvw⟩
      else .left (l.symm ⟨w, huw, hvw⟩)
    else if hvw : X.Adj v w then .right (m.symm ⟨w, hvw, huw⟩)
    else .remainder ⟨w, ⟨Ne.symm hwu, huw⟩, ⟨Ne.symm hwv, hvw⟩⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro p
    cases p with
    | first => simp [f, g]
    | second => simp [f, g, huv.symm]
    | common x =>
      have hux : X.Adj u x := x.property.1
      have hvx : X.Adj v x := x.property.2
      simp [f, g, hux, hvx, hux.ne.symm, hvx.ne.symm]
    | left x =>
      have hrv : (l x : U) ≠ v := fun he ↦ hnav (he ▸ (l x).property.1)
      have hul : X.Adj u (l x) := (l x).property.1
      have hvl : ¬X.Adj v (l x) := (l x).property.2
      simp only [f, g, dite_eq_right hul.ne.symm, dite_eq_right hrv,
        dite_eq_left hul, dite_eq_right hvl,
        TriangleVertex.left.injEq]
      exact l.symm_apply_apply x
    | right x =>
      have hru : (m x : U) ≠ u := fun he ↦ hnav (he ▸ (m x).property.1.symm)
      have hvm : X.Adj v (m x) := (m x).property.1
      have hum : ¬X.Adj u (m x) := (m x).property.2
      simp only [f, g, dite_eq_right hru, dite_eq_right hvm.ne.symm,
        dite_eq_right hum, dite_eq_left hvm,
        TriangleVertex.right.injEq]
      exact m.symm_apply_apply x
    | remainder w => simp [f, g, w.property.1.1.symm, w.property.2.1.symm,
        w.property.1.2, w.property.2.2]
  · intro w
    dsimp only [g]
    split_ifs <;> simp_all only [f, Equiv.apply_symm_apply]

/-- Evaluation of the coordinate equivalence in step 210extendcore of `lem:triangle-iso`
([CGSS, Lemma 2.10]). -/
theorem triangleVertexEquiv_apply {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (p : TriangleVertex (X.commonNeighbors u v) (Xᶜ.commonNeighbors u v)) :
    hX.triangleVertexEquiv huv hnav p = match p with
      | .first => u
      | .second => v
      | .common x => (x : U)
      | .left x => hX.commonNeighborsEquiv u v huv hnav x
      | .right x => hX.rightCommonNeighborsEquiv huv hnav x
      | .remainder w => (w : U) := rfl

/-- Steps 210coreedges and 210mixededges of `lem:triangle-iso` ([CGSS, Lemma 2.10]):
the coordinate equivalence gives every adjacency by the six-part edge rules. -/
theorem triangleVertexEquiv_adj {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (p q : TriangleVertex (X.commonNeighbors u v) (Xᶜ.commonNeighbors u v)) :
    X.Adj (hX.triangleVertexEquiv huv hnav p) (hX.triangleVertexEquiv huv hnav q) ↔
      triangleRelation (fun (w : Xᶜ.commonNeighbors u v) (x : X.commonNeighbors u v) ↦
        ¬X.Adj w x) (fun (w z : Xᶜ.commonNeighbors u v) ↦ X.Adj w z) p q := by
  let l := hX.commonNeighborsEquiv u v huv hnav
  let m := hX.rightCommonNeighborsEquiv huv hnav
  have hkk (x y : X.commonNeighbors u v) : ¬X.Adj x y :=
    hX.not_adj_of_same_adjacency huv hnav ⟨x, x.property.1⟩ ⟨y, y.property.1⟩
      (iff_of_true x.property.2 y.property.2)
  have hll (x y : X.commonNeighbors u v) : ¬X.Adj (l x) (l y) :=
    hX.not_adj_of_same_adjacency huv hnav ⟨l x, (l x).property.1⟩ ⟨l y, (l y).property.1⟩
      (iff_of_false (l x).property.2 (l y).property.2)
  have hmm (x y : X.commonNeighbors u v) : ¬X.Adj (m x) (m y) :=
    hX.not_adj_of_same_adjacency huv.symm (fun ha ↦ hnav ha.symm)
      ⟨m x, (m x).property.1⟩ ⟨m y, (m y).property.1⟩
      (iff_of_false (m x).property.2 (m y).property.2)
  -- 210coreKL, 210coreKM and 210coreLM: equality or inequality of labels.
  have hkl (x y : X.commonNeighbors u v) : X.Adj x (l y) ↔ x = y :=
    hX.adj_commonNeighborsEquiv_iff huv hnav x y
  have hkm (x y : X.commonNeighbors u v) : X.Adj x (m y) ↔ x = y := by
    have h := hX.adj_commonNeighborsEquiv_iff huv.symm (fun ha ↦ hnav ha.symm)
      ⟨x, x.property.2, x.property.1⟩ ⟨y, y.property.2, y.property.1⟩
    exact h.trans ⟨fun he ↦ Subtype.ext
      (congrArg (fun t : X.commonNeighbors v u ↦ (t : U)) he), fun he ↦ by cases he; rfl⟩
  have hlm (x y : X.commonNeighbors u v) : X.Adj (l x) (m y) ↔ x ≠ y :=
    hX.adj_commonNeighborsEquiv_comm_iff huv hnav x y
  -- 210mixedK is the definition of a missed label; 210mixedL and 210mixedM
  -- identify the other two mixed adjacencies with membership in that same missed set.
  have hnl (w : Xᶜ.commonNeighbors u v) (x : X.commonNeighbors u v) :
      X.Adj w (l x) ↔ ¬X.Adj w x :=
    hX.adj_commonNeighborsEquiv_iff_not_adj huv hnav w.property.1.1.symm w.property.1.2 x
  have hnm (w : Xᶜ.commonNeighbors u v) (x : X.commonNeighbors u v) :
      X.Adj w (m x) ↔ ¬X.Adj w x :=
    hX.adj_commonNeighborsEquiv_iff_not_adj huv.symm (fun ha ↦ hnav ha.symm)
      w.property.2.1.symm w.property.2.2 ⟨x, x.property.2, x.property.1⟩
  -- 210coreuK, 210corevK, 210coreuL, 210corevL, 210coreuM and 210corevM.
  have huk (x : X.commonNeighbors u v) : X.Adj u x := x.property.1
  have hvk (x : X.commonNeighbors u v) : X.Adj v x := x.property.2
  have hul (x : X.commonNeighbors u v) : X.Adj u (l x) := (l x).property.1
  have hvl (x : X.commonNeighbors u v) : ¬X.Adj v (l x) := (l x).property.2
  have hum (x : X.commonNeighbors u v) : ¬X.Adj u (m x) := (m x).property.2
  have hvm (x : X.commonNeighbors u v) : X.Adj v (m x) := (m x).property.1
  -- 210mixeduv: the remainder misses both distinguished vertices.
  have hun (w : Xᶜ.commonNeighbors u v) : ¬X.Adj u w := w.property.1.2
  have hvn (w : Xᶜ.commonNeighbors u v) : ¬X.Adj v w := w.property.2.2
  simp only [l, m] at hll hmm hkl hkm hlm hnl hnm hul hvl hum hvm
  -- 210coreuv uses `hnav`; loops use irreflexivity. These and the preceding rules
  -- exhaust all pairs of the six coordinate constructors.
  cases p <;> cases q <;> simp only [triangleVertexEquiv_apply, triangleRelation]
    <;> change (X.Adj _ _ ↔ _)
    <;> first
      | simp only [hkk, hll, hmm, hkl, hkm, hlm, hnl, hnm,
          huk, hvk, hul, hvl, hum, hvm, hun, hvn, hnav, not_not, iff_self, X.irrefl]
      | skip
  all_goals try rw [X.adj_comm]
  all_goals simp only [hkl, hkm, hlm, hnl, hnm, huk, hvk, hul, hvl, hum, hvm, hun, hvn,
    hnav, eq_comm, ne_eq, iff_self]

variable {W : Type*} {Y : SimpleGraph W}

/-- Steps 210extend and 210preserve of `lem:triangle-iso` ([CGSS, Lemma 2.10]):
compatible bijections on `K` and `N` extend to an isomorphism of the whole graphs. -/
noncomputable def isoOfRemainderEquiv (hY : Y.HasTriangleProperty)
    {u v : U} {u' v' : W} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (huv' : u' ≠ v') (hnav' : ¬Y.Adj u' v')
    (b : X.commonNeighbors u v ≃ Y.commonNeighbors u' v')
    (c : Xᶜ.commonNeighbors u v ≃ Yᶜ.commonNeighbors u' v')
    (hA : ∀ w x, (¬Y.Adj (c w) (b x)) ↔ ¬X.Adj w x)
    (hR : ∀ w z, Y.Adj (c w) (c z) ↔ X.Adj w z) : X ≃g Y where
  toEquiv := (hX.triangleVertexEquiv huv hnav).symm.trans
    ((TriangleVertex.congr b c).trans (hY.triangleVertexEquiv huv' hnav'))
  map_rel_iff' := by
    intro x y
    obtain ⟨p, rfl⟩ := (hX.triangleVertexEquiv huv hnav).surjective x
    obtain ⟨q, rfl⟩ := (hX.triangleVertexEquiv huv hnav).surjective y
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [hY.triangleVertexEquiv_adj, hX.triangleVertexEquiv_adj]
    exact TriangleVertex.congr_relation b c hA hR p q

/-- Steps 210extendtwo–210internalfive of `lem:triangle-iso` ([CGSS, Lemma 2.10]):
any bijection on the common-neighbour labels extends to `N`, preserving missed sets
and the internal edges. -/
theorem exists_remainderEquiv [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    [DecidableRel X.Adj] [DecidableRel Y.Adj] (hY : Y.HasTriangleProperty)
    {u v : U} {u' v' : W} (F : hX.NormalForm u v) (F' : hY.NormalForm u' v')
    (b : X.commonNeighbors u v ≃ Y.commonNeighbors u' v') :
    ∃ c : Xᶜ.commonNeighbors u v ≃ Yᶜ.commonNeighbors u' v',
      (∀ w x, (¬Y.Adj (c w) (b x)) ↔ ¬X.Adj w x) ∧
      (∀ w z, Y.Adj (c w) (c z) ↔ X.Adj w z) := by
  classical
  -- 210internaledges: the following cases prove every edge rule inside `N`.
  have hk : (X.commonNeighbors u v).ncard = (Y.commonNeighbors u' v').ncard :=
    Set.ncard_congr' b
  have hkX := F.card_common
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.fintypeCard_eq_ncard] at hkX
  rcases hkX with htwo | hthree | hfive
  · -- 210extendtwo, 210mixedtwo, 210internaltwo.
    obtain ⟨w, hall, hmiss⟩ := F.two htwo
    obtain ⟨w', hall', hmiss'⟩ := F'.two (hk ▸ htwo)
    let c : Xᶜ.commonNeighbors u v ≃ Yᶜ.commonNeighbors u' v' :=
      ⟨fun _ ↦ w', fun _ ↦ w, fun z ↦ (hall z).symm, fun z ↦ (hall' z).symm⟩
    refine ⟨c, ?_, ?_⟩
    · intro z x
      simpa only [hall z, c, Equiv.coe_fn_mk] using iff_of_true (hmiss' (b x)) (hmiss x)
    · intro z t
      simp only [hall z, hall t]
      exact iff_of_false Y.irrefl X.irrefl
  · -- 210extendthree: centre and leaf labels give the remainder bijection.
    obtain ⟨w, e, hcenter, hleaf, hedge⟩ := F.three hthree
    obtain ⟨w', e', hcenter', hleaf', hedge'⟩ := F'.three (hk ▸ hthree)
    let f := (Equiv.optionCongr e).trans (Equiv.optionSubtypeNe w)
    let f' := (Equiv.optionCongr e').trans (Equiv.optionSubtypeNe w')
    let c := f.symm.trans ((Equiv.optionCongr b).trans f')
    have hc (a : Option (X.commonNeighbors u v)) : c (f a) = f' (a.map b) := by
      simp [c]
    have hcw : c w = w' := hc none
    refine ⟨c, ?_, ?_⟩
    · -- 210mixedthree, with 210mixedcentre and 210mixedleaf.
      intro z x
      obtain ⟨a, rfl⟩ := f.surjective z
      rw [hc]
      cases a with
      | none =>
        exact iff_of_false (not_not_intro (hcenter' (b x))) (not_not_intro (hcenter x))
      | some y =>
        change (¬Y.Adj (e' (b y)).val (b x)) ↔ ¬X.Adj (e y).val x
        rw [hleaf', hleaf, b.injective.eq_iff]
    · -- 210internalthree: the centre–leaf edge rule is preserved.
      intro z t
      rw [hedge', hedge, ← hcw]
      simp only [c.injective.eq_iff, ne_eq]
  · -- 210extendfive: transport the two-element subset labels along `b`.
    obtain ⟨e, he, hedge⟩ := F.five hfive
    obtain ⟨e', he', hedge'⟩ := F'.five (hk ▸ hfive)
    let b₂ : {s : Finset (X.commonNeighbors u v) // s.card = 2} ≃
        {s : Finset (Y.commonNeighbors u' v') // s.card = 2} :=
      (Equiv.finsetCongr b).subtypeEquiv (fun s ↦ by simp)
    let c := e.trans (b₂.trans e'.symm)
    have hc (z : Xᶜ.commonNeighbors u v) :
        (e' (c z)).val = (e z).val.map b.toEmbedding := by
      simp [c, b₂]
    refine ⟨c, ?_, ?_⟩
    · -- 210mixedfive: mapped missed sets preserve every mixed edge.
      intro z x
      rw [← mem_missedCommonNeighbors, ← he', hc, Finset.mem_map_equiv,
        b.symm_apply_apply, he, mem_missedCommonNeighbors]
    · -- 210internalfive: disjointness is preserved by an injective label map.
      intro z t
      rw [hedge', hedge, hc, hc, Finset.disjoint_map]

-- Lemma 2.10 (isomorphism from order)
/-- The isomorphism-from-order lemma `lem:triangle-iso`, used in [CGSS, Lemma 2.10]:
two finite triangle-property graphs with an edge and no universal vertex are isomorphic
whenever their orders agree. -/
theorem nonempty_iso_of_card_eq [Fintype U] [Fintype W]
    (hY : Y.HasTriangleProperty)
    (hedge : ∃ x y, X.Adj x y) (hedge' : ∃ x y, Y.Adj x y)
    (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    (hn' : ∀ x, ∃ y, y ≠ x ∧ ¬Y.Adj x y)
    (hcard : Fintype.card U = Fintype.card W) : Nonempty (X ≃g Y) := by
  classical
  -- 210pairs, 210formX, 210formY.
  obtain ⟨u, z, huz⟩ := hedge
  obtain ⟨u', z', huz'⟩ := hedge'
  have hedge : ∃ x y, X.Adj x y := ⟨u, z, huz⟩
  have hedge' : ∃ x y, Y.Adj x y := ⟨u', z', huz'⟩
  obtain ⟨v, hvu, hnav⟩ := hn u
  obtain ⟨v', hvu', hnav'⟩ := hn' u'
  have F := hX.normal_form_of_not_forall_adj hedge hn hvu.symm hnav
  have F' := hY.normal_form_of_not_forall_adj hedge' hn' hvu'.symm hnav'
  -- 210samek: cancel the common order `6k-3` before choosing the core labels.
  have hkX := hX.card_add_three_eq_six_mul hedge hn hvu.symm hnav
  have hkY := hY.card_add_three_eq_six_mul hedge' hn' hvu'.symm hnav'
  have hk : Fintype.card (X.commonNeighbors u v) =
      Fintype.card (Y.commonNeighbors u' v') := by omega
  let b := Fintype.equivOfCardEq hk
  -- 210iso: extend the labels and use the exhaustive adjacency rules.
  obtain ⟨c, hA, hR⟩ := hX.exists_remainderEquiv hY F F' b
  exact ⟨hX.isoOfRemainderEquiv hY F.ne F.not_adj F'.ne F'.not_adj b c hA hR⟩

end HasTriangleProperty
end SimpleGraph
