/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.OrthGraphReconstruction
import LineGraphs.LineSystem.OrthGraphCases
import LineGraphs.LineSystem.Models

/-! # Explicit Section 3 inputs and the one-line case of [CGSS, Theorem 2.13]

The model facts below are hypotheses, as required by Gap 4. This file does not use a
classification theorem from Section 3 to prove any Section 2 result.
-/

open scoped RealInnerProductSpace
open Submodule Module

/-- Step 213Echoose of `thm:2.13` ([CGSS, Theorem 2.13]): positive regular degree
below the order minus one supplies an edge and excludes universal vertices. -/
theorem SimpleGraph.IsSRGWith.exists_edge_and_forall_exists_not_adj
    {U : Type*} [Fintype U] {X : SimpleGraph U} [DecidableRel X.Adj] {n d a b : ℕ}
    (h : X.IsSRGWith n d a b) (hd : 0 < d) (hlt : d + 1 < n) :
      (∃ x y, X.Adj x y) ∧ ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y := by
  classical
  have hpos : 0 < Fintype.card U := by rw [h.card]; omega
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
  have hx : 0 < X.degree x := by rw [h.regular.degree_eq]; exact hd
  obtain ⟨y, hxy⟩ := (X.degree_pos_iff_exists_adj x).mp hx
  refine ⟨⟨x, y, hxy⟩, ?_⟩
  intro z
  by_contra! hz
  have hu : X.IsUniversal z := by intro w hzw; exact hz w hzw.symm
  have he := (SimpleGraph.degree_eq_card_sub_one X z).mpr hu
  rw [h.regular.degree_eq, h.card] at he
  omega

namespace LineSystem

/-- The table `input:sec3-models` used in [CGSS, Theorem 2.13], taken as hypotheses.
Each marked `Hyp24` includes the required star-closure and indecomposability. The ranks
are dimensions of root spans; the exceptional `Δ` entries count lines, not signed roots. -/
structure ModelInputs : Prop where
  /-- The model `A₁` is one antipodal pair. -/
  an_one : ∃ r ∈ (An 1).Φ, (An 1).Φ = {r, -r}
  /-- The ranks in the A row of the table. -/
  an_rank : ∀ n, 1 ≤ n → finrank ℝ (span ℝ (An n).Φ) = n
  /-- The line counts in the A row of the table. -/
  an_lines : ∀ n, 1 ≤ n → (An n).numLines = n * (n + 1) / 2
  /-- The specified empty marked-star graph in the A row. -/
  an_star : ∀ n, 2 ≤ n → ∃ H : Hyp24 (EuclideanSpace ℝ (Fin (n + 1))),
    H.S = An n ∧ Nonempty (H.orthGraph ≃g (⊥ : SimpleGraph (Fin (n - 2))))
  /-- The ranks in the D row of the table. -/
  dn_rank : ∀ n, 4 ≤ n → finrank ℝ (span ℝ (Dn n).Φ) = n
  /-- The line counts in the D row of the table. -/
  dn_lines : ∀ n, 4 ≤ n → (Dn n).numLines = n * (n - 1)
  /-- The specified friendship marked-star graph in the D row. -/
  dn_star : ∀ n, 4 ≤ n → ∃ H : Hyp24 (EuclideanSpace ℝ (Fin n)),
    H.S = Dn n ∧ Nonempty (H.orthGraph ≃g SimpleGraph.friendship (n - 3))
  /-- The rank, line count, marked graph and `Δ` data for `E₈`. -/
  e₈ : ∃ H : Hyp24 (EuclideanSpace ℝ (Fin 8)), H.S = E₈ ∧
    finrank ℝ (span ℝ E₈.Φ) = 8 ∧ E₈.numLines = 120 ∧
    H.orthGraph.IsSRGWith 27 10 1 5 ∧ H.Δ.ncard / 2 = 36
  /-- The rank, line count, marked graph and `Δ` data for `E₇`. -/
  e₇ : ∃ H : Hyp24 (EuclideanSpace ℝ (Fin 8)), H.S = E₇ ∧
    finrank ℝ (span ℝ E₇.Φ) = 7 ∧ E₇.numLines = 63 ∧
    H.orthGraph.IsSRGWith 15 6 1 3 ∧ H.Δ.ncard / 2 = 15
  /-- The rank, line count, marked graph and `Δ` data for `E₆`. -/
  e₆ : ∃ H : Hyp24 (EuclideanSpace ℝ (Fin 8)), H.S = E₆ ∧
    finrank ℝ (span ℝ E₆.Φ) = 6 ∧ E₆.numLines = 36 ∧
    H.orthGraph.IsSRGWith 9 4 1 2 ∧ H.Δ.ncard / 2 = 6

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Step 213rankone of `thm:2.13` ([CGSS, Theorem 2.13]): a root of squared norm two
is different from its negative. -/
theorem ne_neg_of_mem (S : LineSystem V) {r : V} (hr : r ∈ S.Φ) : r ≠ -r := by
  intro he
  have h := congrArg (fun x ↦ ⟪r, x⟫) he
  rw [S.inner_self r hr, inner_neg_right, S.inner_self r hr] at h
  norm_num at h

/-- Step 213rankone of `thm:2.13` ([CGSS, Theorem 2.13]): a single antipodal pair
has rank one and is one line. -/
theorem finrank_span_numLines_of_eq_pair (S : LineSystem V) {r : V} (hr : r ∈ S.Φ)
    (hΦ : S.Φ = {r, -r}) : finrank ℝ (span ℝ S.Φ) = 1 ∧ S.numLines = 1 := by
  have hr0 : r ≠ 0 := by
    intro he
    have h := S.inner_self r hr
    simp [he] at h
  have hspan : span ℝ S.Φ = span ℝ ({r} : Set V) := by
    rw [hΦ]
    apply le_antisymm
    · apply span_le.mpr
      rintro x (hx | hx)
      · rw [hx]
        exact subset_span (Set.mem_singleton r)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact (span ℝ ({r} : Set V)).neg_mem (subset_span (Set.mem_singleton r))
    · exact span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert r {-r}))
  refine ⟨by rw [hspan]; exact finrank_span_singleton hr0, ?_⟩
  rw [numLines, hΦ, Set.ncard_pair (S.ne_neg_of_mem hr)]

/-- The two signs indexing a one-line system in step 213onemap of `thm:2.13`
([CGSS, Theorem 2.13]). -/
noncomputable def pairRootEquiv (S : LineSystem V) {r : V} (hr : r ∈ S.Φ)
    (hΦ : S.Φ = {r, -r}) : Bool ≃ S.Φ := by
  let f : Bool → S.Φ := fun b ↦ if b then ⟨-r, S.neg_mem r hr⟩ else ⟨r, hr⟩
  apply Equiv.ofBijective f
  constructor
  · intro b c he
    have he' := congrArg Subtype.val he
    cases b <;> cases c <;> first
      | rfl
      | exact False.elim ((S.ne_neg_of_mem hr) he')
      | exact False.elim ((S.ne_neg_of_mem hr) he'.symm)
  · intro x
    have hx : (x : V) = r ∨ (x : V) = -r := by
      simpa only [hΦ, Set.mem_insert_iff, Set.mem_singleton_iff] using x.property
    rcases hx with hx | hx
    · exact ⟨false, Subtype.ext hx.symm⟩
    · exact ⟨true, Subtype.ext hx.symm⟩

/-- The equal Gram matrices of the two signs in step 213onemap of `thm:2.13`
([CGSS, Theorem 2.13]). -/
theorem inner_pairRootEquiv (S : LineSystem V) {r : V} (hr : r ∈ S.Φ)
    (hΦ : S.Φ = {r, -r}) (b c : Bool) :
    ⟪(S.pairRootEquiv hr hΦ b : V), S.pairRootEquiv hr hΦ c⟫ =
      if b = c then 2 else -2 := by
  cases b <;> cases c
  · change ⟪r, r⟫ = 2
    exact S.inner_self r hr
  · change ⟪r, -r⟫ = -2
    rw [inner_neg_right, S.inner_self r hr]
  · change ⟪-r, r⟫ = -2
    rw [inner_neg_left, S.inner_self r hr]
  · change ⟪-r, -r⟫ = 2
    rw [inner_neg_left, inner_neg_right, neg_neg, S.inner_self r hr]

/-- Step 213onemap of `thm:2.13` ([CGSS, Theorem 2.13]): any two one-line systems
are isomorphic; the induced `spanIsometry` sends the chosen root to the chosen root. -/
noncomputable def Iso.ofPairs (S : LineSystem V) (T : LineSystem W)
    {r : V} {s : W} (hr : r ∈ S.Φ) (hs : s ∈ T.Φ)
    (hS : S.Φ = {r, -r}) (hT : T.Φ = {s, -s}) : S.Iso T where
  toEquiv := (S.pairRootEquiv hr hS).symm.trans (T.pairRootEquiv hs hT)
  inner_map x y := by
    obtain ⟨b, rfl⟩ := (S.pairRootEquiv hr hS).surjective x
    obtain ⟨c, rfl⟩ := (S.pairRootEquiv hr hS).surjective y
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, inner_pairRootEquiv]

/-- Step 213dimension of `thm:2.13` ([CGSS, Theorem 2.13]): for a spanning source,
its ambient dimension equals the rank of any isomorphic model. -/
theorem Iso.finrank_eq_span_of_span_eq_top {S : LineSystem V} {T : LineSystem W}
    (e : S.Iso T) (hS : span ℝ S.Φ = ⊤) : finrank ℝ V = finrank ℝ (span ℝ T.Φ) := by
  exact (LinearIsometryEquiv.ofTop V _ hS).toLinearEquiv.finrank_eq.symm.trans
    e.finrank_span_eq

/-- Step 213unique of `thm:2.13` ([CGSS, Theorem 2.13]): a root isomorphism between
spanning systems is induced by a surjective linear isometry of their ambient spaces. -/
theorem Iso.exists_ambient_isometry {S : LineSystem V} {T : LineSystem W}
    (e : S.Iso T) (hS : span ℝ S.Φ = ⊤) (hT : span ℝ T.Φ = ⊤) :
    ∃ F : V ≃ₗᵢ[ℝ] W, F '' S.Φ = T.Φ := by
  let F := (LinearIsometryEquiv.ofTop V _ hS).symm.trans
    (e.spanIsometry.trans (LinearIsometryEquiv.ofTop W _ hT))
  have hF (r : S.Φ) : F r = (e.toEquiv r : W) := by
    have hr : (LinearIsometryEquiv.ofTop V _ hS).symm (r : V) =
        (⟨r, subset_span r.property⟩ : span ℝ S.Φ) := by
      apply Subtype.ext
      exact congrArg (fun x : V ↦ x) ((LinearIsometryEquiv.ofTop V _ hS).apply_symm_apply r)
    change (e.spanIsometry ((LinearIsometryEquiv.ofTop V _ hS).symm (r : V)) : W) = _
    rw [hr, e.spanIsometry_apply]
  refine ⟨F, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [hF ⟨x, hx⟩] using (e.toEquiv ⟨x, hx⟩).property
  · intro hy
    refine ⟨e.toEquiv.symm ⟨y, hy⟩, (e.toEquiv.symm ⟨y, hy⟩).property, ?_⟩
    rw [hF]
    exact congrArg Subtype.val (e.toEquiv.apply_symm_apply ⟨y, hy⟩)

/-- Step 213unique of `thm:2.13` ([CGSS, Theorem 2.13]): systems isomorphic to the
same model have a root isomorphism, hence an ambient orthogonal transformation when
both root sets span. -/
theorem Iso.exists_ambient_isometry_of_same_model {S T : LineSystem V}
    {M : LineSystem W} (e : S.Iso M) (f : T.Iso M)
    (hS : span ℝ S.Φ = ⊤) (hT : span ℝ T.Φ = ⊤) :
    ∃ F : V ≃ₗᵢ[ℝ] V, F '' S.Φ = T.Φ := by
  let q : S.Iso T :=
    { toEquiv := e.toEquiv.trans f.toEquiv.symm
      inner_map := fun x y ↦ (f.symm.inner_map (e.toEquiv x) (e.toEquiv y)).trans
        (e.inner_map x y) }
  exact q.exists_ambient_isometry hS hT

namespace Hyp24

variable (H : Hyp24 V)

/-- Steps 213Echoose and 213E of `thm:2.13` ([CGSS, Theorem 2.13]): positive degree
strictly smaller than the order minus one verifies the graph hypotheses for both
instances, so equal strongly regular parameters give a graph isomorphism. -/
theorem orthGraph_iso_of_isSRGWith (H' : Hyp24 W) {n d a b : ℕ}
    (hX : H.orthGraph.IsSRGWith n d a b) (hY : H'.orthGraph.IsSRGWith n d a b)
    (hd : 0 < d) (hlt : d + 1 < n) : Nonempty (H.orthGraph ≃g H'.orthGraph) := by
  classical
  obtain ⟨he, hn⟩ := hX.exists_edge_and_forall_exists_not_adj hd hlt
  obtain ⟨he', hn'⟩ := hY.exists_edge_and_forall_exists_not_adj hd hlt
  exact H.orthGraph_hasTriangleProperty.nonempty_iso_of_card_eq
    H'.orthGraph_hasTriangleProperty he he' hn hn' (hX.card.trans hY.card.symm)

/-- Step 213A of `thm:2.13` ([CGSS, Theorem 2.13]): an empty marked-star graph
matches the specified star in `A_(|Γa|+2)` from the Section 3 input table. -/
theorem nonempty_iso_An_of_orthGraph_eq_bot (D : ModelInputs)
    (hX : H.orthGraph = ⊥) : Nonempty (H.S.Iso (An (H.Γa.ncard + 2))) := by
  classical
  obtain ⟨M, hM, ⟨eM⟩⟩ := D.an_star (H.Γa.ncard + 2) (by omega)
  let b : H.Γa ≃ Fin (H.Γa.ncard + 2 - 2) :=
    Fintype.equivOfCardEq (by simp [Set.fintypeCard_eq_ncard])
  let e : H.orthGraph ≃g (⊥ : SimpleGraph (Fin (H.Γa.ncard + 2 - 2))) :=
    { b with map_rel_iff' := by intro x y; simp only [hX, SimpleGraph.bot_adj] }
  have q := Iso.ofOrthGraphIso H M (e.trans eM.symm)
  exact ⟨by simpa only [hM] using q⟩

/-- Steps 213Dsize and 213D of `thm:2.13` ([CGSS, Theorem 2.13]): a friendship graph
with `m ≥ 1` triangles matches the specified star in `D_(m+3)`. -/
theorem nonempty_iso_Dn_of_iso_friendship (D : ModelInputs) {m : ℕ} (hm : 1 ≤ m)
    (hX : Nonempty (H.orthGraph ≃g SimpleGraph.friendship m)) :
    Nonempty (H.S.Iso (Dn (m + 3))) := by
  obtain ⟨e⟩ := hX
  obtain ⟨M, hM, ⟨eM⟩⟩ := D.dn_star (m + 3) (by omega)
  have eM' : M.orthGraph ≃g SimpleGraph.friendship m := by
    have hidx : m + 3 - 3 = m := by omega
    exact Eq.mp (congrArg (fun n ↦ M.orthGraph ≃g SimpleGraph.friendship n) hidx) eM
  have q := Iso.ofOrthGraphIso H M (e.trans eM'.symm)
  exact ⟨by simpa only [hM] using q⟩

/-- Steps 213spaniso–213delta of `thm:2.13` ([CGSS, Theorem 2.13]): matching an
exceptional marked-star graph transfers rank, line count, and the `Δ` line count
`H.Δ.ncard / 2` (errata Error 6). -/
theorem exceptional_data_of_isSRGWith {T : LineSystem W} (M : Hyp24 W) (hM : M.S = T)
    {r l n d a b t : ℕ} (hr : finrank ℝ (span ℝ T.Φ) = r) (hl : T.numLines = l)
    (hX : H.orthGraph.IsSRGWith n d a b) (hY : M.orthGraph.IsSRGWith n d a b)
    (hd : 0 < d) (hlt : d + 1 < n) (hΔ : M.Δ.ncard / 2 = t)
    (hspan : span ℝ H.S.Φ = ⊤) :
    finrank ℝ V = r ∧ Nonempty (H.S.Iso T) ∧ H.S.numLines = l ∧
      H.Γa.ncard = n ∧ H.Δ.ncard / 2 = t := by
  obtain ⟨e⟩ := H.orthGraph_iso_of_isSRGWith M hX hY hd hlt
  have q : H.S.Iso T := by simpa only [hM] using Iso.ofOrthGraphIso H M e
  refine ⟨(q.finrank_eq_span_of_span_eq_top hspan).trans hr, ⟨q⟩,
    q.numLines_eq.trans hl, ?_, ?_⟩
  · simpa only [Set.fintypeCard_eq_ncard] using hX.card
  · rw [H.card_Δ_eq_of_orthGraphIso M e]
    exact hΔ

end Hyp24
end LineSystem
