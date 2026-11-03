/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Regular

/-!
# The signless Laplacian

Theorem 5.2 of `cgss/proofs/spectraltools/spectraltools-lamport.tex`. The ordinary Laplacian
statements are in Mathlib's `SimpleGraph.LapMatrix`. Here the degrees need not be
constant. An isolated vertex is a bipartite component and contributes one dimension.
-/

open Matrix Module

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V)
  [DecidableRel X.Adj]

/-- The signless Laplacian `D + A` of a finite simple graph. -/
def signlessLapMatrix (R : Type*) [AddMonoidWithOne R] : Matrix V V R :=
  X.degMatrix R + X.adjMatrix R

/-- The signless Laplacian is Hermitian. -/
theorem isHermitian_signlessLapMatrix : (X.signlessLapMatrix ℝ).IsHermitian :=
  (X.isHermitian_degMatrix ℝ).add (X.isHermitian_adjMatrix ℝ)

/-- Theorem 5.2 of the spectral toolkit, step `lap-plus`, with the edge sum written over both
orientations. -/
theorem two_mul_dotProduct_signlessLapMatrix (x : V → ℝ) :
    2 * (x ⬝ᵥ (X.signlessLapMatrix ℝ *ᵥ x)) =
      ∑ u, ∑ v, if X.Adj u v then (x u + x v) ^ 2 else 0 := by
  -- Step `lap-diagonal`: each coordinate square occurs its degree many times.
  have hdiag : ∑ u, ∑ v, (if X.Adj u v then x u ^ 2 else 0) =
      x ⬝ᵥ (X.degMatrix ℝ *ᵥ x) := by
    rw [X.dotProduct_mulVec_degMatrix]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [X.degree_eq_sum_if_adj (R := ℝ), Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  -- Step `lap-cross`: the adjacency form sums the products over oriented edges.
  have hcross := dotProduct_mulVec_adjMatrix (G := X) x x
  -- Step `lap-plus`: expand the squares and exchange the two endpoints.
  have hexpand : ∀ u v, (if X.Adj u v then (x u + x v) ^ 2 else 0) =
      (if X.Adj u v then x u ^ 2 else 0) +
      (if X.Adj v u then x v ^ 2 else 0) +
      2 * (if X.Adj u v then x u * x v else 0) := by
    intro u v
    by_cases huv : X.Adj u v
    · simp only [huv, huv.symm, ite_true]; ring
    · have hvu : ¬ X.Adj v u := fun h => huv h.symm
      simp [huv, hvu]
  have hswap : (∑ u, ∑ v, if X.Adj v u then x v ^ 2 else 0) =
      ∑ u, ∑ v, if X.Adj u v then x u ^ 2 else 0 := Finset.sum_comm
  simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hswap, hdiag, ← hcross]
  simp only [signlessLapMatrix, add_mulVec, dotProduct_add]
  ring

/-- Theorem 5.2 of the spectral toolkit, step `lap-Kpositive`: the signless Laplacian is positive
semidefinite. -/
theorem posSemidef_signlessLapMatrix : (X.signlessLapMatrix ℝ).PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg X.isHermitian_signlessLapMatrix fun x => ?_
  rw [star_trivial]
  have hform := X.two_mul_dotProduct_signlessLapMatrix x
  have hnonneg : 0 ≤ ∑ u, ∑ v, if X.Adj u v then (x u + x v) ^ 2 else (0 : ℝ) :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by
      split_ifs <;> positivity
  linarith

/-- Theorem 5.2 of the spectral toolkit, step `lap-kernelK`: a signless-kernel vector changes sign
on every edge. -/
theorem signlessLapMatrix_mulVec_eq_zero_iff (x : V → ℝ) :
    X.signlessLapMatrix ℝ *ᵥ x = 0 ↔ ∀ u v, X.Adj u v → x u + x v = 0 := by
  -- Step `lap-edges`: use the zero-form criterion and the sum of nonnegative squares.
  have hform := X.two_mul_dotProduct_signlessLapMatrix x
  have hnonneg : ∀ u v, 0 ≤ (if X.Adj u v then (x u + x v) ^ 2 else (0 : ℝ)) :=
    fun u v => by split_ifs <;> positivity
  rw [← X.posSemidef_signlessLapMatrix.dotProduct_mulVec_zero_iff x, star_trivial]
  constructor
  · intro hx u v huv
    have hsum : (∑ u, ∑ v, if X.Adj u v then (x u + x v) ^ 2 else (0 : ℝ)) = 0 := by
      rw [← hform, hx, mul_zero]
    have hu := (Finset.sum_eq_zero_iff_of_nonneg fun u _ =>
      Finset.sum_nonneg fun v _ => hnonneg u v).mp hsum u (Finset.mem_univ _)
    have hv := (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hnonneg u v).mp
      hu v (Finset.mem_univ _)
    simpa [huv] using hv
  · intro hx
    have hsum : (∑ u, ∑ v, if X.Adj u v then (x u + x v) ^ 2 else (0 : ℝ)) = 0 :=
      Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by
        split_ifs with huv
        · rw [hx u v huv]; ring
        · rfl
    linarith

omit [Fintype V] [DecidableEq V] [DecidableRel X.Adj] in
/-- Theorem 5.2 of the spectral toolkit, step `lap-Kpartition`: a nonzero function changing sign
on every
edge of a connected graph gives a two-colouring. -/
theorem Connected.isBipartite_of_forall_adj_add_eq_zero (hc : X.Connected)
    {x : V → ℝ} (hx : x ≠ 0) (he : ∀ u v, X.Adj u v → x u + x v = 0) :
    X.IsBipartite := by
  classical
  obtain ⟨w, hw⟩ := Function.ne_iff.mp hx
  -- Step `lap-Kpaths`: absolute values are constant along paths.
  have habs : ∀ v, x v = x w ∨ x v = -x w := fun v =>
    abs_eq_abs.mp (abs_eq_of_reachable_of_forall_adj he (hc.preconnected v w))
  -- Step `lap-Kpartition`: the two possible values are distinct.
  have hne : x w ≠ -x w := fun h => hw (by rw [Pi.zero_apply]; linarith)
  refine ⟨Coloring.mk (fun v => if x v = x w then (0 : Fin 2) else 1)
    fun {u v} huv => ?_⟩
  have huv' := he u v huv
  rcases habs u with hu | hu <;> rcases habs v with hv | hv
  · exact (hne (by linarith)).elim
  · simp [hu, hv, hne.symm]
  · simp [hu, hv, hne.symm]
  · exact (hne (by linarith)).elim

/-- Theorem 5.2 of the spectral toolkit: the nullity of `D + A` counts the bipartite connected
components,
including isolated vertices. The formula also holds for the empty graph. -/
theorem finrank_ker_signlessLapMatrix_eq_card_bipartite_components :
    finrank ℝ (X.signlessLapMatrix ℝ).toLin'.ker =
      Nat.card {c : X.ConnectedComponent // c.toSimpleGraph.IsBipartite} := by
  classical
  let K := (X.signlessLapMatrix ℝ).toLin'.ker
  let B := {c : X.ConnectedComponent // c.toSimpleGraph.IsBipartite}
  let w : X.ConnectedComponent → V := fun c => c.nonempty_supp.choose
  have hw (c : X.ConnectedComponent) : w c ∈ c.supp := c.nonempty_supp.choose_spec
  have hedge (x : K) : ∀ u v, X.Adj u v → (x : V → ℝ) u + (x : V → ℝ) v = 0 :=
    (X.signlessLapMatrix_mulVec_eq_zero_iff x).mp x.property
  -- Step `lap-Knonbipartite`: a kernel function vanishes on every nonbipartite component.
  have hzero (x : K) (c : X.ConnectedComponent) (hc : ¬ c.toSimpleGraph.IsBipartite)
      (v : V) (hv : v ∈ c.supp) : (x : V → ℝ) v = 0 := by
    have hz : (fun u : c => (x : V → ℝ) u) = 0 := by
      by_contra h
      exact hc (c.connected_toSimpleGraph.isBipartite_of_forall_adj_add_eq_zero _ h
        (fun u v huv => hedge x u v huv))
    exact congrFun hz ⟨v, hv⟩
  let F : K →ₗ[ℝ] (B → ℝ) :=
    { toFun := fun x c => (x : V → ℝ) (w c.val)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Steps `lap-Kinject`, `lap-Kspan`: evaluation at one vertex of each bipartite
  -- component determines a kernel vector; the other components contribute zero.
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    ext v
    let c := X.connectedComponentMk v
    by_cases hc : c.toSimpleGraph.IsBipartite
    · have hxw : (x : V → ℝ) (w c) = 0 := congrFun hx ⟨c, hc⟩
      have habs := abs_eq_of_reachable_of_forall_adj (hedge x)
        (c.reachable_of_mem_supp (by rfl) (hw c))
      simpa [hxw] using habs
    · exact hzero x c hc v (by rfl)
  -- Step `lap-Katmost`: evaluation embeds the kernel in one copy of ℝ per component.
  have hle : finrank ℝ K ≤ Fintype.card B := by
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  -- Step `lap-Ksign`: extend a two-colouring's sign function by zero.
  have hex (c : B) : ∃ x : K, (x : V → ℝ) (w c.val) ≠ 0 ∧
      ∀ v, v ∉ c.val.supp → (x : V → ℝ) v = 0 := by
    obtain ⟨col⟩ := c.property
    let x : V → ℝ := fun v => if hv : v ∈ c.val.supp then
      (if col ⟨v, hv⟩ = 0 then 1 else -1) else 0
    have hx : x ∈ K := by
      apply (X.signlessLapMatrix_mulVec_eq_zero_iff x).mpr
      intro u v huv
      by_cases hu : u ∈ c.val.supp
      · have hv := (c.val.mem_supp_congr_adj huv).mp hu
        have hcol := col.valid (show c.val.toSimpleGraph.Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv)
        dsimp [x]
        rw [dite_eq_left hu, dite_eq_left hv]
        generalize col ⟨u, hu⟩ = a at *
        generalize col ⟨v, hv⟩ = b at *
        fin_cases a <;> fin_cases b
        · exact (hcol rfl).elim
        · norm_num
        · norm_num
        · exact (hcol rfl).elim
      · have hv : v ∉ c.val.supp := fun hv => hu ((c.val.mem_supp_congr_adj huv).mpr hv)
        simp only [x, dite_eq_right hu, dite_eq_right hv, add_zero]
    refine ⟨⟨x, hx⟩, ?_, ?_⟩
    · dsimp [x]
      rw [dite_eq_left (hw c.val)]
      split_ifs <;> norm_num
    · intro v hv
      exact dite_eq_right hv
  choose b hb hbsupp using hex
  -- Step `lap-Kind`: disjoint supports make these signed functions independent.
  have hind : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro a ha c
    have heval := congrArg (fun x : K => (x : V → ℝ) (w c.val)) ha
    have hvanish : ∀ d : B, d ≠ c → (b d : V → ℝ) (w c.val) = 0 := by
      intro d hdc
      apply hbsupp d
      intro hd
      exact hdc (Subtype.ext (ConnectedComponent.eq_of_common_vertex hd (hw c.val)))
    have hsum : (∑ d : B, a d * (b d : V → ℝ) (w c.val)) = a c * (b c : V → ℝ) (w c.val) := by
      apply Finset.sum_eq_single c
      · intro d _ hdc
        rw [hvanish d hdc, mul_zero]
      · simp
    have hmul : a c * (b c : V → ℝ) (w c.val) = 0 := by
      simpa only [Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul,
        Pi.smul_apply, smul_eq_mul, hsum, ZeroMemClass.coe_zero, Pi.zero_apply] using heval
    exact (mul_eq_zero.mp hmul).resolve_right (hb c)
  -- Steps `lap-Kbipartite`, `lap-countbasis`, `lap-isolated`: the matching lower
  -- bound counts one independent vector for each bipartite component.
  have hge : Fintype.card B ≤ finrank ℝ K := hind.fintype_card_le_finrank
  simpa only [Nat.card_eq_fintype_card] using le_antisymm hle hge

end SimpleGraph
