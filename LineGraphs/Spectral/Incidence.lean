/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Signless
import LineGraphs.Spectral.LineGraphRegular
import LineGraphs.Spectral.TraceRank
import Mathlib.Combinatorics.SimpleGraph.IncMatrix

/-!
# Incidence products and line graphs

Theorem 6.2 of the spectral toolkit. Columns are indexed by actual edges, rather
than all unordered pairs as in Mathlib's full incidence matrix.
-/

open Matrix Module

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V)
  [DecidableRel X.Adj]

/-- The unoriented vertex-edge incidence matrix, with actual edges as columns. -/
def edgeIncMatrix (R : Type*) [Zero R] [One R] : Matrix V X.edgeSet R :=
  (X.incMatrix R).submatrix id Subtype.val

omit [Fintype V] in
/-- At an actual edge, the incidence entry tests only endpoint membership. -/
theorem edgeIncMatrix_apply {R : Type*} [Zero R] [One R] (v : V) (e : X.edgeSet) :
    X.edgeIncMatrix R v e = if v ∈ (e : Sym2 V) then 1 else 0 := by
  simp [edgeIncMatrix, incMatrix_apply', incidenceSet, e.property]

/-- Theorem 6.2 of the spectral toolkit: the first incidence product is the signless Laplacian. -/
theorem edgeIncMatrix_mul_transpose :
    X.edgeIncMatrix ℝ * (X.edgeIncMatrix ℝ)ᵀ = X.signlessLapMatrix ℝ := by
  -- Step `inc-restrict`: nonedge columns in the full matrix contribute zero.
  have hrestrict : X.edgeIncMatrix ℝ * (X.edgeIncMatrix ℝ)ᵀ =
      X.incMatrix ℝ * (X.incMatrix ℝ)ᵀ := by
    ext u v
    simp only [mul_apply, transpose_apply, edgeIncMatrix, submatrix_apply, id_eq]
    let f : Sym2 V → ℝ := fun e => X.incMatrix ℝ u e * X.incMatrix ℝ v e
    change (∑ e : X.edgeSet, f e.val) = ∑ e, f e
    symm
    apply Finset.sum_congr_set X.edgeSet f (fun e => f e.val)
    · intro e _; rfl
    · intro e he
      dsimp [f]
      rw [X.incMatrix_of_notMem_incidenceSet (fun h => he h.1), zero_mul]
  -- Step `inc-library`: use Mathlib's full incidence product.
  have hfull := X.incMatrix_mul_transpose (R := ℝ)
  -- Step `inc-identify`: its diagonal is D and its off-diagonal part is A.
  have hid : X.incMatrix ℝ * (X.incMatrix ℝ)ᵀ = X.signlessLapMatrix ℝ := by
    rw [hfull]
    ext u v
    by_cases huv : u = v
    · subst v
      simp [signlessLapMatrix, degMatrix, adjMatrix_apply]
    · simp [signlessLapMatrix, degMatrix, adjMatrix_apply, huv]
  exact hrestrict.trans hid

noncomputable local instance : DecidableRel X.lineGraph.Adj := Classical.decRel _

/-- Theorem 6.2 of the spectral toolkit: the second incidence product is two times the identity plus
the line-graph adjacency matrix. -/
theorem transpose_edgeIncMatrix_mul :
    (X.edgeIncMatrix ℝ)ᵀ * X.edgeIncMatrix ℝ =
      (2 : ℝ) • (1 : Matrix X.edgeSet X.edgeSet ℝ) + X.lineGraph.adjMatrix ℝ := by
  -- Steps `inc-edgediag`, `inc-edgeoff`: a product entry counts common endpoints.
  have hentry (e f : X.edgeSet) :
      ((X.edgeIncMatrix ℝ)ᵀ * X.edgeIncMatrix ℝ) e f =
        ∑ a ∈ (e : Sym2 V).toFinset, if a ∈ (f : Sym2 V) then (1 : ℝ) else 0 := by
    simp only [mul_apply, transpose_apply, X.edgeIncMatrix_apply,
      ite_mul, one_mul, zero_mul, ← Sym2.mem_toFinset]
    exact (Finset.sum_filter _ _).symm.trans (by
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext a
      simp)
  ext e f
  rcases e with ⟨⟨u, v⟩, huv⟩
  rcases f with ⟨⟨w, z⟩, hwz⟩
  have huv' : u ≠ v := huv.ne
  have hwz' : w ≠ z := hwz.ne
  rw [hentry, Sym2.toFinset_mk_eq, Finset.sum_pair huv']
  -- Step `inc-linedef`: distinct intersecting edges are precisely line-graph neighbours.
  have hline : X.lineGraph.Adj ⟨s(u, v), huv⟩ ⟨s(w, z), hwz⟩ ↔
      s(u, v) ≠ s(w, z) ∧ (u = w ∨ u = z ∨ v = w ∨ v = z) := by
    rw [lineGraph_adj_iff_exists]
    simp only [Sym2.mem_iff]
    constructor
    · rintro ⟨hne, a, ha, hb⟩
      refine ⟨fun h ↦ hne (Subtype.ext h), ?_⟩
      rcases ha with rfl | rfl
      · exact hb.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
      · exact Or.inr (Or.inr hb)
    · rintro ⟨hne, huw | huz | hvw | hvz⟩
      · exact ⟨fun h ↦ hne (congrArg Subtype.val h), u, Or.inl rfl, Or.inl huw⟩
      · exact ⟨fun h ↦ hne (congrArg Subtype.val h), u, Or.inl rfl, Or.inr huz⟩
      · exact ⟨fun h ↦ hne (congrArg Subtype.val h), v, Or.inr rfl, Or.inl hvw⟩
      · exact ⟨fun h ↦ hne (congrArg Subtype.val h), v, Or.inr rfl, Or.inr hvz⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, adjMatrix_apply,
    hline, Subtype.mk.injEq, Sym2.mem_iff, Sym2.eq_iff]
  by_cases huw : u = w
  · subst w
    by_cases hvz : v = z
    · subst z
      simp [huv', huv'.symm]
      norm_num
    · simp [huv'.symm, hwz', hvz]
  · by_cases huz : u = z
    · subst z
      by_cases hvw : v = w
      · subst w
        simp [huv', huv'.symm]
        norm_num
      · simp [huw, huv'.symm, hvw]
    · by_cases hvw : v = w
      · subst w
        simp [huw, huz, hwz']
      · by_cases hvz : v = z
        · subst z
          simp [huw, huz, hvw]
        · simp [huw, huz, hvw, hvz]

/-- Theorem 6.2 of the spectral toolkit, step `inc-rankM`: incidence rank is the number of
vertices minus
the number of bipartite components, including isolated vertices. -/
theorem rank_edgeIncMatrix : (X.edgeIncMatrix ℝ).rank = Fintype.card V -
    Nat.card {c : X.ConnectedComponent // c.toSimpleGraph.IsBipartite} := by
  -- Step `inc-kernel`: use the general signless-Laplacian nullity formula.
  have hk := X.finrank_ker_signlessLapMatrix_eq_card_bipartite_components
  have hrn := LinearMap.finrank_range_add_finrank_ker (X.signlessLapMatrix ℝ).toLin'
  have hr : (X.signlessLapMatrix ℝ).rank = (X.edgeIncMatrix ℝ).rank := by
    rw [← X.edgeIncMatrix_mul_transpose, rank_self_mul_transpose]
  -- Step `inc-rankM`: the first Gram product has the same rank as the incidence matrix.
  have hrank : (X.signlessLapMatrix ℝ).rank =
      finrank ℝ (X.signlessLapMatrix ℝ).toLin'.range :=
    (X.signlessLapMatrix ℝ).rank_eq_finrank_range_toLin (Pi.basisFun ℝ V) (Pi.basisFun ℝ V)
  rw [← hrank, hr, hk, finrank_pi] at hrn
  omega

/-- Theorem 6.2 of the spectral toolkit: a subtraction-free form of the line-graph -2 multiplicity
formula,
`mult(-2) + |V| = |E| + b`, valid even when the original graph has isolated vertices. -/
theorem multiplicity_neg_two_lineGraph :
    X.lineGraph.eigenvalueMultiplicity (-2) + Fintype.card V = X.edgeFinset.card +
      Nat.card {c : X.ConnectedComponent // c.toSimpleGraph.IsBipartite} := by
  classical
  let M := X.edgeIncMatrix ℝ
  -- Step `inc-shift`: shifting adjacency by two takes its -2 eigenspace to the kernel.
  have hker : Module.End.eigenspace (X.lineGraph.adjMatrix ℝ).toLin' (-2) =
      (Mᵀ * M).toLin'.ker := by
    ext x
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, toLin'_apply, toLin'_apply]
    change X.lineGraph.adjMatrix ℝ *ᵥ x = (-2 : ℝ) • x ↔ _
    rw [show Mᵀ * M = (2 : ℝ) • 1 + X.lineGraph.adjMatrix ℝ
      from X.transpose_edgeIncMatrix_mul, add_mulVec, smul_mulVec, one_mulVec]
    constructor <;> intro hx
    · rw [hx, ← add_smul]; simp
    · ext u
      have hu := congrFun hx u
      simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hu ⊢
      linarith
  -- Step `inc-zeros`: rank-nullity for the second Gram product.
  have hrn := LinearMap.finrank_range_add_finrank_ker (Mᵀ * M).toLin'
  have hrank : (Mᵀ * M).rank = finrank ℝ (Mᵀ * M).toLin'.range :=
    (Mᵀ * M).rank_eq_finrank_range_toLin (Pi.basisFun ℝ X.edgeSet)
      (Pi.basisFun ℝ X.edgeSet)
  rw [← hrank, rank_transpose_mul_self, ← hker, finrank_pi] at hrn
  rw [← (X.lineGraph.isHermitian_adjMatrix ℝ).eigenvalueMultiplicity_eq_finrank] at hrn
  have hr := X.rank_edgeIncMatrix
  have hk := X.finrank_ker_signlessLapMatrix_eq_card_bipartite_components
  have hle : Nat.card {c : X.ConnectedComponent // c.toSimpleGraph.IsBipartite} ≤
      Fintype.card V := by
    rw [← hk]
    exact (Submodule.finrank_le _).trans_eq (finrank_pi ℝ)
  have hc : Fintype.card X.edgeSet = X.edgeFinset.card := X.card_edgeSet
  change M.rank + X.lineGraph.eigenvalueMultiplicity (-2) = Fintype.card X.edgeSet at hrn
  rw [hc] at hrn
  dsimp [M] at hrn
  omega

/-- Theorem 6.2 of the spectral toolkit, step `inc-lower`: every nonempty line graph has least
eigenvalue
at least -2. -/
theorem neg_two_le_leastEigenvalue_lineGraph [Nonempty X.edgeSet] :
    -2 ≤ X.lineGraph.leastEigenvalue := by
  -- Step `inc-lower`: the shifted adjacency is a positive semidefinite Gram product.
  have hpsd : ((X.edgeIncMatrix ℝ)ᵀ * X.edgeIncMatrix ℝ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      posSemidef_conjTranspose_mul_self (X.edgeIncMatrix ℝ)
  rw [X.transpose_edgeIncMatrix_mul] at hpsd
  exact (X.lineGraph.posSemidef_two_add_adjMatrix_iff_neg_two_le_leastEigenvalue).mp hpsd

end SimpleGraph
