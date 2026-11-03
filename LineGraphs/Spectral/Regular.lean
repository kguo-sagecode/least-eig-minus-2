/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Positivity
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Analysis.Matrix.Order

/-!
# Regular graphs: SP1 and SP3

Theorem 5.3 (SP1, Lemma 5.1 of [CGSS]) and Theorem 5.6 (SP3, Lemma 5.3 of [CGSS]) of the spectral
toolkit (`cgss/proofs/spectraltools/spectraltools-lamport.tex`, `thm:sp1`, `thm:sp3`).

The toolkit derives both from its Laplacian theorem (Theorem 5.2). Its `L`-half is Mathlib's
`SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`, which the multiplicity
statement of SP1 uses. The signless half, `kI + A`, is not in Mathlib, so for a `k`-regular graph
this file proves what SP3 and the bound `-k ≤ μ ≤ k` need directly (steps `lap-forms`,
`lap-edges`, `lap-Kcomponent`), writing both Laplacians as `kI + sA` with `s² = 1`.
-/

open Module Module.End Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A function constant across every edge is constant on reachable pairs (Theorem 5.2 of the
spectral toolkit, step `lap-Lfromedges`). -/
theorem eq_of_reachable_of_forall_adj {x : V → ℝ} (hx : ∀ i j, G.Adj i j → x i = x j)
    {u v : V} (huv : G.Reachable u v) : x u = x v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hx _ _ hadj).trans ih

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A function whose values sum to zero across every edge has constant absolute value on
reachable pairs (Theorem 5.2 of the spectral toolkit, step `lap-Kpaths`). -/
theorem abs_eq_of_reachable_of_forall_adj {x : V → ℝ} (hx : ∀ i j, G.Adj i j → x i + x j = 0)
    {u v : V} (huv : G.Reachable u v) : |x u| = |x v| := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => rfl
  | cons hadj _ ih => rw [eq_neg_of_add_eq_zero_left (hx _ _ hadj), abs_neg, ih]

/-- The sign vector of a two-colouring (`1` on colour `0`, `-1` on colour `1`) takes opposite
values at distinct colours, so its entries sum to zero across every edge. -/
private theorem sign_add_sign {a b : Fin 2} (hab : a ≠ b) :
    (if a = 0 then (1 : ℝ) else -1) + (if b = 0 then 1 else -1) = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all

/-- An eigenvector equation `Ax = θx` rearranged as `(kI + sA)x = 0`, for `θ = -k/s`
(Theorem 5.3, step `sp1-ker`, and Theorem 5.6, step `sp3-identify`). No regularity is needed. -/
theorem adjMatrix_mulVec_eq_smul_iff (s : ℝ) (hs : s ^ 2 = 1) (x : V → ℝ) :
    G.adjMatrix ℝ *ᵥ x = (-(s * k)) • x ↔
      ((k : ℝ) • (1 : Matrix V V ℝ) + s • G.adjMatrix ℝ) *ᵥ x = 0 := by
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
  constructor
  · intro hx
    rw [hx, smul_smul]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination (-(k : ℝ) * x i) * hs
  · intro hx
    have h2 : s • (s • G.adjMatrix ℝ *ᵥ x) = s • (-((k : ℝ) • x)) := by
      rw [eq_neg_of_add_eq_zero_right hx]
    rw [smul_smul, ← sq, hs, one_smul] at h2
    rw [h2, smul_neg, smul_smul, neg_smul]

namespace IsRegularOfDegree

/-- Theorem 5.2 of the spectral toolkit, steps `lap-diagonal`, `lap-cross`, `lap-minus` and
`lap-plus`, for a `k`-regular graph: with `s² = 1`,
`2 xᵀ(kI + sA)x = ∑ᵢ ∑ⱼ [i ~ j] (xᵢ + s xⱼ)²`. -/
theorem two_mul_dotProduct_mulVec (h : G.IsRegularOfDegree k) {s : ℝ} (hs : s ^ 2 = 1)
    (x : V → ℝ) :
    2 * (x ⬝ᵥ (((k : ℝ) • (1 : Matrix V V ℝ) + s • G.adjMatrix ℝ) *ᵥ x)) =
      ∑ i, ∑ j, if G.Adj i j then (x i + s * x j) ^ 2 else 0 := by
  -- Expand each square.
  have hS : ∀ i j, (if G.Adj i j then (x i + s * x j) ^ 2 else 0) =
      (if G.Adj i j then x i ^ 2 else 0) + (if G.Adj j i then x j ^ 2 else 0) +
        2 * s * (if G.Adj i j then x i * x j else 0) := by
    intro i j
    by_cases hij : G.Adj i j
    · simp only [hij, hij.symm, ite_true]
      linear_combination (x j ^ 2) * hs
    · have hji : ¬ G.Adj j i := fun h => hij h.symm
      simp [hij, hji]
  -- Step `lap-diagonal`: `∑_{i ~ j} xᵢ² = ∑ᵢ deg(i) xᵢ² = k ‖x‖²`.
  have hdiag : ∑ i, ∑ j, (if G.Adj i j then x i ^ 2 else 0) = (k : ℝ) * (x ⬝ᵥ x) := by
    rw [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- The degree count `k = ∑ⱼ [i ~ j]` (Mathlib's `degree_eq_sum_if_adj`).
    rw [← h.degree_eq i, G.degree_eq_sum_if_adj (R := ℝ) i, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have hswap : ∑ i, ∑ j, (if G.Adj j i then x j ^ 2 else 0) =
      ∑ i, ∑ j, (if G.Adj i j then x i ^ 2 else 0) := Finset.sum_comm
  -- Step `lap-cross`: `xᵀAx = ∑_{i ~ j} xᵢ xⱼ`.
  have hcross := dotProduct_mulVec_adjMatrix (G := G) x x
  simp_rw [hS, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hswap, hdiag, ← hcross]
  simp only [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

/-- Theorem 5.2 of the spectral toolkit, step `lap-positive`, for a `k`-regular graph:
`kI + sA ⪰ 0` when `s² = 1`; these are `L = kI - A` and `K = kI + A`. -/
theorem posSemidef_smul_one_add_smul (h : G.IsRegularOfDegree k) {s : ℝ} (hs : s ^ 2 = 1) :
    ((k : ℝ) • (1 : Matrix V V ℝ) + s • G.adjMatrix ℝ).PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg ((G.isHermitian_adjMatrix ℝ).smul_one_add_smul k s)
    fun x => ?_
  rw [star_trivial]
  have hform := h.two_mul_dotProduct_mulVec hs x
  have hnn : 0 ≤ ∑ i, ∑ j, if G.Adj i j then (x i + s * x j) ^ 2 else (0 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

/-- Theorem 5.2 of the spectral toolkit, step `lap-edges`, for a `k`-regular graph:
`(kI + sA)x = 0` iff `xᵢ + s xⱼ = 0` across every edge, when `s² = 1`. -/
theorem mulVec_eq_zero_iff (h : G.IsRegularOfDegree k) {s : ℝ} (hs : s ^ 2 = 1)
    (x : V → ℝ) :
    ((k : ℝ) • (1 : Matrix V V ℝ) + s • G.adjMatrix ℝ) *ᵥ x = 0 ↔
      ∀ i j, G.Adj i j → x i + s * x j = 0 := by
  have hpsd := h.posSemidef_smul_one_add_smul hs
  have hform := h.two_mul_dotProduct_mulVec hs x
  have hnn : ∀ i j, 0 ≤ (if G.Adj i j then (x i + s * x j) ^ 2 else (0 : ℝ)) := fun i j => by
    split_ifs <;> positivity
  -- The zero-form criterion of Theorem 3.3 (Mathlib's `PosSemidef.dotProduct_mulVec_zero_iff`).
  rw [← hpsd.dotProduct_mulVec_zero_iff x, star_trivial]
  constructor
  · intro h0 i j hij
    have hsum : ∑ i, ∑ j, (if G.Adj i j then (x i + s * x j) ^ 2 else (0 : ℝ)) = 0 := by
      rw [← hform, h0, mul_zero]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hnn i j).mp hsum i (Finset.mem_univ _)
    have hij' := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn i j).mp hi j (Finset.mem_univ _)
    simpa [hij] using hij'
  · intro hx
    have hsum : ∑ i, ∑ j, (if G.Adj i j then (x i + s * x j) ^ 2 else (0 : ℝ)) = 0 :=
      Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        split_ifs with hij
        · rw [hx i j hij]; ring
        · rfl
    linarith

/-- Theorem 5.3 of the spectral toolkit (SP1), step `sp1-extremes`: every eigenvalue of a
`k`-regular graph lies in `[-k, k]`. -/
theorem mem_Icc_of_mem_spectrumMultiset (h : G.IsRegularOfDegree k) {μ : ℝ}
    (hμ : μ ∈ G.spectrumMultiset) : -(k : ℝ) ≤ μ ∧ μ ≤ k := by
  -- Step `sp1-bounds`: `kI - A ⪰ 0` and `kI + A ⪰ 0`.
  have hL : ((k : ℝ) • (1 : Matrix V V ℝ) - G.adjMatrix ℝ).PosSemidef := by
    have := h.posSemidef_smul_one_add_smul (s := -1) (by norm_num)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hK : (G.adjMatrix ℝ - (-(k : ℝ)) • (1 : Matrix V V ℝ)).PosSemidef := by
    have := h.posSemidef_smul_one_add_smul (s := 1) (by norm_num)
    rwa [one_smul, add_comm, ← sub_neg_eq_add, ← neg_smul] at this
  -- Step `sp1-extremes`: the shifts of Theorem 3.3.
  exact ⟨((G.isHermitian_adjMatrix ℝ).posSemidef_sub_smul_one_iff _).mp hK μ hμ,
    ((G.isHermitian_adjMatrix ℝ).posSemidef_smul_one_sub_iff _).mp hL μ hμ⟩

/-- Theorem 5.3 of the spectral toolkit (SP1; Lemma 5.1 of [CGSS]): a nonempty `k`-regular graph
has largest eigenvalue `k`. -/
theorem largestEigenvalue_eq [Nonempty V] (h : G.IsRegularOfDegree k) :
    G.largestEigenvalue = k := by
  -- Step `sp1-eigen`: `k ∈ Spec(X)` (Mathlib's `IsRegularOfDegree.mem_spectrum_adjMatrix`, with
  -- Theorem 2.2).
  have hk : (k : ℝ) ∈ G.spectrumMultiset :=
    (G.isHermitian_adjMatrix ℝ).mem_spectrumMultiset_iff_mem_spectrum.mpr
      (IsRegularOfDegree.mem_spectrum_adjMatrix ℝ G h)
  have hmax := (G.isHermitian_adjMatrix ℝ).largestEigenvalue_mem_spectrumMultiset
  -- Step `sp1-extremes`, with Lemma 2.4.
  exact le_antisymm (h.mem_Icc_of_mem_spectrumMultiset hmax).2
    ((G.isHermitian_adjMatrix ℝ).le_largestEigenvalue_of_mem hk)

/-- Theorem 5.3 of the spectral toolkit (SP1; Lemma 5.1 of [CGSS]): in a `k`-regular graph the
multiplicity of `k` is the number of connected components. -/
theorem multiplicity_eq_card_components (h : G.IsRegularOfDegree k) :
    G.eigenvalueMultiplicity k = Fintype.card G.ConnectedComponent := by
  -- Step `sp1-ker`: `V_A(k) = ker(kI - A) = ker L`, since the degree matrix is `kI`.
  have hW : eigenspace (toLin' (G.adjMatrix ℝ)) (k : ℝ) =
      LinearMap.ker (toLin' (G.lapMatrix ℝ)) := by
    ext x
    rw [mem_eigenspace_iff, LinearMap.mem_ker, toLin'_apply, toLin'_apply, lapMatrix,
      h.degMatrix_eq ℝ, sub_mulVec, sub_eq_zero, eq_comm, natCast_mulVec, Nat.cast_smul_eq_nsmul]
  -- Steps `sp1-count` and `sp1-mult`: Mathlib's Laplacian theorem and Theorem 2.2.
  rw [card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix, eigenvalueMultiplicity,
    (G.isHermitian_adjMatrix ℝ).eigenvalueMultiplicity_eq_finrank, hW]

/-- Theorem 5.6 of the spectral toolkit (SP3; Lemma 5.3 of [CGSS]), step `sp3-kernel`: a connected
`k`-regular graph is bipartite iff `-k` is an eigenvalue. -/
theorem isBipartite_iff_neg_eigenvalue (h : G.IsRegularOfDegree k) (hc : G.Connected) :
    G.IsBipartite ↔ -(k : ℝ) ∈ G.spectrumMultiset := by
  have hne := hc.nonempty
  -- Step `sp3-identify`: `V_A(-k) = ker(kI + A)`, the functions summing to zero across edges.
  have hker : ∀ x : V → ℝ, G.adjMatrix ℝ *ᵥ x = (-(k : ℝ)) • x ↔
      ∀ i j, G.Adj i j → x i + x j = 0 := by
    intro x
    have h1 := adjMatrix_mulVec_eq_smul_iff (G := G) (k := k) 1 (by norm_num) x
    rw [one_mul] at h1
    rw [h1, h.mulVec_eq_zero_iff (by norm_num)]
    simp only [one_mul]
  change G.IsBipartite ↔ -(k : ℝ) ∈ (G.adjMatrix ℝ).spectrumMultiset
  rw [(G.isHermitian_adjMatrix ℝ).mem_spectrumMultiset_iff]
  constructor
  · -- Step `lap-Ksign`: a bipartition gives the signed vector.
    rintro ⟨c⟩
    refine ⟨fun v => if c v = 0 then 1 else -1, ?_, (hker _).mpr fun i j hij => sign_add_sign
      (c.valid hij)⟩
    obtain ⟨v⟩ := hne
    refine Function.ne_iff.mpr ⟨v, ?_⟩
    split_ifs <;> norm_num
  · -- Step `lap-Kpartition`: a nonzero kernel vector gives a bipartition.
    rintro ⟨x, hx0, hx⟩
    have hedge := (hker x).mp hx
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hx0
    have habs : ∀ v, x v = x w ∨ x v = -x w := fun v =>
      abs_eq_abs.mp (abs_eq_of_reachable_of_forall_adj hedge (hc.preconnected v w))
    refine ⟨Coloring.mk (fun v => if x v = x w then (0 : Fin 2) else 1) fun {u v} huv => ?_⟩
    have huv' := eq_neg_of_add_eq_zero_left (hedge u v huv)
    have hw' : x w ≠ -x w := fun h => hw (by rw [Pi.zero_apply]; linarith)
    rcases habs u with hu | hu <;> rcases habs v with hv | hv
    · exact (hw' (by linarith)).elim
    · simp [hu, hv, hw'.symm]
    · simp [hu, hv, hw'.symm]
    · exact (hw' (by linarith)).elim

/-- Theorem 5.6 of the spectral toolkit (SP3), step `sp3-occurrence`: for a connected bipartite
`k`-regular graph, `-k` has multiplicity one. -/
theorem multiplicity_neg_eq_one (h : G.IsRegularOfDegree k) (hc : G.Connected)
    (hb : G.IsBipartite) : G.eigenvalueMultiplicity (-(k : ℝ)) = 1 := by
  obtain ⟨w⟩ := hc.nonempty
  set W := eigenspace (toLin' (G.adjMatrix ℝ)) (-(k : ℝ))
  -- Step `sp3-identify`, as in `isBipartite_iff_neg_eigenvalue`.
  have hker : ∀ x : V → ℝ, x ∈ W → ∀ i j, G.Adj i j → x i + x j = 0 := by
    intro x hx
    rw [mem_eigenspace_iff, toLin'_apply] at hx
    have h1 := adjMatrix_mulVec_eq_smul_iff (G := G) (k := k) 1 (by norm_num) x
    rw [one_mul] at h1
    have := (h.mulVec_eq_zero_iff (s := 1) (by norm_num) x).mp (h1.mp hx)
    simpa only [one_mul] using this
  -- Step `lap-Kinject`: evaluation at `w` is injective on `W`.
  have hinj : Function.Injective ((LinearMap.proj w : (V → ℝ) →ₗ[ℝ] ℝ).comp W.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    ext v
    have hv := abs_eq_of_reachable_of_forall_adj (hker x x.2) (hc.preconnected v w)
    have hxw : (x : V → ℝ) w = 0 := hx
    rw [hxw, abs_zero, abs_eq_zero] at hv
    exact hv
  -- Step `lap-Katmost`: the dimension is at most one.
  have hle : finrank ℝ W ≤ 1 := by
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  -- Step `lap-Kbipartite`: the dimension is positive.
  have hpos : 0 < G.eigenvalueMultiplicity (-(k : ℝ)) :=
    Multiset.count_pos.mpr ((h.isBipartite_iff_neg_eigenvalue hc).mp hb)
  have hmult := (G.isHermitian_adjMatrix ℝ).eigenvalueMultiplicity_eq_finrank (-(k : ℝ))
  have hpos' : 0 < finrank ℝ W := by
    rw [← hmult]
    exact hpos
  change (G.adjMatrix ℝ).eigenvalueMultiplicity _ = 1
  rw [hmult]
  exact le_antisymm hle hpos'

end IsRegularOfDegree

/-- Theorem 5.6 of the spectral toolkit (SP3), step `sp3-sign`: the spectrum of a bipartite graph
is symmetric about zero, with multiplicities. -/
theorem IsBipartite.multiplicity_neg_eq (hb : G.IsBipartite) (μ : ℝ) :
    G.eigenvalueMultiplicity μ = G.eigenvalueMultiplicity (-μ) := by
  obtain ⟨c⟩ := hb
  -- Let `T` be the diagonal sign matrix of the bipartition.
  let t : V → ℝ := fun v => if c v = 0 then 1 else -1
  let T : Matrix V V ℝ := diagonal t
  -- Step `sp3-T`: `T² = I` and `AT = -TA`.
  have hsq : ∀ v, t v * t v = 1 := fun v => by simp only [t]; split_ifs <;> norm_num
  have hTT : ∀ x, T *ᵥ (T *ᵥ x) = x := fun x => by
    ext v
    simp only [T, mulVec_diagonal, ← mul_assoc, hsq, one_mul]
  have hAT : ∀ x, G.adjMatrix ℝ *ᵥ (T *ᵥ x) = -(T *ᵥ (G.adjMatrix ℝ *ᵥ x)) := fun x => by
    have hdiag : ∀ y, T *ᵥ y = fun v => t v * y v := fun y => by
      ext v
      exact mulVec_diagonal t y v
    ext u
    rw [hdiag, hdiag, Pi.neg_apply]
    simp only [mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    -- Step `sp3-entries`, by the three cases.
    by_cases huv : G.Adj u v
    · have hs : t u + t v = 0 := sign_add_sign (c.valid huv)
      rw [eq_neg_of_add_eq_zero_right hs]
      ring
    · simp [adjMatrix_apply, huv]
  -- Steps `sp3-map` and `sp3-inverse`: `x ↦ Tx` maps `V_A(θ)` injectively into `V_A(-θ)`.
  have hmono : ∀ θ : ℝ, finrank ℝ (eigenspace (toLin' (G.adjMatrix ℝ)) θ) ≤
      finrank ℝ (eigenspace (toLin' (G.adjMatrix ℝ)) (-θ)) := by
    intro θ
    have hinj : Function.Injective (toLin' T) := fun x y hxy => by
      have := congrArg (fun z => T *ᵥ z) hxy
      simpa only [toLin'_apply, hTT] using this
    have hmap : (eigenspace (toLin' (G.adjMatrix ℝ)) θ).map (toLin' T) ≤
        eigenspace (toLin' (G.adjMatrix ℝ)) (-θ) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, mem_eigenspace_iff, toLin'_apply] at hx
      rw [mem_eigenspace_iff, toLin'_apply, toLin'_apply, hAT, hx, mulVec_smul, neg_smul]
    calc finrank ℝ (eigenspace (toLin' (G.adjMatrix ℝ)) θ)
        = finrank ℝ ((eigenspace (toLin' (G.adjMatrix ℝ)) θ).map (toLin' T)) :=
          (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _))
      _ ≤ _ := Submodule.finrank_mono hmap
  -- Step `sp3-dimensions`, with Theorem 2.2.
  rw [eigenvalueMultiplicity, eigenvalueMultiplicity,
    (G.isHermitian_adjMatrix ℝ).eigenvalueMultiplicity_eq_finrank,
    (G.isHermitian_adjMatrix ℝ).eigenvalueMultiplicity_eq_finrank]
  exact le_antisymm (hmono μ) (by have := hmono (-μ); rwa [neg_neg] at this)

end SimpleGraph
