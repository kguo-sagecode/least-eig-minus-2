/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Hadamard

/-!
# Spectral characterization of design flag graphs

Corollaries 5.9–5.11 of [CGSS]. The exception in Corollary 5.9 is unordered
(Error 17). The design corollaries use the family interpretation of `def:flag`,
and the single-block and hexagon lemmas repair Gap 16.
-/

open Matrix

namespace SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Step `s559swap`, Corollary 5.9 of [CGSS]: exchange the two bipartite parts. -/
def completeBipartiteSwapIso (m n : ℕ) :
    completeBipartiteGraph (Fin m) (Fin n) ≃g completeBipartiteGraph (Fin n) (Fin m) where
  toEquiv := Equiv.sumComm _ _
  map_rel_iff' := by
    rintro (u | u) (w | w) <;> simp [completeBipartiteGraph]

/-- Step `s559one`, Corollary 5.9 of [CGSS]: the line graph of a star is complete. -/
theorem lineGraph_completeBipartite_eq_top_of_right_eq_one (m : ℕ) :
    (completeBipartiteGraph (Fin m) (Fin 1)).lineGraph = ⊤ := by
  apply eq_top_iff_forall_ne_adj.mpr
  intro u w huw
  obtain ⟨p, rfl⟩ := (completeBipartiteEdgeEquiv (Fin m) (Fin 1)).surjective u
  obtain ⟨q, rfl⟩ := (completeBipartiteEdgeEquiv (Fin m) (Fin 1)).surjective w
  apply (lineGraph_completeBipartiteGraph_adj p q).mpr
  exact ⟨fun h ↦ huw (congrArg _ h), Or.inr (Subsingleton.elim _ _)⟩

/-- The unordered exceptional parameter condition of `cor:5.9`, Corollary 5.9 of [CGSS]. -/
def HasCompleteBipartiteHadamardException (m n : ℕ) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧
    ((m = 2 * t ^ 2 + t ∧ n = 2 * t ^ 2 - t) ∨
      (n = 2 * t ^ 2 + t ∧ m = 2 * t ^ 2 - t)) ∧
    Matrix.HasSymmetricHadamardWithConstantDiagonal (4 * t ^ 2)

/-- Steps `s559st`–`s559H`, Corollary 5.9 of [CGSS]: the nonbipartite alternative
for a full-block design forces the unordered Hadamard exception. -/
theorem hasCompleteBipartiteHadamardException_of_parameters
    {m n s t : ℕ} (hp : Design.NonbipartiteParameters n n m m m s t)
    {W : Type} [Fintype W] [DecidableEq W] (Y : SimpleGraph W) [DecidableRel Y.Adj]
    (hc : Y.Connected) (hr : Y.IsRegularOfDegree ((s + 1) * t))
    (hn : Fintype.card W = s * (s + 2))
    (hspec : Y.spectrumMultiset =
      {((s : ℝ) + 1) * t} + Multiset.replicate (s + 1) (-(t : ℝ)) +
      Multiset.replicate ((s - 1) * (s + 2) / 2)
        (Real.sqrt (t * (s + 1) * ((s : ℝ) - t) / (s - 1))) +
      Multiset.replicate ((s - 1) * (s + 2) / 2)
        (-Real.sqrt (t * (s + 1) * ((s : ℝ) - t) / (s - 1)))) :
    HasCompleteBipartiteHadamardException m n := by
  have hQ : (s : ℚ) * (s + 1) / 2 = s * t := by
    have hv : 2 * (n : ℚ) = s * (s + 1) := by exact_mod_cast hp.point_count
    have hk : (n : ℚ) = s * t := by exact_mod_cast hp.block_size
    nlinarith
  obtain ⟨hst, _, _, _, ht, hcQ⟩ := Computations.C12.full_block_parameters s t
    ((t : ℚ) * (s + 1) * (s - t) / (s - 1)) (by exact_mod_cast hp.two_le_s)
    (by have := hp.t_pos; omega) (by simpa using hQ) rfl
  have hstN : s + 1 = 2 * t := by omega
  have hsmall : n = 2 * t ^ 2 - t := by
    have hnt : n + t = 2 * t ^ 2 := by nlinarith [hp.block_size]
    omega
  have hlarge : m = 2 * t ^ 2 + t := by nlinarith [hp.block_count]
  have hdeg : (s + 1) * t = 2 * t ^ 2 := by nlinarith
  have hcard : Fintype.card W + 1 = 4 * t ^ 2 := by rw [hn]; nlinarith
  have hcR : (t : ℝ) * (s + 1) * ((s : ℝ) - t) / (s - 1) = (t : ℝ) ^ 2 := by
    exact_mod_cast hcQ
  have hsupport : ∀ μ ∈ Y.spectrumMultiset, μ ≠ ((2 * t ^ 2 : ℕ) : ℝ) →
      μ ^ 2 = (t : ℝ) ^ 2 := by
    intro μ hμ hne
    rw [hspec, hcR, Real.sqrt_sq (Nat.cast_nonneg t)] at hμ
    simp only [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_replicate] at hμ
    rcases hμ with ((hμ | ⟨_, hμ⟩) | ⟨_, hμ⟩) | ⟨_, hμ⟩
    · have hdR : ((s : ℝ) + 1) * t = ((2 * t ^ 2 : ℕ) : ℝ) := by exact_mod_cast hdeg
      exact (hne (hμ.trans hdR)).elim
    · rw [hμ, neg_sq]
    · rw [hμ]
    · rw [hμ, neg_sq]
  exact ⟨t, by omega, Or.inl ⟨hlarge, hsmall⟩,
    Y.hasSymmetricHadamardWithConstantDiagonal_of_spectrum t hc (hdeg ▸ hr) hcard hsupport⟩

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Step `s559ordered`, Corollary 5.9 of [CGSS]: the ordered part-size case. -/
theorem lineGraph_completeBipartite_characterized_of_le (m n : ℕ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hlarge : 9 < m + n)
    (hno : ¬ HasCompleteBipartiteHadamardException m n)
    (X : SimpleGraph V) [DecidableRel X.Adj]
    (hs : (completeBipartiteGraph (Fin m) (Fin n)).lineGraph.Cospectral X) :
    Nonempty (X ≃g (completeBipartiteGraph (Fin m) (Fin n)).lineGraph) := by
  by_cases hn1 : n = 1
  · subst n
    have : Nonempty (completeBipartiteGraph (Fin m) (Fin 1)).edgeSet :=
      ⟨completeBipartiteEdgeEquiv _ _ (⟨0, hm⟩, 0)⟩
    apply hs.nonempty_iso_of_isRegularOfDegree_card_sub_one
    intro u
    apply (degree_eq_card_sub_one _ u).mpr
    rw [lineGraph_completeBipartite_eq_top_of_right_eq_one]
    exact fun _ h ↦ h
  · let D := Design.trivial m n hm (by omega)
    let e := D.incidenceGraphCompleteBipartiteIso.lineGraph
    have hsD : D.flagGraph.Cospectral X := e.cospectral.trans hs
    rcases D.flagGraph_cospectral hnm X hsD with hsmall | hflag | hnon
    · have := hsmall.1
      omega
    · obtain ⟨P₂, B₂, _, _, _, _, D₂, ⟨f⟩⟩ := hflag
      exact ⟨f.trans D₂.incidenceGraphCompleteBipartiteIso.lineGraph⟩
    · obtain ⟨s, t, hp, _, W, _, _, Y, _, hc, hr, hcard, hspec, _⟩ := hnon
      exact (hno (hasCompleteBipartiteHadamardException_of_parameters hp Y hc hr hcard hspec)).elim

-- Corollary 5.9
/-- Corollary 5.9 of [CGSS], `cor:5.9` (Doob). The Hadamard exception is unordered,
as required by Error 17. Both part sizes satisfy `m,n ≥ 1` and are not assumed
ordered; the excluded zero-size cases have empty line graphs. -/
theorem lineGraph_completeBipartite_characterized (m n : ℕ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hlarge : 9 < m + n)
    (hno : ¬ HasCompleteBipartiteHadamardException m n)
    (X : SimpleGraph V) [DecidableRel X.Adj]
    (hs : (completeBipartiteGraph (Fin m) (Fin n)).lineGraph.Cospectral X) :
    Nonempty (X ≃g (completeBipartiteGraph (Fin m) (Fin n)).lineGraph) := by
  by_cases hnm : n ≤ m
  · exact lineGraph_completeBipartite_characterized_of_le m n hm hn hnm hlarge hno X hs
  · let e := (completeBipartiteSwapIso m n).lineGraph
    have hno' : ¬ HasCompleteBipartiteHadamardException n m := by
      rintro ⟨t, ht, hp, hH⟩
      exact hno ⟨t, ht, hp.symm, hH⟩
    obtain ⟨f⟩ := lineGraph_completeBipartite_characterized_of_le n m hn hm (by omega)
      (by omega) hno' X (e.symm.cospectral.trans hs)
    exact ⟨f.trans e.symm⟩

end SimpleGraph

namespace Design

attribute [local instance] Classical.propDecidable

variable {P B : Type} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam : ℕ} {D : Design P B v k b r lam}

-- Corollary 5.10
/-- Corollary 5.10 of [CGSS], `cor:5.10` (Hoffman and Ray-Chaudhuri).
A proper symmetric design, other than the `(4,3,2)` exception, has its flag-graph
family characterized by the spectrum, in the sense of `def:flag`. -/
theorem IsSymmetric.flagGraphCharacterized (hD : D.IsSymmetric)
    (hkv : k < v) (hne : (v, k, lam) ≠ (4, 3, 2)) : D.FlagGraphCharacterized := by
  -- Step `s5510rk`.
  have hb : v = b := hD
  have hbk := D.b_mul_k_eq_v_mul_r
  have hpair := D.r_mul_k_sub_one_eq
  have hv := D.one_lt_v
  have hk := D.one_lt_k
  have hrk : r = k := by rw [← hb] at hbk; nlinarith
  intro V _ _ X _ hs
  rcases D.flagGraph_cospectral (by omega) X hs with hsmall | hflag | hnon
  · -- Steps `s5510v`–`s5510fourthree`.
    have hv34 : v = 3 ∨ v = 4 := by have := hsmall.1; omega
    have hparams : v = 3 ∧ k = 2 ∧ b = 3 ∧ r = 2 ∧ lam = 1 := by
      rcases hv34 with hv3 | hv4
      · have hk2 : k = 2 := by omega
        rw [hrk, hv3, hk2] at hpair
        norm_num at hpair
        exact ⟨hv3, hk2, by omega, by omega, by omega⟩
      · have hk23 : k = 2 ∨ k = 3 := by omega
        rcases hk23 with hk2 | hk3
        · rw [hrk, hv4, hk2] at hpair
          norm_num at hpair
          omega
        · rw [hrk, hv4, hk3] at hpair
          norm_num at hpair
          exact (hne (by simp [hv4, hk3, show lam = 2 by omega])).elim
    rcases hparams with ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact D.flagGraphCharacterized_of_parameters_3_2_1 V X hs
  · exact hflag
  · -- Step `s5510iii`: nonbipartite parameters force unequal replication and block size.
    obtain ⟨s, t, hp, _⟩ := hnon
    have := hp.t_pos
    nlinarith [hp.replication, hp.block_size]

-- Corollary 5.11
/-- Corollary 5.11 of [CGSS], `cor:5.11` (Doob). The one-block case omitted in
the paper is handled before using Fisher's inequality or Theorem 5.8 (Gap 16). -/
theorem flagGraphCharacterized_of_lam_eq_one (D : Design P B v k b r lam)
    (hlam : lam = 1) : D.FlagGraphCharacterized := by
  subst lam
  have hv := D.one_lt_v
  have hk := D.one_lt_k
  have hbk := D.b_mul_k_eq_v_mul_r
  have hpair := D.r_mul_k_sub_one_eq
  by_cases hfull : k = v
  · -- Step `s5511full`: the complete flag graph of a single block.
    have hr1 : r = 1 := (D.lam_eq_r_iff.mpr hfull).symm
    have hb1 : b = 1 := by rw [hfull, hr1] at hbk; nlinarith
    exact D.flagGraphCharacterized_of_b_eq_one hb1
  · -- Step `s5511fisher`.
    have hkv : k < v := lt_of_le_of_ne D.k_le_v hfull
    have hlr : 1 < r := lt_of_le_of_ne D.lam_le_r
      (fun h ↦ hfull (D.lam_eq_r_iff.mp h))
    have hvb := D.v_le_b_of_lam_lt_r hlr
    intro V _ _ X _ hs
    rcases D.flagGraph_cospectral hvb X hs with hsmall | hflag | hnon
    · -- Steps `s5511v`–`s5511fourthree`.
      have hsmall := hsmall.1
      have hv34 : v = 3 ∨ v = 4 := by omega
      have hparams : v = 3 ∧ k = 2 ∧ b = 3 ∧ r = 2 := by
        rcases hv34 with hv3 | hv4
        · have hk2 : k = 2 := by omega
          rw [hv3, hk2] at hpair hbk
          norm_num at hpair
          exact ⟨hv3, hk2, by omega, by omega⟩
        · have hk23 : k = 2 ∨ k = 3 := by omega
          rcases hk23 with hk2 | hk3
          · rw [hv4, hk2] at hpair hbk
            norm_num at hpair
            omega
          · rw [hv4, hk3] at hpair
            norm_num at hpair
            omega
      rcases hparams with ⟨rfl, rfl, rfl, rfl⟩
      exact D.flagGraphCharacterized_of_parameters_3_2_1 V X hs
    · exact hflag
    · -- Step `s5511iii`: the pair equation forces λ ≥ 2.
      obtain ⟨s, t, hp, _⟩ := hnon
      have hs : (2 : ℝ) ≤ s := by exact_mod_cast hp.two_le_s
      have ht : (1 : ℝ) ≤ t := by exact_mod_cast hp.t_pos
      have hst : (s : ℝ) - 1 ≤ (s : ℝ) * t - 1 := by nlinarith
      have hlow := mul_le_mul_of_nonneg_left hst (show (0 : ℝ) ≤ 2 * t by positivity)
      have htwo : 2 * ((s : ℝ) - 1) ≤ 2 * t * ((s : ℝ) - 1) := by nlinarith
      have hpair := hp.pair_count_real
      norm_num at hpair
      nlinarith

end Design
