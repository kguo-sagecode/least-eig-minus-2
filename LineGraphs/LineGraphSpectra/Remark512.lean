/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Corollaries
import LineGraphs.Computations.C14
import LineGraphs.Cited.HallConnor.Complement

/-!
# The range between two and nineteen

Remark 5.12 (`rem:5.12`) of [CGSS]. C14 excludes every nonbipartite parameter
choice except the full-block case and `(15,10,21,14,9)`. Hall–Connor excludes
the latter by complementing to `(15,5,21,7,2)`.
-/

namespace Design

attribute [local instance] Classical.propDecidable

variable {P B : Type} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam : ℕ}

-- Remark 5.12
/-- Remark 5.12 of [CGSS], `rem:5.12`: a proper design with `2 < λ < 19`
has its flag-graph family characterized by its spectrum. The exceptional tuple
is excluded by `hc:cor:complement`, via the shared Hall–Connor design structure. -/
theorem flagGraphCharacterized_of_lam_lt_nineteen (D : Design P B v k b r lam)
    (hkv : k < v) (hlow : 2 < lam) (hhigh : lam < 19) : D.FlagGraphCharacterized := by
  -- Step `s5512fisher`.
  have hv := D.one_lt_v
  have hk := D.one_lt_k
  have hlr : lam < r := lt_of_le_of_ne D.lam_le_r
    (fun he ↦ (ne_of_lt hkv) (D.lam_eq_r_iff.mp he))
  have hvb := D.v_le_b_of_lam_lt_r hlr
  intro V _ _ X _ hs
  rcases D.flagGraph_cospectral hvb X hs with hsmall | hflag | hnon
  · -- Steps `s5512b`, `s5512three`, and `s5512four`.
    have hsmall := hsmall.1
    have hbk := D.b_mul_k_eq_v_mul_r
    have hpair := D.r_mul_k_sub_one_eq
    have hv34 : v = 3 ∨ v = 4 := by omega
    rcases hv34 with hv3 | hv4
    · have hk2 : k = 2 := by omega
      rw [hv3, hk2] at hbk hpair
      norm_num at hpair
      omega
    · have hk23 : k = 2 ∨ k = 3 := by omega
      rcases hk23 with hk2 | hk3
      · rw [hv4, hk2] at hbk hpair
        norm_num at hpair
        omega
      · rw [hv4, hk3] at hbk hpair
        norm_num at hpair
        omega
  · exact hflag
  · -- Steps `s5512lam`–`s5512t2`.
    obtain ⟨s, t, hp, _⟩ := hnon
    have hsZ : (2 : ℤ) ≤ s := by exact_mod_cast hp.two_le_s
    by_cases ht1 : t = 1
    · have he := Computations.C14.lambda_eq_two s lam hsZ
        (by simpa only [ht1, Nat.cast_one, mul_one] using hp.pair_count)
      have : lam = 2 := by exact_mod_cast he
      omega
    · by_cases ht3 : 3 ≤ t
      · have he := Computations.C14.lambda_ge_nineteen s t lam hsZ
          (by exact_mod_cast ht3) hp.pair_count
        have : 19 ≤ lam := by exact_mod_cast he
        omega
      · have ht2 : t = 2 := by have := hp.t_pos; omega
        have hs3 : (3 : ℤ) ≤ s := by have := hp.bound; omega
        have hdvd : ((s : ℤ) - 1) ∣ 4 := by norm_num [ht2] at hp ⊢; exact hp.dvd
        have hcases := Computations.C14.eq_three_or_five s hs3 hdvd
        rcases hcases with hs3 | hs5
        · -- Step `s5512s3`: full blocks contradict properness.
          have hs3 : s = 3 := by exact_mod_cast hs3
          have hv6 := hp.point_count
          have hk6 := hp.block_size
          norm_num [hs3, ht2] at hv6 hk6
          omega
        · -- Step `s5512s5`: complement to Hall–Connor's forbidden design.
          have hs5 : s = 5 := by exact_mod_cast hs5
          have hv15 := hp.point_count
          have hk10 := hp.block_size
          have hb21 := hp.block_count
          have hr14 := hp.replication
          have hl9 := hp.pair_count
          norm_num [hs5, ht2] at hv15 hk10 hb21 hr14 hl9
          have hv15 : v = 15 := by omega
          have hb21 : b = 21 := by omega
          have hl9 : lam = 9 := by omega
          subst v k b r lam
          exact D.false_of_parameters_15_10_9.elim

end Design
