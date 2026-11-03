/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Hyp24
import LineGraphs.Computations.C21
import Batteries.Tactic.OpenPrivate

/-! # Axiom audit for Hypothesis 2.4 and the simple-root Gram determinants of [CGSS]

All 103 explicit declarations in `LineSystem/Hyp24.lean` are audited, including the
supporting instances, simp lemmas, and private lemmas. The three Gram determinants from
Computation C21 are audited as well. Only `propext`, `Classical.choice`, and `Quot.sound`
may occur.
-/

open private LineSystem.Hyp24.add_mem_cyclic LineSystem.Hyp24.inner_add_translation
  LineSystem.Hyp24.inner_eq_zero_or_one_cyclic from LineGraphs.LineSystem.Hyp24

-- LineGraphs/LineSystem/Hyp24.lean, in source order.
#print axioms LineSystem.inner_eq_two_iff
#print axioms LineSystem.inner_eq_neg_two_iff
#print axioms LineSystem.inner_eq_neg_one_or_zero_or_one
#print axioms LineSystem.IsMaximal.isStarClosed
#print axioms LineSystem.Hyp24
#print axioms LineSystem.Hyp24.c
#print axioms LineSystem.Hyp24.Γa
#print axioms LineSystem.Hyp24.Γb
#print axioms LineSystem.Hyp24.Γc
#print axioms LineSystem.Hyp24.Δ
#print axioms LineSystem.Hyp24.sigmaSet
#print axioms LineSystem.Hyp24.third
#print axioms LineSystem.Hyp24.Γa_subset_Φ
#print axioms LineSystem.Hyp24.finite_Γa
#print axioms LineSystem.Hyp24.instFiniteΓa
#print axioms LineSystem.Hyp24.instFintypeΓa
#print axioms LineSystem.Hyp24.Γb_subset_Φ
#print axioms LineSystem.Hyp24.finite_Γb
#print axioms LineSystem.Hyp24.instFiniteΓb
#print axioms LineSystem.Hyp24.instFintypeΓb
#print axioms LineSystem.Hyp24.Γc_subset_Φ
#print axioms LineSystem.Hyp24.finite_Γc
#print axioms LineSystem.Hyp24.instFiniteΓc
#print axioms LineSystem.Hyp24.instFintypeΓc
#print axioms LineSystem.Hyp24.Δ_subset_Φ
#print axioms LineSystem.Hyp24.finite_Δ
#print axioms LineSystem.Hyp24.instFiniteΔ
#print axioms LineSystem.Hyp24.instFintypeΔ
#print axioms LineSystem.Hyp24.orthGraph
#print axioms LineSystem.Hyp24.instDecidableRelOrthGraphAdj
#print axioms LineSystem.Hyp24.orthGraph_adj
#print axioms LineSystem.Hyp24.c_mem
#print axioms LineSystem.Hyp24.inner_b_c
#print axioms LineSystem.Hyp24.inner_c_a
#print axioms LineSystem.Hyp24.inner_c_b
#print axioms LineSystem.Hyp24.inner_a_c
#print axioms LineSystem.Hyp24.inner_b_a
#print axioms LineSystem.Hyp24.star
#print axioms LineSystem.Hyp24.mem_Γa_iff
#print axioms LineSystem.Hyp24.mem_Γb_iff
#print axioms LineSystem.Hyp24.mem_Γc_iff
#print axioms LineSystem.Hyp24.mem_Δ_iff
#print axioms LineSystem.Hyp24.inner_a_of_mem_Γa
#print axioms LineSystem.Hyp24.inner_b_of_mem_Γa
#print axioms LineSystem.Hyp24.inner_c_of_mem_Γa
#print axioms LineSystem.Hyp24.inner_c_left_of_mem_Γa
#print axioms LineSystem.Hyp24.inner_b_of_mem_Γb
#print axioms LineSystem.Hyp24.inner_c_of_mem_Γb
#print axioms LineSystem.Hyp24.inner_a_of_mem_Γb
#print axioms LineSystem.Hyp24.inner_c_of_mem_Γc
#print axioms LineSystem.Hyp24.inner_a_of_mem_Γc
#print axioms LineSystem.Hyp24.inner_b_of_mem_Γc
#print axioms LineSystem.Hyp24.inner_a_of_mem_Δ
#print axioms LineSystem.Hyp24.inner_b_of_mem_Δ
#print axioms LineSystem.Hyp24.inner_c_of_mem_Δ
#print axioms LineSystem.Hyp24.mem_Γa_of
#print axioms LineSystem.Hyp24.mem_sigmaSet_iff
#print axioms LineSystem.Hyp24.sigmaSet_subset_Φ
#print axioms LineSystem.Hyp24.finite_sigmaSet
#print axioms LineSystem.Hyp24.instFiniteSigmaSet
#print axioms LineSystem.Hyp24.instFintypeSigmaSet
#print axioms LineSystem.Hyp24.Φ_eq_sigmaSet_union_neg
#print axioms LineSystem.Hyp24.add_mem_cyclic
#print axioms LineSystem.Hyp24.add_c_mem_Γb
#print axioms LineSystem.Hyp24.add_a_mem_Γc
#print axioms LineSystem.Hyp24.add_b_mem_Γa
#print axioms LineSystem.Hyp24.sub_b_mem_Γc
#print axioms LineSystem.Hyp24.ΓaEquivΓb
#print axioms LineSystem.Hyp24.coe_ΓaEquivΓb_apply
#print axioms LineSystem.Hyp24.coe_ΓaEquivΓb_symm_apply
#print axioms LineSystem.Hyp24.ΓbEquivΓc
#print axioms LineSystem.Hyp24.coe_ΓbEquivΓc_apply
#print axioms LineSystem.Hyp24.coe_ΓbEquivΓc_symm_apply
#print axioms LineSystem.Hyp24.ΓcEquivΓa
#print axioms LineSystem.Hyp24.coe_ΓcEquivΓa_apply
#print axioms LineSystem.Hyp24.coe_ΓcEquivΓa_symm_apply
#print axioms LineSystem.Hyp24.inner_add_translation
#print axioms LineSystem.Hyp24.inner_ΓaEquivΓb
#print axioms LineSystem.Hyp24.inner_ΓbEquivΓc
#print axioms LineSystem.Hyp24.inner_ΓcEquivΓa
#print axioms LineSystem.Hyp24.inner_eq_zero_or_one_cyclic
#print axioms LineSystem.Hyp24.inner_eq_zero_or_one
#print axioms LineSystem.Hyp24.inner_eq_zero_or_one_of_mem_Γb
#print axioms LineSystem.Hyp24.inner_eq_zero_or_one_of_mem_Γc
#print axioms LineSystem.Hyp24.Γb_eq_image_add_c
#print axioms LineSystem.Hyp24.Γc_eq_image_sub_b
#print axioms LineSystem.Hyp24.sub_mem_Δ
#print axioms LineSystem.Hyp24.exists_sub_of_inner_ne_zero
#print axioms LineSystem.Hyp24.Δ_eq_sub
#print axioms LineSystem.Hyp24.recoverySet
#print axioms LineSystem.Hyp24.sigmaSet_eq_recoverySet
#print axioms LineSystem.Hyp24.finite_recoverySet
#print axioms LineSystem.Hyp24.instFiniteRecoverySet
#print axioms LineSystem.Hyp24.instFintypeRecoverySet
#print axioms LineSystem.Hyp24.Φ_eq_recovery_union_neg
#print axioms LineSystem.Hyp24.image_recoverySet
#print axioms LineSystem.Hyp24.image_Φ_eq
#print axioms LineSystem.Hyp24.span_Φ_eq_span_pair_union_Γa
#print axioms LineSystem.Hyp24.Φ_eq_of_Γa_eq
#print axioms LineSystem.Hyp24.triangle
#print axioms LineSystem.Hyp24.third_mem_Γa
#print axioms LineSystem.Hyp24.inner_third_left
#print axioms LineSystem.Hyp24.inner_third_right

-- LineGraphs/Computations/C21E6.lean, C21E7.lean, and C21E8.lean.
#print axioms Computations.C21.e6_gram_det
#print axioms Computations.C21.e7_gram_det
#print axioms Computations.C21.e8_gram_det
