/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Degree
import LineGraphs.Hadamard.FourthRows
import LineGraphs.Hadamard.Entries
import LineGraphs.Hadamard.Sixteenths
import LineGraphs.Computations.C16

/-!
# Axiom audit for Section 6 and computation C16

Every new theorem, together with the structures containing proof fields and the hyperplane
isometry, is audited here. Kernel computations use only `decide +kernel`.
The continuation includes LN3, components, decomposition, the classical orthogonality
obstructions, the `E₇` exclusion and Theorem 6.2 with classification as a hypothesis.
-/

#print axioms Matrix.hadamardRowProduct_comm
#print axioms Matrix.hadamardPairs_gram_apply
#print axioms Matrix.IsHadamard.FourRowAgreement.inner_hadamardPairs_mem
#print axioms Matrix.IsHadamard.hadamardSignedAdj_diag
#print axioms Matrix.IsHadamard.FourRowAgreement.hadamardSignedAdj_mem
#print axioms Matrix.IsHadamard.hadamardSignedAdj_gram
#print axioms Matrix.IsHadamard.hadamardSignedAdj_quadratic_scaled
#print axioms Matrix.IsHadamard.hadamardSignedAdj_quadratic
#print axioms Matrix.IsHadamard.hadamardSignedAdj_symm
#print axioms Matrix.IsHadamard.sum_sq_hadamardSignedAdj
#print axioms Matrix.IsHadamard.card_adj_lineSystem
#print axioms Matrix.IsHadamard.inner_hadamardPairs_of_meet
#print axioms Matrix.IsHadamard.hadamardSignedAdj_of_meet
#print axioms Matrix.IsHadamard.hadamardSignedAdj_eq_zero_iff_of_disjoint
#print axioms Matrix.IsHadamard.hadamardRowProduct_self
#print axioms Matrix.IsHadamard.hadamardPairs_orthogonal_of_mem
#print axioms Matrix.IsHadamard.hadamardRowProduct_linearIndependent
#print axioms Matrix.IsHadamard.hadamardRowBasis
#print axioms Matrix.IsHadamard.hadamardRowBasis_apply
#print axioms Matrix.IsHadamard.eq_sum_inner_hadamardRowProduct
#print axioms Matrix.IsHadamard.eq_sum_inner_hadamardPairs
#print axioms Matrix.IsHadamard.span_hadamardPairs_fixedRow
#print axioms Matrix.IsHadamard.finrank_hadamardPairs_fixedRow
#print axioms Matrix.IsHadamard.sum_sq_inner_hadamardPairs
#print axioms Matrix.IsHadamard.FourRowAgreement.inner_sq_eq_indicator
#print axioms Matrix.IsHadamard.FourRowAgreement.card_fourthRows
#print axioms Matrix.IsHadamard.FourRowAgreement.dvd_card
#print axioms Matrix.IsHadamard.FourRowAgreement.div_sq_eq_card_fourthRows
#print axioms Matrix.IsHadamard.lineSystem
#print axioms Matrix.IsHadamard.signed_hadamardRoot_injective
#print axioms Matrix.IsHadamard.lineSystemSigning
#print axioms Matrix.IsHadamard.numLines_lineSystem
#print axioms Matrix.IsHadamard.lineSystem_signedAdj
#print axioms Matrix.IsHadamard.lineSystem_quadratic
#print axioms Matrix.IsHadamard.lineSystem_inner_one
#print axioms Matrix.IsHadamard.lineSystem_apply_mem
#print axioms Matrix.IsHadamard.hadamardRoots_orthogonal_of_mem
#print axioms Matrix.card_hadamardPair
#print axioms Matrix.two_mul_sum_hadamardPair
#print axioms Matrix.IsHadamard.transpose_hadamardPairs_mul
#print axioms Matrix.IsHadamard.hadamardPairs_mulVec_one
#print axioms Matrix.IsHadamard.hadamardPairs_mul_allOnes
#print axioms Matrix.IsHadamard.hadamardPairs_gram_sq
#print axioms Matrix.IsHadamard.entry_sq
#print axioms Matrix.IsHadamard.sum_row_mul
#print axioms Matrix.IsHadamard.sum_col_mul
#print axioms Matrix.IsHadamard.hadamardPairs_apply_mem
#print axioms Matrix.IsHadamard.inner_hadamardPairs_self
#print axioms Matrix.IsHadamard.inner_hadamardRowProduct_of_ne
#print axioms Matrix.IsHadamard.inner_hadamardPairs_of_card_inter_eq_one
#print axioms Matrix.IsHadamard.four_sign_identity
#print axioms Matrix.IsHadamard.inner_hadamardPairs_of_disjoint
#print axioms Matrix.IsHadamard.inner_hadamardPairs_one
#print axioms Matrix.inner_hadamardRoot
#print axioms Matrix.IsHadamard.inner_hadamardRoot_self
#print axioms Matrix.IsHadamard.hadamardRoot_apply_mem
#print axioms Matrix.IsHadamard.inner_hadamardRoot_one
#print axioms Matrix.IsHadamard.div_half_eq_two
#print axioms Matrix.IsHadamard.inner_hadamardRoot_eq_signedAdj
#print axioms Matrix.IsHadamard.inner_hadamardRoot_mem
#print axioms Matrix.IsHadamard.sixteen_dvd_of_agree_sixteenths
#print axioms Matrix.IsHadamard.fourRowAgreement_half
#print axioms Computations.C16.h12_transpose_hadamardPairs_mul
#print axioms Computations.C16.fourRow_agreements
#print axioms Computations.C16.agreementCount_eq
#print axioms Computations.C16.agreement_swap_first
#print axioms Computations.C16.agreement_swap_last
#print axioms Computations.C16.checkAgreementRow_sound
#print axioms Computations.C16.checkFourRowAgreement_sound
#print axioms Computations.C16.h12_inner_self
#print axioms Computations.C16.h12_inner_mem
#print axioms Computations.C16.h12_root_inner_self
#print axioms Computations.C16.h12_root_inner_mem
#print axioms Computations.C16.h12_root_mem_hyperplane
#print axioms Computations.C16.h12_hyperplane_finrank
#print axioms Computations.C16.h12HyperplaneIsometry
#print axioms Computations.C16.h12_lines_injective
#print axioms Computations.C16.h12_numLines
#print axioms Computations.C16.h12_line_angles
#print axioms Computations.C16.h12_agreement_example
#print axioms Computations.C16.h12_inner_values_attained
#print axioms Computations.C16.h12_isHadamard
#print axioms Computations.C16.h12_agreement_checked
#print axioms Computations.C16.h12_fourRowAgreement
#print axioms Computations.C16.h16_isHadamard
#print axioms Computations.C16.h16_agreement_checked
#print axioms Computations.C16.h16_fourRowAgreement
#print axioms Computations.C16.h16_agreement_chunk0_left
#print axioms Computations.C16.h16_agreement_chunk0_right
#print axioms Computations.C16.h16_agreement_chunk0
#print axioms Computations.C16.h16_agreement_chunk1
#print axioms Computations.C16.h16_agreement_chunk2
#print axioms Computations.C16.h16_agreement_chunk3
#print axioms Computations.C16.h2_isHadamard
#print axioms Computations.C16.h2_agreement_checked
#print axioms Computations.C16.h2_fourRowAgreement
#print axioms Computations.C16.h4_isHadamard
#print axioms Computations.C16.h4_agreement_checked
#print axioms Computations.C16.h4_fourRowAgreement
#print axioms Computations.C16.h8_isHadamard
#print axioms Computations.C16.h8_agreement_checked
#print axioms Computations.C16.h8_fourRowAgreement

-- Section 6: the line system of a Hadamard matrix.
#print axioms Matrix.HadamardPair.ofRows
#print axioms Matrix.hadamardRoot_ofRows
#print axioms Matrix.hadamardGraph
#print axioms Matrix.componentRowPairs
#print axioms Matrix.componentSpan
#print axioms Matrix.componentRank
#print axioms Matrix.IsHadamard.eq_sum_inner_normalizedRowProduct
#print axioms Matrix.IsHadamard.mem_component_of_inner_ne_zero
#print axioms Matrix.IsHadamard.span_component_row
#print axioms Matrix.IsHadamard.component_row_linearIndependent
#print axioms Matrix.IsHadamard.card_component_row
#print axioms Matrix.IsHadamard.two_mul_card_component
#print axioms Matrix.IsHadamard.componentRank_pos
#print axioms Matrix.IsHadamard.componentRank_le
#print axioms LineSystem.StarGenerated
#print axioms LineSystem.StarGenerated.inner_self
#print axioms LineSystem.StarGenerated.mem_span
#print axioms LineSystem.StarGenerated.neg
#print axioms LineSystem.StarGenerated.inner_integral
#print axioms LineSystem.StarGenerated.inner_mem
#print axioms LineSystem.finite_starGenerated
#print axioms LineSystem.starClosure
#print axioms LineSystem.subset_starClosure
#print axioms LineSystem.isStarClosed_starClosure
#print axioms LineSystem.IsStarClosed.starClosure_subset
#print axioms LineSystem.span_starClosure
#print axioms LineSystem.IsIndecomposable.starClosure
#print axioms Matrix.IsHadamard.componentLineSystem
#print axioms Matrix.IsHadamard.componentLineSystem_subset
#print axioms Matrix.IsHadamard.hadamardRoot_mem_componentLineSystem
#print axioms Matrix.IsHadamard.componentLineSystem_nonempty
#print axioms Matrix.IsHadamard.ncard_componentLineSystem
#print axioms Matrix.IsHadamard.span_componentLineSystem
#print axioms Matrix.IsHadamard.isIndecomposable_componentLineSystem
#print axioms Matrix.IsHadamard.componentStarClosure
#print axioms Matrix.IsHadamard.componentStarClosure_properties
#print axioms Matrix.IsHadamard.component_rootType_of_classification
#print axioms Matrix.HadamardPair.rowEquiv
#print axioms Matrix.card_hadamardPair_row
#print axioms Matrix.IsHadamard.sum_componentRank
#print axioms Matrix.IsHadamard.component_type_bounds
#print axioms Matrix.IsHadamard.add_componentRank_le
#print axioms Matrix.IsHadamard.component_eq_univ_of_forall_eq
#print axioms Matrix.IsHadamard.component_cases_of_classification
#print axioms LineSystem.An.disjoint_supports_of_integerInner_eq_zero
#print axioms LineSystem.An.not_card_pairwise_orthogonal
#print axioms LineSystem.Dn.disjoint_or_eq_supports_of_integerInner_eq_zero
#print axioms LineSystem.Dn.integerInner_same_support
#print axioms LineSystem.Dn.card_le_two_of_same_support
#print axioms LineSystem.Dn.even_of_card_pairwise_orthogonal
#print axioms Matrix.IsHadamard.ncard_component_inner_eq_neg_one
#print axioms Matrix.IsHadamard.add_not_mem_lineSystem
#print axioms Matrix.IsHadamard.card_support_add_lineSystem
#print axioms Matrix.IsHadamard.add_mem_componentStarClosure_sdiff
#print axioms LineSystem.Iso.neighborEquiv
#print axioms LineSystem.Iso.e₇_data
#print axioms Matrix.IsHadamard.not_component_E₇_of_classification
#print axioms Matrix.IsHadamard.exists_orthogonal_family_of_component_eq_univ
#print axioms Matrix.IsHadamard.not_fourRow_agree_sixteenths_of_classification
