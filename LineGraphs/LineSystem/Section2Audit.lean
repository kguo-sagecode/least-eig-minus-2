/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.ClassificationModels
import LineGraphs.LineSystem.FivePossibilities
import LineGraphs.LineSystem.OrthGraphGram

/-! # Axiom audit for the new Section 2 declarations of [CGSS]

Every named theorem and supporting definition in the Section 2 implementation is audited.
Only `propext`, `Classical.choice`, and `Quot.sound` may occur.
-/

-- LineGraphs/Graphs/TriangleProperty.lean
#print axioms SimpleGraph.HasTriangleProperty
#print axioms SimpleGraph.HasTriangleProperty.existsUnique_common_neighbor
#print axioms SimpleGraph.HasTriangleProperty.common_neighbor_unique
#print axioms SimpleGraph.HasTriangleProperty.outside
#print axioms SimpleGraph.HasTriangleProperty.third
#print axioms SimpleGraph.HasTriangleProperty.adj_third_left
#print axioms SimpleGraph.HasTriangleProperty.adj_third_right
#print axioms SimpleGraph.HasTriangleProperty.third_third
#print axioms SimpleGraph.HasTriangleProperty.neighborPairing
#print axioms SimpleGraph.HasTriangleProperty.neighborPairing_ne
#print axioms SimpleGraph.HasTriangleProperty.adj_iff_neighborPairing
#print axioms SimpleGraph.HasTriangleProperty.exists_neighbor_pair_labels
#print axioms SimpleGraph.HasTriangleProperty.nonempty_iso_friendship_of_forall_adj
#print axioms SimpleGraph.HasTriangleProperty.exists_adj
#print axioms SimpleGraph.HasTriangleProperty.adj_neighborPairing_iff
#print axioms SimpleGraph.HasTriangleProperty.commonNeighborsEquiv
#print axioms SimpleGraph.HasTriangleProperty.degree_eq_two_mul_card_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.degree_eq_of_not_adj
#print axioms SimpleGraph.HasTriangleProperty.degree_eq_of_not_forall_adj
#print axioms SimpleGraph.HasTriangleProperty.not_adj_of_same_adjacency
#print axioms SimpleGraph.HasTriangleProperty.isIndepSet_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.isIndepSet_neighborSet_diff
#print axioms SimpleGraph.HasTriangleProperty.adj_commonNeighborsEquiv_iff
#print axioms SimpleGraph.HasTriangleProperty.adj_commonNeighborsEquiv_comm_iff
#print axioms SimpleGraph.HasTriangleProperty.adj_commonNeighborsEquiv_iff_not_adj
#print axioms SimpleGraph.HasTriangleProperty.third_mem_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.third_mem_compl_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.commonNeighborsPairing
#print axioms SimpleGraph.HasTriangleProperty.third_mem_neighborSet_diff
#print axioms SimpleGraph.HasTriangleProperty.existsUnique_other_non_neighbor
#print axioms SimpleGraph.HasTriangleProperty.card_non_neighbors_eq_zero_or_two
#print axioms SimpleGraph.HasTriangleProperty.eq_or_eq_or_eq_of_degree_two
#print axioms SimpleGraph.HasTriangleProperty.two_le_card_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.neighborSet_diff_compl_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.ncard_neighbors_in_compl_commonNeighbors_add_four
#print axioms SimpleGraph.HasTriangleProperty.neighborSet_diff_compl_commonNeighbors_of_mem_diff
#print axioms SimpleGraph.HasTriangleProperty.ncard_neighbors_in_compl_commonNeighbors_add_card
#print axioms SimpleGraph.missedCommonNeighbors
#print axioms SimpleGraph.mem_missedCommonNeighbors
#print axioms SimpleGraph.degree_induce_eq_ncard
#print axioms SimpleGraph.sum_ncard_neighbors_inter
#print axioms SimpleGraph.HasTriangleProperty.sum_ncard_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.ncard_neighbors_common_add_diff
#print axioms SimpleGraph.HasTriangleProperty.ncard_compl_commonNeighbors_add_five
#print axioms SimpleGraph.HasTriangleProperty.card_eq_two_add_three_mul_add_compl_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.card_add_three_eq_six_mul
#print axioms SimpleGraph.HasTriangleProperty.isSRGWith_of_not_forall_adj
#print axioms SimpleGraph.HasTriangleProperty.ncard_commonNeighbors_inter_eq_or_add_two
#print axioms SimpleGraph.HasTriangleProperty.ncard_compl_commonNeighbors_inter_eq
#print axioms SimpleGraph.HasTriangleProperty.two_mul_card_high_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.card_commonNeighbors_le_five
#print axioms SimpleGraph.HasTriangleProperty.ncard_commonNeighbors_eq_three_of_high
#print axioms SimpleGraph.HasTriangleProperty.card_commonNeighbors_mem
#print axioms SimpleGraph.HasTriangleProperty.third_commonNeighborsEquiv_mem_compl_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.existsUnique_pair_label
#print axioms SimpleGraph.HasTriangleProperty.card_edgeFinset_induce_common_neighbor_compl
#print axioms SimpleGraph.HasTriangleProperty.card_edgeFinset_induce_compl_commonNeighbors
#print axioms SimpleGraph.HasTriangleProperty.card_missedCommonNeighbors_eq_two
#print axioms SimpleGraph.HasTriangleProperty.exists_pair_label_equiv
#print axioms SimpleGraph.HasTriangleProperty.disjoint_missedCommonNeighbors_of_adj
#print axioms SimpleGraph.HasTriangleProperty.adj_iff_disjoint_missedCommonNeighbors_of_five
#print axioms SimpleGraph.HasTriangleProperty.singleton_compl_commonNeighbors_of_two
#print axioms SimpleGraph.HasTriangleProperty.claw_compl_commonNeighbors_of_three
#print axioms SimpleGraph.HasTriangleProperty.NormalForm
#print axioms SimpleGraph.HasTriangleProperty.normal_form_of_not_forall_adj

-- LineGraphs/Graphs/TrianglePropertyIso.lean
#print axioms SimpleGraph.TriangleVertex
#print axioms SimpleGraph.instDecidableEqTriangleVertex
#print axioms SimpleGraph.triangleRelation
#print axioms SimpleGraph.decidableTriangleRelation
#print axioms SimpleGraph.TriangleVertex.congr
#print axioms SimpleGraph.TriangleVertex.congr_relation
#print axioms SimpleGraph.HasTriangleProperty.rightCommonNeighborsEquiv
#print axioms SimpleGraph.HasTriangleProperty.triangleVertexEquiv
#print axioms SimpleGraph.HasTriangleProperty.triangleVertexEquiv_apply
#print axioms SimpleGraph.HasTriangleProperty.triangleVertexEquiv_adj
#print axioms SimpleGraph.HasTriangleProperty.isoOfRemainderEquiv
#print axioms SimpleGraph.HasTriangleProperty.exists_remainderEquiv
#print axioms SimpleGraph.HasTriangleProperty.nonempty_iso_of_card_eq

-- LineGraphs/LineSystem/TriangleProperty.lean
#print axioms LineSystem.Hyp24.orthGraph_hasTriangleProperty
#print axioms LineSystem.Hyp24.orthGraph_iso_friendship_of_forall_adj

-- LineGraphs/LineSystem/OrthGraphParameters.lean
#print axioms LineSystem.Hyp24.orthGraph_isSRGWith
#print axioms LineSystem.Hyp24.card_Γa_mem
#print axioms LineSystem.Hyp24.orthGraph_iso_of_card_Γa_eq

-- LineGraphs/Computations/C1Certificate.lean
#print axioms Computations.C1.coeffAdd
#print axioms Computations.C1.coeffMul
#print axioms Computations.C1.coeffSub
#print axioms Computations.C1.polynomialOfCoeffs_add
#print axioms Computations.C1.polynomialOfCoeffs_scale
#print axioms Computations.C1.polynomialOfCoeffs_mul
#print axioms Computations.C1.polynomialOfCoeffs_sub
#print axioms Computations.C1.detCoeffsThree
#print axioms Computations.C1.polynomialOfCoeffs_detCoeffsThree
#print axioms Computations.C1.minor_zero_checked
#print axioms Computations.C1.minor_two_checked

-- LineGraphs/Computations/C1.lean
#print axioms Computations.C1.blockSumMatrix
#print axioms Computations.C1.blockSumMinor
#print axioms Computations.C1.blockSumMinor_eq_submatrix
#print axioms Computations.C1.det_minor_zero
#print axioms Computations.C1.det_minor_two
#print axioms Computations.C1.det_blockSumMinor

-- LineGraphs/LineSystem/OrthGraphGram.lean
#print axioms LineSystem.Hyp24.inner_Γa_eq
#print axioms LineSystem.Hyp24.gramCoreVector
#print axioms LineSystem.Hyp24.inner_gramCoreVector
#print axioms LineSystem.Hyp24.blockSumVectors
#print axioms LineSystem.Hyp24.gram_blockSumVectors
#print axioms LineSystem.Hyp24.blockSumMinor_posSemidef
#print axioms LineSystem.Hyp24.card_commonNeighbors_le_five_of_gram

-- LineGraphs/LineSystem/OrthGraphCases.lean
#print axioms LineSystem.IsIndecomposable.eq_pair_or_exists_hyp24
#print axioms LineSystem.Hyp24.orthGraph_cases

-- LineGraphs/LineSystem/OrthGraphReconstruction.lean
#print axioms LineSystem.exists_isometry_of_eq_gram
#print axioms LineSystem.Hyp24.starFamily
#print axioms LineSystem.Hyp24.starFamily_mem
#print axioms LineSystem.Hyp24.span_range_starFamily
#print axioms LineSystem.Hyp24.inner_starFamily_map
#print axioms LineSystem.Hyp24.exists_spanIsometry_of_orthGraphIso
#print axioms LineSystem.Hyp24.exists_iso_of_orthGraphIso
#print axioms LineSystem.Iso.ofOrthGraphIso
#print axioms LineSystem.Iso.ofOrthGraphIso_a
#print axioms LineSystem.Iso.ofOrthGraphIso_b
#print axioms LineSystem.Iso.ofOrthGraphIso_c
#print axioms LineSystem.Iso.ofOrthGraphIso_Γa
#print axioms LineSystem.Hyp24.card_Δ_eq_of_orthGraphIso

-- LineGraphs/LineSystem/Section2Models.lean
#print axioms SimpleGraph.IsSRGWith.exists_edge_and_forall_exists_not_adj
#print axioms LineSystem.ModelInputs
#print axioms LineSystem.ne_neg_of_mem
#print axioms LineSystem.finrank_span_numLines_of_eq_pair
#print axioms LineSystem.pairRootEquiv
#print axioms LineSystem.inner_pairRootEquiv
#print axioms LineSystem.Iso.ofPairs
#print axioms LineSystem.Iso.finrank_eq_span_of_span_eq_top
#print axioms LineSystem.Iso.exists_ambient_isometry
#print axioms LineSystem.Iso.exists_ambient_isometry_of_same_model
#print axioms LineSystem.Hyp24.orthGraph_iso_of_isSRGWith
#print axioms LineSystem.Hyp24.nonempty_iso_An_of_orthGraph_eq_bot
#print axioms LineSystem.Hyp24.nonempty_iso_Dn_of_iso_friendship
#print axioms LineSystem.Hyp24.exceptional_data_of_isSRGWith

-- LineGraphs/LineSystem/FivePossibilities.lean
#print axioms LineSystem.five_possibilities
#print axioms LineSystem.Hyp24.six_lines_of_iso_friendship_zero

#print axioms LineSystem.five_possibilities_forall_hyp24
