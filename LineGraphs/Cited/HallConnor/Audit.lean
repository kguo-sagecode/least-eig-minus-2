/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.Complement

/-!
# Axiom audit for Hall–Connor

Every new theorem, definition, and instance is listed below, including the two design
constructors whose fields contain proofs. The result is cited in Remark 5.12 and
Example 5.13 of [CGSS]. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
-/

-- Basic
#print axioms Design
#print axioms Design.IsSymmetric
#print axioms Design.incMatrix
#print axioms Design.G
#print axioms Design.C
#print axioms Design.Z
#print axioms Design.sixCliques
#print axioms Design.card_blocksThrough_of_pair_counts_15_5_2
#print axioms Design.card_blocks_of_pair_counts_15_5_2
#print axioms Design.exists_of_pair_counts_15_5_2

-- Incidence
#print axioms Design.incMatrix_row_sum
#print axioms Design.incMatrix_col_sum
#print axioms Design.incMatrix_mul_transpose_apply
#print axioms Design.G_apply
#print axioms Design.G_transpose
#print axioms Design.incMatrix_mul_transpose_15_5_2
#print axioms Design.incMatrix_row_sum_15_5_2
#print axioms Design.incMatrix_col_sum_15_5_2
#print axioms Design.incMatrix_rat_mul_transpose_15_5_2
#print axioms Design.G_row_sum
#print axioms Design.G_mul_J
#print axioms Design.J_mul_G
#print axioms Design.J_mul_J
#print axioms Design.G_mul_G

-- Intersections
#print axioms Design.intersectionCount
#print axioms Design.sum_intersectionCount
#print axioms Design.sum_inter_card
#print axioms Design.sum_sq_inter_card
#print axioms Design.intersection_moments_sum
#print axioms Design.intersection_moments_15_5_2
#print axioms Design.inter_card_eq_one_or_two
#print axioms Design.intersectionCount_eq_zero
#print axioms Design.intersectionCount_one_two
#print axioms Design.decidableRelZ
#print axioms Design.card_neighbors
#print axioms Design.card_filter_inter_card_eq_two

-- CommonNeighbors
#print axioms Design.intersectionPairCount
#print axioms Design.sum_intersectionPairCount
#print axioms Design.intersection_pair_count_equations
#print axioms Design.intersection_pair_counts
#print axioms Design.card_commonNeighbors

-- Determinant
#print axioms Matrix.det_smul_one_add_smul_J

-- Connor
#print axioms Design.C_transpose
#print axioms Design.C_apply
#print axioms Design.C_mul_C
#print axioms Design.C_mul_incMatrix_transpose
#print axioms Design.C_quadratic_identity
#print axioms Design.C_quadratic_nonneg
#print axioms Design.rank_incMatrix_rat
#print axioms Design.rank_C_le_six
#print axioms Design.C_submatrix_gram
#print axioms Design.C_submatrix_quadratic_nonneg
#print axioms Design.rank_C_submatrix_le_six
#print axioms Design.det_C_submatrix_eq_zero

-- C19
#print axioms Computations.C19.clawMatrix
#print axioms Computations.C19.fiveBlockMatrix
#print axioms Computations.C19.Q1
#print axioms Computations.C19.Q2
#print axioms Computations.C19.K1
#print axioms Computations.C19.K2
#print axioms Computations.C19.claw_quadratic
#print axioms Computations.C19.five_block_quadratic
#print axioms Computations.C19.left_inverse_Q1
#print axioms Computations.C19.det_Q1_ne_zero
#print axioms Computations.C19.left_inverse_Q2
#print axioms Computations.C19.det_Q2_ne_zero

-- LocalRestrictions
#print axioms Design.Z_clawFree
#print axioms Design.not_adj_of_five_block_pattern

-- Neighborhood
#print axioms Design.neighborFiber
#print axioms Design.neighborFiber_eq
#print axioms Design.card_neighborFiber_of_adj
#print axioms Design.neighborFinset_eq_fibers
#print axioms Design.disjoint_neighborFiber
#print axioms Design.adj_or_adj_or_adj_of_three_neighbors
#print axioms Design.isClique_neighborFiber_true_false
#print axioms Design.card_common_part_neighbors
#print axioms Design.sum_card_common_part_neighbors
#print axioms Design.exists_common_neighbor_with_two_neighbors

-- LocalCounts
#print axioms Design.neighborFiber_swap
#print axioms Design.card_filter_neighborFinset
#print axioms Design.common_part_neighbor_sum
#print axioms Design.localDefect
#print axioms Design.localDefect_add_neighbors
#print axioms Design.local_counts
#print axioms Design.not_adj_local_parts

-- SevenPatterns
#print axioms Design.localDefect_ne_one
#print axioms Design.localDefect_ne_two
#print axioms Design.localDefect_eq_zero

-- SixCliques
#print axioms Design.mem_sixCliques
#print axioms Design.exists_sixClique_neighborhood_split

-- CliqueCounts
#print axioms Design.exists_unique_sixClique_of_adj
#print axioms Design.sixClique_eq_of_adj
#print axioms Design.card_sixCliques_through_block
#print axioms Design.card_sixCliques
#print axioms Design.sixClique_inter_card_le_one
#print axioms Design.sum_sixClique_inter_card
#print axioms Design.sixClique_inter_card

-- PointsInCliques
#print axioms Design.card_blocksThrough_in_sixClique

-- Extension
#print axioms Design.SixClique
#print axioms Design.card_SixClique
#print axioms Design.card_filter_SixClique
#print axioms Design.sixCliqueIncMatrix
#print axioms Design.hallConnorBlocks
#print axioms Design.hallConnorIncMatrix
#print axioms Design.card_hallConnorBlocks
#print axioms Design.card_blocksThrough_hallConnorBlocks
#print axioms Design.card_blocksThroughPair_hallConnorBlocks
#print axioms Design.hallConnorBlocks_parameters
#print axioms Design.hallConnorExtension
#print axioms Design.hallConnorExtension_isSymmetric
#print axioms Design.hallConnorExtension_residual

-- ExtensionMatrix
#print axioms Design.incMatrix_mul_sixCliqueIncMatrix
#print axioms Design.sixCliqueIncMatrix_transpose_mul
#print axioms Design.hallConnorIncMatrix_mul_transpose
#print axioms Design.hall_connor

-- C19Arithmetic
#print axioms Computations.C19.not_sq_eq_49_mul_5_pow_odd
#print axioms Computations.C19.not_sq_eq_49_mul_5_pow_21

-- BruckRyserChowla
#print axioms Matrix.bruck_ryser_chowla_twenty_two

-- Nonexistence
#print axioms Design.false_of_parameters_15_5_2
#print axioms Design.not_nonempty_15_5_2
#print axioms Design.not_pair_counts_15_5_2

-- Complement
#print axioms Design.card_compl_block
#print axioms Design.card_blocksThrough_compl
#print axioms Design.card_blocksThroughPair_compl
#print axioms Design.compl
#print axioms Design.false_of_parameters_15_10_9
#print axioms Design.not_nonempty_15_10_9
