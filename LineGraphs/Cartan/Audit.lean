/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Classification
import LineGraphs.Cartan.SmithGram

/-!
# Axiom audit for the finite Cartan classification prerequisites

This audit covers every public declaration introduced in `LineGraphs/Cartan/`,
including the full weighted dichotomy, the weighted classification of finite
Cartan matrices, and Theorem A of Remark 3.11 (`Matrix.IsFiniteCartan.classification`)
with its converse and uniqueness, and the Smith-graph facts of computation C17.
Private proof helpers are included transitively through their public callers.
-/

-- Affine.lean
#print axioms WeightedGraph.affineD
#print axioms WeightedGraph.endPath
#print axioms WeightedGraph.fork
#print axioms WeightedGraph.middlePath
#print axioms WeightedGraph.triplePath
#print axioms SimpleGraph.smithD
#print axioms WeightedGraph.IsAffineObstruction
#print axioms WeightedGraph.connected_reindex
#print axioms WeightedGraph.affineD_connected
#print axioms WeightedGraph.endPath_connected
#print axioms WeightedGraph.fork_connected
#print axioms WeightedGraph.IsAffineObstruction.connected
-- AffineDEigenvector.lean
#print axioms WeightedGraph.affineDEigenvector
#print axioms WeightedGraph.affineD_eigenvector
-- AffineEigenvectors.lean
#print axioms WeightedGraph.endPathEigenvector
#print axioms WeightedGraph.endPath_eigenvector
#print axioms WeightedGraph.armEigenvector
#print axioms WeightedGraph.smithE₆_eigenvector
#print axioms WeightedGraph.smithE₇_eigenvector
#print axioms WeightedGraph.smithE₈_eigenvector
#print axioms WeightedGraph.middlePath_eigenvector
#print axioms WeightedGraph.triplePath_eigenvector
-- AffineForkEigenvector.lean
#print axioms WeightedGraph.forkEigenvector
#print axioms WeightedGraph.fork_eigenvector
-- AffineSpectrum.lean
#print axioms WeightedGraph.exists_pos_eigenvector_reindex
#print axioms WeightedGraph.IsAffineObstruction.exists_pos_eigenvector
#print axioms WeightedGraph.IsAffineObstruction.maxRayleigh_eq_two
#print axioms Matrix.IsFiniteCartan.not_contains_affine
-- Attachments.lean
#print axioms WeightedGraph.attachLeaves
#print axioms WeightedGraph.attachLeaves_connected
#print axioms WeightedGraph.attachLeaves_mulVec_inl
#print axioms WeightedGraph.attachLeaves_mulVec_inr
-- Branches.lean
#print axioms SimpleGraph.Connected.exists_neighbor_deletedComponent
#print axioms SimpleGraph.IsAcyclic.eq_of_neighbor_deletedComponent
#print axioms SimpleGraph.IsTree.existsUnique_neighbor_deletedComponent
#print axioms SimpleGraph.IsTree.deletedComponentEquivNeighbor
#print axioms SimpleGraph.IsTree.deletedComponent_path_labelling
-- Cycle.lean
#print axioms SimpleGraph.cycleGraph_adj_iff_consecutive
#print axioms SimpleGraph.Walk.IsCycle.exists_cycle_embedding
#print axioms SimpleGraph.smithA_connected
#print axioms SimpleGraph.smithA_mulVec_one
-- DObstructions.lean
#print axioms SimpleGraph.Walk.IsPath.smithD_copy
#print axioms SimpleGraph.smithD_four_copy_of_degree_ge_four
#print axioms SimpleGraph.IsAcyclic.exists_two_neighbors_off_path
#print axioms SimpleGraph.IsTree.exists_smithD_copy_of_two_branches
-- DynkinD.lean
#print axioms SimpleGraph.finiteDToAffineD
#print axioms WeightedGraph.finiteD_maxRayleigh_lt_two
#print axioms WeightedGraph.HasDynkinLabelling.maxRayleigh_lt_two
#print axioms WeightedGraph.hasDynkinLabelling_iff_maxRayleigh_lt_two
#print axioms WeightedGraph.HasDynkinLabelling.not_contains_affine
#print axioms WeightedGraph.affine_or_dynkin
-- DynkinSpectrum.lean
#print axioms WeightedGraph.maxRayleigh_lt_two_of_contains_affine
#print axioms WeightedGraph.unit_path_maxRayleigh_lt_two
#print axioms WeightedGraph.terminal_double_path_maxRayleigh_lt_two
#print axioms WeightedGraph.middle_double_path_maxRayleigh_lt_two
#print axioms WeightedGraph.tripleEdge_maxRayleigh_lt_two
#print axioms WeightedGraph.finiteE_maxRayleigh_lt_two
-- LabelledGraphs.lean
#print axioms WeightedGraph.unit
#print axioms WeightedGraph.support_unit
#print axioms WeightedGraph.reindex
#print axioms WeightedGraph.unit_contains_iff_support_embedding
#print axioms WeightedGraph.path
#print axioms WeightedGraph.support_path
#print axioms SimpleGraph.ArmVertex
#print axioms SimpleGraph.armTree
#print axioms SimpleGraph.instDecidableRelArmTree
#print axioms SimpleGraph.armTree_connected
#print axioms SimpleGraph.smithA
#print axioms SimpleGraph.instDecidableRelSmithA
#print axioms SimpleGraph.smithE₆
#print axioms SimpleGraph.smithE₇
#print axioms SimpleGraph.smithE₈
#print axioms SimpleGraph.instDecidableRelSmithE₆
#print axioms SimpleGraph.instDecidableRelSmithE₇
#print axioms SimpleGraph.instDecidableRelSmithE₈
#print axioms WeightedGraph.connected_of_path_or_arm
-- Monotonicity.lean
#print axioms Matrix.extendByZero
#print axioms Matrix.extendByZero_apply
#print axioms Matrix.extendByZero_eq_zero
#print axioms Matrix.extendByZero_nonneg
#print axioms Matrix.dotProduct_extendByZero
#print axioms Matrix.dotProduct_extendByZero_self
#print axioms Matrix.quadratic_extendByZero
#print axioms Matrix.quadratic_mono_of_nonneg
#print axioms WeightedGraph.maxRayleigh_mono
#print axioms WeightedGraph.Contains.eq_of_maxRayleigh_eq
#print axioms WeightedGraph.maxRayleigh_strictMono
-- ObstructionFree.lean
#print axioms WeightedGraph.ext
#print axioms WeightedGraph.affineD_eq_unit
#print axioms WeightedGraph.ContainsAffineObstruction
#print axioms WeightedGraph.not_contains_of_no_affine
#print axioms WeightedGraph.not_containsAffineObstruction_reindex
#print axioms WeightedGraph.not_contains_affine_of_maxRayleigh_lt_two
#print axioms WeightedGraph.not_containsAffineObstruction_of_maxRayleigh_lt_two
#print axioms WeightedGraph.support_isAcyclic_of_no_affine
#print axioms WeightedGraph.support_isAcyclic_of_maxRayleigh_lt_two
#print axioms WeightedGraph.dynkin_support_of_no_affine
#print axioms WeightedGraph.dynkin_support_of_maxRayleigh_lt_two
#print axioms Matrix.IsFiniteCartan.one_le_weight
#print axioms Matrix.IsFiniteCartan.support_isAcyclic
#print axioms Matrix.IsFiniteCartan.dynkin_support
-- PathClassification.lean
#print axioms WeightedGraph.eq_path_of_consecutive
#print axioms WeightedGraph.singleDoublePath
#print axioms WeightedGraph.path_classification_of_no_affine
#print axioms WeightedGraph.path_classification_of_maxRayleigh_lt_two
-- PathLabelling.lean
#print axioms SimpleGraph.nonempty_iso_pathGraph
#print axioms SimpleGraph.path_labelling_reverse
#print axioms SimpleGraph.exists_path_labelling_from
-- PathMatrix.lean
#print axioms WeightedGraph.path_mulVec_first
#print axioms WeightedGraph.path_mulVec_last
#print axioms WeightedGraph.path_mulVec_interior
#print axioms WeightedGraph.path_mulVec_const
-- Positivity.lean
#print axioms Matrix.mulVec_eq_zero_of_quadratic_eq_zero
#print axioms Matrix.quadratic_nonneg_rat_of_posSemidef_int
#print axioms Matrix.posSemidef_real_of_posSemidef_int
#print axioms Matrix.posDef_real_of_posDef_int
-- Rayleigh.lean
#print axioms Matrix.maxRayleigh
#print axioms Matrix.IsHermitian.quadratic_le_maxRayleigh
#print axioms Matrix.IsHermitian.rayleigh_eq_iff
#print axioms Matrix.IsHermitian.maxRayleigh_eigenvalue
#print axioms Matrix.IsHermitian.exists_nonneg_max_eigenvector
#print axioms Matrix.IsHermitian.supportGraph
#print axioms Matrix.IsHermitian.eq_zero_of_nonneg_eigenvector_zero
#print axioms Matrix.IsHermitian.exists_pos_max_eigenvector
#print axioms Matrix.IsHermitian.eigenvector_eq_smul_of_pos
#print axioms Matrix.IsHermitian.max_eigenspace_simple
#print axioms Matrix.IsHermitian.eigenvalue_eq_maxRayleigh_of_pos
#print axioms Matrix.IsHermitian.maxRayleigh_reindex
#print axioms WeightedGraph.support_eq_supportGraph
#print axioms WeightedGraph.eigenvalue_eq_maxRayleigh_of_pos
#print axioms WeightedGraph.exists_pos_max_eigenvector
-- Support.lean
#print axioms SimpleGraph.Connected.constant_of_edge_eq
#print axioms SimpleGraph.Connected.exists_constant_of_edge_eq
#print axioms Matrix.supportGraph
#print axioms Matrix.isIndecomposable_iff_connected_support
-- Symmetrization.lean
#print axioms Matrix.cartanSymmetrization
#print axioms Matrix.cartanSymmetrization_apply
#print axioms Matrix.posDef_cartanSymmetrization
#print axioms Matrix.PosDef.apply_sq_lt_four
#print axioms Matrix.IsFiniteCartan.weightedGraph
#print axioms Matrix.IsFiniteCartan.cartanSymmetrization_diag
#print axioms Matrix.IsFiniteCartan.cartanSymmetrization_sq
#print axioms Matrix.IsFiniteCartan.edge_product_mem
#print axioms Matrix.IsFiniteCartan.weightedGraph_support
#print axioms Matrix.IsFiniteCartan.cartanSymmetrization_eq
#print axioms Matrix.IsFiniteCartan.weightedGraph_weight_mem
#print axioms Matrix.IsFiniteCartan.maxRayleigh_weightedGraph_lt_two
#print axioms Matrix.IsFiniteCartan.symmetrization
-- ThreeArmLabelling.lean
#print axioms SimpleGraph.exists_three_arm_labelling
-- TripleEdge.lean
#print axioms WeightedGraph.contains_triplePath_of_two_edges
#print axioms WeightedGraph.eq_or_eq_of_sqrt_three_le_weight_of_no_affine
#print axioms WeightedGraph.eq_or_eq_of_sqrt_three_le_weight
#print axioms WeightedGraph.tripleEdge
#print axioms WeightedGraph.eq_tripleEdge_reindex_of_weight_eq_sqrt_three_of_no_affine
#print axioms WeightedGraph.eq_tripleEdge_reindex_of_weight_eq_sqrt_three
-- UnweightedTrees.lean
#print axioms SimpleGraph.armTreeEmbedding
#print axioms SimpleGraph.dynkin_labelling_of_no_affine
-- WeightedArms.lean
#print axioms SimpleGraph.armPathVertex
#print axioms SimpleGraph.armPathVertex_injective
#print axioms SimpleGraph.armPathVertex_adj
#print axioms SimpleGraph.armPathVertex_succ
#print axioms SimpleGraph.armTree_adj_exists_consecutive
#print axioms WeightedGraph.contains_fork_of_heavy_arm
#print axioms WeightedGraph.arm_edge_lt_sqrt_two_of_no_affine
#print axioms WeightedGraph.arm_edge_lt_sqrt_two_of_maxRayleigh_lt_two
#print axioms WeightedGraph.eq_unit_of_arm_support_of_no_affine
#print axioms WeightedGraph.eq_unit_of_arm_support
-- WeightedClassification.lean
#print axioms WeightedGraph.reindex_symm_cancel
#print axioms WeightedGraph.reindex_trans
#print axioms WeightedGraph.HasDynkinLabelling
#print axioms WeightedGraph.dynkin_labelling_of_no_affine
#print axioms WeightedGraph.dynkin_labelling_of_maxRayleigh_lt_two
#print axioms Matrix.IsFiniteCartan.weighted_classification
-- WeightedGraph.lean
#print axioms WeightedGraph
#print axioms WeightedGraph.support
#print axioms WeightedGraph.isHermitian
#print axioms WeightedGraph.Contains
#print axioms WeightedGraph.eq_zero_of_nonneg_eigenvector_zero
-- WeightedPaths.lean
#print axioms WeightedGraph.contains_path_of_consecutive
#print axioms WeightedGraph.intervalEmbedding
#print axioms WeightedGraph.contains_endPath_of_two_heavy_edges
#print axioms WeightedGraph.contains_middlePath_of_heavy_interior
#print axioms WeightedGraph.contains_middlePath_of_heavy_second
#print axioms WeightedGraph.heavy_edge_unique_of_no_affine
#print axioms WeightedGraph.heavy_edge_unique_of_maxRayleigh_lt_two
#print axioms WeightedGraph.heavy_edge_position_of_no_affine
#print axioms WeightedGraph.heavy_edge_position_of_maxRayleigh_lt_two

-- Structure fields and inductive constructors.
#print axioms WeightedGraph.mk
#print axioms WeightedGraph.weights
#print axioms WeightedGraph.symmetric
#print axioms WeightedGraph.nonneg
#print axioms WeightedGraph.diag
#print axioms WeightedGraph.IsAffineObstruction.cycle
#print axioms WeightedGraph.IsAffineObstruction.d
#print axioms WeightedGraph.IsAffineObstruction.e₆
#print axioms WeightedGraph.IsAffineObstruction.e₇
#print axioms WeightedGraph.IsAffineObstruction.e₈
#print axioms WeightedGraph.IsAffineObstruction.ends
#print axioms WeightedGraph.IsAffineObstruction.fork
#print axioms WeightedGraph.IsAffineObstruction.middle
#print axioms WeightedGraph.IsAffineObstruction.triple
#print axioms WeightedGraph.HasDynkinLabelling.a
#print axioms WeightedGraph.HasDynkinLabelling.doublePath
#print axioms WeightedGraph.HasDynkinLabelling.d
#print axioms WeightedGraph.HasDynkinLabelling.e₆
#print axioms WeightedGraph.HasDynkinLabelling.e₇
#print axioms WeightedGraph.HasDynkinLabelling.e₈
#print axioms WeightedGraph.HasDynkinLabelling.g₂

-- Theorem A of Remark 3.11: the named models, orientations, converse, invariants.
-- Models.lean
#print axioms CartanMatrix.FiniteType
#print axioms CartanMatrix.instDecidableEqFiniteType
#print axioms CartanMatrix.modelEntries
#print axioms CartanMatrix.IsFiniteTypeModel
#print axioms CartanMatrix.FiniteType.rank_pos
#print axioms CartanMatrix.modelEntries_isFiniteTypeModel
#print axioms CartanMatrix.isFiniteTypeModel_iff
#print axioms CartanMatrix.weightedGraph
#print axioms CartanMatrix.weightedGraph_eq
#print axioms CartanMatrix.weightedGraph_transpose
#print axioms CartanMatrix.weightedGraph_A
#print axioms CartanMatrix.weightedGraph_B
#print axioms CartanMatrix.weightedGraph_C
#print axioms CartanMatrix.dVertex
#print axioms CartanMatrix.dVertex_bijective
#print axioms CartanMatrix.dEquiv
#print axioms CartanMatrix.D_dVertex_apply
#print axioms CartanMatrix.weightedGraph_eq_unit_reindex
#print axioms CartanMatrix.weightedGraph_D
#print axioms CartanMatrix.eVertex
#print axioms CartanMatrix.eVertex_bijective
#print axioms CartanMatrix.eEquiv
#print axioms CartanMatrix.E_eVertex_apply
#print axioms CartanMatrix.weightedGraph_E
#print axioms CartanMatrix.weightedGraph_E_support_connected
#print axioms CartanMatrix.weightedGraph_F₄
#print axioms CartanMatrix.weightedGraph_G₂
#print axioms CartanMatrix.model_support_labelling
#print axioms WeightedGraph.HasDynkinLabelling.connected
#print axioms CartanMatrix.model_diag
#print axioms CartanMatrix.model_offDiag_nonpos
#print axioms CartanMatrix.B_zero_comm
#print axioms CartanMatrix.model_zero_comm
#print axioms CartanMatrix.model_support_connected
-- Orientation.lean
#print axioms Matrix.IsFiniteCartan.submatrix
#print axioms Matrix.IsFiniteCartan.weightedGraph_submatrix
#print axioms Matrix.IsFiniteCartan.weightedGraph_weight_sq
#print axioms Matrix.IsFiniteCartan.entry_eq_zero_of_weight_eq_zero
#print axioms Matrix.IsFiniteCartan.entry_eq_neg_one_of_weight_eq_one
#print axioms Matrix.IsFiniteCartan.entry_pair_of_weight_eq_sqrt_two
#print axioms Matrix.IsFiniteCartan.entry_pair_of_weight_eq_sqrt_three
#print axioms Matrix.IsFiniteCartan.eq_of_weightedGraph_eq_of_isSimplyLaced
#print axioms Matrix.IsFiniteCartan.eq_of_weightedGraph_eq_of_entry_pair
#print axioms Matrix.IsFiniteCartan.eq_or_transpose_of_weightedGraph_eq
#print axioms WeightedGraph.singleDoublePath_reindex_rev
#print axioms Matrix.IsFiniteCartan.eq_B_or_C_of_weightedGraph_eq
#print axioms Matrix.IsFiniteCartan.eq_F₄_or_transpose_of_weightedGraph_eq
#print axioms Matrix.IsFiniteCartan.eq_G₂_or_transpose_of_weightedGraph_eq
#print axioms CartanMatrix.C_two_submatrix_rev
#print axioms CartanMatrix.F₄_transpose_submatrix_rev
#print axioms CartanMatrix.G₂_transpose_submatrix_rev
-- Recognition.lean
#print axioms WeightedGraph.reindex_change
#print axioms Matrix.IsFiniteCartan.weightedGraph_eq_of_labelling
#print axioms Matrix.IsFiniteCartan.exists_model_of_terminal_double_path
#print axioms Matrix.IsFiniteCartan.exists_model_of_middle_double_path
#print axioms Matrix.IsFiniteCartan.exists_model_of_triple_edge
#print axioms Matrix.IsFiniteCartan.exists_model_of_dynkin_labelling
-- Converse.lean
#print axioms Matrix.IsHermitian.posDef_two_smul_one_sub
#print axioms Matrix.PosDef.posDef_int_of_posDef_real
#print axioms Matrix.cartanSymmetrization_eq_of_balance
#print axioms Matrix.PosDef.posDef_diagonal_mul_of_cartanSymmetrization
#print axioms CartanMatrix.modelSymmetrizer
#print axioms CartanMatrix.modelSymmetrizer_pos
#print axioms CartanMatrix.modelSymmetrizer_balance
#print axioms CartanMatrix.IsFiniteTypeModel.isFiniteCartan
#print axioms CartanMatrix.IsFiniteTypeModel.isIndecomposable
-- Invariants.lean
#print axioms CartanMatrix.supportDegree
#print axioms CartanMatrix.supportInvariants
#print axioms CartanMatrix.supportDegree_submatrix
#print axioms CartanMatrix.supportInvariants_reindex
#print axioms CartanMatrix.sum_ite_fin_val_eq
#print axioms CartanMatrix.supportDegree_A
#print axioms CartanMatrix.supportDegree_B
#print axioms CartanMatrix.supportDegree_C
#print axioms CartanMatrix.supportInvariants_A
#print axioms CartanMatrix.supportDegree_D
#print axioms CartanMatrix.supportDegree_D_eq_three
#print axioms CartanMatrix.sum_ite_pair_eq
#print axioms CartanMatrix.supportInvariants_of_single_double_path
#print axioms CartanMatrix.supportInvariants_B
#print axioms CartanMatrix.supportInvariants_C
#print axioms CartanMatrix.supportInvariants_D
#print axioms CartanMatrix.supportInvariants_E₆
#print axioms CartanMatrix.supportInvariants_E₇
#print axioms CartanMatrix.supportInvariants_E₈
#print axioms CartanMatrix.supportInvariants_F₄
#print axioms CartanMatrix.supportInvariants_G₂
#print axioms CartanMatrix.modelInvariants
#print axioms CartanMatrix.model_supportInvariants
#print axioms CartanMatrix.FiniteType.eq_of_modelInvariants_eq
#print axioms CartanMatrix.IsFiniteTypeModel.type_eq_of_reindex_eq
-- SmithGram.lean
#print axioms WeightedGraph.posSemidef_two_sub_of_maxRayleigh_eq_two
#print axioms WeightedGraph.posDef_two_sub_delete
#print axioms WeightedGraph.gram_delete_basis
#print axioms WeightedGraph.rank_two_sub_eq_card_sub_one
#print axioms WeightedGraph.exists_gram_card_sub_one
#print axioms WeightedGraph.IsAffineObstruction.gram_delete_basis
#print axioms SimpleGraph.smith_gram_delete_basis
#print axioms WeightedGraph.unit_support_eq
#print axioms WeightedGraph.affineD_weights_eq_zero_or_one
#print axioms SimpleGraph.smithA_maxRayleigh
#print axioms SimpleGraph.unit_smithD
#print axioms SimpleGraph.smithD_maxRayleigh
#print axioms SimpleGraph.smithE₆_maxRayleigh
#print axioms SimpleGraph.smithE₇_maxRayleigh
#print axioms SimpleGraph.smithE₈_maxRayleigh
-- Classification.lean
#print axioms Matrix.IsFiniteCartan.classification
#print axioms Matrix.IsFiniteCartan.classification_type_unique
-- Constructors of the permitted types.
#print axioms CartanMatrix.FiniteType.a
#print axioms CartanMatrix.FiniteType.b
#print axioms CartanMatrix.FiniteType.c
#print axioms CartanMatrix.FiniteType.d
#print axioms CartanMatrix.FiniteType.e₆
#print axioms CartanMatrix.FiniteType.e₇
#print axioms CartanMatrix.FiniteType.e₈
#print axioms CartanMatrix.FiniteType.f₄
#print axioms CartanMatrix.FiniteType.g₂
