/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.TrivialDesignException
import LineGraphs.Computations.C13Characterization
import LineGraphs.LineGraphSpectra.Remark512
import LineGraphs.LineGraphSpectra.Example513

/-!
# Axiom audit of the design flag-graph classification

Theorem 5.8 (`thm:5.8`), Corollaries 5.9–5.11 (`cor:5.9`–`cor:5.11`),
Remark 5.12 (`rem:5.12`), and Example 5.13 (`ex:5.13`) of [CGSS], with
all new supporting declarations.
The expected axiom set is contained in `propext`, `Classical.choice`, and `Quot.sound`.
-/

#print axioms SimpleGraph.completeBipartiteSwapIso
#print axioms SimpleGraph.lineGraph_completeBipartite_eq_top_of_right_eq_one
#print axioms SimpleGraph.HasCompleteBipartiteHadamardException
#print axioms SimpleGraph.hasCompleteBipartiteHadamardException_of_parameters
#print axioms SimpleGraph.lineGraph_completeBipartite_characterized_of_le
#print axioms SimpleGraph.lineGraph_completeBipartite_characterized
#print axioms Design.IsSymmetric.flagGraphCharacterized
#print axioms Design.flagGraphCharacterized_of_lam_eq_one
#print axioms Design.incidenceGraph
#print axioms Design.incidenceGraphDecidable
#print axioms Design.flagGraph
#print axioms Design.FlagGraphCharacterized
#print axioms Design.incidenceGraph_degree_inl
#print axioms Design.incidenceGraph_degree_inr
#print axioms Design.pointPart
#print axioms Design.blockPart
#print axioms Design.pointPartEquiv
#print axioms Design.blockPartEquiv
#print axioms Design.card_pointPart
#print axioms Design.card_blockPart
#print axioms Design.incidenceGraph_isBiregularWith
#print axioms Design.incidenceGraph_degree_pos
#print axioms Design.incidenceGraph_edgeSet_nonempty
#print axioms Design.incidenceGraph_connected
#print axioms Design.incidenceGraph_isRegular_iff
#print axioms Design.flagGraph_connected
#print axioms Design.flagGraph_isRegularOfDegree
#print axioms Design.card_flagGraph
#print axioms Design.posSemidef_two_add_adjMatrix_flagGraph
#print axioms Design.rank_two_add_adjMatrix_flagGraph
#print axioms Design.biadjMatrix_submatrix_eq_realIncMatrix
#print axioms Design.spectrumMultiset_biadjMatrix_mul_transpose
#print axioms Design.rank_biadjMatrix
#print axioms Design.b_mul_k_eq_v_mul_r
#print axioms Design.r_mul_k_sub_one_eq
#print axioms Design.k_le_v
#print axioms Design.r_pos
#print axioms Design.one_le_lam
#print axioms Design.lam_le_r
#print axioms Design.lam_eq_r_iff
#print axioms Design.block_eq_univ_of_k_eq_v
#print axioms Design.realIncMatrix
#print axioms Design.realIncMatrix_apply
#print axioms Design.realIncMatrix_row_sum
#print axioms Design.realIncMatrix_col_sum
#print axioms Design.incMatrix_mul_transpose
#print axioms Design.spectrumMultiset_incMatrix_mul_transpose
#print axioms Design.rank_realIncMatrix_of_lam_lt_r
#print axioms Design.v_le_b_of_lam_lt_r
#print axioms Matrix.gram_eq_of_two_eigenvalues
#print axioms Design.ofIncMatrix
#print axioms SimpleGraph.IsBiregularWith.biadjMatrix_row_sum
#print axioms SimpleGraph.IsBiregularWith.biadjMatrix_col_sum
#print axioms Design.exists_design_of_biregular_gram_spectrum
#print axioms Design.spectrumMultiset_signlessLapMatrix_incidenceGraph
#print axioms SimpleGraph.lineGraph_cospectral_of_signless_spectrum_add_zero
#print axioms Design.rank_realIncMatrix_of_lam_eq_r
#print axioms Design.lineGraph_spectrum_of_not_isBipartite
#print axioms Matrix.IsHermitian.eq_spectralIdempotent_of_eigenprojections
#print axioms Matrix.IsHermitian.finrank_eigenspace_of_eigenprojections
#print axioms Matrix.IsHermitian.spectrumMultiset_eq_of_eigenprojections
#print axioms SimpleGraph.Cospectral.change_instances
#print axioms Design.not_flagGraphCharacterized_of_resolvable
#print axioms Computations.C15.incidenceGraph_eq_shared
#print axioms Computations.C15.sharedFlagGraphIso
#print axioms Computations.C15.design_flagGraph_cospectral_petersen
#print axioms Computations.C15.design_flagGraph_not_nonempty_iso_petersen
#print axioms Computations.C15.not_flagGraphCharacterized
#print axioms Design.nonbipartiteParameters_and_even_resolution_family
#print axioms Design.Resolution.spectrumMultiset_graph_nonbipartite_form
#print axioms Design.NonbipartiteParameters
#print axioms Design.exists_nonbipartite_parameters
#print axioms Design.NonbipartiteParameters.pair_count_real
#print axioms Design.NonbipartiteParameters.root_order
#print axioms Design.NonbipartiteParameters.root_degree
#print axioms SimpleGraph.even_mul_of_nonbipartite_design_spectrum
#print axioms Matrix.resolutionProjections
#print axioms Matrix.resolutionEigenvalues
#print axioms Matrix.resolutionMultiplicities
#print axioms Matrix.resolutionEigenvalues_injective
#print axioms Matrix.mul_resolutionProjections
#print axioms Matrix.isHermitian_resolutionProjections
#print axioms Matrix.sum_resolutionProjections
#print axioms Matrix.trace_resolutionProjections
#print axioms SimpleGraph.exists_forall_degree_pos_nonempty_iso_lineGraph
#print axioms SimpleGraph.cocktailParty_isRegularOfDegree
#print axioms SimpleGraph.nonempty_iso_cocktailParty
#print axioms Matrix.HasSymmetricHadamardWithConstantDiagonal
#print axioms SimpleGraph.hasSymmetricHadamardWithConstantDiagonal_of_spectrum
#print axioms Sym2.exists_common_mem_of_card_gt_three
#print axioms SimpleGraph.card_clique_lineGraph_le
#print axioms Design.exists_clique_flagGraph_card_replication
#print axioms Design.not_nonempty_iso_flagGraph_lineGraph_of_degree
#print axioms Design.flagGraphCharacterized_of_lam_lt_nineteen
#print axioms Design.Resolution
#print axioms Design.transpose_realIncMatrix_mul_apply
#print axioms Design.inter_card_le_one_of_lam_eq_one
#print axioms Design.Resolution.classMatrix
#print axioms Design.Resolution.graph
#print axioms Design.Resolution.disjoint_of_classOf_eq
#print axioms Design.Resolution.card_blocksThrough_class
#print axioms Design.Resolution.card_class_mul
#print axioms Design.Resolution.realIncMatrix_mul_classMatrix_transpose
#print axioms Design.Resolution.sum_classMatrix
#print axioms Design.Resolution.transpose_classMatrix_mul_apply
#print axioms Design.Resolution.adjMatrix_graph
#print axioms Design.Resolution.card_class
#print axioms Design.Resolution.classMatrix_mul_transpose
#print axioms Design.Resolution.realIncMatrix_mul_transpose
#print axioms Design.Resolution.rank_realIncMatrix
#print axioms Design.spectrumMultiset_signlessLapMatrix_incidenceGraph_resolution_family
#print axioms Design.Resolution.spectrumMultiset_signlessLapMatrix_graph
#print axioms Design.Resolution.signless_spectrum_pos
#print axioms Design.Resolution.card_edges_graph
#print axioms Design.Resolution.flagGraph_cospectral_lineGraph
#print axioms Design.Resolution.zeroSum
#print axioms Design.Resolution.W₁
#print axioms Design.Resolution.W₂
#print axioms Design.Resolution.W₃
#print axioms Design.Resolution.projections_eq_spectralIdempotent
#print axioms Design.Resolution.projections_mulVec_of_eigenvector
#print axioms Design.Resolution.eigenvector_of_projection_fixed
#print axioms Design.Resolution.sum_classMatrix_mulVec
#print axioms Design.Resolution.sum_realIncMatrix_mulVec
#print axioms Design.Resolution.allOnes_mulVec
#print axioms Design.Resolution.sum_eq_zero_of_eigenvector
#print axioms Design.Resolution.sum_transpose_realIncMatrix_mulVec
#print axioms Design.Resolution.W₁_eq_eigenspace
#print axioms Design.Resolution.W₂_eq_eigenspace
#print axioms Design.Resolution.W₃_eq_eigenspace
#print axioms Design.Resolution.classMatrix_transpose_mulVec_injective
#print axioms Design.Resolution.finrank_ker_realIncMatrix
#print axioms Design.Resolution.realIncMatrix_transpose_mulVec_injective
#print axioms Design.Resolution.W₁_le_ker_realIncMatrix
#print axioms Design.Resolution.mem_W₃_iff_ker_and_orthogonal
#print axioms Design.Resolution.finrank_W₁_W₂_W₃
#print axioms Design.Resolution.classGram_row_sum
#print axioms Design.Resolution.incidenceGram_row_sum
#print axioms Design.Resolution.adjMatrix_products
#print axioms Design.Resolution.projections
#print axioms Design.Resolution.mul_projections
#print axioms Design.Resolution.isHermitian_projections
#print axioms Design.Resolution.sum_projections
#print axioms Design.Resolution.trace_projections
#print axioms Design.Resolution.finrank_eigenspace
#print axioms Design.Resolution.spectrumMultiset_graph
#print axioms Design.Resolution.graph_isRegularOfDegree
#print axioms Design.Resolution.graph_connected
#print axioms Design.Resolution.graph_not_isBipartite
#print axioms SimpleGraph.eq_top_of_isRegularOfDegree_card_sub_one
#print axioms SimpleGraph.Cospectral.nonempty_iso_of_isRegularOfDegree_card_sub_one
#print axioms Design.flagGraphCharacterized_of_b_eq_one
#print axioms Design.flagGraphCharacterized_of_parameters_3_2_1
#print axioms Design.trivial
#print axioms Design.incidenceGraphCompleteBipartiteIso
#print axioms Design.nonempty_iso_flagGraph_lineGraph_completeBipartite
#print axioms Design.flagGraph_cospectral

#print axioms Computations.C13.not_flagGraphCharacterized

-- Remark 5.12 of [CGSS]: the trivial-design exception
#print axioms Computations.TrivialDesignException.design
#print axioms Computations.TrivialDesignException.incidenceSignless
#print axioms Computations.TrivialDesignException.completeAdjacency
#print axioms Computations.TrivialDesignException.incidence_spectrum_checked
#print axioms Computations.TrivialDesignException.complete_spectrum_checked
#print axioms Computations.TrivialDesignException.incidence_signless_eq
#print axioms Computations.TrivialDesignException.spectrum_incidence_signless
#print axioms Computations.TrivialDesignException.spectrum_complete
#print axioms Computations.TrivialDesignException.spectrum_triangular
#print axioms Computations.TrivialDesignException.spectrum_flagGraph
#print axioms Computations.TrivialDesignException.spectrum_double_lineGraph
#print axioms Computations.TrivialDesignException.flagGraph_cospectral_double_lineGraph
#print axioms Computations.TrivialDesignException.not_flagGraphCharacterized

#print axioms Computations.TrivialDesignException.incidenceIndex

#print axioms
  Computations.TrivialDesignException.lineGraph_completeBipartite_cospectral_double_lineGraph

#print axioms Computations.TrivialDesignException.flagGraph_not_nonempty_iso_double_lineGraph
