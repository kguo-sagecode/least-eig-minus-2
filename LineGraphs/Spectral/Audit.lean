/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.LineGraphSpectrum
import LineGraphs.Spectral.Multiplicity
import LineGraphs.Spectral.Positivity
import LineGraphs.Spectral.Rayleigh
import LineGraphs.Spectral.Regular
import LineGraphs.Spectral.Signless
import LineGraphs.Spectral.Regularity
import LineGraphs.Spectral.LineGraphRegular
import LineGraphs.Spectral.Interlacing
import LineGraphs.Spectral.PerronFrobenius
import LineGraphs.Spectral.StrictMono
import LineGraphs.Spectral.Polynomial
import LineGraphs.Spectral.Cospectral
import LineGraphs.Spectral.GraphCertificates
import LineGraphs.Spectral.TraceRank
import LineGraphs.Spectral.GramProducts
import LineGraphs.Spectral.Incidence
import LineGraphs.Spectral.Applications
import LineGraphs.Spectral.LineGraphRecovery
import LineGraphs.Spectral.Gram
import LineGraphs.Spectral.GraphRepresentation
import LineGraphs.Spectral.AllOnes
import LineGraphs.Spectral.Frames
import LineGraphs.Spectral.RationalEigenvalues
import LineGraphs.Spectral.Walks
import LineGraphs.Spectral.HoffmanPolynomial
import LineGraphs.Spectral.RelativeBound

/-!
# Axiom audit for the spectral toolkit

Each declaration should use only `propext`, `Classical.choice` and `Quot.sound`.

This module is imported by the root `LineGraphs.lean`, so that `lake build LineGraphs` prints the
audit. It could equally be left out of the root imports and run on its own with
`lake env lean LineGraphs/Spectral/Audit.lean`.
-/

-- Theorem 2.2 and Lemma 2.4
#print axioms Matrix.spectrumMultiset_eq_of_orthonormal_eigenbasis
#print axioms Matrix.eigenvalueMultiplicity_eq_rootMultiplicity
#print axioms Matrix.IsHermitian.sortedEigenvectorBasis
#print axioms Matrix.IsHermitian.mulVec_sortedEigenvectorBasis
#print axioms Matrix.IsHermitian.spectrumMultiset_eq_eigenvalues₀
#print axioms Matrix.IsHermitian.card_spectrumMultiset
#print axioms Matrix.IsHermitian.eigenvalueMultiplicity_eq_finrank
#print axioms Matrix.IsHermitian.mem_spectrumMultiset_iff
#print axioms Matrix.IsHermitian.mem_spectrumMultiset_iff_mem_spectrum
#print axioms Matrix.IsHermitian.eigenvalues_mem_spectrumMultiset
#print axioms Matrix.IsHermitian.largestEigenvalue_mem_spectrumMultiset
#print axioms Matrix.IsHermitian.leastEigenvalue_mem_spectrumMultiset
#print axioms Matrix.lastIndex
#print axioms Matrix.IsHermitian.le_largestEigenvalue_of_mem
#print axioms Matrix.IsHermitian.leastEigenvalue_le_of_mem
#print axioms Matrix.IsHermitian.eigenvalues_le_largestEigenvalue
#print axioms Matrix.IsHermitian.leastEigenvalue_le_eigenvalues

-- Theorem 3.3 and Corollary 3.4 (positivity, shifts, the -2 bridge)
#print axioms Matrix.IsHermitian.spectrumMultiset_smul_one_add_smul
#print axioms Matrix.IsHermitian.smul_one_add_smul
#print axioms Matrix.IsHermitian.det_eq_prod_spectrumMultiset
#print axioms Matrix.IsHermitian.posSemidef_iff_spectrumMultiset_nonneg
#print axioms Matrix.IsHermitian.posDef_iff_spectrumMultiset_pos
#print axioms Matrix.IsHermitian.posSemidef_sub_smul_one_iff
#print axioms Matrix.IsHermitian.posSemidef_smul_one_sub_iff
#print axioms Matrix.IsHermitian.mem_spectrumMultiset_iff_det_eq_zero
#print axioms Matrix.IsHermitian.le_leastEigenvalue_iff
#print axioms Matrix.IsHermitian.largestEigenvalue_le_iff
#print axioms SimpleGraph.posSemidef_two_add_adjMatrix_iff
#print axioms SimpleGraph.neg_two_mem_spectrumMultiset_iff_det_eq_zero
#print axioms SimpleGraph.posSemidef_two_add_adjMatrix_iff_neg_two_le_leastEigenvalue
#print axioms SimpleGraph.leastEigenvalue_eq_neg_two_iff
#print axioms SimpleGraph.posSemidef_two_sub_adjMatrix_iff

-- Theorem 4.1 (Rayleigh)
#print axioms Matrix.toEuclideanLin_eq_sum_of_orthonormal_eigenbasis
#print axioms Matrix.dotProduct_mulVec_eq_sum_of_orthonormal_eigenbasis
#print axioms Matrix.dotProduct_self_eq_sum_of_orthonormal_basis
#print axioms Matrix.mulVec_eq_smul_iff_of_orthonormal_eigenbasis
#print axioms Matrix.IsHermitian.largestEigenvalue_mul_sub_eq_sum
#print axioms Matrix.IsHermitian.sub_leastEigenvalue_mul_eq_sum
#print axioms Matrix.IsHermitian.mem_Icc_of_orthonormal_eigenbasis
#print axioms Matrix.IsHermitian.dotProduct_mulVec_le_largestEigenvalue_mul
#print axioms Matrix.IsHermitian.leastEigenvalue_mul_le_dotProduct_mulVec
#print axioms Matrix.IsHermitian.rayleigh_le_largestEigenvalue
#print axioms Matrix.IsHermitian.leastEigenvalue_le_rayleigh
#print axioms Matrix.IsHermitian.rayleigh_eq_largestEigenvalue_iff
#print axioms Matrix.IsHermitian.rayleigh_eq_leastEigenvalue_iff
#print axioms Matrix.re_inner_toEuclideanLin_div
#print axioms Matrix.IsHermitian.mulVec_sortedEigenvectorBasis_zero
#print axioms Matrix.IsHermitian.iSup_rayleigh_eq_largestEigenvalue
#print axioms Matrix.IsHermitian.mulVec_sortedEigenvectorBasis_last
#print axioms Matrix.IsHermitian.iInf_rayleigh_eq_leastEigenvalue
#print axioms Matrix.IsHermitian.dotProduct_eq_zero_of_eigenvalue_ne

-- Theorems 5.3 and 5.6 (SP1, SP3)
#print axioms SimpleGraph.eq_of_reachable_of_forall_adj
#print axioms SimpleGraph.abs_eq_of_reachable_of_forall_adj
#print axioms SimpleGraph.adjMatrix_mulVec_eq_smul_iff
#print axioms SimpleGraph.IsRegularOfDegree.two_mul_dotProduct_mulVec
#print axioms SimpleGraph.IsRegularOfDegree.posSemidef_smul_one_add_smul
#print axioms SimpleGraph.IsRegularOfDegree.mulVec_eq_zero_iff
#print axioms SimpleGraph.IsRegularOfDegree.mem_Icc_of_mem_spectrumMultiset
#print axioms SimpleGraph.IsRegularOfDegree.largestEigenvalue_eq
#print axioms SimpleGraph.IsRegularOfDegree.multiplicity_eq_card_components
#print axioms SimpleGraph.IsRegularOfDegree.isBipartite_iff_neg_eigenvalue
#print axioms SimpleGraph.IsRegularOfDegree.multiplicity_neg_eq_one
#print axioms SimpleGraph.IsBipartite.multiplicity_neg_eq

-- Theorem 5.2 (general signless Laplacian)
#print axioms SimpleGraph.signlessLapMatrix
#print axioms SimpleGraph.isHermitian_signlessLapMatrix
#print axioms SimpleGraph.two_mul_dotProduct_signlessLapMatrix
#print axioms SimpleGraph.posSemidef_signlessLapMatrix
#print axioms SimpleGraph.signlessLapMatrix_mulVec_eq_zero_iff
#print axioms SimpleGraph.Connected.isBipartite_of_forall_adj_add_eq_zero
#print axioms SimpleGraph.finrank_ker_signlessLapMatrix_eq_card_bipartite_components

-- Theorem 5.4 (SP2), second moments, and Corollary 5.5
#print axioms SimpleGraph.sum_sq_spectrumMultiset_eq_sum_degrees
#print axioms SimpleGraph.sum_sq_spectrumMultiset_eq_twice_card_edges
#print axioms SimpleGraph.isRegular_iff_sum_sq_eigenvalues
#print axioms Matrix.IsHermitian.spectrumMultiset_eq_iff_charpoly_eq
#print axioms SimpleGraph.cospectral_iff_spectrumMultiset_eq
#print axioms SimpleGraph.Cospectral.spectrumMultiset_eq
#print axioms SimpleGraph.Cospectral.card_eq
#print axioms SimpleGraph.Cospectral.eigenvalueMultiplicity_eq
#print axioms SimpleGraph.Cospectral.largestEigenvalue_eq
#print axioms SimpleGraph.Cospectral.isRegularOfDegree
#print axioms SimpleGraph.Cospectral.card_connectedComponent_eq_of_regular
#print axioms SimpleGraph.Cospectral.connected_of_regular

-- Lemma 6.3 and Theorem 6.4 (SP4), including the blueprint interface
#print axioms SimpleGraph.IsBiregularWith
#print axioms SimpleGraph.IsBiregularWith.isBipartiteWith
#print axioms SimpleGraph.IsBiregularWith.union_eq
#print axioms SimpleGraph.IsBiregularWith.degree_left
#print axioms SimpleGraph.IsBiregularWith.degree_right
#print axioms SimpleGraph.connected_of_lineGraph_connected
#print axioms SimpleGraph.lineGraph_connected_iff_of_no_isolated
#print axioms SimpleGraph.degree_lineGraph
#print axioms SimpleGraph.regular_or_semiregular_of_lineGraph_regular
#print axioms SimpleGraph.regular_or_isBiregularWith_of_lineGraph_regular

-- Lemma 4.2 and Theorem 4.3 (full interlacing)
#print axioms Matrix.IsHermitian.eigenvectorSpan
#print axioms Matrix.IsHermitian.finrank_eigenvectorSpan
#print axioms Matrix.IsHermitian.rayleigh_head_tail
#print axioms Matrix.IsHermitian.exists_rayleigh_le_of_finrank
#print axioms Matrix.IsHermitian.exists_le_rayleigh_of_finrank
#print axioms Matrix.exists_principal_submatrix_extension
#print axioms Matrix.IsHermitian.eigenvalues_principal_submatrix_le
#print axioms Matrix.IsHermitian.le_eigenvalues_principal_submatrix
#print axioms Matrix.IsHermitian.largestEigenvalue_principal_submatrix_le
#print axioms Matrix.IsHermitian.leastEigenvalue_le_principal_submatrix

-- Theorem 4.5 (symmetric Perron–Frobenius), edge constancy, and Theorem 4.8
#print axioms Matrix.positiveSupportGraph
#print axioms Matrix.abs_dotProduct_mulVec_le
#print axioms Matrix.IsHermitian.exists_nonneg_eigenvector_largest
#print axioms Matrix.IsHermitian.largestEigenvalue_nonneg
#print axioms Matrix.IsHermitian.abs_eigenvalue_le_largest
#print axioms Matrix.IsHermitian.eq_zero_of_nonneg_eigenvector_of_eq_zero
#print axioms Matrix.IsHermitian.pos_of_nonneg_eigenvector
#print axioms Matrix.IsHermitian.exists_pos_eigenvector_largest
#print axioms Matrix.IsHermitian.eq_smul_of_pos_eigenvector
#print axioms Matrix.IsHermitian.multiplicity_largest_eq_one
#print axioms Matrix.IsHermitian.eigenvector_ratio_eq_of_pos_entry
#print axioms Matrix.IsHermitian.largestEigenvalue_le_of_le_submatrix
#print axioms Matrix.IsHermitian.largestEigenvalue_lt_of_lt_submatrix
#print axioms SimpleGraph.positiveSupportGraph_adjMatrix
#print axioms SimpleGraph.largestEigenvalue_lt_of_proper_subgraph

-- Theorem 3.1 (polynomial calculus and spectral projectors)
#print axioms Matrix.IsHermitian.aeval_eq_conj_diagonal
#print axioms Matrix.IsHermitian.isHermitian_aeval
#print axioms Matrix.IsHermitian.mulVec_aeval_eigenvectorBasis
#print axioms Matrix.IsHermitian.spectrumMultiset_aeval
#print axioms Matrix.IsHermitian.aeval_eq_zero_iff
#print axioms Matrix.IsHermitian.spectralIdempotent
#print axioms Matrix.IsHermitian.isHermitian_spectralIdempotent
#print axioms Matrix.IsHermitian.spectralIdempotent_mulVec_eigenvectorBasis
#print axioms Matrix.IsHermitian.spectralIdempotent_mulVec_of_eigenvector
#print axioms Matrix.IsHermitian.spectralIdempotent_mul
#print axioms Matrix.IsHermitian.aeval_eq_sum_spectralIdempotent
#print axioms Matrix.IsHermitian.sum_spectralIdempotent
#print axioms Matrix.IsHermitian.eq_sum_eigenvalue_smul_spectralIdempotent
#print axioms Matrix.IsHermitian.trace_spectralIdempotent
#print axioms Matrix.IsHermitian.rank_spectralIdempotent
#print axioms Matrix.IsHermitian.eigenvalueMultiplicity_aeval
#print axioms Matrix.IsHermitian.spectralIdempotent_eq_aeval
#print axioms Matrix.IsHermitian.eq_spectralIdempotent_of_mulVec_eigenvectorBasis

-- Graph forms of the C13/C15 certificate lemmas
#print axioms SimpleGraph.spectrumMultiset_eq_of_annihilatingPolynomial_trace
#print axioms SimpleGraph.cospectral_of_annihilatingPolynomial_trace
#print axioms SimpleGraph.cospectral_of_intertwiner
#print axioms SimpleGraph.cospectral_of_scaled_inverse_intertwiner
#print axioms SimpleGraph.cospectral_of_involution_conj

-- Theorem 3.2 (remaining trace and rank statements)
#print axioms Matrix.IsHermitian.rank_eq_card_sub_eigenvalueMultiplicity_zero
#print axioms Matrix.IsHermitian.rank_add_eigenvalueMultiplicity_zero
#print axioms Matrix.IsHermitian.trace_aeval_eq_sum
#print axioms Matrix.IsHermitian.rank_aeval_eq_sum_multiplicity
#print axioms Matrix.trace_eq_rank_of_idempotent

-- Theorem 6.1 (rectangular products)
#print axioms Matrix.PosSemidef.spectrumMultiset_eq_filter_pos_add_replicate_zero
#print axioms Matrix.spectrumMultiset_mul_comm_add_zeros
#print axioms Matrix.eigenvalueMultiplicity_mul_comm_of_ne_zero
#print axioms Matrix.card_add_eigenvalueMultiplicity_zero_mul_comm
#print axioms Matrix.eigenspaceMulEquivOfNeZero
#print axioms Matrix.spectrumMultiset_gram_products

-- Theorem 6.2 (incidence identities)
#print axioms SimpleGraph.edgeIncMatrix
#print axioms SimpleGraph.edgeIncMatrix_apply
#print axioms SimpleGraph.edgeIncMatrix_mul_transpose
#print axioms SimpleGraph.transpose_edgeIncMatrix_mul
#print axioms SimpleGraph.rank_edgeIncMatrix
#print axioms SimpleGraph.multiplicity_neg_two_lineGraph
#print axioms SimpleGraph.neg_two_le_leastEigenvalue_lineGraph

-- Lemma 3.6 and Theorem 10.1 (trace bounds and scaled idempotents)
#print axioms Matrix.IsHermitian.trace_sq_le_rank_mul_trace_sq
#print axioms Matrix.IsHermitian.trace_sq_eq_rank_mul_trace_sq_iff
#print axioms Matrix.IsHermitian.trace_sq_le_rank_mul_sum_sq
#print axioms Matrix.IsHermitian.eq_zero_or_eq_of_mem_spectrumMultiset_of_sq_eq_smul
#print axioms Matrix.IsHermitian.posSemidef_of_sq_eq_pos_smul
#print axioms Matrix.IsHermitian.rank_eq_trace_div_of_sq_eq_smul
#print axioms Matrix.rank_le_card_sub_rank_of_mul_eq_zero
#print axioms Matrix.det_principal_submatrix_eq_zero_of_rank_lt

-- Theorem 6.5 and Lemma 5.5 of [CGSS]
#print axioms SimpleGraph.IsRegularOfDegree.lineGraph_isRegularOfDegree
#print axioms SimpleGraph.IsRegularOfDegree.spectrumMultiset_signlessLapMatrix
#print axioms SimpleGraph.IsRegularOfDegree.degree_eq_of_lineGraph_cospectral
#print axioms SimpleGraph.IsRegularOfDegree.card_eq_of_lineGraph_cospectral
#print axioms SimpleGraph.IsRegularOfDegree.lineGraph_parameters
#print axioms SimpleGraph.spectrumMultiset_of_regular_lineGraph
#print axioms SimpleGraph.IsRegularOfDegree.charpoly_lineGraph
#print axioms SimpleGraph.cospectral_of_lineGraph_cospectral

-- Theorem 3.5 (matrix Gram representations and rank control)
#print axioms Matrix.rank_gram_eq_finrank_span
#print axioms Matrix.IsHermitian.exists_gram_rank
#print axioms Matrix.PosSemidef.exists_gram_euclideanSpace

-- Theorem 3.5 (graph representations and both extremal multiplicity bounds)
#print axioms SimpleGraph.IsRepresentation
#print axioms SimpleGraph.IsRepresentation.posSemidef
#print axioms SimpleGraph.exists_representation_iff_posSemidef
#print axioms SimpleGraph.IsRepresentation.rank_two_add_adjMatrix
#print axioms SimpleGraph.rank_two_add_adjMatrix_add_multiplicity_neg_two
#print axioms SimpleGraph.IsRepresentation.multiplicity_neg_two_ge
#print axioms SimpleGraph.IsRepresentation.leastEigenvalue_eq_neg_two_of_finrank_lt
#print axioms SimpleGraph.rank_two_sub_adjMatrix_add_multiplicity_two
#print axioms SimpleGraph.multiplicity_two_ge_of_gram_representation
#print axioms SimpleGraph.eigenvalue_le_two_of_gram_representation
#print axioms SimpleGraph.largestEigenvalue_eq_two_of_gram_representation

-- Theorem 5.7 and Corollaries 5.8–5.9 (the all-ones direction)
#print axioms Matrix.IsHermitian.spectrumMultiset_smul_add_smul_one_add_smul_allOnes
#print axioms Matrix.PosSemidef.rank_sub_allOnes
#print axioms Matrix.spectrumMultiset_smul_one_add_smul_allOnes
#print axioms Matrix.charpoly_smul_one_add_smul_allOnes
#print axioms Matrix.det_smul_one_add_smul_allOnes
#print axioms SimpleGraph.IsRegularOfDegree.spectrumMultiset_compl
#print axioms SimpleGraph.IsRegularOfDegree.spectrumMultiset_seidelMatrix

-- Theorem 3.7 (tight frames and the relative bound)
#print axioms Matrix.gram_sq_of_tightFrame
#print axioms Matrix.spectrumMultiset_gram_of_tightFrame
#print axioms Matrix.shifted_gram_polynomial_of_tightFrame
#print axioms Matrix.card_le_relative_bound_of_abs_inner_eq

-- EQ2 (the cone and pair-counting steps for Theorem 4.4 of [CGSS])
#print axioms InnerProductSpace.equiangularCone
#print axioms InnerProductSpace.inner_equiangularCone_none
#print axioms InnerProductSpace.inner_equiangularCone_some_none
#print axioms InnerProductSpace.inner_equiangularCone_some_some
#print axioms InnerProductSpace.inner_equiangularCone_self
#print axioms InnerProductSpace.span_range_equiangularCone
#print axioms InnerProductSpace.finrank_span_equiangularCone
#print axioms SimpleGraph.equiangularConeGraph
#print axioms SimpleGraph.equiangularConeGraph_isUniversal_none
#print axioms SimpleGraph.equiangularConeGraph_connected
#print axioms SimpleGraph.equiangularConeGraph_degree_none
#print axioms SimpleGraph.isRepresentation_equiangularCone
#print axioms LineSystem.IsStarClosed.two_mul_card_le_ncard_N
#print axioms LineSystem.RootType.card_le_fourteen_of_rank_eq_nine
#print axioms SimpleGraph.IsRepresentedIn.card_le_fourteen_of_equiangularCone

-- Theorem 9.6 (rational eigenvalues of integer matrices)
#print axioms Matrix.eigenvalue_isInteger_of_rat

-- Theorem 5.1 (walk counts and the first two moments)
#print axioms SimpleGraph.trace_pow_adjMatrix_eq_closedWalks
#print axioms SimpleGraph.dotProduct_pow_adjMatrix_eq_walks
#print axioms SimpleGraph.card_spectrumMultiset
#print axioms SimpleGraph.sum_spectrumMultiset_eq_zero

-- Theorem 7.10 (the polynomial on the constant direction)
#print axioms SimpleGraph.IsRegularOfDegree.aeval_eq_smul_allOnes_iff_of_connected
#print axioms SimpleGraph.IsRegularOfDegree.aeval_eq_smul_allOnes_of_connected

#print axioms SimpleGraph.spectrumMultiset_lineGraph_of_card_le
