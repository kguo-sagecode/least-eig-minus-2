/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Nonbipartite

/-!
# Axiom audit for Section 5

Every theorem introduced in `LineGraphSpectra`, together with the existing
declarations implementing Lemmas 5.1–5.5 of [CGSS] in the blueprint's forms.
-/

#print axioms SimpleGraph.IsRegularOfDegree.largestEigenvalue_eq
#print axioms SimpleGraph.IsRegularOfDegree.multiplicity_eq_card_components
#print axioms SimpleGraph.isRegular_iff_sum_sq_eigenvalues
#print axioms SimpleGraph.IsRegularOfDegree.isBipartite_iff_neg_eigenvalue
#print axioms SimpleGraph.IsRegularOfDegree.multiplicity_neg_eq_one
#print axioms SimpleGraph.regular_or_isBiregularWith_of_lineGraph_regular
#print axioms SimpleGraph.cospectral_of_lineGraph_cospectral

#print axioms SimpleGraph.biadjMatrix
#print axioms SimpleGraph.Connected.degree_pos_of_edgeSet_nonempty
#print axioms SimpleGraph.Connected.card_bipartite_components
#print axioms SimpleGraph.Connected.multiplicity_zero_signlessLapMatrix
#print axioms SimpleGraph.IsBiregularWith.symm
#print axioms SimpleGraph.IsBiregularWith.isBipartite
#print axioms SimpleGraph.IsBiregularWith.degrees_pos
#print axioms SimpleGraph.IsBiregularWith.card_mul_degree_left
#print axioms SimpleGraph.IsBiregularWith.card_mul_degree_right
#print axioms SimpleGraph.IsBiregularWith.sumEquiv
#print axioms SimpleGraph.IsBiregularWith.card_add_card
#print axioms SimpleGraph.IsBiregularWith.degree_right_le_left
#print axioms SimpleGraph.IsBiregularWith.lineGraph_isRegularOfDegree
#print axioms SimpleGraph.IsBiregularWith.multiplicity_zero_signlessLapMatrix
#print axioms SimpleGraph.IsBiregularWith.card_eq_rank_add_one
#print axioms SimpleGraph.IsBiregularWith.signlessLapMatrix_eq_fromBlocks
#print axioms SimpleGraph.exists_isBiregularWith_of_lineGraph_regular

#print axioms Matrix.spectrumMultiset_submatrix_equiv
#print axioms Matrix.spectrumMultiset_fromBlocks_zero
#print axioms Matrix.fromBlocks_scalar_quadratic
#print axioms Matrix.spectrumMultiset_map_quadratic_fromBlocks

#print axioms SimpleGraph.Cospectral.eigenvalueMultiplicity_signlessLapMatrix_of_ne_zero
#print axioms SimpleGraph.Cospectral.spectrumMultiset_signlessLapMatrix_of_connected_bipartite
#print axioms SimpleGraph.Cospectral.card_add_bipartite_eq_of_connected
#print axioms
  SimpleGraph.IsBiregularWith.spectrumMultiset_map_quadratic_signlessLapMatrix_eq_gram_add_gram
#print axioms SimpleGraph.IsBiregularWith.spectrumMultiset_map_quadratic_signlessLapMatrix
#print axioms SimpleGraph.IsBiregularWith.parameters_eq_of_lineGraph_cospectral
#print axioms SimpleGraph.IsBiregularWith.eq_of_lineGraph_cospectral
#print axioms SimpleGraph.lineGraph_cospectral_bipartite_forall_isBiregularWith

#print axioms Matrix.isHermitian_fromBlocks_scalar
#print axioms Matrix.fromBlocks_scalar_mulVec_eq_iff
#print axioms Matrix.eigenvalueMultiplicity_fromBlocks_scalar_of_ne
#print axioms Matrix.eigenvalueMultiplicity_fromBlocks_scalar_right
#print axioms Matrix.count_map_quadratic_roots
#print axioms Matrix.spectrumMultiset_fromBlocks_scalar_of_ne
#print axioms Matrix.spectrumMultiset_sub_center_fromBlocks_scalar
#print axioms SimpleGraph.Cospectral.spectrumMultiset_signlessLapMatrix_add_singleton_zero
#print axioms SimpleGraph.lineGraph_cospectral_bipartite_spectrum_of_not_isBipartite
