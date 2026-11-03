/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Basic
import LineGraphs.RootSetClassification.Coordinates
import LineGraphs.RootSetClassification.Classical
import LineGraphs.RootSetClassification.ClassicalBases
import LineGraphs.RootSetClassification.ClassicalCartan
import LineGraphs.RootSetClassification.ExceptionalCoordinates
import LineGraphs.RootSetClassification.EvenLattice
import LineGraphs.RootSetClassification.MinimalBase
import LineGraphs.RootSetClassification.LatticeRootSet
import LineGraphs.RootSetClassification.ERealization
import LineGraphs.RootSetClassification.ESubspaces
import LineGraphs.RootSetClassification.ESystems
import LineGraphs.RootSetClassification.FCoordinates
import LineGraphs.RootSetClassification.FSystem
import LineGraphs.RootSetClassification.GCoordinates
import LineGraphs.RootSetClassification.GSystem
import LineGraphs.RootSetClassification.ConnectedBase
import LineGraphs.RootSetClassification.Models
import LineGraphs.RootSetClassification.RootCounts
import LineGraphs.RootSetClassification.LengthCounts
import LineGraphs.RootSetClassification.LineCounts
import LineGraphs.RootSetClassification.BaseBridge
import LineGraphs.RootSetClassification.Similarity
import LineGraphs.RootSetClassification.Components
import LineGraphs.RootSetClassification.ClassificationExists
import LineGraphs.RootSetClassification.ModelUniqueness
import LineGraphs.RootSetClassification.LengthSpectrum
import LineGraphs.RootSetClassification.SmallRankSimilarity
import LineGraphs.RootSetClassification.Classification
import LineGraphs.RootSetClassification.Reflections
import LineGraphs.RootSetClassification.AnglePairings
import LineGraphs.RootSetClassification.Angles
import LineGraphs.RootSetClassification.FixedLengths
import LineGraphs.RootSetClassification.Projectors
import LineGraphs.RootSetClassification.RootFrame
import LineGraphs.RootSetClassification.LineRepresentatives
import LineGraphs.RootSetClassification.LineFrame
import LineGraphs.RootSetClassification.MatrixConvention
import LineGraphs.RootSetClassification.ThreeLines
import LineGraphs.RootSetClassification.ClassicalLines
import LineGraphs.RootSetClassification.LineAngles
import LineGraphs.RootSetClassification.LineOccurrence
import LineGraphs.RootSetClassification.ModelMatrices
import LineGraphs.RootSetClassification.RemarkLines
import LineGraphs.RootSetClassification.LeafDeterminant
import LineGraphs.RootSetClassification.LeadingDeterminants
import LineGraphs.RootSetClassification.ExceptionalLDL
import LineGraphs.RootSetClassification.RationalFrame
import LineGraphs.Cartan.SmallRanks
import LineGraphs.Cartan.GramRealization

/-!
# Audit of Theorems B and C of Remark 3.11 of [CGSS]

The axioms of every public declaration in `LineGraphs/RootSetClassification/`, the Lean form
of Theorem B (`thm:B`, `IsRootSet.classification`) and Theorem C (`thm:C`,
`IsRootSet.remark_lines`, the line statement of Remark 3.11) of
`blueprint/sec3-remark311.tex`, with their lemmas and the finite certificates of that
blueprint (`lem:rem-leaf-det`, `comp:rem-minors`, `comp:rem-ldl`, `comp:rem-rational-frame`).
It also covers the two results of the part on Theorem A and Corollary D whose modules
`LineGraphs/Cartan/Audit.lean` does not import: `rem:small`
(`CartanMatrix.small_rank_identifications`, in `LineGraphs/Cartan/SmallRanks.lean`) and
`lem:rem-gram` (`Matrix.exists_gram_realization`, in `LineGraphs/Cartan/GramRealization.lean`).
Only the standard Lean axioms `propext`, `Classical.choice` and `Quot.sound` are permitted.
The sections follow the blueprint's order; each names the file and the blueprint results.
-/

-- Basic.lean: def:rem-bases, the similarity laws (`IsRootSet.similarity_comp`, `similarity_symm`)
#print axioms IsRootSet.IsSimilarity
#print axioms IsRootSet.similarity_comp
#print axioms IsRootSet.similarity_symm
#print axioms IsRootSet.cartanPairing
#print axioms IsRootSet.IsBase
#print axioms IsRootSet.IsBase.span_eq_top
#print axioms IsRootSet.IsBase.toBasis
#print axioms IsRootSet.IsBase.toBasis_apply
#print axioms IsRootSet.coefficients_of_mem_nat_span_or_neg_mem
#print axioms IsRootSet.isBase_of_mem_nat_span_or_neg_mem

-- Cartan/SmallRanks.lean: rem:small, with steps rsmallElarge and rsmallnotfinite
#print axioms CartanMatrix.exists_weightedGraph_E_contains_smithE₈
#print axioms CartanMatrix.not_isFiniteCartan_E
#print axioms CartanMatrix.small_rank_identifications

-- Cartan/GramRealization.lean: lem:rem-gram, with steps rgrelations and rgdimension
#print axioms Matrix.sum_smul_eq_zero_iff_gram_mulVec_eq_zero
#print axioms Matrix.finrank_span_eq_card_sub_finrank_ker_gram
#print axioms Matrix.exists_gram_realization

-- Coordinates.lean: def:rem-classical and lem:rem-coordinate-reflections
#print axioms RootSetModel.unit
#print axioms RootSetModel.axisRoots
#print axioms RootSetModel.An
#print axioms RootSetModel.Bn
#print axioms RootSetModel.Cn
#print axioms RootSetModel.Dn
#print axioms RootSetModel.span_An_eq_ker_coordinateSum
#print axioms RootSetModel.reflect
#print axioms RootSetModel.reflect_sub_unit
#print axioms RootSetModel.reflect_add_unit
#print axioms RootSetModel.reflect_smul_unit
#print axioms RootSetModel.coordinate_reflection
#print axioms RootSetModel.signedPermutation
#print axioms RootSetModel.signedPermutation_unit
#print axioms RootSetModel.signedPermutation_mem_axisRoots
#print axioms RootSetModel.signedPermutation_mem_Dn
#print axioms RootSetModel.halfRoots
#print axioms RootSetModel.signedPermutation_mem_halfRoots
#print axioms RootSetModel.coordinateSum_signedPermutation
#print axioms RootSetModel.signedPermutation_mem_An
#print axioms RootSetModel.reflect_neg
#print axioms RootSetModel.reflect_sub_unit_eq_signedPermutation
#print axioms RootSetModel.reflect_add_unit_eq_signedPermutation
#print axioms RootSetModel.reflect_smul_unit_eq_signedPermutation
#print axioms RootSetModel.dnRoot_eq_signed_units
#print axioms RootSetModel.exists_signedPermutation_reflect_of_mem_Dn

-- Classical.lean: lem:classical, the classical root sets
#print axioms RootSetModel.finite_axisRoots
#print axioms RootSetModel.zero_notMem_axisRoots
#print axioms RootSetModel.inner_self_of_mem_axisRoots
#print axioms RootSetModel.smul_unit_notMem_Dn
#print axioms RootSetModel.reduced_axisRoots_union_Dn
#print axioms RootSetModel.reflection_mem_axisRoots_union_Dn
#print axioms RootSetModel.span_axisRoots_union_Dn
#print axioms RootSetModel.exists_integerVector_of_mem_axisRoots_union_Dn
#print axioms RootSetModel.crystallographic_axisRoots_union_Dn
#print axioms RootSetModel.isRootSet_axisRoots_union_Dn
#print axioms RootSetModel.An_isRootSet
#print axioms RootSetModel.Bn_isRootSet
#print axioms RootSetModel.Cn_isRootSet
#print axioms RootSetModel.Dn_isRootSet
#print axioms RootSetModel.classical_isRootSet

-- ClassicalBases.lean: lem:classical, the classical bases
#print axioms RootSetModel.sub_mem_natSpan_of_le
#print axioms RootSetModel.An.simpleRoot
#print axioms RootSetModel.axisSimpleRoots
#print axioms RootSetModel.Bn.simpleRoot
#print axioms RootSetModel.Cn.simpleRoot
#print axioms RootSetModel.Dn.simpleRoot
#print axioms RootSetModel.mem_or_neg_mem_of_mem_Dn
#print axioms RootSetModel.sub_mem_natSpan_axisSimpleRoots
#print axioms RootSetModel.unit_mem_natSpan_Bn
#print axioms RootSetModel.two_smul_unit_mem_natSpan_Cn
#print axioms RootSetModel.sub_mem_natSpan_Dn
#print axioms RootSetModel.add_last_mem_natSpan_Dn
#print axioms RootSetModel.add_mem_natSpan_Dn
#print axioms RootSetModel.An.base
#print axioms RootSetModel.Bn.base
#print axioms RootSetModel.Cn.base
#print axioms RootSetModel.Dn.base
#print axioms RootSetModel.classical_base

-- ClassicalCartan.lean: lem:classical, the classical Cartan matrices
#print axioms RootSetModel.inner_unit
#print axioms RootSetModel.inner_consecutive_differences
#print axioms RootSetModel.inner_consecutive_difference_self
#print axioms RootSetModel.An.cartanMatrix
#print axioms RootSetModel.inner_difference_last
#print axioms RootSetModel.inner_smul_unit_self
#print axioms RootSetModel.Bn.cartanMatrix
#print axioms RootSetModel.Cn.cartanMatrix
#print axioms RootSetModel.inner_difference_fork
#print axioms RootSetModel.inner_fork_self
#print axioms RootSetModel.Dn.cartanMatrix
#print axioms RootSetModel.classical_cartanMatrix

-- ExceptionalCoordinates.lean: def:rem-exceptional
#print axioms RootSetModel.E₈
#print axioms RootSetModel.e₇Space
#print axioms RootSetModel.e₆Space
#print axioms RootSetModel.E₇
#print axioms RootSetModel.E₆
#print axioms RootSetModel.F₄
#print axioms RootSetModel.g₂Space
#print axioms RootSetModel.g₂LongRoot
#print axioms RootSetModel.G₂
#print axioms RootSetModel.mem_e₇Space
#print axioms RootSetModel.mem_e₆Space

-- EvenLattice.lean: lem:even-lattice
#print axioms RootSetModel.evenCoordinateLattice
#print axioms RootSetModel.halfShift
#print axioms RootSetModel.add_halfShift_mem_evenCoordinateLattice
#print axioms RootSetModel.e₈Lattice
#print axioms RootSetModel.inner_integerVector_halfShift
#print axioms RootSetModel.inner_halfShift_self
#print axioms RootSetModel.even_integerInner_of_even_sum
#print axioms RootSetModel.inner_mem_int_evenCoordinateLattice
#print axioms RootSetModel.inner_halfShift_mem_int
#print axioms RootSetModel.inner_mem_int_e₈Lattice
#print axioms RootSetModel.inner_self_even_e₈Lattice
#print axioms RootSetModel.two_le_inner_self_of_mem_e₈Lattice
#print axioms RootSetModel.E₈_lattice_even
#print axioms RootSetModel.inner_integerVector_add_halfShift_self
#print axioms RootSetModel.coordinate_eq_zero_or_neg_one_of_shift_norm_two
#print axioms RootSetModel.even_sum_halfRoot_shift
#print axioms RootSetModel.halfRoot_restrict_of_even_signs
#print axioms RootSetModel.E₈_subset_e₈Lattice
#print axioms RootSetModel.mem_E₈_of_mem_evenCoordinateLattice_of_norm_two
#print axioms RootSetModel.mem_E₈_of_shift_mem_evenCoordinateLattice_of_norm_two
#print axioms RootSetModel.E₈_eq_norm_two

-- MinimalBase.lean: lem:minimal-base
#print axioms RootSetModel.coefficients_one_sign_of_minimal_sum
#print axioms RootSetModel.coefficients_one_sign_of_minimal

-- LatticeRootSet.lean: lem:E, the norm-two vectors of an even lattice
#print axioms IsRootSet.of_norm_two_lattice

-- ERealization.lean: lem:E, the E₈ simple roots and coefficients
#print axioms RootSetModel.eSimpleEntries
#print axioms RootSetModel.E₈.simpleRoot
#print axioms RootSetModel.eCoefficients
#print axioms RootSetModel.sum_eCoefficients_simpleRoot
#print axioms RootSetModel.eCoefficients_sum_simpleRoot
#print axioms RootSetModel.E₈.simpleRoot_linearIndependent
#print axioms RootSetModel.span_E₈_simpleRoot
#print axioms RootSetModel.E₈.simpleBasis
#print axioms RootSetModel.E₈.simpleBasis_apply
#print axioms RootSetModel.E₈.simpleRoot_mem
#print axioms RootSetModel.E₈.gram_simpleRoot
#print axioms RootSetModel.eIntegerCoefficients
#print axioms RootSetModel.eCoefficients_integerVector
#print axioms RootSetModel.eCoefficients_add
#print axioms RootSetModel.eCoefficients_halfShift
#print axioms RootSetModel.exists_integer_eCoefficients
#print axioms RootSetModel.mem_e₈Lattice_iff_exists_coefficients

-- ESubspaces.lean: lem:E, the E₇ and E₆ subspaces
#print axioms RootSetModel.mem_e₇Space_iff_coefficient
#print axioms RootSetModel.mem_e₆Space_iff_coefficients
#print axioms RootSetModel.E₈.simpleRoot_mem_e₇Space
#print axioms RootSetModel.E₈.simpleRoot_mem_e₆Space
#print axioms RootSetModel.E₇.simpleRoot
#print axioms RootSetModel.E₆.simpleRoot
#print axioms RootSetModel.E₇.sum_eCoefficients
#print axioms RootSetModel.E₆.sum_eCoefficients
#print axioms RootSetModel.E₇.simpleRoot_linearIndependent
#print axioms RootSetModel.E₆.simpleRoot_linearIndependent
#print axioms RootSetModel.span_E₇_simpleRoot
#print axioms RootSetModel.span_E₆_simpleRoot
#print axioms RootSetModel.E₇.simpleBasis
#print axioms RootSetModel.E₆.simpleBasis
#print axioms RootSetModel.E₇.simpleBasis_apply
#print axioms RootSetModel.E₆.simpleBasis_apply
#print axioms RootSetModel.finrank_e₇Space
#print axioms RootSetModel.finrank_e₆Space
#print axioms RootSetModel.e₇Lattice
#print axioms RootSetModel.e₆Lattice
#print axioms RootSetModel.mem_e₇Lattice_iff_exists_coefficients
#print axioms RootSetModel.mem_e₆Lattice_iff_exists_coefficients

-- ESystems.lean: lem:E
#print axioms RootSetModel.E₇.gram_simpleRoot
#print axioms RootSetModel.E₆.gram_simpleRoot
#print axioms RootSetModel.E₈_isRootSet
#print axioms RootSetModel.E₇_isRootSet
#print axioms RootSetModel.E₆_isRootSet
#print axioms RootSetModel.E_isRootSet
#print axioms RootSetModel.E₈.base
#print axioms RootSetModel.E₇.base
#print axioms RootSetModel.E₆.base
#print axioms RootSetModel.E_base
#print axioms RootSetModel.E₈.cartanMatrix
#print axioms RootSetModel.E₇.cartanMatrix
#print axioms RootSetModel.E₆.cartanMatrix
#print axioms RootSetModel.E_cartanMatrix

-- FCoordinates.lean: lem:F, coordinates
#print axioms RootSetModel.F₄Index
#print axioms RootSetModel.fRootEntries
#print axioms RootSetModel.F₄_eq_range
#print axioms RootSetModel.F₄_finite
#print axioms RootSetModel.inner_self_of_mem_halfRoots_four
#print axioms RootSetModel.F₄_inner_self
#print axioms RootSetModel.F₄_zero_notMem
#print axioms RootSetModel.exists_zero_coordinate_of_mem_F₄_integer
#print axioms RootSetModel.F₄_reduced
#print axioms RootSetModel.span_F₄_eq_top
#print axioms RootSetModel.signedPermutation_mem_F₄
#print axioms RootSetModel.signedPermutation_inner
#print axioms RootSetModel.reflect_signedPermutation
#print axioms RootSetModel.signedPermutation_sign_involutive
#print axioms RootSetModel.fHalf
#print axioms RootSetModel.reflect_fHalf
#print axioms RootSetModel.fHalf_reflection_entries
#print axioms RootSetModel.reflect_fHalf_mem_F₄
#print axioms RootSetModel.reflect_half_mem_F₄
#print axioms RootSetModel.F₄_reflection_mem

-- FSystem.lean: lem:F
#print axioms RootSetModel.fPairing
#print axioms RootSetModel.fPairing_mul
#print axioms RootSetModel.F₄_crystallographic
#print axioms RootSetModel.F₄_isRootSet
#print axioms RootSetModel.fSimpleEntries
#print axioms RootSetModel.F₄.simpleRoot
#print axioms RootSetModel.fCoefficients
#print axioms RootSetModel.sum_fCoefficients_simpleRoot
#print axioms RootSetModel.fCoefficients_sum_simpleRoot
#print axioms RootSetModel.F₄.simpleRoot_linearIndependent
#print axioms RootSetModel.F₄.simpleRoot_mem
#print axioms RootSetModel.fCoefficientNumerators
#print axioms RootSetModel.fIntegerCoefficients
#print axioms RootSetModel.fIntegerCoefficients_spec
#print axioms RootSetModel.fCoefficients_root
#print axioms RootSetModel.F₄_base
#print axioms RootSetModel.F₄.simpleRoot_inner_self
#print axioms RootSetModel.F₄_cartanMatrix

-- GCoordinates.lean: lem:G, coordinates
#print axioms RootSetModel.gRoots
#print axioms RootSetModel.mem_g₂Space
#print axioms RootSetModel.g₂LongRoot_apply
#print axioms RootSetModel.g₂LongRoot_eq_integerVector
#print axioms RootSetModel.g₂LongRoot_inner_self
#print axioms RootSetModel.G₂Index
#print axioms RootSetModel.gRootEntries
#print axioms RootSetModel.gRoots_eq_range
#print axioms RootSetModel.gRootEntries_sum
#print axioms RootSetModel.gRoot
#print axioms RootSetModel.G₂_eq_range
#print axioms RootSetModel.gRoots_inner_self
#print axioms RootSetModel.exists_zero_coordinate_of_mem_G₂_short
#print axioms RootSetModel.gRoots_reduced
#print axioms RootSetModel.signedPermutation_g₂LongRoot
#print axioms RootSetModel.signedPermutation_mem_gRoots
#print axioms RootSetModel.neg_mem_gRoots
#print axioms RootSetModel.inner_g₂LongRoot
#print axioms RootSetModel.reflect_g₂LongRoot_zero
#print axioms RootSetModel.signedPermutation_swap_involutive
#print axioms RootSetModel.reflect_g₂LongRoot_mem
#print axioms RootSetModel.gRoots_reflection_mem
#print axioms RootSetModel.gRoots_crystallographic

-- GSystem.lean: lem:G
#print axioms RootSetModel.gSimpleEntries
#print axioms RootSetModel.G₂.simpleRoot
#print axioms RootSetModel.gCoefficients
#print axioms RootSetModel.sum_gCoefficients_simpleRoot
#print axioms RootSetModel.gCoefficients_sum_simpleRoot
#print axioms RootSetModel.G₂.simpleRoot_linearIndependent
#print axioms RootSetModel.G₂.simpleRoot_mem
#print axioms RootSetModel.span_G₂_simpleRoot
#print axioms RootSetModel.G₂_isRootSet
#print axioms RootSetModel.gIntegerCoefficients
#print axioms RootSetModel.gPositiveCoefficients
#print axioms RootSetModel.gIntegerCoefficients_eq_signed_positive
#print axioms RootSetModel.gIntegerCoefficients_one_sign
#print axioms RootSetModel.gCoefficients_root
#print axioms RootSetModel.G₂_base
#print axioms RootSetModel.G₂.gram_simpleRoot
#print axioms RootSetModel.G₂_cartanMatrix

-- ConnectedBase.lean: lem:rem-base-connected
#print axioms IsRootSet.nonorthogonalityGraph
#print axioms IsRootSet.isIndecomposable_of_connected_base

-- Models.lean: lem:models-irreducible and the canonical model family
#print axioms RootSetModel.Space
#print axioms RootSetModel.spaceNormedAddCommGroup
#print axioms RootSetModel.spaceInnerProductSpace
#print axioms RootSetModel.roots
#print axioms RootSetModel.isRootSet
#print axioms RootSetModel.simpleRoot
#print axioms RootSetModel.base
#print axioms RootSetModel.cartanMatrix
#print axioms RootSetModel.finrank_space
#print axioms RootSetModel.nonorthogonalityGraph_eq_support
#print axioms RootSetModel.isIndecomposable

-- RootCounts.lean: lem:counts, root counts
#print axioms RootSetModel.ncard_restrict_range
#print axioms RootSetModel.An_ncard
#print axioms RootSetModel.Dn_ncard
#print axioms RootSetModel.axisRoots_eq_range
#print axioms RootSetModel.axisRoot_injective
#print axioms RootSetModel.axisRoots_ncard
#print axioms RootSetModel.disjoint_axisRoots_Dn
#print axioms RootSetModel.Bn_ncard
#print axioms RootSetModel.Cn_ncard
#print axioms RootSetModel.E₈_ncard
#print axioms RootSetModel.E₇Index
#print axioms RootSetModel.E₆Index
#print axioms RootSetModel.integerVector_mem_e₇Space
#print axioms RootSetModel.integerVector_mem_e₆Space
#print axioms RootSetModel.E₇_ncard
#print axioms RootSetModel.E₆_ncard
#print axioms RootSetModel.fRootEntries_injective
#print axioms RootSetModel.F₄_ncard
#print axioms RootSetModel.gRootEntries_injective
#print axioms RootSetModel.G₂_ncard
#print axioms RootSetModel.rootCount
#print axioms RootSetModel.root_counts

-- LengthCounts.lean: lem:counts, length counts
#print axioms RootSetModel.ncard_length_of_constant
#print axioms RootSetModel.ncard_length_union
#print axioms RootSetModel.Bn_length_counts
#print axioms RootSetModel.Cn_length_counts
#print axioms RootSetModel.halfRoots_eq_range
#print axioms RootSetModel.halfRoots_ncard
#print axioms RootSetModel.disjoint_F₄_integer_half
#print axioms RootSetModel.F₄_length_counts
#print axioms RootSetModel.ncard_range_filter
#print axioms RootSetModel.G₂_length_counts_two_six
#print axioms RootSetModel.G₂_length_counts
#print axioms RootSetModel.lengthCount
#print axioms RootSetModel.length_counts

-- LineCounts.lean: lem:counts, line counts
#print axioms IsRootSet.roots_on_line
#print axioms IsRootSet.ncard_roots_on_line
#print axioms IsRootSet.numLines
#print axioms RootSetModel.lineCount
#print axioms RootSetModel.numLines

-- BaseBridge.lean: lem:pairing-construction, bases of Mathlib's root pairing
#print axioms IsRootSet.IsBase.mem_nat_span_or_neg_mem
#print axioms IsRootSet.IsBase.rootIndex
#print axioms IsRootSet.IsBase.rootIndex_injective
#print axioms IsRootSet.IsBase.toRootPairingBase
#print axioms IsRootSet.IsBase.mem_toRootPairingBase_support
#print axioms IsRootSet.IsBase.baseIndexEquiv
#print axioms IsRootSet.IsBase.root_baseIndexEquiv
#print axioms IsRootSet.IsBase.cartanMatrix_toRootPairingBase

-- Similarity.lean: lem:similarity
#print axioms IsRootSet.exists_pos_inner_map_of_cartanMatrix_eq
#print axioms IsRootSet.similarity_of_cartanMatrix_eq

-- Components.lean: lem:rem-components
#print axioms IsRootSet.rootGraph
#print axioms IsRootSet.componentRoots
#print axioms IsRootSet.componentSpan
#print axioms IsRootSet.inner_eq_zero_of_component_ne
#print axioms IsRootSet.componentRoots_orthogonal
#print axioms IsRootSet.restrictSpan_isRootSet
#print axioms IsRootSet.reflection_mem_componentRoots
#print axioms IsRootSet.component_isRootSet
#print axioms IsRootSet.isIndecomposable_of_connected
#print axioms IsRootSet.isIndecomposable_iff_connected
#print axioms IsRootSet.component_isIndecomposable
#print axioms IsRootSet.orthogonalFamily_componentSpan
#print axioms IsRootSet.iSup_componentSpan_eq_top
#print axioms IsRootSet.orthogonal_components
#print axioms IsRootSet.subsingleton_of_eq_empty
#print axioms IsRootSet.eq_empty_iff_subsingleton
#print axioms IsRootSet.isEmpty_connectedComponent_of_eq_empty

-- ClassificationExists.lean: lem:rem-indecomp-classification, existence
#print axioms IsRootSet.cartanPairing_toWeightBasis
#print axioms IsRootSet.connected_toWeightBasis
#print axioms IsRootSet.exists_similarity_model

-- ModelUniqueness.lean: lem:rem-indecomp-classification, uniqueness (rBunique)
#print axioms IsRootSet.IsSimilarity.ncard_eq
#print axioms IsRootSet.IsSimilarity.length_ncard_eq
#print axioms RootSetModel.minLengthSq
#print axioms RootSetModel.shortRootCount
#print axioms RootSetModel.lengthCount_minLengthSq
#print axioms RootSetModel.minLengthSq_pos
#print axioms RootSetModel.shortRootCount_pos
#print axioms RootSetModel.minLengthSq_le
#print axioms RootSetModel.exists_minLengthSq
#print axioms RootSetModel.minLengthSq_eq_mul_of_similarity
#print axioms RootSetModel.shortRootCount_eq_of_similarity
#print axioms RootSetModel.type_eq_of_counts
#print axioms RootSetModel.type_eq_of_similarity

-- LengthSpectrum.lean: thm:B, the two-length models (rBonevsTwo)
#print axioms IsRootSet.squaredLengths
#print axioms RootSetModel.IsSimplyLaced
#print axioms RootSetModel.maxLengthSq
#print axioms RootSetModel.lengthCount_pos_iff
#print axioms RootSetModel.squaredLengths_eq
#print axioms RootSetModel.maxLengthSq_eq_min_iff
#print axioms RootSetModel.two_lengths_iff
#print axioms RootSetModel.one_length_iff
#print axioms RootSetModel.lengthRatio
#print axioms RootSetModel.maxLengthSq_eq_lengthRatio_mul

-- SmallRankSimilarity.lean: lem:rem-indecomp-classification, B₂ and C₂ (rBCtwo)
#print axioms RootSetModel.b₂ToC₂
#print axioms RootSetModel.b₂ToC₂_unit
#print axioms RootSetModel.b₂ToC₂_inner
#print axioms RootSetModel.b₂ToC₂_mem
#print axioms RootSetModel.B₂_C₂_similarity

-- Classification.lean: lem:rem-indecomp-classification and thm:B
#print axioms IsRootSet.IsSimilarToModel
#print axioms IsRootSet.classification_of_isIndecomposable
#print axioms IsRootSet.classification

-- Reflections.lean: lem:rem-reflection
#print axioms IsRootSet.reflection_eq_neg_iff
#print axioms IsRootSet.reflection_neg
#print axioms IsRootSet.reflection_map
#print axioms IsRootSet.reflection_identities

-- AnglePairings.lean: lem:angles, pairings (rangpair)
#print axioms IsRootSet.inner_sq_lt_of_not_mem_line
#print axioms IsRootSet.exists_integer_pairings
#print axioms IsRootSet.pairing_product_mem
#print axioms IsRootSet.integer_pairing_bounds
#print axioms IsRootSet.squared_angle_length_cases

-- Angles.lean: lem:angles, lengths and angles (rangcases)
#print axioms IsRootSet.lineAngle
#print axioms IsRootSet.lineAngle_eq_of_inner_sq
#print axioms IsRootSet.lineAngle_eq_pi_div_three
#print axioms IsRootSet.lineAngle_eq_pi_div_four
#print axioms IsRootSet.lineAngle_eq_pi_div_six
#print axioms IsRootSet.lineAngle_eq_pi_div_two
#print axioms IsRootSet.norm_ratio_eq_sqrt
#print axioms IsRootSet.angle_length_cases

-- FixedLengths.lean: lem:angles, fixed-length subsystems (rangfixed, rangADE)
#print axioms IsRootSet.fixedLength
#print axioms IsRootSet.fixedLengthInSpan
#print axioms IsRootSet.fixedLength_isRootSet
#print axioms IsRootSet.IsSimilarToModel.isSimplyLaced_of_constant
#print axioms IsRootSet.fixedLength_components_simplyLaced

-- Projectors.lean: lem:rem-projectors
#print axioms IsRootSet.lineProjector
#print axioms IsRootSet.lineProjector_apply
#print axioms IsRootSet.lineProjector_neg
#print axioms IsRootSet.lineProjector_symmetric
#print axioms IsRootSet.trace_lineProjector
#print axioms IsRootSet.lineProjector_isometry
#print axioms IsRootSet.lineProjector_conjugate
#print axioms IsRootSet.lineProjector_identities
#print axioms IsRootSet.normalizedRoot
#print axioms IsRootSet.norm_normalizedRoot
#print axioms IsRootSet.normalizedRoot_neg
#print axioms IsRootSet.normalizedRoot_isometry
#print axioms IsRootSet.rootProjector
#print axioms IsRootSet.rootProjector_neg
#print axioms IsRootSet.rootProjector_isometry
#print axioms IsRootSet.trace_rootProjector

-- RootFrame.lean: lem:tight-frame, the root frame
#print axioms IsRootSet.finrank_pos_of_isIndecomposable
#print axioms IsRootSet.rootFrame
#print axioms IsRootSet.rootFrame_symmetric
#print axioms IsRootSet.rootFrame_reflection
#print axioms IsRootSet.rootFrame_root
#print axioms IsRootSet.rootFrame_eq_scalar
#print axioms IsRootSet.trace_rootFrame
#print axioms IsRootSet.rootFrame_eq_smul_id

-- LineRepresentatives.lean: thm:C, root lines and representatives
#print axioms IsRootSet.rootLines
#print axioms IsRootSet.RootRepresentatives
#print axioms IsRootSet.root_ne_neg
#print axioms IsRootSet.RootRepresentatives.signedRoot
#print axioms IsRootSet.RootRepresentatives.signedRoot_bijective
#print axioms IsRootSet.RootRepresentatives.signEquiv
#print axioms IsRootSet.RootRepresentatives.card
#print axioms IsRootSet.RootRepresentatives.lineEquiv
#print axioms IsRootSet.RootRepresentatives.numLines
#print axioms IsRootSet.RootRepresentatives.span_normalized
#print axioms IsRootSet.lineRoot
#print axioms IsRootSet.lineRoot_mem
#print axioms IsRootSet.span_lineRoot
#print axioms IsRootSet.lineRoot_representatives
#print axioms IsRootSet.finite_rootLines
#print axioms IsRootSet.ncard_rootLines

-- LineFrame.lean: lem:tight-frame
#print axioms IsRootSet.lineFrame
#print axioms IsRootSet.RootRepresentatives.span_unit
#print axioms IsRootSet.rootProjector_eq_of_unit_mem
#print axioms IsRootSet.RootRepresentatives.rootFrame_eq_twice
#print axioms IsRootSet.frame_identity_normalized
#print axioms IsRootSet.frame_identity

-- MatrixConvention.lean: lem:C-convention
#print axioms IsRootSet.lineGram
#print axioms IsRootSet.signedAdj
#print axioms IsRootSet.lineGram_sq_apply
#print axioms IsRootSet.lineGram_sq_eq_iff_frame
#print axioms IsRootSet.signedAdj_polynomial
#print axioms IsRootSet.signedAdj_quadratic_iff_gram
#print axioms IsRootSet.trace_lineFrame
#print axioms IsRootSet.signedAdj_quadratic_iff_frame
#print axioms IsRootSet.lineFrame_signs
#print axioms IsRootSet.lineGram_signs
#print axioms IsRootSet.signedAdj_signs

-- ThreeLines.lean: lem:rem-three-lines
#print axioms IsRootSet.not_mem_line_of_inner_sq_lt
#print axioms IsRootSet.squared_length_ratio_two
#print axioms IsRootSet.not_contains_three_equiangular_lines
#print axioms IsRootSet.fortyFiveCos
#print axioms IsRootSet.fortyFiveCos_properties
#print axioms IsRootSet.fortyFiveTriple
#print axioms IsRootSet.fortyFiveTriple_inner
#print axioms IsRootSet.fortyFiveTriple_properties

-- ClassicalLines.lean: thm:C, the Bₙ and Cₙ lines (rCclassicalsame, rCcounts)
#print axioms IsRootSet.IsSimilarity.isIndecomposable
#print axioms RootSetModel.rootLines_axisRoots
#print axioms RootSetModel.Bn_Cn_same_lines
#print axioms RootSetModel.Bn_Cn_line_counts
#print axioms RootSetModel.Cn_isIndecomposable

-- LineAngles.lean: thm:C, allowed angles (rCallowed)
#print axioms IsRootSet.lineAngles
#print axioms IsRootSet.lineAngle_smul
#print axioms IsRootSet.lineAngle_eq_of_same_lines
#print axioms IsRootSet.lineAngles_eq_of_rootLines_eq
#print axioms IsRootSet.lineAngles_subset_of_lengths_two
#print axioms IsRootSet.lineAngles_subset_of_lengths_three

-- LineOccurrence.lean: thm:C, allowed and occurring angles (rCallowed, rCoccurrence)
#print axioms IsRootSet.lineAngle_mem_lineAngles
#print axioms IsRootSet.inner_sq_of_lineAngle_eq_pi_div_three
#print axioms RootSetModel.inner_unit_of_ne
#print axioms RootSetModel.inner_unit_self
#print axioms RootSetModel.unit_mem_axisRoots_one
#print axioms RootSetModel.unit_add_unit_mem_Dn
#print axioms RootSetModel.lineAngle_unit_unit
#print axioms RootSetModel.lineAngle_unit_add_unit
#print axioms RootSetModel.lineAngle_add_add
#print axioms RootSetModel.Bn_lengths
#print axioms RootSetModel.Cn_lengths
#print axioms RootSetModel.G₂_lengths
#print axioms RootSetModel.lineAngles_Bn_subset
#print axioms RootSetModel.lineAngles_Bn_eq_Cn
#print axioms RootSetModel.lineAngles_F₄_subset
#print axioms RootSetModel.lineAngles_G₂_subset
#print axioms RootSetModel.pi_div_two_pi_div_four_mem_lineAngles_Bn
#print axioms RootSetModel.pi_div_three_mem_lineAngles_Bn
#print axioms RootSetModel.b₂Entries
#print axioms RootSetModel.exists_b₂Entries
#print axioms RootSetModel.b₂Entries_ne
#print axioms RootSetModel.pi_div_three_notMem_lineAngles_B₂
#print axioms RootSetModel.angles_mem_lineAngles_F₄
#print axioms RootSetModel.unit_sub_unit_mem_g₂Space
#print axioms RootSetModel.g₂LongRoot_mem_g₂Space
#print axioms RootSetModel.angles_mem_lineAngles_G₂
#print axioms RootSetModel.lineAngles_Bn
#print axioms RootSetModel.lineAngles_B₂
#print axioms RootSetModel.lineAngles_F₄
#print axioms RootSetModel.lineAngles_G₂

-- ModelMatrices.lean: thm:C, the matrix equations (rCequations), and cor:rem-constants
#print axioms IsRootSet.signedAdj_quadratic
#print axioms RootSetModel.matrixConstant
#print axioms RootSetModel.matrixConstant_eq
#print axioms RootSetModel.signedAdj_quadratic_model
#print axioms RootSetModel.signedAdj_quadratic_Bn
#print axioms RootSetModel.signedAdj_quadratic_Cn
#print axioms RootSetModel.signedAdj_quadratic_F₄
#print axioms RootSetModel.signedAdj_quadratic_G₂
#print axioms RootSetModel.signedAdj_quadratic_simplyLaced

-- RemarkLines.lean: thm:C
#print axioms RootSetModel.F₄_line_counts
#print axioms RootSetModel.G₂_line_counts
#print axioms IsRootSet.remark_lines

-- LeafDeterminant.lean: lem:rem-leaf-det
#print axioms Matrix.det_eq_mul_det_of_row_eq_zero
#print axioms Matrix.det_eq_mul_det_of_col_eq_zero
#print axioms Matrix.det_eq_of_leaf

-- LeadingDeterminants.lean: comp:rem-minors
#print axioms Matrix.det_submatrix_eq_castLE
#print axioms Matrix.det_eq_of_last_leaf
#print axioms CartanMatrix.A_castLE
#print axioms CartanMatrix.B_castLE_of_lt
#print axioms CartanMatrix.C_castLE_of_lt
#print axioms CartanMatrix.D_castLE_of_lt
#print axioms CartanMatrix.E_castLE
#print axioms CartanMatrix.det_A
#print axioms CartanMatrix.det_B
#print axioms CartanMatrix.det_C
#print axioms CartanMatrix.D_last_entry
#print axioms CartanMatrix.D_entry_last
#print axioms CartanMatrix.det_D
#print axioms CartanMatrix.det_E_leading
#print axioms CartanMatrix.leadingDet
#print axioms CartanMatrix.model_leading_determinants

-- ExceptionalLDL.lean: comp:rem-ldl
#print axioms Matrix.dotProduct_ldl_mulVec
#print axioms Matrix.transpose_mulVec_injective_of_unitLower
#print axioms Matrix.posDef_of_ldl
#print axioms RootSetModel.IsExceptional
#print axioms RootSetModel.symmetrizer
#print axioms RootSetModel.symmetrizer_eq_modelSymmetrizer
#print axioms RootSetModel.e₈Lower
#print axioms RootSetModel.e₈Pivots
#print axioms RootSetModel.ldlLower
#print axioms RootSetModel.ldlPivots
#print axioms RootSetModel.ldl_eq
#print axioms RootSetModel.exceptional_ldl

-- RationalFrame.lean: comp:rem-rational-frame
#print axioms IsRootSet.card_eq_two_mul_numLines
#print axioms IsRootSet.rootProjector_apply_eq
#print axioms IsRootSet.half_rootSum_eq_smul_starProjection
#print axioms Matrix.columnVector
#print axioms Matrix.inner_columnVector
#print axioms Matrix.toLp_mulVec_eq_sum
#print axioms Matrix.projection_mulVec_eq_starProjection
#print axioms RootSetModel.ambientDim
#print axioms RootSetModel.toAmbient
#print axioms RootSetModel.simpleRootMatrix
#print axioms RootSetModel.fintypeRoots
#print axioms RootSetModel.halfRootSum
#print axioms RootSetModel.columnVector_simpleRootMatrix
#print axioms RootSetModel.span_columnVector_simpleRootMatrix
#print axioms RootSetModel.simpleRootMatrix_mulVec_injective
#print axioms RootSetModel.toLp_halfRootSum_mulVec
#print axioms RootSetModel.halfRootSum_eq
#print axioms RootSetModel.exists_rat_integerVector
#print axioms RootSetModel.exists_rat_coordinates
#print axioms RootSetModel.halfRootSum_rational
#print axioms RootSetModel.exists_rat_simpleRootMatrix
#print axioms RootSetModel.exists_rat_inv_gram_simpleRootMatrix
#print axioms RootSetModel.rational_frame

#print axioms IsRootSet.exists_rootRepresentatives
