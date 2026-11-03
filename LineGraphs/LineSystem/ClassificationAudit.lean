/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.ClassificationMaximal
import LineGraphs.LineSystem.ClassificationConnected
import LineGraphs.LineSystem.ClassificationChoices
import LineGraphs.Representation.RootTypeClassified
import LineGraphs.Spectral.RelativeBoundFourteen

/-!
# Axiom audit for Theorems 2.13, 3.5 and 3.6 and their consequences

Every declaration of `ClassificationModels.lean`, `Classification.lean`,
`ClassificationMaximal.lean`, `ClassificationConnected.lean`, `ClassificationChoices.lean`,
`Representation/RootTypeClassified.lean` and `Spectral/RelativeBoundFourteen.lean`; only
`propext`, `Classical.choice` and `Quot.sound` are permitted.
-/

-- Theorem 2.13, unconditional (`ClassificationModels.lean`)
#print axioms LineSystem.An.exists_eq_pair_one
#print axioms LineSystem.modelInputs
#print axioms LineSystem.five_possibilities'
-- Theorem 3.5 (`Classification.lean`)
#print axioms LineSystem.Iso.trans
#print axioms LineSystem.Iso.ncard_eq
#print axioms LineSystem.RootType.eq_of_rank_eq_of_numLines_eq
#print axioms LineSystem.RootType.eq_of_iso
#print axioms LineSystem.RootType.isIndecomposable_model
#print axioms LineSystem.RootType.isStarClosed_model
#print axioms LineSystem.exists_iso_rootType
#print axioms LineSystem.classification
-- Theorem 3.6 (`ClassificationMaximal.lean`)
#print axioms LineSystem.ncard_Φ_E₆
#print axioms LineSystem.choose_two_mul_four
#print axioms LineSystem.RootType.Φ_nonempty_model
#print axioms LineSystem.RootType.ncard_model_A
#print axioms LineSystem.RootType.ncard_model_D
#print axioms LineSystem.RootType.ncard_model_E₆
#print axioms LineSystem.RootType.ncard_model_E₇
#print axioms LineSystem.RootType.ncard_model_E₈
#print axioms LineSystem.RootType.exists_inclusion_of_not_isMaximal
#print axioms LineSystem.isMaximal_An
#print axioms LineSystem.isMaximal_Dn
#print axioms LineSystem.isMaximal_E₆
#print axioms LineSystem.isMaximal_E₇
#print axioms LineSystem.isMaximal_E₈
#print axioms LineSystem.classification_of_isMaximal
#print axioms LineSystem.IsMaximal.exists_iso_rootType
-- Lemma (a connected spanning set) (`ClassificationConnected.lean`)
#print axioms LineSystem.eq_empty_of_connected_spanning_of_mem
#print axioms LineSystem.isIndecomposable_of_connected_spanning
-- Lemma (independence of the perpendicular choices) (`ClassificationChoices.lean`)
#print axioms LineSystem.Iso.ofLinearIsometryEquiv
#print axioms LineSystem.nonempty_iso_orthogonalTo_of_mem_isometryGroup
#print axioms LineSystem.E₈.exists_isometry_of_ordered_star
#print axioms LineSystem.E₈.exists_inner_eq_neg_one
#print axioms LineSystem.E₈.nonempty_iso_E₇_orthogonalTo
#print axioms LineSystem.E₈.nonempty_iso_E₆_orthogonalTo
-- Section 4 (`RootTypeClassified.lean`, `RelativeBoundFourteen.lean`)
#print axioms SimpleGraph.IsRepresentation.exists_isRepresentedIn_rootType
#print axioms InnerProductSpace.card_le_fourteen_of_finrank_eq_eight
