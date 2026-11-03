/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C2
import LineGraphs.LineSystem.ClassificationChoicesModels

/-!
# Axiom audit for C2 and the perpendicular choices in the other models

Every new public declaration of `Computations/C2.lean` and
`LineSystem/ClassificationChoicesModels.lean`, in the order of `blueprint/sec3-rootsystems.tex`:
Lemma (integer realizations) `lem:sec3-integer`, the cuts `T₇`, `T₆` of Definition 3.3
(`def:3.3`), Computation C2 (`comp:C2`), and Lemma (independence of the perpendicular choices)
`lem:sec3-choices`, in the order of its steps. Each line should print only `propext`,
`Classical.choice` and `Quot.sound`. -/

-- lem:sec3-integer
#print axioms LineSystem.exists_halfRoot_eq
#print axioms LineSystem.range_halfRoot
#print axioms LineSystem.steinerBlock_inter_card_of_ne
#print axioms Computations.C2.IsIntegerPresentation
#print axioms Computations.C2.model_presentations

-- def:3.3, the cuts T₇ and T₆ of model (iii)
#print axioms LineSystem.integerVector_inner_single_eq_zero
#print axioms LineSystem.integerVector_inner_e₅₆₇₈_eq_zero
#print axioms LineSystem.T₇
#print axioms LineSystem.T₆
#print axioms LineSystem.T₇.Index
#print axioms LineSystem.T₆.Index
#print axioms LineSystem.T₇_roots_eq_range
#print axioms LineSystem.T₆_roots_eq_range
#print axioms LineSystem.T₇.integerModel
#print axioms LineSystem.T₆.integerModel

-- comp:C2
#print axioms LineSystem.card_T₇Index
#print axioms LineSystem.card_T₆Index
#print axioms LineSystem.numLines_T₇
#print axioms LineSystem.numLines_T₆
#print axioms Computations.C2.line_counts

-- lem:sec3-choices, steps s3choicepair, s3choiceroot and s3choicecuts, through an isomorphism
-- with E₈, and the root assertion for the default model
#print axioms LineSystem.ext
#print axioms LineSystem.ext_iff
#print axioms LineSystem.orthogonalTo_smul
#print axioms LineSystem.Iso.orthogonalTo
#print axioms LineSystem.Iso.exists_isometry
#print axioms LineSystem.Iso.exists_isometry_of_ordered_stars
#print axioms LineSystem.Iso.exists_inner_eq_neg_one
#print axioms LineSystem.Iso.exists_isometry_of_roots
#print axioms LineSystem.E₈.exists_isometry_of_root
#print axioms LineSystem.Iso.nonempty_iso_E₇_orthogonalTo
#print axioms LineSystem.Iso.nonempty_iso_E₆_orthogonalTo

-- lem:sec3-choices, step s3choiceSteiner
#print axioms LineSystem.t₇Normal
#print axioms LineSystem.t₆Normal
#print axioms LineSystem.t₇Normal_eq_integerVector
#print axioms LineSystem.t₆Normal_eq_integerVector
#print axioms LineSystem.t₇Normal_mem_E₈viaSteiner
#print axioms LineSystem.t₆Normal_mem_E₈viaSteiner
#print axioms LineSystem.inner_t₇Normal_t₆Normal
#print axioms LineSystem.T₇_eq_orthogonalTo
#print axioms LineSystem.T₆_eq_orthogonalTo

-- lem:sec3-choices, the final qedstep: model (i), model (iii), T₇ and T₆
#print axioms LineSystem.E₈viaA₈.exists_isometry_of_ordered_stars
#print axioms LineSystem.E₈viaA₈.exists_isometry_of_roots
#print axioms LineSystem.E₈viaA₈.nonempty_iso_E₇_orthogonalTo
#print axioms LineSystem.E₈viaA₈.nonempty_iso_E₆_orthogonalTo
#print axioms LineSystem.E₈viaSteiner.exists_isometry_of_ordered_stars
#print axioms LineSystem.E₈viaSteiner.exists_isometry_of_ordered_star
#print axioms LineSystem.E₈viaSteiner.exists_isometry_of_roots
#print axioms LineSystem.E₈viaSteiner.exists_isometry_of_root
#print axioms LineSystem.E₈viaSteiner.nonempty_iso_E₇_orthogonalTo
#print axioms LineSystem.E₈viaSteiner.nonempty_iso_E₆_orthogonalTo
#print axioms LineSystem.T₇.nonempty_iso_E₇
#print axioms LineSystem.T₆.nonempty_iso_E₆
