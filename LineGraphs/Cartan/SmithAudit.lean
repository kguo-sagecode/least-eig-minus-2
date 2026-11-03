/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Smith

/-!
# Audit of the Smith graph classification

Theorem 3.8 of [CGSS], Corollary D (`thm:3.8`, `cor:D`) of the Remark 3.11 blueprint.
This file checks the explicit vertex types of the five existing Smith graph models and
prints the axioms of all six public declarations in `Smith.lean`. It also prints the
axioms of the reused spectral certificates and the every-realization, every-deletion
basis theorem. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Blueprint coverage:

* `rDunit`, `rDobstructionUnit`: `IsAffineObstruction.nonempty_iso_smith`.
* `rDproper`, `rDequal`: `Contains.nonempty_iso_of_maxRayleigh_eq`, `supportReindexIso`.
* `rDdynkin`, `rDobstruction`, `rDforward`: the forward direction of `SimpleGraph.smith`.
* `rDlisted`, `rDtransport`, `rDbackward`: the five imported spectral certificates,
  `SimpleGraph.Iso.maxRayleigh_eq`, and the reverse direction of `SimpleGraph.smith`.
* `rDrealize`: `SimpleGraph.smith_exists_gram`, using the existing weighted Gram result.
* `rDdelete`: the imported `SimpleGraph.smith_gram_delete_basis`, with the ambient space
  correctly given by the span of the whole realizing family.

The statement is the blueprint's equivalence at largest eigenvalue exactly two; no
classification below two is asserted there. No settled model or theorem name is changed.
-/

#check (SimpleGraph.smithA : (ℓ : ℕ) → SimpleGraph (Fin (ℓ + 1)))
#check (SimpleGraph.smithD : (ℓ : ℕ) → SimpleGraph (Fin (ℓ - 4 + 1) ⊕ Fin 4))
#check (SimpleGraph.smithE₆ : SimpleGraph (SimpleGraph.ArmVertex ![2, 2, 2]))
#check (SimpleGraph.smithE₇ : SimpleGraph (SimpleGraph.ArmVertex ![1, 3, 3]))
#check (SimpleGraph.smithE₈ : SimpleGraph (SimpleGraph.ArmVertex ![1, 2, 5]))

-- New declarations: Theorem 3.8 and its isomorphism and realization interfaces.
#print axioms WeightedGraph.supportReindexIso
#print axioms WeightedGraph.Contains.nonempty_iso_of_maxRayleigh_eq
#print axioms WeightedGraph.IsAffineObstruction.nonempty_iso_smith
#print axioms SimpleGraph.Iso.maxRayleigh_eq
#print axioms SimpleGraph.smith
#print axioms SimpleGraph.smith_exists_gram

-- Existing declarations reused for Corollary D of Remark 3.11, Theorem 3.8 of [CGSS].
#print axioms WeightedGraph.affine_or_dynkin
#print axioms WeightedGraph.Contains.eq_of_maxRayleigh_eq
#print axioms WeightedGraph.IsAffineObstruction.maxRayleigh_eq_two
#print axioms Matrix.IsHermitian.maxRayleigh_reindex
#print axioms SimpleGraph.smithA_maxRayleigh
#print axioms SimpleGraph.smithD_maxRayleigh
#print axioms SimpleGraph.smithE₆_maxRayleigh
#print axioms SimpleGraph.smithE₇_maxRayleigh
#print axioms SimpleGraph.smithE₈_maxRayleigh
#print axioms WeightedGraph.exists_gram_card_sub_one
#print axioms SimpleGraph.smith_gram_delete_basis
