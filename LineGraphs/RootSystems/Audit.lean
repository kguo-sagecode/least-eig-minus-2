/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.Correspondence

/-!
# Audit of Definition 3.9, RS1, and Theorem 3.10 of [CGSS]

The definition and finite-root-set pairing follow `def:roots` and
`lem:pairing-construction` in `blueprint/sec3-remark311.tex`. Theorem 3.10 follows
the corrected paper and Theorem 3.5 (`thm:3.5`); its settled name is
`LineSystem.isRootSet_tfae`. Only the standard Lean axioms are permitted.
-/

#print axioms IsRootSet
#print axioms IsRootSet.ne_zero
#print axioms IsRootSet.finiteDimensional
#print axioms IsRootSet.IsIndecomposable
#print axioms IsRootSet.coroot
#print axioms IsRootSet.coroot_coroot
#print axioms IsRootSet.coroot_injective
#print axioms IsRootSet.inner_coroot_self
#print axioms IsRootSet.reflection
#print axioms IsRootSet.reflection_apply
#print axioms IsRootSet.reflection_involutive
#print axioms IsRootSet.reflection_self
#print axioms IsRootSet.neg_mem
#print axioms IsRootSet.coroot_reflection
#print axioms IsRootSet.reflectionPerm
#print axioms IsRootSet.inner_isPerfPair
#print axioms IsRootSet.toRootPairing
#print axioms IsRootSet.finite_root_index
#print axioms IsRootSet.toRootPairing_pairing
#print axioms IsRootSet.toRootPairing_isCrystallographic
#print axioms IsRootSet.toRootPairing_isReduced
#print axioms IsRootSet.toRootPairing_isRootSystem
#print axioms IsRootSet.toRootPairing_reflection
#print axioms IsRootSet.toRootPairing_coreflection
#print axioms IsRootSet.toRootPairing_coroot'_eq_zero_iff
#print axioms IsRootSet.isIrreducible_of_isIndecomposable
#print axioms IsRootSet.isIndecomposable_of_isIrreducible
#print axioms IsRootSet.isIrreducible_iff
#print axioms LineSystem.IsStarClosed.isRootSet
#print axioms LineSystem.isStarClosed_of_isRootSet
#print axioms LineSystem.isRootSet_iff_isStarClosed
#print axioms LineSystem.IsStarClosed.isRootSet_restrictSpan
#print axioms LineSystem.IsStarClosed.toRootPairing
#print axioms LineSystem.IsStarClosed.toRootPairing_isCrystallographic
#print axioms LineSystem.IsStarClosed.toRootPairing_isReduced
#print axioms LineSystem.IsStarClosed.toRootPairing_isRootSystem
#print axioms LineSystem.IsStarClosed.toRootPairing_isIrreducible_iff
#print axioms IsRootSet.inner_mem_of_inner_self_eq_two
#print axioms IsRootSet.toLineSystem
#print axioms IsRootSet.isStarClosed_toLineSystem
#print axioms LineSystem.IsOrthogonalSumOfModels
#print axioms LineSystem.ofOrthogonalPartition
#print axioms LineSystem.IsStarClosed.ofOrthogonalPartition
#print axioms LineSystem.ncard_lt_of_orthogonal_partition
#print axioms LineSystem.IsStarClosed.isOrthogonalSumOfModels
#print axioms LineSystem.IsOrthogonalSumOfModels.isStarClosed
#print axioms LineSystem.orthogonalFamily_span
#print axioms LineSystem.iSup_span_eq_of_root_cover
#print axioms LineSystem.IsOrthogonalSumOfModels.exists_isInternal
#print axioms LineSystem.isRootSet_tfae
#print axioms LineSystem.isRootSet_tfae_of_inner_self_eq_two
#print axioms LineSystem.isRootSet_and_isIndecomposable_iff
