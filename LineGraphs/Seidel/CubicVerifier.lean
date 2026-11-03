/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.CubicCertificates

/-!
# Verification of the local cubic certificates

Kernel checks for the neighbourhood case split of `res:414-SE4` (Remark 4.14).
-/

namespace SimpleGraph.CubicEight

/-- Small adjacency masks for the six SE4 models; checked against their graph definitions. -/
def modelMask : Fin 6 → Fin 8 → ℕ :=
  ![![14, 13, 11, 7, 224, 208, 176, 112],
    ![138, 69, 42, 21, 168, 84, 162, 81],
    ![146, 37, 74, 148, 41, 82, 164, 73],
    ![134, 37, 11, 84, 168, 82, 168, 81],
    ![134, 37, 11, 148, 104, 82, 176, 73],
    ![134, 13, 11, 22, 104, 208, 176, 97]]

/-- The bit tables used by the local SE4 checker have the intended graph adjacencies. -/
theorem modelMask_adj :
    ∀ m i j, (modelMask m i).testBit j.val = true ↔ (model m).Adj i j := by
  decide +kernel

/-- Base-256 encoding of the neighbourhood table used by the SE4 certificates. -/
def rowKey (rows : Rows) : ℕ :=
  (List.finRange 8).foldl (fun key i ↦ 256 * key + ∑ j ∈ rows i, 2 ^ j.val) 0

/-- Check both bijectivity and every adjacency of the proposed SE4 isomorphism. -/
def checkCertificate (rows : Rows) : Bool :=
  let c := certificate (rowKey rows)
  decide (Function.Bijective c.2 ∧
    ∀ i j, j ∈ rows i ↔ (modelMask c.1 (c.2 i)).testBit (c.2 j).val = true)

/-- The local certificate gives an actual isomorphism, as required by `res:414-SE4`. -/
theorem nonempty_iso_of_checkCertificate (X : SimpleGraph (Fin 8)) [DecidableRel X.Adj]
    (hc : checkCertificate (fun i ↦ X.neighborFinset i) = true) :
    ∃ i, Nonempty (X ≃g model i) := by
  obtain ⟨hb, ha⟩ := of_decide_eq_true hc
  refine ⟨(certificate (rowKey (fun i ↦ X.neighborFinset i))).1,
    ⟨{ toEquiv := Equiv.ofBijective _ hb, map_rel_iff' := ?_ }⟩⟩
  intro i j
  exact (modelMask_adj _ _ _).symm.trans
    ((ha i j).symm.trans (X.mem_neighborFinset i j))

end SimpleGraph.CubicEight
