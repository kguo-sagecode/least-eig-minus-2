/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Clebsch
import LineGraphs.Computations.C9Shrikhande
import LineGraphs.Representation.Switching
import LineGraphs.Graphs.Basic

/-!
# The switching certificates in C9

Example 4.8 of [CGSS]: Clebsch is switching equivalent to Shrikhande and to
the line graph of `K₄,₄`. The sign lists are from `cgss/certificates/data/c09.json`.
-/

namespace SimpleGraph

set_option maxRecDepth 4000

/-- C9, Example 4.8 of [CGSS]: the signs for the switching to Shrikhande. -/
def clebsch.shrikhandeSigns : Fin 16 → ℤ :=
  ![1, -1, -1, -1, -1, 1, -1, -1, 1, 1, -1, 1, 1, 1, 1, -1]

/-- C9, Example 4.8 of [CGSS]: the Clebsch and Shrikhande vector graphs
are switching equivalent under the certified signing. -/
theorem clebsch_isSwitchingEquivalent_shrikhande : clebsch.IsSwitchingEquivalent shrikhande :=
  isSwitchingEquivalent_of_integer_certificate clebsch shrikhande (Equiv.refl _)
    clebsch.shrikhandeSigns (by decide +kernel) (by decide +kernel)

/-- C9, Example 4.8 of [CGSS]: the signs for the switching to `L(K₄,₄)`. -/
def clebsch.bipartiteSigns : Fin 16 → ℤ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1]

/-- C9, Example 4.8 of [CGSS]: the certificate's row labels as edges of `K₄,₄`. -/
noncomputable def clebsch.bipartiteEdgeEquiv :
    Fin 16 ≃ (completeBipartiteGraph (Fin 4) (Fin 4)).edgeSet :=
  finProdFinEquiv.symm.trans (completeBipartiteEdgeEquiv (Fin 4) (Fin 4))

noncomputable local instance :
    DecidableRel (completeBipartiteGraph (Fin 4) (Fin 4)).Adj := Classical.decRel _

noncomputable local instance :
    DecidableRel (completeBipartiteGraph (Fin 4) (Fin 4)).lineGraph.Adj := Classical.decRel _

/-- C9, Example 4.8 of [CGSS]: the Clebsch vector graph is switching
equivalent to the line graph of `K₄,₄`, with the certificate interpreted on edges. -/
theorem clebsch_isSwitchingEquivalent_lineGraph_completeBipartite :
    clebsch.IsSwitchingEquivalent (completeBipartiteGraph (Fin 4) (Fin 4)).lineGraph := by
  apply isSwitchingEquivalent_of_integer_certificate _ _ clebsch.bipartiteEdgeEquiv
    clebsch.bipartiteSigns (by decide +kernel)
  intro i j
  simp only [clebsch.bipartiteEdgeEquiv.injective.eq_iff]
  simp only [clebsch.bipartiteEdgeEquiv, Equiv.trans_apply, lineGraph_completeBipartiteGraph_adj]
  exact (by decide +kernel : ∀ i j : Fin 16,
    ((if i = j then 0 else 1) - 2 * (if clebsch.Adj i j then 1 else 0) : ℤ) =
      clebsch.bipartiteSigns i * clebsch.bipartiteSigns j *
        ((if i = j then 0 else 1) - 2 *
          (if (finProdFinEquiv.symm i : Fin 4 × Fin 4) ≠ finProdFinEquiv.symm j ∧
            ((finProdFinEquiv.symm i : Fin 4 × Fin 4).1 =
                (finProdFinEquiv.symm j : Fin 4 × Fin 4).1 ∨
             (finProdFinEquiv.symm i : Fin 4 × Fin 4).2 =
                (finProdFinEquiv.symm j : Fin 4 × Fin 4).2)
            then 1 else 0))) i j

end SimpleGraph
