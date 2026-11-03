import LineGraphs.Computations.C15Petersen
import LineGraphs.Computations.C9Petersen

/-!
# C15: the settled Petersen graph in [CGSS], Example 5.13

The explicit permutation identifies the pentagon/pentagram model used by the C15 certificate
with `SimpleGraph.petersen`, the vector graph of Example 4.9. Lean checks both inverse tables
and every adjacency by kernel reduction.
-/

namespace Computations.C15

-- Example 5.13 (the final remark, C15)
/-- C15, [CGSS] Example 5.13, final blueprint remark: relabel the Petersen vertices. -/
def petersenEquiv : Fin 10 ≃ Fin 10 where
  toFun := ![0, 1, 6, 3, 5, 9, 8, 4, 2, 7]
  invFun := ![0, 1, 8, 3, 7, 4, 2, 9, 6, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

-- Example 5.13 (the final remark, C15)
/-- C15, [CGSS] Example 5.13, final blueprint remark: the two Petersen models agree. -/
def petersenIso : petersen ≃g SimpleGraph.petersen where
  toEquiv := petersenEquiv
  map_rel_iff' := by decide +kernel

-- Example 5.13 (the final remark, C15)
/-- C15, [CGSS] Example 5.13, final blueprint remark: the certificate uses Petersen. -/
theorem nonempty_iso_petersen : Nonempty (petersen ≃g SimpleGraph.petersen) :=
  ⟨petersenIso⟩

end Computations.C15
