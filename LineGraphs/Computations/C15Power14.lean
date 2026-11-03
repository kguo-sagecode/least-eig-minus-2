import LineGraphs.Computations.C15Products1

/-! # C15, [CGSS] Example 5.13: adjacency power 4, graph 1. -/

namespace Computations.C15.Table1

/-- C15, [CGSS] Example 5.13: one exact power multiplication. -/
theorem power4_checked : matrixMul 30 power3 adjacency1 = power4 := by
  decide +kernel

end Computations.C15.Table1
