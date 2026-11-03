import LineGraphs.Computations.C15Products1

/-! # C15, [CGSS] Example 5.13: adjacency power 2, graph 1. -/

namespace Computations.C15.Table1

/-- C15, [CGSS] Example 5.13: one exact power multiplication. -/
theorem power2_checked : matrixMul 30 power1 adjacency1 = power2 := by
  decide +kernel

end Computations.C15.Table1
