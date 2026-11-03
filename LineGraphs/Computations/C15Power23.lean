import LineGraphs.Computations.C15Products2

/-! # C15, [CGSS] Example 5.13: adjacency power 3, graph 2. -/

namespace Computations.C15.Table2

/-- C15, [CGSS] Example 5.13: one exact power multiplication. -/
theorem power3_checked : matrixMul 30 power2 adjacency2 = power3 := by
  decide +kernel

end Computations.C15.Table2
