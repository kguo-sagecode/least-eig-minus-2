import LineGraphs.Computations.C15Products2

/-! # C15, [CGSS] Example 5.13: adjacency power 2, graph 2. -/

namespace Computations.C15.Table2

/-- C15, [CGSS] Example 5.13: one exact power multiplication. -/
theorem power2_checked : matrixMul 30 power1 adjacency2 = power2 := by
  decide +kernel

end Computations.C15.Table2
