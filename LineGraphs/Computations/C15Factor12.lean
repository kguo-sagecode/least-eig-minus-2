import LineGraphs.Computations.C15Products1

/-! # C15, [CGSS] Example 5.13: factored annihilator product 2, graph 1. -/

namespace Computations.C15.Table1

/-- C15, [CGSS] Example 5.13: one exact annihilator multiplication. -/
theorem factor2_checked :
    matrixMul 30 (matrixAdd 30 adjacency1 (scalarMatrix 30 (0))) factor1 =
      factor2 := by
  decide +kernel

end Computations.C15.Table1
