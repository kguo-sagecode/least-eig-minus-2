import LineGraphs.Computations.C15Products1

/-! # C15, [CGSS] Example 5.13: factored annihilator product 3, graph 1. -/

namespace Computations.C15.Table1

/-- C15, [CGSS] Example 5.13: one exact annihilator multiplication. -/
theorem factor3_checked :
    matrixMul 30 (matrixAdd 30 adjacency1 (scalarMatrix 30 (-1))) factor2 =
      factor3 := by
  decide +kernel

end Computations.C15.Table1
