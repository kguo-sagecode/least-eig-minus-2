import LineGraphs.Computations.C15Products2

/-! # C15, [CGSS] Example 5.13: factored annihilator product 1, graph 2. -/

namespace Computations.C15.Table2

/-- C15, [CGSS] Example 5.13: one exact annihilator multiplication. -/
theorem factor1_checked :
    matrixMul 30 (matrixAdd 30 adjacency2 (scalarMatrix 30 (2))) (scalarMatrix 30 1) =
      factor1 := by
  decide +kernel

end Computations.C15.Table2
