import LineGraphs.Computations.C13Data
import LineGraphs.Computations.SpectrumChecker
import LineGraphs.Computations.SwitchingChecker

/-!
# Computation C13: graph 2 spectra for [CGSS], Corollary 5.10

The kernel checks an annihilating polynomial and the traces of its first powers.
-/

namespace Computations.C13

/-- C13, [CGSS] Corollary 5.10: table 2 is an adjacency matrix. -/
theorem adjacency2_checked : checkAdjacency 12 adjacency2 = true := by
  decide +kernel

/-- C13, [CGSS] Corollary 5.10: the adjacency spectral certificate for table 2. -/
theorem spectrum2_checked : checkSpectrum 12 adjacency2 spectralData = true := by
  decide +kernel

/-- C13, [CGSS] Corollary 5.10: the Seidel certificate uses `J - I - 2A`. -/
theorem seidel2_checked :
    checkSpectrum 12 (seidelData 12 adjacency2) seidelSpectralData = true := by
  decide +kernel

end Computations.C13
