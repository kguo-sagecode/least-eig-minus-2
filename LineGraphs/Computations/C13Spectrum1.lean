import LineGraphs.Computations.C13Data
import LineGraphs.Computations.SpectrumChecker
import LineGraphs.Computations.SwitchingChecker

/-!
# Computation C13: graph 1 spectra for [CGSS], Corollary 5.10

The kernel checks an annihilating polynomial and the traces of its first powers.
-/

namespace Computations.C13

/-- C13, [CGSS] Corollary 5.10: table 1 is an adjacency matrix. -/
theorem adjacency1_checked : checkAdjacency 12 adjacency1 = true := by
  decide +kernel

/-- C13, [CGSS] Corollary 5.10: the adjacency spectral certificate for table 1. -/
theorem spectrum1_checked : checkSpectrum 12 adjacency1 spectralData = true := by
  decide +kernel

/-- C13, [CGSS] Corollary 5.10: the Seidel certificate uses `J - I - 2A`. -/
theorem seidel1_checked :
    checkSpectrum 12 (seidelData 12 adjacency1) seidelSpectralData = true := by
  decide +kernel

end Computations.C13
