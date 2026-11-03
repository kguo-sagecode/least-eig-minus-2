import LineGraphs.Computations.C15Design
import LineGraphs.Computations.C15PetersenIso

/-! # C15: the graphs named in [CGSS], Example 5.13. -/

namespace Computations.C15

-- Example 5.13 (the final remark, C15)
/-- C15, [CGSS] Example 5.13, the final blueprint remark: the named graphs are cospectral. -/
theorem flagGraph_cospectral_double_lineGraph :
    (C13.incidenceGraph design.block).lineGraph.Cospectral
      SimpleGraph.petersen.lineGraph.lineGraph := by
  apply SimpleGraph.cospectral_iff_spectrumMultiset_eq.mpr
  rw [← flagGraphIso.cospectral.spectrumMultiset_eq,
    ← petersenIso.lineGraph.lineGraph.cospectral.spectrumMultiset_eq,
    ← doubleLineGraphIso.cospectral.spectrumMultiset_eq]
  exact cospectral.spectrumMultiset_eq

-- Example 5.13 (the final remark, C15)
/-- C15, [CGSS] Example 5.13, the final blueprint remark: the named graphs are not isomorphic. -/
theorem flagGraph_not_nonempty_iso_double_lineGraph :
    ¬ Nonempty ((C13.incidenceGraph design.block).lineGraph ≃g
      SimpleGraph.petersen.lineGraph.lineGraph) := by
  rintro ⟨e⟩
  exact not_nonempty_iso
    ⟨flagGraphIso.trans (e.trans (doubleLineGraphIso.trans petersenIso.lineGraph.lineGraph).symm)⟩

end Computations.C15
