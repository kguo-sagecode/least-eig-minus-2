#!/usr/bin/env python3
"""Untrusted C22 benchmark data; every count is checked independently by Lean."""
from pathlib import Path
from lean_output import write_lean
import json

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'LineGraphs' / 'Computations'
data = json.loads((ROOT / 'cgss/certificates/data/c22.json').read_text())['E8']
header = """/-
Copyright (c) 2026 Krystal Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
"""
source = header + """import LineGraphs.Computations.ListData

/-!
# C22 matrices used to measure the clique certificate checker

Generated from the untrusted Sage output by `generate_checker_benchmarks.py`.
The benchmark modules certify the counts; this is not the C22 classification.
-/

namespace Computations.CliqueBenchmarkData

"""
cases = [('T8', 't8'), ('Chang I', 'changI'), ('Chang II', 'changII'), ('Chang III', 'changIII')]
for title, name in cases:
    rows = data['targets'][title]['adjacency']
    source += f'/-- The supplied adjacency data for {title}. -/\ndef {name} : IntMatrix :=\n  ['
    source += ',\n   '.join(str(row) for row in rows) + ']\n\n'
source += 'end Computations.CliqueBenchmarkData\n'
write_lean(OUT / 'CliqueBenchmarkData.lean', source, 'Clique benchmark data')
for title, name in cases:
    inv = data['invariants'][title]
    code = header + f"""import LineGraphs.Computations.CliqueCertificates
import LineGraphs.Computations.CliqueBenchmarkData

/-!
# Kernel benchmark for {title}

Counts of four- and five-cliques and the per-vertex four-clique profile.
-/

namespace Computations.Examples

open CliqueBenchmarkData

theorem {name}_adjacency : checkAdjacency 28 {name} = true := by decide +kernel

theorem {name}_four_cliques : cliqueCount 28 4 {name} = {inv['four_cliques']} := by
  decide +kernel

theorem {name}_five_cliques : cliqueCount 28 5 {name} = {inv['five_cliques']} := by
  decide +kernel

theorem {name}_clique_profile : cliqueProfile 28 4 {name} =
    """ + str(inv['four_cliques_through_vertex']) + """ := by
  decide +kernel

end Computations.Examples
"""
    # Keep the literal profile under the style limit.
    code = code.replace(str(inv['four_cliques_through_vertex']),
        '[' + ', '.join(map(str, inv['four_cliques_through_vertex'][:14])) + ',\n     ' +
        ', '.join(map(str, inv['four_cliques_through_vertex'][14:])) + ']')
    write_lean(OUT / ('CliqueBenchmark' + name[0].upper() + name[1:] + '.lean'),
               code, 'Clique checker benchmark')
