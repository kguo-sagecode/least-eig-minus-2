#!/usr/bin/env python3
"""Translate the Sage C3 maps into Lean certificates (not part of the trust base)."""
import json
from fractions import Fraction
from functools import reduce
from math import lcm
from pathlib import Path
from lean_output import write_lean

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'LineGraphs' / 'Computations'
CERT = ROOT / 'cgss' / 'certificates' / 'data'
models = json.loads((CERT / 'c02_models.json').read_text())['models']
maps = json.loads((CERT / 'c03_maps.json').read_text())['maps']


def rational(x):
    return Fraction(x['num'], x['den']) if isinstance(x, dict) else Fraction(x)


def matrix(xs):
    return '[\n' + ',\n'.join('  ' + str(x) for x in xs) + ']'


data = '''import LineGraphs.Computations.RootMapData
import LineGraphs.Computations.ExceptionalData

/-! Rational maps and images from `cgss/certificates/data/c03_maps.json`.
Rows are reordered into the existing Lean source tables. -/

namespace Computations.C3

'''
names = []
for name, packet, source, qs in zip(['a', 'steiner'], maps, ['e₈ARoots', 'e₈SteinerRoots'], [9, 2]):
    roots = models[packet['source']]['roots']
    targets = models[packet['target']]['roots']
    pairs = sorted((r, targets[j]) for r, j in zip(roots, packet['permutation']))
    mat = [[rational(x) for x in row] for row in packet['matrix']]
    den = reduce(lcm, (x.denominator for row in mat for x in row), 1)
    num = [[int(x * den) for x in row] for row in mat]
    for r, t in pairs:
        assert [sum(r[k] * num[k][j] for k in range(len(r))) for j in range(8)] == [den*x for x in t]
    for chunk in range(12):
        data += f'/-- Twenty images from the Sage map. -/\ndef {name}Images{chunk} : List IntVector := {matrix([t for _,t in pairs[20*chunk:20*chunk+20]])}\n\n'
    data += f'/-- Sage images in the order of the Lean source table. -/\ndef {name}Images : List IntVector := ' + ' ++\n    '.join(f'{name}Images{k}' for k in range(12)) + '\n\n'
    data += f'/-- Numerator of the rational row-vector map; denominator {den}. -/\ndef {name}Matrix : IntMatrix := {matrix(num)}\n\n'
    data += f'/-- A block of twenty rows in the scaled Gram comparison. -/\ndef {name}GramChunk (k : ℕ) : Bool :=\n  ((List.range 240).drop (20 * k) |>.take 20).all\n    (checkScaledGramRow {qs} 4 {source} {name}Images)\n\n'
    for k in range(12):
        module = f'C3{name.capitalize()}Rows{k:02}'
        names.append(module)
        code = f'''import LineGraphs.Computations.C3Data
import LineGraphs.Computations.ExceptionalData

/-! Twenty rows of the scaled Gram comparison for the Sage map. -/

namespace Computations.C3

theorem {name}_gram_chunk_{k} : {name}GramChunk {k} = true := by
  decide +kernel

end Computations.C3
'''
        write_lean(OUT / (module+'.lean'), code, 'C3 scaled Gram certificate')
data += 'end Computations.C3\n'
write_lean(OUT / 'C3Data.lean', data, 'Sage E₈ model maps')

code = 'import LineGraphs.Computations.ModelCertificates\n' + ''.join(f'import LineGraphs.Computations.{n}\n' for n in names)
code += '''
/-! The two isomorphisms of computation C3, from the Sage root maps. -/

open Computations

namespace Computations.C3

'''
for name, source, model, qs, idx, sagesrc in [('a','e₈ARoots','E₈viaA₈',9,0,'`E8_A`'),
        ('steiner','e₈SteinerRoots','E₈viaSteiner',2,1,'`E8_S`')]:
    chunk_lemmas = ',\n    '.join(f'{name}_gram_chunk_{k}' for k in range(12))
    code += f'''theorem {name}_gram_checked : (List.range 240).all
    (checkScaledGramRow {qs} 4 {source} {name}Images) = true := by
  apply all_eq_true_of_chunks
    (chunk := fun k => (List.range 240).drop (20 * k) |>.take 20) (m := 12)
    (by decide +kernel)
  apply List.all_eq_true.mp
  change (List.range 12).all {name}GramChunk = true
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    {chunk_lemmas}, Bool.and_self]

theorem {name}_images_perm : {name}Images.Perm E₈Data.e₈Roots := by
  have hs : {name}Images.insertionSort
      (fun v w => vectorKey v ≤ vectorKey w) = E₈Data.e₈Roots := by
    decide +kernel
  rw [← hs]
  exact (List.perm_insertionSort _ _).symm

theorem {name}_images_set : {name}Images.toFinset = E₈Data.e₈Roots.toFinset := by
  ext w
  simpa using {name}_images_perm.mem_iff (a := w)

/-- Target presentation in the order prescribed by the Sage map. -/
@[instance_reducible] noncomputable def {name}Target : LineSystem.IntegerModel LineSystem.E₈ :=
  LineSystem.E₈viaD₈.integerModel.ofTable {name}Images 240 (by decide +kernel)
    ({name}_images_perm.nodup_iff.mpr (of_decide_eq_true E₈Data.e₈_nodup_checked))
    (fun w => (mem_iff_of_toFinset_eq {name}_images_set w).trans
      (LineSystem.E₈viaD₈.mem_rootList w))

end Computations.C3

namespace LineSystem

/-- C3: the isomorphism sending the `i`-th root of `{source}` to the `i`-th entry of
`C3.{name}Images`, which preserves the Gram matrix up to the scale `C3.{name}_gram_checked`. The
images are those of the Sage map `maps[{idx}]` of `cgss/certificates/data/c03_maps.json`
({sagesrc} to `E8_D`, as row vectors), which `scripts/generate_c3.py` checks; Lean checks only
the root correspondence, and the iso is not stated as induced by the matrix. -/
noncomputable def {model}.isoE₈ : {model}.Iso E₈ :=
  Iso.ofIntegerModels
    ({model}.integerModel.ofTable {source} 240 (by decide +kernel) {source}_nodup
      {model}.mem_rootList)
    C3.{name}Target (Equiv.refl _) fun i j =>
      checkScaledGram_sound (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) C3.{name}_gram_checked i j

/-- C3: existence of the isomorphism between this presentation and the default E₈. -/
theorem {model}.nonempty_iso_E₈ : Nonempty ({model}.Iso E₈) := ⟨{model}.isoE₈⟩

end LineSystem

namespace Computations.C3

'''
code += 'end Computations.C3\n'
start = code.index('theorem a_gram_checked')
second = code.index('theorem steiner_gram_checked')
prefix = code[:start]
for stem, body in [('C3A', code[start:second]), ('C3Steiner', code[second:])]:
    # The first fragment already opens the next namespace.
    if stem == 'C3A':
        body += 'end Computations.C3\n'
    write_lean(OUT / (stem+'.lean'), prefix + body, 'C3 isomorphism')
write_lean(OUT / 'C3.lean', 'import LineGraphs.Computations.C3A\n'
    'import LineGraphs.Computations.C3Steiner\n\n/-! The two certified E₈ model isomorphisms. -/\n',
    'Isomorphisms of the three E₈ models')

# The assertion above checks the images of every root against the matrices;
# the Lean proofs use the certified Gram matrices and isomorphisms.

