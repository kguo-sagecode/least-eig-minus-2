#!/usr/bin/env python3
"""Translate the C4 Sage trees and marked-star data; Lean checks all witnesses."""
import json
from collections import deque
from pathlib import Path
from lean_output import write_lean

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'LineGraphs' / 'Computations'
CERT = ROOT / 'cgss' / 'certificates' / 'data'
systems = json.loads((CERT / 'c04.json').read_text())['systems']
roots = json.loads((CERT / 'c06.json').read_text())['systems']


def nat_list(xs):
    return '[\n' + ',\n'.join('  '+', '.join(map(str,xs[k:k+16])) for k in range(0,len(xs),16)) + ']'


for key, name, N, k, degree, mu, delta in [('E6','E₆',72,9,4,2,12),
        ('E7','E₇',126,15,6,3,30), ('E8','E₈',240,27,10,5,72)]:
    cert = systems[key]
    original = roots[key]['roots']
    table = sorted(original)
    pos = {tuple(r): i for i,r in enumerate(table)}
    remap = [pos[tuple(r)] for r in original]
    representatives = cert['line_representative_indices']
    adj = [[] for _ in representatives]
    for a,b,_ in cert['nonorthogonality_spanning_tree']:
        adj[a].append(b)
        adj[b].append(a)
    depths={0:0}; parents={0:0}; queue=deque([0])
    while queue:
        a=queue.popleft()
        for b in adj[a]:
            if b not in depths:
                depths[b]=depths[a]+1; parents[b]=a; queue.append(b)
    par=[0]*N; dep=[0]*N
    for j,ridx in enumerate(representatives):
        a=remap[ridx]; neg=pos[tuple(-x for x in original[ridx])]
        par[a]=remap[representatives[parents[j]]]; dep[a]=depths[j]
        par[neg]=a; dep[neg]=depths[j]+1
    base=remap[representatives[0]]
    a,b,_=[remap[i] for i in cert['star']]
    data = '''import LineGraphs.Computations.ListData

/-! Marked-star and connectivity witnesses translated from the Sage C4 certificate. -/

namespace Computations.C4

'''
    for label, xs in [('parents',par),('depths',dep),('gamma', [remap[i] for i in cert['gamma']]),
                      ('delta',[remap[i] for i in cert['delta']])]:
        data += f'/-- Sage {label} certificate, reindexed by the sorted root table. -/\ndef {key.lower()}{label.capitalize()} : List ℕ := {nat_list(xs)}\n\n'
    A = '[\n' + ',\n'.join('  '+str(row) for row in cert['gamma_graph']['adjacency']) + ']'
    data+=f'/-- Orthogonality adjacency on the certified Gamma labels. -/\ndef {key.lower()}Adjacency : IntMatrix := {A}\n\nend Computations.C4\n'
    write_lean(OUT/(f'C4{key}Data.lean'),data,f'C4 {name} witnesses')
    ns=key.lower()
    original_model = 'E₈viaD₈' if key=='E8' else name
    code=f'''import LineGraphs.Computations.C4{key}Data
import LineGraphs.Computations.StarCertificates
import LineGraphs.Computations.E8

/-! Computation C4 for {name}: connectivity and the specified ordered star. -/

open Computations C4
open scoped RealInnerProductSpace

namespace LineSystem

/-- The sorted finite presentation used for this model's certificates. -/
@[reducible] noncomputable def {name}.tableModel : IntegerModel {name} :=
  {original_model}.integerModel.ofTable {original_model}.rootList {N}
    (by decide +kernel) (by decide +kernel) {original_model}.mem_rootList

/-- C4: the spanning tree in the Sage certificate proves indecomposability. -/
theorem isIndecomposable_{name} : {name}.IsIndecomposable := by
  apply {name}.tableModel.isIndecomposable_of_parent ({base} : Fin {N})
    (fun i => ⟨{ns}Parents[i.val]?.getD 0 % {N}, Nat.mod_lt _ (by decide)⟩)
    (fun i => {ns}Depths[i.val]?.getD 0)
  · change ∀ i : Fin {N}, i ≠ {base} →
      {ns}Depths[{ns}Parents[i.val]?.getD 0 % {N}]?.getD 0 < {ns}Depths[i.val]?.getD 0
    decide +kernel
  · change ∀ i : Fin {N}, i ≠ {base} →
      integerInner ({name}.tableModel.v i)
        ({name}.tableModel.v ⟨{ns}Parents[i.val]?.getD 0 % {N}, Nat.mod_lt _ (by decide)⟩) ≠ 0
    decide +kernel

/-- The ordered star `(e₀+e₁, -e₀+e₂, -e₁-e₂)` in the normalized model. -/
noncomputable def {name}.hyp24 : Hyp24 (EuclideanSpace ℝ (Fin 8)) :=
  {name}.tableModel.hyp24 isIndecomposable_{name} isStarClosed_{name}
    ({a} : Fin {N}) ({b} : Fin {N}) (by decide +kernel)

/-- Identification of the first marked root in standard coordinates. -/
theorem {name}.hyp24_a : {name}.hyp24.a =
    EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 1 := by
  change integerVector (1 / 2) ({name}.tableModel.v ({a} : Fin {N})) = _
  have hv : {name}.tableModel.v ({a} : Fin {N}) = ![2, 2, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

/-- Identification of the second marked root in standard coordinates. -/
theorem {name}.hyp24_b : {name}.hyp24.b =
    -EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 2 1 := by
  change integerVector (1 / 2) ({name}.tableModel.v ({b} : Fin {N})) = _
  have hv : {name}.tableModel.v ({b} : Fin {N}) = ![-2, 0, 2, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

/-- Identification of the third marked root in standard coordinates. -/
theorem {name}.hyp24_c : {name}.hyp24.c =
    -EuclideanSpace.single 1 (1 : ℝ) - EuclideanSpace.single 2 1 := by
  rw [Hyp24.c, {name}.hyp24_a, {name}.hyp24_b]
  module

'''
    for label,size,pred,subset in [('gamma',k,'Γa','Γa_subset_Φ'), ('delta',delta,'Δ','Δ_subset_Φ')]:
        rhs='= 4' if label=='gamma' else '= 0'
        code+=f'''/-- Indices of the {pred} roots, in the Sage certificate order. -/
def {name}.{label}Label (i : Fin {size}) : Fin {N} :=
  ⟨{ns}{label.capitalize()}[i.val]?.getD 0 % {N}, Nat.mod_lt _ (by decide)⟩

/-- The labels enumerate exactly the actual set `{name}.hyp24.{pred}`. -/
noncomputable def {name}.{label}Equiv : Fin {size} ≃ {name}.hyp24.{pred} :=
  {name}.tableModel.subsetEquiv _ {name}.hyp24.{subset} {name}.{label}Label
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      unfold {name}.hyp24
      rw [{name}.tableModel.mem_{pred}_iff]
      exact (by decide +kernel : ∀ i : Fin {N},
        integerInner ({name}.tableModel.v i) ({name}.tableModel.v ({a} : Fin {N})) = 0 ∧
        integerInner ({name}.tableModel.v i) ({name}.tableModel.v ({b} : Fin {N})) {rhs} ↔
          ∃ j, {name}.{label}Label j = i) i)

'''
    code+=f'''/-- C4: the graph on Γa has the Sage adjacency table. -/
noncomputable def {name}.orthGraphIso :
    graphOfMatrix (by decide +kernel : checkAdjacency {k} {ns}Adjacency = true) ≃g
      {name}.hyp24.orthGraph :=
  graphOfMatrixIso _ _ {name}.gammaEquiv fun i j => by
    change (⟪integerVector {name}.tableModel.c
      ({name}.tableModel.v ({name}.gammaLabel i)),
      integerVector {name}.tableModel.c ({name}.tableModel.v ({name}.gammaLabel j))⟫ = 0) ↔ _
    rw [{name}.tableModel.inner_eq_zero_iff]
    exact (by decide +kernel : ∀ i j : Fin {k},
      integerInner ({name}.tableModel.v ({name}.gammaLabel i))
        ({name}.tableModel.v ({name}.gammaLabel j)) = 0 ↔ entry {ns}Adjacency i j = 1) i j

/-- C4: the orthogonality graph on the specified Γa is strongly regular. -/
theorem {name}.orthGraph_isSRGWith : {name}.hyp24.orthGraph.IsSRGWith {k} {degree} 1 {mu} :=
  {name}.orthGraphIso.isSRGWith (checkSRG_sound _ (by decide +kernel))

/-- C4: the number of vertices in the specified Γa. -/
theorem {name}.card_Γa : {name}.hyp24.Γa.ncard = {k} := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr {name}.gammaEquiv, Nat.card_eq_fintype_card]
  exact Fintype.card_fin {k}

/-- C4: Delta contains both signs; this is its number of lines. -/
theorem {name}.card_Δ_div_two : {name}.hyp24.Δ.ncard / 2 = {delta//2} := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr {name}.deltaEquiv, Nat.card_eq_fintype_card]
  rfl

end LineSystem
'''
    write_lean(OUT/(f'C4{key}.lean'),code,f'C4 {name} marked-star verification')
