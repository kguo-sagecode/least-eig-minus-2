#!/usr/bin/env python3
"""Materialize C20 neighborhood and pairing certificates from the Sage JSON."""
import json
from pathlib import Path
from lean_output import write_lean

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'LineGraphs' / 'Computations'
systems = json.loads((ROOT / 'cgss/certificates/data/c20.json').read_text())['systems']

data = '''import LineGraphs.Computations.E8Data
import LineGraphs.Computations.NeighborData

/-! The C20 root tables and the Sage apex-pair labels. -/

namespace Computations.C20

'''
for key in ['A9','D9']:
    roots = systems[key]['roots']
    chunks = (len(roots)+19)//20
    for c in range(chunks):
        literal = '[\n'+',\n'.join('  '+str(r) for r in roots[20*c:20*c+20])+']'
        data+=f'/-- A block of integer roots from the Sage certificate. -/\ndef {key.lower()}Roots{c} : List IntVector := {literal}\n\n'
    data+=f'/-- The root table in Sage and Lean structured-index order. -/\ndef {key.lower()}Roots : List IntVector :=\n  '+ ' ++\n    '.join(f'{key.lower()}Roots{c}' for c in range(chunks))+'\n\n'
data+='''/-- The default E₈ table. -/
def e8Roots : List IntVector := E₈Data.e₈Roots

/-- The coordinate restriction defining E₇. -/
def e7Roots : List IntVector := e8Roots.filter (fun w => decide (w[6]?.getD 0 = w[7]?.getD 0))

/-- The coordinate restriction defining E₆. -/
def e6Roots : List IntVector := e8Roots.filter
  (fun w => decide (w[6]?.getD 0 = w[7]?.getD 0 ∧ w[5]?.getD 0 = w[6]?.getD 0))

'''
for key in ['E6','E7','E8']:
    roots = systems[key]['roots']
    order={tuple(v):i for i,v in enumerate(sorted(roots))}
    pairs=[[order[tuple(roots[i])] for i in pair] for pair in systems[key]['apex_pairs']]
    literal='[\n'+',\n'.join('  '+str(row) for row in pairs)+']'
    data+=f'/-- Pairs from the Sage certificate, reindexed by sorted roots. -/\ndef {key.lower()}Pairs : List (List ℕ) := {literal}\n\n'
for key in systems:
    count = systems[key]['counts'][0]
    ns=key.lower(); q=systems[key]['q']; N=len(systems[key]['roots']); chunks=(N+19)//20
    data+=f'/-- Twenty neighborhood counts at a time. -/\ndef {ns}Chunk (k : ℕ) : Bool :=\n  ({ns}Roots.drop (20 * k) |>.take 20).all (checkNeighborCount {q} {count} {ns}Roots)\n\n'
    for c in range(chunks):
        code=f'''import LineGraphs.Computations.C20Data

/-! A block of the exhaustive C20 neighborhood count. -/

namespace Computations.C20

theorem {ns}_chunk_{c} : {ns}Chunk {c} = true := by decide +kernel

end Computations.C20
'''
        write_lean(OUT/f'C20{key}Rows{c:02}.lean',code,'C20 neighborhood sweep')
data+='end Computations.C20\n'
write_lean(OUT/'C20Data.lean',data,'C20 integer data')

for key in systems:
    ns=key.lower(); packet=systems[key]; count=packet['counts'][0]; q=packet['q']
    N=len(packet['roots']); chunks=(N+19)//20
    model={'A9':'(An 9)','D9':'(Dn 9)','E6':'E₆','E7':'E₇','E8':'E₈'}[key]
    model_ns={'A9':'An','D9':'Dn','E6':'E₆','E7':'E₇','E8':'E₈viaD₈'}[key]
    arg=' 9' if key in ['A9','D9'] else ''
    model_instance=model_ns+'.integerModel'+arg
    mem=model_ns+'.mem_rootList'+arg
    imports=''.join(f'import LineGraphs.Computations.C20{key}Rows{c:02}\n' for c in range(chunks))
    imports+='import LineGraphs.Computations.NeighborCertificates\n'
    if key[0]=='E':imports+=f'import LineGraphs.Computations.C4{key}\n'
    lemmas=',\n    '.join(f'{ns}_chunk_{c}' for c in range(chunks))
    code=imports+f'''
/-! C20 for {key}, transferred to neighborhoods of real roots. -/

open Computations
open scoped RealInnerProductSpace

namespace Computations.C20

theorem {ns}_counts_checked : {ns}Roots.all (checkNeighborCount {q} {count} {ns}Roots) = true := by
  apply all_eq_true_of_chunks (chunk := fun k => {ns}Roots.drop (20 * k) |>.take 20)
    (m := {chunks}) (by decide +kernel)
  apply List.all_eq_true.mp
  change (List.range {chunks}).all {ns}Chunk = true
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    {lemmas}, Bool.and_self]

'''
    if key[0]!='E':
        code+=f'''/-- The finite integer model in the certificate's order. -/
@[reducible] noncomputable def {ns}Model : LineSystem.IntegerModel (LineSystem.{key[0]}n 9) :=
  (LineSystem.{model_instance}).ofTable {ns}Roots {N} (by decide +kernel)
    (by decide +kernel) (by
      have he : {ns}Roots = LineSystem.{model_ns}.rootList 9 := by decide +kernel
      intro w
      rw [he]
      exact LineSystem.{mem} w)

'''
        M=f'C20.{ns}Model'
    else:M=model+'.tableModel'
    theorem=model_ns+'.card_N' if key[0]=='E' else model_ns+'.card_N_nine'
    if key=='E8':theorem='E₈.card_N'
    code+=f'''end Computations.C20

namespace LineSystem

/-- C20: every root of {key} has {count} roots at inner product one. -/
theorem {theorem} {{r}} (hr : r ∈ {model}.Φ) : ({model}.N r).ncard = {count} := by
  apply {M}.card_N_of_check (Equiv.refl (Fin {N})) C20.{ns}Roots
    (by decide +kernel) C20.{ns}_counts_checked hr

'''
    if key[0]=='E':
        name=model
        order={tuple(v):i for i,v in enumerate(sorted(packet['roots']))}
        apex=order[tuple(packet['roots'][packet['apex_index']])]
        pairs=count//2
        code+=f'''/-- The apex used in the Sage C20 pairs. -/
noncomputable def {name}.neighborApex : EuclideanSpace ℝ (Fin 8) :=
  integerVector {name}.tableModel.c ({name}.tableModel.v ({apex} : Fin {N}))

/-- The two roots of each pair, as integer root indices. -/
def {name}.neighborPairLabel (p : Fin {pairs} × Bool) : Fin {N} :=
  ⟨(C20.{ns}Pairs[p.1.val]?.getD [])[if p.2 then 1 else 0]?.getD 0 % {N},
    Nat.mod_lt _ (by decide)⟩

/-- The pairs enumerate exactly N at the certified apex. -/
noncomputable def {name}.neighborPairs : (Fin {pairs} × Bool) ≃ {name}.N {name}.neighborApex :=
  {name}.tableModel.subsetEquiv _ (fun _ h => h.1) {name}.neighborPairLabel
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      change (_ ∧ _) ↔ _
      rw [and_iff_right ({name}.tableModel.root_mem i)]
      change (⟪integerVector {name}.tableModel.c ({name}.tableModel.v i),
        integerVector {name}.tableModel.c ({name}.tableModel.v ({apex} : Fin {N}))⟫ = 1) ↔ _
      rw [{name}.tableModel.inner_eq_one_iff]
      exact (by decide +kernel : ∀ i : Fin {N},
        integerInner ({name}.tableModel.v i) ({name}.tableModel.v ({apex} : Fin {N})) = 4 ↔
          ∃ p, {name}.neighborPairLabel p = i) i)

/-- The two roots of each enumerated pair sum to the apex. -/
theorem {name}.neighborPairs_add (i : Fin {pairs}) :
    ({name}.neighborPairs (i, false) : EuclideanSpace ℝ (Fin 8)) +
      {name}.neighborPairs (i, true) = {name}.neighborApex := by
  change integerVector {name}.tableModel.c
    ({name}.tableModel.v ({name}.neighborPairLabel (i, false))) +
    integerVector {name}.tableModel.c
      ({name}.tableModel.v ({name}.neighborPairLabel (i, true))) = _
  rw [← integerVector_add]
  apply congrArg (integerVector {name}.tableModel.c)
  exact (by decide +kernel : ∀ j : Fin {pairs},
    {name}.tableModel.v ({name}.neighborPairLabel (j, false)) +
      {name}.tableModel.v ({name}.neighborPairLabel (j, true)) =
        {name}.tableModel.v ({apex} : Fin {N})) i

'''
    code+='end LineSystem\n'
    write_lean(OUT/f'C20{key}.lean',code,f'C20 {key} neighborhoods')
write_lean(OUT/'C20.lean', 'import LineGraphs.Computations.C20Classical\n'+''.join(f'import LineGraphs.Computations.C20{k}\n' for k in systems)+
    '\n/-! C20 neighborhood counts and the exceptional apex pairs. -/\n','Root neighborhoods')
