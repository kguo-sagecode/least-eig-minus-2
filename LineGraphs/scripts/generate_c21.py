#!/usr/bin/env python3
"""Convert Sage's simple roots, integral coordinates and LDL witnesses for C21."""
import json
from fractions import Fraction
from pathlib import Path
from lean_output import write_lean

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'LineGraphs/Computations'
CERT = ROOT / 'cgss/certificates/data'
systems=json.loads((CERT/'c21.json').read_text())['systems']
models=json.loads((CERT/'c02_models.json').read_text())['models']


def frac(x):
    return Fraction(x['num'],x['den']) if isinstance(x,dict) else Fraction(x)


def matrix(x):
    return '[\n'+',\n'.join('  '+str(row) for row in x)+']'



def cartan_E(n):
    """Mathlib's `CartanMatrix.E n` (Bourbaki's numbering)."""
    adj=lambda i,j: (i,j) in [(0,2),(2,0),(1,3),(3,1)] or (2<=i and i+1==j) or (2<=j and j+1==i)
    return [[2 if i==j else (-1 if adj(i,j) else 0) for j in range(n)] for i in range(n)]


def relabel(gram,n):
    """A permutation s with gram[i][j] == E(n)[s[i]][s[j]]."""
    C=cartan_E(n)
    def bt(p):
        if len(p)==n: return p
        k=len(p)
        for c in range(n):
            if c not in p and C[c][c]==gram[k][k] and all(gram[k][t]==C[c][p[t]] for t in range(k)):
                r=bt(p+[c])
                if r: return r
    s=bt([])
    assert s is not None
    return s


CARTAN = """
namespace Computations.C21

/-- The relabelling of the simple roots of `NAME` onto Mathlib's order of `CartanMatrix.E K`
(Bourbaki's numbering): `NSGram i j = CartanMatrix.E K (NSRelabel i) (NSRelabel j)`. -/
def NSRelabel : Fin K ≃ Fin K :=
  ⟨![SIGMA], ![INV], by decide, by decide⟩

/-- C21: the certified Gram matrix is Mathlib's Cartan matrix `CartanMatrix.E K`, up to the
relabelling `NSRelabel`. -/
theorem NS_gram_eq_cartan :
    toMatrix (R := ℤ) K NSGram = (CartanMatrix.E K).submatrix NSRelabel NSRelabel := by
  ext i j
  change entry NSGram i j = CartanMatrix.E K (NSRelabel i) (NSRelabel j)
  exact (by decide +kernel : ∀ i j : Fin K,
    entry NSGram i j = CartanMatrix.E K (NSRelabel i) (NSRelabel j)) i j

end Computations.C21

/-- C21: the Gram matrix of the simple roots is `CartanMatrix.E K` up to a relabelling. -/
theorem LineSystem.NAME.gram_simpleRoot_eq_cartan : Matrix.gram ℝ LineSystem.NAME.simpleRoot =
    ((CartanMatrix.E K).submatrix C21.NSRelabel C21.NSRelabel).map (Int.cast : ℤ → ℝ) := by
  rw [LineSystem.NAME.gram_simpleRoot, ← C21.NS_gram_eq_cartan]
  rfl
"""


def cartan_block(name,ns,k,sig):
    inv=[sig.index(i) for i in range(k)]
    return (CARTAN.replace('NAME',name).replace('NS',ns).replace('SIGMA',', '.join(map(str,sig)))
            .replace('INV',', '.join(map(str,inv))).replace('K',str(k)))

for key,name,k,N in [('E6','E₆',6,72),('E7','E₇',7,126),('E8','E₈',8,240)]:
    ns=key.lower(); cert=systems[key]; det=cert['determinant']
    roots=models['E8_D' if key=='E8' else key]['roots']
    coeff=[c for _,c in sorted(zip(roots,cert['root_coefficients']))]
    simple=cert['simple_roots']
    for root,c in sorted(zip(roots,cert['root_coefficients'])):
        assert [sum(c[i]*simple[i][j] for i in range(k)) for j in range(8)]==root
        assert all(x>=0 for x in c) or all(x<=0 for x in c)
    lower=[[int(2*frac(x)) for x in row] for row in cert['LDL']['lower']]
    diagonal=[int(4*frac(x)) for x in cert['LDL']['diagonal']]
    data='''import LineGraphs.Computations.ListData

/-! Simple roots, coordinates and scaled LDL data from the Sage C21 certificate. -/

namespace Computations.C21

'''
    for label,mat in [('Simple',simple),('Gram',cert['gram']),('Lower',lower)]:
        data+=f'/-- The Sage {label.lower()} matrix in integer coordinates. -/\ndef {ns}{label} : IntMatrix := {matrix(mat)}\n\n'
    data+=f'/-- Four times the diagonal in the rational LDL factorization. -/\ndef {ns}Diagonal : IntVector := {diagonal}\n\n'
    chunks=(N+19)//20
    for c in range(chunks):
        data+=f'/-- Integral coordinates of twenty roots. -/\ndef {ns}Coefficients{c} : IntMatrix := {matrix(coeff[20*c:20*c+20])}\n\n'
    data+=f'/-- Coordinates in the sorted root-table order. -/\ndef {ns}Coefficients : IntMatrix :=\n  '+' ++\n    '.join(f'{ns}Coefficients{c}' for c in range(chunks))+'\n\nend Computations.C21\n'
    write_lean(OUT/f'C21{key}Data.lean',data,f'C21 {name} integer data')
    code=f'''import LineGraphs.Computations.C21{key}Data
import LineGraphs.Computations.C20Data
import LineGraphs.Computations.C4{key}
import LineGraphs.Computations.SimpleRootCertificates
import Mathlib.LinearAlgebra.Matrix.Cartan

/-! C21: the simple-root basis of {name} and its Gram determinant. -/

open Computations
open scoped RealInnerProductSpace

namespace Computations.C21

theorem {ns}_ldl_checked : checkScaledLDL {k} 16 {ns}Gram {ns}Lower {ns}Diagonal = true := by
  decide +kernel

theorem {ns}_gram_det : (toMatrix (R := ℤ) {k} {ns}Gram).det = {det} := by
  have hl : (toMatrix (R := ℤ) {k} {ns}Lower).IsLowerTriangular := by
    intro i j hij
    exact (by decide +kernel : ∀ i j : Fin {k}, i < j → entry {ns}Lower i j = 0) i j hij
  have hd : (toMatrix (R := ℤ) {k} {ns}Lower).det = 2 ^ {k} := by
    rw [Matrix.det_of_isLowerTriangular _ hl]
    decide +kernel
  have he := congrArg Matrix.det (checkScaledLDL_sound {ns}_ldl_checked)
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, hd] at he
  have hp : (∏ i : Fin {k}, {ns}Diagonal[i.val]?.getD 0) = {4**k*det} := by decide +kernel
  rw [hp] at he
  norm_num at he
  omega

theorem {ns}_coordinates_checked :
    checkRootCoordinates {N} 8 {k} C20.{ns}Roots {ns}Simple {ns}Coefficients = true := by
  decide +kernel

end Computations.C21

namespace LineSystem

/-- The simple roots specified by the Sage C21 certificate, with squared norm two. -/
noncomputable def {name}.simpleRoot (i : Fin {k}) : EuclideanSpace ℝ (Fin 8) :=
  integerVector (1 / 2) (fun j => entry C21.{ns}Simple i j)

theorem {name}.simpleRoot_mem (i : Fin {k}) : {name}.simpleRoot i ∈ {name}.Φ := by
  apply (integerVector_mem_{name}_iff _).mpr
  exact (by decide +kernel : ∀ i : Fin {k},
    is{name}Root (fun j => entry C21.{ns}Simple i j) = true) i

/-- The Gram matrix of the actual normalized roots is the certified Cartan matrix. -/
theorem {name}.gram_simpleRoot : Matrix.gram ℝ {name}.simpleRoot =
    toMatrix (R := ℝ) {k} C21.{ns}Gram := by
  ext i j
  change ⟪integerVector (1 / 2) (fun t => entry C21.{ns}Simple i t),
    integerVector (1 / 2) (fun t => entry C21.{ns}Simple j t)⟫ = _
  rw [inner_integerVector]
  have he := (by decide +kernel : ∀ i j : Fin {k},
    integerInner (fun t : Fin 8 => entry C21.{ns}Simple i t)
      (fun t => entry C21.{ns}Simple j t) = 4 * entry C21.{ns}Gram i j) i j
  rw [he]
  norm_num [toMatrix]
  ring

/-- C21: the Gram determinant of the simple roots. -/
theorem {name}.det_gram_simpleRoot : (Matrix.gram ℝ {name}.simpleRoot).det = {det} := by
  rw [{name}.gram_simpleRoot, det_toMatrix_real, C21.{ns}_gram_det]
  norm_num

/-- The simple roots, considered in the real root span. -/
noncomputable def {name}.simpleRootInSpan (i : Fin {k}) : Submodule.span ℝ {name}.Φ :=
  ⟨{name}.simpleRoot i, Submodule.subset_span ({name}.simpleRoot_mem i)⟩

/-- C21: the certified simple roots form a basis of the root span. -/
noncomputable def {name}.simpleBasis : Module.Basis (Fin {k}) ℝ (Submodule.span ℝ {name}.Φ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (Matrix.linearIndependent_of_det_gram_ne_zero (v := {name}.simpleRootInSpan) (by
      change (Matrix.gram ℝ {name}.simpleRoot).det ≠ 0
      rw [{name}.det_gram_simpleRoot]
      norm_num)) (by rw [finrank_span_{name}]; exact Fintype.card_fin {k})

@[simp] theorem {name}.simpleBasis_apply (i : Fin {k}) :
    ({name}.simpleBasis i : EuclideanSpace ℝ (Fin 8)) = {name}.simpleRoot i := by
  simp [simpleBasis, coe_basisOfLinearIndependentOfCardEqFinrank, simpleRootInSpan]

/-- C21: every root has integral simple-root coordinates, all of one sign. -/
theorem {name}.exists_simpleRoot_coordinates {{r}} (hr : r ∈ {name}.Φ) :
    ∃ z : Fin {k} → ℤ, ((∀ i, 0 ≤ z i) ∨ (∀ i, z i ≤ 0)) ∧
      r = ∑ i, (z i : ℝ) • {name}.simpleRoot i := by
  rw [{name}.tableModel.Φ_eq] at hr
  obtain ⟨a, rfl⟩ := hr
  change Fin {N} at a
  have hc := checkRootCoordinates_sound C21.{ns}_coordinates_checked a
  refine ⟨fun i => entry C21.{ns}Coefficients a i, hc.1, ?_⟩
  have he : {name}.tableModel.v a = fun j : Fin 8 =>
      ∑ i : Fin {k}, entry C21.{ns}Coefficients a i * entry C21.{ns}Simple i j := by
    funext j
    exact hc.2 j
  change integerVector (1 / 2) ({name}.tableModel.v a) = _
  rw [he, integerVector_sum]
  rfl

end LineSystem
'''
    code+=cartan_block(name,ns,k,relabel(cert['gram'],k))
    write_lean(OUT/f'C21{key}.lean',code,f'C21 {name} simple-root basis')
write_lean(OUT/'C21.lean',''.join(f'import LineGraphs.Computations.C21{k}\n' for k in systems)+
    '\n/-! C21: simple-root bases with Gram determinants 3, 2, and 1. -/\n','Simple-root bases')
