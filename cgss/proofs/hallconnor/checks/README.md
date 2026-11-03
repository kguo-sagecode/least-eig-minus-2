# Checks for `hallconnor.tex`

The two scripts in this folder check, in exact arithmetic, the explicit matrices and the
arithmetic of the ordinary proof `hallconnor.tex`. They need Python 3 with SymPy, and they write no
files. Run them from `cgss/proofs/hallconnor/`:

```bash
python checks/check_proof.py
python checks/check_t7.py
```

The first command runs both scripts, since `check_proof.py` calls `check_t7.py`; the second runs
the graph control on its own. Each script prints one line for each group of checks, and
`check_proof.py` also prints the versions of Python and SymPy. We ran them with Python 3.12.14 and
SymPy 1.14.0.

`check_proof.py` uses exact SymPy arithmetic. It reads the six certificate matrices from
`hallconnor.tex` itself (between the comments `% BEGIN MATRIX` and `% END MATRIX`), so that a copy
of a matrix cannot hide a typo in the document, and it reconstructs the seven-block patterns
independently. It checks the quadratic certificates, integer inverses, determinants, rank boundary,
counting constants, Connor identities and arithmetic obstruction, including the determinant at
order 15 used in the rank proof. There is no search over designs.

`check_t7.py` constructs `T(7)` from two-subsets, and checks both intersection tables, the matrix
identities and rank, absence of claws, and all 2,520 ordered five-block configurations. For every
one of the 210 ordered adjacent pairs, it checks the full local clique construction: sizes
`5,4,4,6`, eight edges, the eligible third vertex, the counts `(h,e,ell) = (j,4-j,j)`, the two
six-cliques, their intersection and union, and uniqueness. It independently enumerates all
six-cliques and checks the global graph incidence identities. Only `j=0` occurs; the excluded
`j=1,2` matrices have separate certificate checks in `check_proof.py`.

These controls do not establish the quantified structural proof or the design-to-matrix bridge. The
biplane controls have residual block sizes three and four, so they do not exercise the structural
argument at block size five. `T(7)` is a consistent graph model but supplies no integral incidence
matrix for the excluded design. The formula diagnostics in `check_counts_and_algebra` re-evaluate
the displayed formulas rather than independently deriving them.
