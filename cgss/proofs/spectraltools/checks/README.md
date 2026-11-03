# Checks for the spectral toolkit

The script `check_spectraltools.py` accompanies the ordinary and structured spectral toolkit,
`spectraltools.tex` and `spectraltools-lamport.tex`. It makes exact small certificate checks and
independent numerical sanity checks; these are not Lean proofs. It needs Python 3 with NumPy and
SymPy. Run it from the repository root:

```bash
OPENBLAS_NUM_THREADS=1 python cgss/proofs/spectraltools/checks/check_spectraltools.py
```

It takes about a second, and it writes its results to `results.json` in this folder.

`check_spectraltools.py` uses Python integers for the C13 and C15 annihilating
products and moments and the C17 positive-vector identities. NumPy independently
compares eigenvalues; SymPy checks small ranks, determinants and eigenspaces.
It also checks malformed and rejected certificates, empty matrices and empty
node lists, signless Laplacians, interlacing, strongly regular graphs,
rectangular zero multiplicities, design Gram matrices, complete bipartite line
graphs, scaled similarity, and the Section 6 row-sum counterexample.

Further regression checks cover the nonsymmetric similarity example, the missing
principal-minor hypothesis, both signs of the Gram rank bound, local triangle
counts, arbitrary rank-one vectors, sorted repeated eigenvalues and both Rayleigh
gaps. The exact `K_{6,10}` / `T(6)` example verifies the endpoint and multiplicity
correction of Error 14 of `cgss/errata.md`.
