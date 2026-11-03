# Checks for Theorem 3.12

The script `check_thm312.py` is that of `cgss/proofs/thm312/checks/`. It makes finite checks for
Theorem 3.12, whose structured proof is `blueprint/sec3-thm312.tex` and whose ordinary proof is
`cgss/proofs/thm312/thm312.tex`. It needs Python 3 with SymPy and NumPy, and it writes no files. Run it
from the repository root (it can be run from any directory):

```bash
python blueprint/checks/thm312/check_thm312.py
```

All acceptance decisions use integer, rational, or exact algebraic arithmetic.
NumPy eigenvalues supplement the exact checks for the two noncontaining
examples. The script prints the Python, SymPy and NumPy versions; we ran it with
Python 3.12.14, SymPy 1.14.0 and NumPy 2.5.2, and it takes about half a minute.

The checks cover:

- Every ordered root pair of B_n and C_n for ranks 2–8, and F_4: integrality,
  reflection closure, reducedness, root and line counts, allowed angles, and
  agreement of the computed partition with root lengths up to swapping parts.
- Reflection closure from simple-root seeds, after common normalization to
  squared lengths 2 and 4. The generated root set must equal the complete
  coordinate model. Every new root satisfies the norm and parity conditions
  defining `Psi`. These closure counts are distinct from counts of `Psi`.
- The explicit `Psi` construction on the empty set and independent seeds for
  A1 squared, A1 cubed, A2 + A1, B2, C3 and D4. Every axiom is checked, including
  spanning and reducedness. Enumeration exhausts the integer coefficient box
  justified by `a[i]^2 <= 4 * inverse(Gram)[i,i]`. `Psi` contains the reflection
  closure, but may be larger: their root counts are 8 versus 4 for A1 squared,
  18 versus 6 for A1 cubed, and 48 versus 24 for D4.
- Empty sets, singleton lines of either assigned length, orthogonal lines,
  nonclosed two-line and three-line sets, dependent A2 seeds, completion of a
  B2 plane inside R4, and differently scaled orthogonal B2 components. The
  ambient construction adjoins two orthogonal norm-2 seeds before applying
  `Psi`, as in the proof. Its result has 32 roots; reflection closure
  has 12. Both ranks are asserted to be 4.
- Two positive-definite Gram matrices whose lines cannot have the partition:
  three mutually 45-degree lines, and a triangle with angles 60, 60, 45 degrees.
- All 125 labelled signed unit Gram matrices on three lines with off-diagonal
  entries in {0, ±1/2, ±1/sqrt(2)}. Exact positive-semidefiniteness tests retain
  97 matrices. Graph propagation and all eight binary colourings agree. The
  script asserts and prints the cross-tabulation below. Each accepted case
  is completed and checked for both assignments of squared lengths to the
  parts. The 162 closures have sizes 6, 8, 10, 12, 18 with asserted
  multiplicities 10, 36, 12, 32, 72.
- Independently of the colourings, all 27 assignments of squared lengths in
  {1, 2, 4} for each of the 97 feasible three-line configurations, including
  all 16 configurations without a partition. Each assignment is checked for
  both ordered crystallographic coefficients on every seed pair. Integral
  assignments are closed under reflections and checked for every axiom and
  the correct rank, without assuming the normalized parity condition.
  Nonreduced closures are counted and rejected, even when the seed pairings
  are integral: of 2619 assignments, 2190 fail seed integrality, 24 give
  nonreduced closures, and 405 give Root Systems. For each configuration,
  an integral assignment exists iff
  a reduced Root System completion exists iff a partition exists. Every
  assignment for a configuration without a partition fails seed integrality.
- 3000 proper random subsets of 2 to 9 lines from each of
  F4 + sqrt(3)*B3 and C3 + G2 + (17/10)*B2, with fixed seed 20260928. All
  axioms of the containing systems are verified first. Positive rational
  weights in the inner product represent the component scales exactly;
  G2 uses the integer-coordinate model in the plane x+y+z=0. Subsets with
  30-degree pairs are counted and skipped (1014); all 4986 allowed subsets pass both
  graph propagation and the colouring by the parity of the exact integer
  logarithm of squared root length. Squared-length rescalings by 2^-4 and
  2^-3 also test negative logarithms and both parity shifts. Assertions ensure
  coverage of 45-degree pairs, multiple components and both G2 length classes.
- A norm-4 vector in an integral integer span whose reflection coefficient
  is -1/2, demonstrating the need for the stronger parity invariant.

The three-line census is:

| Gram matrix | With partition | Without partition | Total |
| --- | ---: | ---: | ---: |
| Positive definite | 65 | 16 | 81 |
| Singular | 16 | 0 | 16 |
| Total feasible | 81 | 16 | 97 |

The closure algorithm identifies coefficient vectors by their Gram images,
so dependent seeds are supported. It terminates only on reaching a fixed
point; exceeding the failure guard raises an assertion instead of accepting
a truncated set. The {1, 2, 4} search tests finite length assignments; it
does not itself prove noncontainment for all real scalings. These computations
are finite checks, not premises of the ordinary proof or Lean proofs.
