# The exceptional graphs

This directory holds all **exceptional graphs**, up to isomorphism, split by least eigenvalue and
number of vertices: 54,732,619 graphs, 54,732,046 with least eigenvalue −2 and 573 with least
eigenvalue greater than −2. It is the database of the note [Exc], *A database of exceptional
graphs with least eigenvalue ≥ −2* (`exceptional/note/exceptional.tex`). The note proves that the
lists are complete and irredundant (Theorems 1.1 and C.1), explains the program and why its tests
are exact (Appendix A), describes the checks of the program and of its output and what each of
them could detect (Appendix B), and describes the files (Appendix C). This file repeats the
definitions, describes the files and how to read them, and gives the commands that regenerate and
verify them.

## Definitions

All graphs are finite and simple. For a graph X, A is its adjacency matrix and M = 2I + A.

* A graph is a **generalized line graph** if it is isomorphic to some L(Y; a_1, ..., a_m) (Hoffman;
  [CGSS] §4; [CRS04] §1.1). These include the line graphs and the cocktail party graphs CP(m).
* A graph X is **exceptional** if it is connected, its least eigenvalue is at least −2, and it is
  not a generalized line graph ([CRS04] §1.1).
* List (A), `minus2/`: the exceptional graphs with least eigenvalue exactly −2 (M singular).
* List (B), `above-minus2/`: the exceptional graphs with least eigenvalue greater than −2
  (M positive definite). These are the classical 573 graphs, on 6, 7 and 8 vertices.
* `maximal/`: the maximal exceptional graphs (no exceptional graph contains them as a proper induced
  subgraph); these are a subset of list (A), recorded as a check against [CLRS02].

## Files

* `minus2/nNN.g6`, `above-minus2/nNN.g6`, `maximal/nNN.g6`: one graph6 string per line, the graphs
  on NN vertices, where NN is n written with two digits. A file is gzipped (`nNN.g6.gz`) when it
  would exceed 20 MB; the three directories take about 770 MB in all. SageMath reads a graph6
  string `s` with `Graph(s)`. The tools of nauty read the files directly, but not the gzipped
  ones, so decompress those first, as in `zcat minus2/n22.g6.gz | countg`. An absent file means
  that there are no such graphs on NN vertices. The present `extract.py` writes the gzip header
  with time stamp 0, so that a rerun gives identical bytes; the stored files `nNN.g6.gz` were
  written by an earlier version, and differ from those of a rerun only in the four bytes of that
  time stamp.
* So that every file stays under 100 MB, each of the lists (A) on 19, 20 and 21 vertices is split
  in two by number of edges (`scripts/split_by_edges.py`), at the lower median m₀ of the numbers of
  edges, that is, the least integer m₀ such that at least half of the graphs have at most m₀ edges.
  One part holds the graphs with at most m₀ edges and the other those with at least m₀ + 1 edges,
  each in C byte order, and the file names give the bounds. The script writes the parts with a
  fixed gzip header (so reruns give identical bytes), and checks that they merge back to the whole
  list line for line. The function `read_list` in `scripts/e8common.py` merges the parts;
  `verify.py`, `count_regular.py` and `check_named.sage` read the lists through it.

  | n | m₀ | part | graphs | bytes |
  |---:|---:|---|---:|---:|
  | 19 | 92 | `minus2/n19.edges_le_92.g6.gz` | 4,348,448 | 62,378,409 |
  | 19 | 92 | `minus2/n19.edges_ge_93.g6.gz` | 3,939,179 | 52,628,533 |
  | 20 | 103 | `minus2/n20.edges_le_103.g6.gz` | 4,047,472 | 64,995,112 |
  | 20 | 103 | `minus2/n20.edges_ge_104.g6.gz` | 3,676,989 | 55,549,942 |
  | 21 | 115 | `minus2/n21.edges_le_115.g6.gz` | 3,392,738 | 60,812,343 |
  | 21 | 115 | `minus2/n21.edges_ge_116.g6.gz` | 2,834,489 | 48,045,339 |

  The graphs have 65 to 131 edges for n = 19, 74 to 141 for n = 20 and 82 to 154 for n = 21.
* `counts.json`: under `per_n`, for each n, the numbers of graphs in the three lists (`minus2`,
  `above_minus2`, `maximal`), the size of the level S_n (`connected_E8_represented`: all connected
  graphs on n vertices represented in E8, that is, with M positive semidefinite of rank at most
  8), the lattice types of the graphs in S_n (`lattice_types`; `AD` for rank at most 5, where the
  lattice determinant is not computed), the names of the files (`files`), the time in seconds of
  the growth step from n to n + 1 vertices (`growth_step_seconds`), and that n is complete
  (`status`); `complete_for_n` lists the complete values of n, which are all n from 1 to 36, and
  `totals_over_complete_n` gives the totals. Table 1 of [Exc] is made from it, by
  `scripts/make_table.py`.
* `SHA256SUMS`: the SHA-256 checksum of every file of the three lists (`minus2/`, `above-minus2/`,
  `maximal/`), made with `sha256sum`. To check that the files are intact, run
  `sha256sum -c SHA256SUMS` in this directory. A rerun of the program (see Regenerating) gives the
  same bytes for the plain files and for the six parts above, but not for the stored files
  `nNN.g6.gz`, whose gzip headers carry a time stamp (see above); compare those decompressed.
* `scripts/`: the programs (see Scripts).

Every string is the graph6 string of the **canonical form given by `labelg` of nauty 2.9.3**
(default mode: dense nauty, no `-S`, no `-t`), and every file is sorted in byte order
(`LC_ALL=C sort`), without repetitions. The canonical form depends on the program and its version:
to look up a graph, canonically label it with the same `labelg` (or relabel the files with another
canonical labelling before comparing strings).

## Counts

| n | S_n (connected, represented in E8) | (A) λ_min = −2 | (B) λ_min > −2 | maximal | status |
|---:|---:|---:|---:|---:|---|
| 1 | 1 | 0 | 0 | 0 | complete |
| 2 | 1 | 0 | 0 | 0 | complete |
| 3 | 2 | 0 | 0 | 0 | complete |
| 4 | 6 | 0 | 0 | 0 | complete |
| 5 | 18 | 0 | 0 | 0 | complete |
| 6 | 67 | 0 | 20 | 0 | complete |
| 7 | 291 | 51 | 110 | 0 | complete |
| 8 | 1410 | 585 | 443 | 0 | complete |
| 9 | 6428 | 5594 | 0 | 0 | complete |
| 10 | 25584 | 24097 | 0 | 0 | complete |
| 11 | 87484 | 85341 | 0 | 0 | complete |
| 12 | 257048 | 254444 | 0 | 0 | complete |
| 13 | 649914 | 647196 | 0 | 0 | complete |
| 14 | 1418205 | 1415651 | 0 | 0 | complete |
| 15 | 2677814 | 2675647 | 0 | 0 | complete |
| 16 | 4385365 | 4383688 | 0 | 0 | complete |
| 17 | 6238430 | 6237257 | 0 | 0 | complete |
| 18 | 7714028 | 7713273 | 0 | 0 | complete |
| 19 | 8288067 | 8287627 | 0 | 0 | complete |
| 20 | 7724697 | 7724461 | 0 | 0 | complete |
| 21 | 6227347 | 6227227 | 0 | 0 | complete |
| 22 | 4324420 | 4324362 | 0 | 1 | complete |
| 23 | 2572833 | 2572808 | 0 | 0 | complete |
| 24 | 1303562 | 1303551 | 0 | 0 | complete |
| 25 | 559586 | 559581 | 0 | 0 | complete |
| 26 | 203365 | 203363 | 0 | 0 | complete |
| 27 | 63212 | 63211 | 0 | 0 | complete |
| 28 | 17245 | 17244 | 0 | 1 | complete |
| 29 | 4367 | 4367 | 0 | 432 | complete |
| 30 | 1041 | 1041 | 0 | 25 | complete |
| 31 | 272 | 272 | 0 | 7 | complete |
| 32 | 75 | 75 | 0 | 3 | complete |
| 33 | 22 | 22 | 0 | 1 | complete |
| 34 | 7 | 7 | 0 | 2 | complete |
| 35 | 2 | 2 | 0 | 0 | complete |
| 36 | 1 | 1 | 0 | 1 | complete |
| total | 54752217 | 54732046 | 573 | 473 | |

The totals are 54,732,046 graphs in list (A), 573 in list (B) and 473 maximal graphs. There are no
connected graphs represented in E8 on 37 or more vertices ([CGSS] Theorem 4.3).

## The method

The note gives the proofs (Sections 2 and 3 of [Exc]) and the program (Appendix A).

1. A connected graph with least eigenvalue at least −2 has a representation by norm-2 vectors with
   Gram matrix M; the norm-2 vectors of its Z-span form an indecomposable root system of rank
   r = rk M, of type A_r, D_r, E6, E7 or E8, and the Z-span is its root lattice ([Exc] Lemmas 2.1
   and 2.2, from [CGSS] Theorem 3.5). The graph is a generalized line graph if and only if the type
   is A or D ([CGSS] Theorem 4.2, and the fact that the E6 root lattice does not embed in any Z^m,
   [Exc] Lemma 2.5), so it is exceptional if and only if (r, det of the lattice) is (6,3), (7,2) or
   (8,1). It is represented in E8 if and only if r ≤ 8 ([Exc] Proposition 2.6).
2. S_1 = {K_1}; S_{n+1} is obtained from S_n by adding one vertex in all possible ways that keep M
   positive semidefinite of rank at most 8 (every connected graph has a vertex whose deletion
   leaves it connected, so this finds everything; [Exc] Lemma 3.1 and Theorem 3.6). With a
   certificate basis B of r ≤ 8 vertices, the new vertex is determined by its adjacencies to B, so
   there are at most 2^8 − 1 candidates per graph; the tests are exact integer identities ([Exc]
   Definition 3.2 and Lemmas 3.4 and 3.5). Duplicates are removed by canonical form: each worker
   pipes its candidates through `labelg -q | sort -u`, run under `bash -o pipefail`, so that a
   failure of `labelg` (even after its input is closed) makes the step fail instead of passing for
   a complete but truncated set of children. Without pipefail the exit status is that of `sort`
   alone, and a `labelg` error gives exit status 0. The first run of the growth, which produced the
   stored files, used the pipeline without pipefail; a second run, with it, gave the same levels,
   so no graph was left out of a level ([Exc] Appendix B).
3. Each graph of S_n is classified by rank and lattice determinant (exact), and written to list
   (A) (r < n) or list (B) (r = n) when exceptional. An exceptional graph with no extension is
   maximal ([Exc] Proposition 3.7).

No floating-point number decides anything: floating point only proposes a basis and the adjugate
of its Gram matrix, which are then checked exactly. The proposed adjugate T is accepted only if its
entries are finite and at most 2^(r−1) in absolute value, the bound that the adjugate satisfies by
Hadamard's inequality, and G·T = D·I holds in 64-bit integers, which cannot overflow under the
bound; otherwise the adjugate is computed exactly over the rationals (`adjugate_exact` in
`e8common.py`). The first three runs of the growth checked the identity without the bound, so
that, in principle, an overflow could have let a wrong proposal pass; the fourth run, with the
bound, reproduced the stored files ([Exc] Appendices A and B).

## Regenerating

The scripts take their environment from the caller: nauty (`geng`, `labelg`) and Python 3 with
NumPy and SciPy must be on the PATH, together with GNU `sort` and Bash; the checks also need
cypari2 (`verify.py`) and SageMath (`check_named.sage`). We used Python 3.12.14, NumPy 2.5.2,
SciPy 1.18.0, nauty 2.9.3, GNU Coreutils 8.32, GNU Bash 5.1.8 and gzip 1.12, and, for the checks,
cypari2 2.2.4 with PARI 2.17.3 and SageMath 10.9 ([Exc] Appendix A); any environment with these
programs will do. Run in this directory (the number 13 is the number of worker processes, which
share the graphs of a level):

```bash
scripts/run_levels.sh WORKDIR DBDIR 1 37 13
for n in 19 20 21; do
  python scripts/split_by_edges.py DBDIR/minus2/n$n.g6.gz DBDIR/minus2
done
rm -f DBDIR/minus2/n19.g6.gz DBDIR/minus2/n20.g6.gz DBDIR/minus2/n21.g6.gz
```

Here WORKDIR is a scratch directory, DBDIR is the directory in which the script writes the lists
and `counts.json`, and `1 37` asks for the growth steps from n to n + 1 vertices for 1 ≤ n < 37.
With `.` as DBDIR the script overwrites the stored files; to compare a rerun with them, give an
empty directory instead. WORKDIR receives the levels S_n (`levels/nNN.g6`, all connected graphs
represented in E8; 54,752,217 graphs in all, 1.7 GB) and their classification (`levels/infoNN.txt`:
g6, rank, lattice determinant, number of extensions, that is, of the nonzero admissible vectors of
[Exc] Lemma 3.5; 2.1 GB). After each n, the script writes that
n's files to DBDIR and marks it complete in `counts.json`. With the present scripts a full run
takes about 45 minutes on 13 cores; in the run of 9 October 2026, whose memory we measured, the
processes used at most 3.2 GiB together. Then `split_by_edges.py` splits the three lists (A) on
19, 20 and 21 vertices (`minus2/n19.g6.gz`, `n20.g6.gz`, `n21.g6.gz`) into their two parts (see
Files), and the three whole files are deleted.

Three variables may be set, and none is needed: PYTHON, the Python that `run_levels.sh` calls
(default `python3`); LABELG, the `labelg` that `grow.py` calls; and SORTMEM, the memory for all the
sorts of a growth step together (default 6G), which the workers share equally (each worker's sort
runs single-threaded, and beyond its share it uses temporary files in WORKDIR, with the same
output). For each step, `WORKDIR/levels/log.txt` records the numbers of graphs in and out, the time
in seconds, and the memory: the largest memory used during the step, sampled every second from the
memory cgroup of the run (the nearest one with a memory limit, such as that of a batch job;
`step_mem_MiB`), the high-water mark of that cgroup so far (`job_peak_MiB`), and the largest
resident set of a single process (`maxrss_proc_kB`, from GNU time; it is not a total). A column is
`NA` when there is no such cgroup, or no GNU time.

## Verifying

With the same PATH as above (cypari2 for `verify.py`, SageMath for `check_named.sage`), in this
directory:

```bash
python scripts/verify.py . 13 [n ...]                          # default: every n in counts.json
python scripts/check_bruteforce.py n WORKDIR/levels/nNN.g6 13  # for small n
sage scripts/check_named.sage . [WORKDIR/levels]
python scripts/count_regular.py . 13 OUTFILE
```

Appendix B of [Exc] gives the full account of these checks, of what each of them could detect and
of their outcomes. In short, `verify.py` checks that every listed graph is exceptional, in the
right list and listed once, but it cannot detect a missing graph; the brute-force comparison, the
runs of the growth and the comparisons with the literature bear on completeness, and the check of
named graphs bears on both, for the graphs it names.

* `verify.py` (needs cypari2) rereads every file of lists (A) and (B) and checks, for every graph:
  the number of lines is the count in `counts.json`; sorted, unique, canonical (labelg); connected;
  an exact certificate that M is positive semidefinite of rank r ≤ 8 (r < n for (A), r = n for
  (B)), found and checked by the function `certificate` of `e8common.py`, which the growth uses as
  well; r is 6, 7 or 8 and the product of the nonzero elementary divisors of M (PARI `matsnf`) is
  9 − r, so that the graph is exceptional; and, independently, an LLL-reduced basis of the lattice
  (PARI `qflllgram`, flag 4) has Gram determinant 9 − r and the lattice has exactly 72, 126 or 240
  roots (PARI `qfminim`), so it is E6, E7 or E8. For a list split in two parts, it also checks that
  every graph in a part has its number of edges in the range of the part. The order of each file,
  and of the merged parts of a split list, is checked as the files are read, by `read_list`. Thus
  the verification would detect a listed graph that is not exceptional, or is in the wrong list,
  or is listed twice, or a count that differs from `counts.json`. A full verification takes about
  100 minutes on 13 cores.
* `check_bruteforce.py n` runs over all connected graphs on n vertices (nauty `geng -c`, read in
  batches as it runs), decides exactly whether 2I + A is positive semidefinite, and its rank, by
  fraction-free symmetric elimination with diagonal pivoting in 64-bit integers (the entries are
  minors, at most 13^(n/2) < 4·10⁵ for n ≤ 10; every division is checked to be exact), and
  compares the canonical forms of the graphs of rank at most 8 with the level file. No floating
  point is used. For n = 10 it runs over 11,716,571 connected graphs, of which 28,113 have 2I + A
  positive semidefinite and 25,584 have rank at most 8, in about a minute on 12 workers. Thus it
  is an independent check of the levels, and of the completeness of the growth, for small n.
* `check_named.sage` checks that the exceptional strongly regular graphs (Petersen (10,3,0,1),
  Clebsch (16,10,6,6), Shrikhande (16,6,2,2), Schläfli (27,16,10,8), the three Chang graphs
  (28,12,6,4)) are in list (A), and that 34 generalized line graphs (L(K_m) for 3 ≤ m ≤ 9, CP(m)
  for 2 ≤ m ≤ 9, L(K_{s,t}) for 1 ≤ s ≤ t, 3 ≤ s + t ≤ 9) are in neither list; given the level
  directory, it also looks up their rank and lattice determinant in `infoNN.txt`. It keeps only
  the last list it has read of each kind, and looks a graph up in it by bisection.
* `count_regular.py` counts the regular graphs in the lists, per n and valency, and writes them to
  OUTFILE. It reads each list as a stream and hands it to the workers in chunks of 20,000 graphs,
  so that no whole list is in memory.
* Four further runs of the growth from scratch (the first of them for n ≤ 14 only), each with the
  scripts as they were on its date, reproduced the stored files: the levels byte for byte, and the
  lists, the gzipped ones up to the time stamp of their header. Appendix B of [Exc] describes them.

## Checks against the literature

* Brute force (`scripts/check_bruteforce.py`, exact): for every n = 1, …, 10 the set of connected
  graphs on n vertices with 2I + A positive semidefinite of rank at most 8 equals the growth's S_n
  (for n = 10: 25,584 graphs both ways).
* List (B) has 573 graphs, 20 on 6 vertices, 110 on 7 and 443 on 8, as in [CRS04] §2.3 and
  Table A2 and [DC79] (the exceptional graphs with least eigenvalue greater than −2).
* Minimal and maximal graphs. Cvetković [Cve04]: "The set E of exceptional graphs is finite. The
  number of exceptional graphs is very big but not known. The set E can be partially ordered by
  the induced subgraph relation. In this order E has 20 minimal elements and 473 maximal ones.
  Minimal exceptional graphs, all having 6 vertices, were found some 25 years ago"; "There are
  exactly 473 maximal exceptional graphs. Their number of vertices varies between 22 and 36";
  "Most of the maximal exceptional graphs (432 of them) are 29 vertex cones". Our lists: 20
  exceptional graphs on 6 vertices (all minimal, since an exceptional graph has at least 6
  vertices); 473 maximal ones on 22 to 36 vertices, 1 on 22, 1 on 28, 432 on 29, 25 on 30, 7 on
  31, 3 on 32, 1 on 33, 2 on 34 and 1 on 36, as in [Cve04] and [CLRS02]. [CRS04] Chapter 6, as
  reported in [DBvV26] §3, divides the maximal exceptional graphs into (a) those with largest
  valency 28 and exactly 29 vertices, which are cones (430 graphs), (b) those with largest valency
  28 and more than 29 vertices (37), and (c) those with largest valency less than 28 (6). Our
  counts agree exactly: 430, 37 and 6. Thus the "432 of them" of [Cve04] are the 432 maximal
  graphs on 29 vertices, two of which are not cones: the two type (c) graphs on 29 vertices
  (largest valency 26),

  ```
  \??GWWJ@}[ThijhfxLuIzom}`vx{]AyXdYijTeUxrLNEiizKkrnS[N^}@~~{~~~~Z~~~{
  \@G?GGBEDkLp\R[jthtTZkY|hfyk}C[xeTYjcmUyYlNHUizS[rna[N^~B~~}N^~~N~~~{
  ```
* To our knowledge, the total of 54,732,619 exceptional graphs (54,732,046 in list (A) and 573 in
  list (B)) and their numbers by number of vertices are the first published count; in 2004 the
  number was "very big but not known" [Cve04].
* Named graphs (`scripts/check_named.sage`, SageMath 10.9): the seven exceptional strongly regular
  graphs are all in list (A). None of the 34 generalized line graphs is in either list; the 31 of
  rank at most 8 are in the levels S_n (the 17 of rank 6 to 8 with lattice determinant 4 or r + 1,
  that is, of type D_r or A_r; the other 14 of rank at most 5), and L(K_9), CP(8) and CP(9) have
  rank 9, 9 and 10, so they are not represented in E8.
* Regular graphs (`scripts/count_regular.py`): 187 regular graphs in the lists, all in list (A),
  as in [BCS] (see [BCN89] §3.11): 163 with n = 2(k + 2), 21 with n = 3(k + 2)/2 and 3 with
  n = 4(k + 2)/3 (k the valency), as [BCN89] Theorem 3.12.2 requires. These are the three classes
  of 163, 21 and 3 regular exceptional graphs of [DBvV26], with ratio bounds 4, 3 and 8/3 (the
  ratio bound of a k-regular graph on n vertices with least eigenvalue −2 is 2n/(k + 2)). By
  number of vertices: 1, 2, 5, 14, 21, 6, 36, 42, 27, 2, 18, 9, 1 and 3 on 8, 9, 10, 12, 14, 15,
  16, 18, 20, 21, 22, 24, 27 and 28 vertices.

## The verification runs

Every graph of lists (A) and (B), for every n, has passed all the checks of `verify.py`. The
verification of record ran on 16 October 2026 with the present scripts, in which the certificate
check accepts the proposed adjugate only under the bound above: 54,732,619 graphs, all checks
passed, in 101 minutes on 13 cores. Before the bound was added, earlier versions of `verify.py`,
which make the same checks and differ from the present one only in how they use memory, had
verified every list by 30 September 2026: the lists for n ≤ 14 and n ≥ 26 with the first version,
those for 15 ≤ n ≤ 20 with the second and those for 21 ≤ n ≤ 25 with the third. On 9 October
2026 a later version checked the lists for n = 6, ..., 14 and n = 19 again (10,721,159 graphs),
and all checks passed.

## Scripts

* `e8common.py`: graph6 coding, the exact certificate, the lattice determinant, and the reading of
  the lists: `iter_list` reads a list as a stream, merging the two parts of a split list and, when
  asked, checking the order of the strings and their numbers of edges as it reads; `read_list`
  returns the same strings as a list.
* `grow.py`: one growth step, in parallel, piping the candidates through `labelg | sort -u`; each
  worker's sort runs single-threaded with an equal share of SORTMEM, and each worker seeks to the
  start of its chunk of the level file.
* `run_levels.sh`: the driver (retries a failed step; checks every input graph was processed; logs
  the time and the memory of each step). It takes its environment from the caller.
* `extract.py`: writes the lists for one n and updates `counts.json`. It writes a list in batches,
  gzipped when it is over 20 MB, with time stamp 0 in the gzip header, so that a rerun gives
  identical bytes.
* `split_by_edges.py`: splits a list in two parts by number of edges (see Files).
* `verify.py`, `check_bruteforce.py`, `check_named.sage`, `count_regular.py`: the checks.
* `make_table.py`: writes Table 1 of [Exc] (`exceptional/note/counts-table.tex`) from
  `counts.json`, as in `python scripts/make_table.py counts.json ../note/counts-table.tex`.

## References

* [Exc] K. Guo, A database of exceptional graphs with least eigenvalue ≥ −2, 2026
  (`exceptional/note/exceptional.tex` in this repository).
* [CGSS] P. J. Cameron, J.-M. Goethals, J. J. Seidel, E. E. Shult, Line graphs, root systems, and
  elliptic geometry, J. Algebra 43 (1976) 305–327.
* [CRS04] D. Cvetković, P. Rowlinson, S. Simić, Spectral Generalizations of Line Graphs, LMS
  Lecture Note Ser. 314, Cambridge University Press, 2004.
* [CLRS02] D. Cvetković, M. Lepović, P. Rowlinson, S. K. Simić, The maximal exceptional graphs,
  J. Combin. Theory Ser. B 86 (2002) 347–363.
* [BCS] F. C. Bussemaker, D. M. Cvetković, J. J. Seidel, Graphs related to exceptional root
  systems, Colloq. Math. Soc. János Bolyai 18 (1978) 185–191.
* [BCN89] A. E. Brouwer, A. M. Cohen, A. Neumaier, Distance-Regular Graphs, Springer, 1989.
* [Cve04] D. Cvetković, Notes on maximal exceptional graphs, Univ. Beograd. Publ. Elektrotehn.
  Fak. Ser. Mat. 15 (2004) 103–107.
* [DBvV26] B. De Bruyn, T. van Veluw, Hoffman colorability of graphs with smallest eigenvalue at
  least −2, arXiv:2603.03859 (2026).
* [DC79] M. Doob, D. Cvetković, On spectral characterizations and embeddings of graphs, Linear
  Algebra Appl. 27 (1979) 17–26.
