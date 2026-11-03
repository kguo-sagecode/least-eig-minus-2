"""Exact finite checks for the ordinary proof of CGSS Theorem 3.12.

Run from any directory with python3; requires NumPy and SymPy.
All decisions use integers, fractions, or exact algebraic numbers. Floating
point eigenvalues are supplementary diagnostics. No calculation is a premise
of the ordinary proof. This script writes no files by itself.
"""

from collections import Counter, deque
from fractions import Fraction as Q
from itertools import combinations, product
from math import isqrt
from random import Random
import sys

import numpy as np
import sympy as sp


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def vec(n, entries):
    x = [Q(0)] * n
    for i, a in entries:
        x[i] += Q(a)
    return tuple(x)


def line(x):
    first = next(a for a in x if a)
    return tuple(a / first for a in x)


def model(kind, n):
    roots = {vec(n, [(i, a), (j, b)])
             for i, j in combinations(range(n), 2)
             for a, b in product((-1, 1), repeat=2)}
    axis = 2 if kind == "C" else 1
    roots |= {vec(n, [(i, a * axis)])
              for i in range(n) for a in (-1, 1)}
    if kind == "F":
        assert n == 4
        roots |= {tuple(Q(a, 2) for a in signs)
                  for signs in product((-1, 1), repeat=4)}
        base = [vec(n, [(1, 1), (2, -1)]),
                vec(n, [(2, 1), (3, -1)]), vec(n, [(3, 1)]),
                tuple(Q(a, 2) for a in (1, -1, -1, -1))]
    else:
        assert kind in ("B", "C")
        base = [vec(n, [(i, 1), (i + 1, -1)]) for i in range(n - 1)]
        base.append(vec(n, [(n - 1, axis)]))
    return sorted(roots), base


def angle_data(roots):
    representatives = sorted({line(r) for r in roots})
    angles = {}
    for i, j in combinations(range(len(representatives)), 2):
        x, y = representatives[i], representatives[j]
        c2 = dot(x, y) ** 2 / (dot(x, x) * dot(y, y))
        assert c2 in (Q(0), Q(1, 4), Q(1, 2))
        angles[i, j] = c2
    return representatives, angles


def partition(n, angles):
    """60-degree edges preserve colour; 45-degree edges reverse it."""
    adjacency = [[] for _ in range(n)]
    for (i, j), c2 in angles.items():
        if c2 == 0:
            continue
        flip = int(c2 == Q(1, 2))
        assert c2 in (Q(1, 4), Q(1, 2))
        adjacency[i].append((j, flip))
        adjacency[j].append((i, flip))
    colour = [None] * n
    for start in range(n):
        if colour[start] is not None:
            continue
        colour[start] = 0
        queue = deque([start])
        while queue:
            i = queue.popleft()
            for j, flip in adjacency[i]:
                wanted = colour[i] ^ flip
                if colour[j] is None:
                    colour[j] = wanted
                    queue.append(j)
                elif colour[j] != wanted:
                    return None
    return colour


def valid_colouring(colour, angles):
    return all(c2 == 0 or ((colour[i] != colour[j]) == (c2 == Q(1, 2)))
               for (i, j), c2 in angles.items())


def is_reduced(roots):
    """Check proportionality on Gram images, also for dependent seeds."""
    for r in roots:
        pivot = next(i for i, a in enumerate(r) if a)
        for s in roots:
            ratio = Q(s[pivot]) / r[pivot]
            if all(b == ratio * a for a, b in zip(r, s)) and ratio not in (-1, 1):
                return False
    return True


def verify_root_axioms(gram, roots, require_reduced=True):
    """Check axioms in the seed span; optionally return a failed reducedness test."""
    def signature(a):
        return tuple(dot(row, a) for row in gram)

    # Containing the seeds certifies spanning, including for dependent seeds.
    assert all(tuple(row) in roots for row in gram)
    for key_r, r in roots.items():
        assert signature(r) == key_r
        assert any(key_r)
        assert tuple(-a for a in key_r) in roots
        qr = dot(r, key_r)
        assert qr > 0
        for key_s, s in roots.items():
            c = Q(2 * dot(r, key_s)) / qr
            assert c.denominator == 1
            reflected = tuple(b - c.numerator * a for a, b in zip(r, s))
            assert signature(reflected) in roots
    reduced = is_reduced(roots)
    if require_reduced:
        assert reduced
    return reduced


def closure(gram, cap=1000, normalized=True):
    """Reflect all current roots in all current roots until stable.

    Roots are integer combinations of the seeds. We identify coefficient
    vectors a,b when Gram*a = Gram*b. For a positive semidefinite Gram matrix
    this is precisely equality of the represented Euclidean vectors; this
    also handles dependent seeds. A retained representative remains integral.
    The cap is only a failure guard, never a successful termination rule.
    With normalized=False we impose neither the norm-{2,4} assumptions nor
    the parity condition: this independently tests proposed length assignments.
    Such a closure may be nonreduced; the caller must test is_reduced separately.
    """
    n = len(gram)
    assert all(len(row) == n for row in gram)
    assert all(gram[i][j] == gram[j][i] for i in range(n) for j in range(n))
    lengths = {gram[i][i] for i in range(n)}
    if normalized:
        assert all(type(a) is int for row in gram for a in row)
        assert lengths <= {2, 4}
        assert all(gram[i][i] != 4 or all(a % 2 == 0 for a in gram[i])
                   for i in range(n))
    else:
        assert all(isinstance(a, (int, Q)) for row in gram for a in row)
        assert all(a > 0 for a in lengths)

    def signature(a):
        return tuple(dot(row, a) for row in gram)

    def norm(a):
        return dot(a, signature(a))

    def check_invariant(a):
        q = norm(a)
        assert q in lengths
        if normalized:
            assert q != 4 or all(x % 2 == 0 for x in signature(a))

    roots = {}
    for i in range(n):
        a = tuple(int(j == i) for j in range(n))
        roots[signature(a)] = a
    stages = [len(roots)]
    while True:
        current = list(roots.items())
        added = {}
        for key_r, r in current:
            check_invariant(r)
            qr = dot(r, key_r)
            for key_s, s in current:
                coeff = Q(2 * dot(r, key_s)) / qr
                assert coeff.denominator == 1
                coeff = coeff.numerator
                t = tuple(b - coeff * a for a, b in zip(r, s))
                check_invariant(t)
                assert norm(t) == dot(s, key_s)
                key_t = signature(t)
                if key_t not in roots:
                    added[key_t] = t
        if not added:
            break
        roots.update(added)
        assert len(roots) <= cap, "Closure exceeded its failure guard"
        stages.append(len(roots))

    verify_root_axioms(gram, roots, require_reduced=normalized)
    return roots, stages


def integral_span_roots(gram):
    """Enumerate the explicit Psi for independent seeds, with a proved bound.

    For q(a) <= 4, Cauchy--Schwarz in the Gram metric gives
    a[i]^2 <= 4 * inverse(Gram)[i,i]. Thus this coefficient box exhausts
    the shell; no arbitrary search cutoff is used. Evenness on every seed
    is equivalent to evenness on its integer span.
    """
    n = len(gram)
    matrix = sp.Matrix(gram)
    assert all(type(a) is int for row in gram for a in row)
    assert matrix == matrix.T
    assert all(matrix[:k, :k].det() > 0 for k in range(1, n + 1))
    if not n:
        return {}
    inverse = matrix.inv()
    bounds = [isqrt(int(sp.floor(4 * inverse[i, i]))) for i in range(n)]
    roots = {}
    for a in product(*(range(-b, b + 1) for b in bounds)):
        key = tuple(dot(row, a) for row in gram)
        q = dot(a, key)
        if q == 2 or (q == 4 and all(x % 2 == 0 for x in key)):
            roots[key] = a
    verify_root_axioms(gram, roots)
    return roots


def model_checks():
    for kind, n in [(k, n) for k in ("B", "C") for n in range(2, 9)] + [("F", 4)]:
        roots, base = model(kind, n)
        rootset = set(roots)
        lengths = {r: dot(r, r) for r in roots}
        assert set(lengths.values()) == ({2, 4} if kind == "C" else {1, 2})
        lines, angles = angle_data(roots)
        assert len(roots) == (48 if kind == "F" else 2 * n * n)
        assert len(lines) == len(roots) // 2
        assert sp.Matrix.hstack(*map(sp.Matrix, base)).rank() == n
        root_on_line = {line(r): r for r in roots}
        short = min(lengths.values())
        colours = [int(lengths[root_on_line[x]] != short) for x in lines]
        assert valid_colouring(colours, angles)
        computed = partition(len(lines), angles)
        assert computed == colours or computed == [1 - a for a in colours]
        for r in roots:
            assert tuple(-a for a in r) in rootset
            for s in roots:
                c = 2 * dot(r, s) / lengths[r]
                assert c.denominator == 1
                assert tuple(b - c * a for a, b in zip(r, s)) in rootset
                if line(r) == line(s):
                    assert s == r or s == tuple(-a for a in r)
        scale_sq = 1 if kind == "C" else 2
        gram = [[int(scale_sq * dot(x, y)) for y in base] for x in base]
        assert all(sp.Matrix(gram)[:k, :k].det() > 0 for k in range(1, n + 1))
        generated, stages = closure(gram)
        inverse = sp.Matrix.hstack(*map(sp.Matrix, base)).inv()
        expected = set()
        for r in roots:
            coefficients = inverse * sp.Matrix(r)
            assert all(a.q == 1 for a in coefficients)
            a = tuple(map(int, coefficients))
            expected.add(tuple(dot(row, a) for row in gram))
        assert set(generated) == expected
        print(f"{kind}{n}: roots={len(roots)}, lines={len(lines)}, "
              f"length_parts={dict(sorted(Counter(colours).items()))}, "
              f"cos2={sorted(set(angles.values()))}, closure_stages={stages}")
    for n in range(2, 9):
        b, _ = model("B", n)
        c, _ = model("C", n)
        assert {line(x) for x in b} == {line(x) for x in c}
    print("B_n and C_n: identical line sets for every checked rank 2..8")


def normalized_gram(unit_gram, colour):
    n = len(colour)
    gram = []
    for i in range(n):
        row = []
        for j in range(n):
            entry = sp.simplify(unit_gram[i, j] * sp.sqrt((2 * 2 ** colour[i]) *
                                                       (2 * 2 ** colour[j])))
            assert entry.is_Integer
            row.append(int(entry))
        gram.append(row)
    return gram


def small_checks():
    root_sizes = {}
    examples = {
        "empty": [],
        "singleton_short": [[2]],
        "singleton_long": [[4]],
        "orthogonal_mixed": [[2, 0], [0, 4]],
        "A2_two_lines_not_closed": [[2, -1], [-1, 2]],
        "A2_three_dependent_lines": [[2, -1, -1], [-1, 2, -1], [-1, -1, 2]],
        "B2_two_lines_not_closed": [[2, 2], [2, 4]],
        "C3_three_lines_not_closed": [[2, 2, 1], [2, 4, 2], [1, 2, 2]],
    }
    expected = [0, 2, 2, 4, 6, 6, 8, 18]
    for (name, gram), count in zip(examples.items(), expected):
        # Exact positive semidefiniteness for these possibly dependent seeds.
        m = sp.Matrix(gram)
        for k in range(1, len(gram) + 1):
            assert all(m.extract(rows, rows).det() >= 0
                       for rows in combinations(range(len(gram)), k))
        roots, stages = closure(gram)
        assert len(roots) == count
        root_sizes[name] = count
        print(f"{name}: closure_stages={stages}, roots={count}")

    # Completing the ambient space: a B2 seed plane inside R^4.
    gram = [[2, 2, 0, 0], [2, 4, 0, 0], [0, 0, 2, 0], [0, 0, 0, 2]]
    roots, _ = closure(gram)
    assert len(roots) == 12
    assert all(not (any(r[:2]) and any(r[2:])) for r in roots.values())
    assert sp.Matrix(gram).rank() == 4
    assert sp.Matrix(list(roots)).rank() == 4
    psi = integral_span_roots(gram)
    assert len(psi) == 32
    assert sp.Matrix(list(psi)).rank() == 4
    assert set(roots) < set(psi)
    print("B2 plane in R4, two orthogonal norm-2 seeds: "
          "reflection closure=12 roots, Psi=32 roots; both ranks asserted to be 4")

    # Independent component scales: the second B2 is multiplied by 3.
    b2, _ = model("B", 2)
    scaled = [r + (Q(0), Q(0)) for r in b2]
    scaled += [(Q(0), Q(0)) + tuple(3 * a for a in r) for r in b2]
    lines, angles = angle_data(scaled)
    assert partition(len(lines), angles) is not None
    assert {dot(r, r) for r in scaled} == {1, 2, 9, 18}
    for r in scaled:
        for s in scaled:
            c = 2 * dot(r, s) / dot(r, r)
            assert c.denominator == 1
            assert tuple(b - c * a for a, b in zip(r, s)) in scaled
    print("B2 orthogonal sum 3*B2: four squared lengths {1,2,9,18}; partition passes")

    c = sp.sqrt(2) / 2
    negative = {
        "three_45_degree_lines": sp.Matrix([[1, c, c], [c, 1, c], [c, c, 1]]),
        "two_60_one_45": sp.Matrix([[1, sp.Rational(1, 2), c],
                                    [sp.Rational(1, 2), 1, sp.Rational(1, 2)],
                                    [c, sp.Rational(1, 2), 1]]),
    }
    for name, gram in negative.items():
        assert all(sp.simplify(gram[:k, :k].det()).is_positive for k in range(1, 4))
        angles = {(i, j): Q(gram[i, j] ** 2) for i, j in combinations(range(3), 2)}
        assert partition(3, angles) is None
        assert not any(valid_colouring(a, angles) for a in product((0, 1), repeat=3))
        # Exact Cholesky vectors, with an independent numerical eigenvalue check.
        a = gram.cholesky()
        assert (a * a.T - gram).applyfunc(sp.simplify) == sp.zeros(3)
        mineig = np.linalg.eigvalsh(np.array(gram, dtype=float))[0]
        assert mineig > 0
        print(f"{name}: det={sp.simplify(gram.det())}, "
              f"min_eigenvalue~{mineig:.9f}, no compatible partition")


def all_three_line_checks():
    """Every labelled, signed, unit Gram matrix with three allowed angles."""
    c = sp.sqrt(2) / 2
    values = [0, sp.Rational(1, 2), -sp.Rational(1, 2), c, -c]
    counts = Counter()
    closures = Counter()
    cross_tab = Counter()
    assignment_counts = Counter()
    # Precompute all exact scaled inner products and coefficients. The lengths
    # are tried independently of the partition algorithm, including rejected
    # configurations. An irrational/noninteger coefficient rejects a candidate
    # by the integrality axiom on the seeds alone.
    lengths = (1, 2, 4)
    scaled = {(v, x, y): sp.simplify(v * sp.sqrt(x * y))
              for v, x, y in product(values, lengths, lengths)}
    integral = {(v, x, y): (2 * entry / x).is_Integer
                for (v, x, y), entry in scaled.items()}
    assert all(decision is not None for decision in integral.values())
    for a, b, c in product(values, repeat=3):
        gram = sp.Matrix([[1, a, b], [a, 1, c], [b, c, 1]])
        det = sp.simplify(gram.det())
        # All proper principal minors are positive. Only det can obstruct PSD.
        if det.is_nonnegative is not True:
            assert det.is_negative is True
            counts["not_psd"] += 1
            continue
        counts["psd"] += 1
        definiteness = "singular" if det == 0 else "positive_definite"
        counts[definiteness] += 1
        angles = {(i, j): Q(gram[i, j] ** 2) for i, j in combinations(range(3), 2)}
        colour = partition(3, angles)
        brute = [a for a in product((0, 1), repeat=3) if valid_colouring(a, angles)]
        assert (colour is not None) == bool(brute)
        cross_tab[definiteness, colour is not None] += 1

        integral_assignments = completed_assignments = 0
        for assigned_lengths in product(lengths, repeat=3):
            assignment_counts["tried"] += 1
            if not all(integral[gram[i, j], assigned_lengths[i], assigned_lengths[j]]
                       for i in range(3) for j in range(3) if i != j):
                assignment_counts["rejected_on_seeds"] += 1
                continue
            integral_assignments += 1
            assigned = [[Q(assigned_lengths[i]) if i == j else
                         Q(scaled[gram[i, j], assigned_lengths[i], assigned_lengths[j]])
                         for j in range(3)] for i in range(3)]
            completed, _ = closure(assigned, normalized=False)
            assert sp.Matrix(list(completed)).rank() == gram.rank()
            if is_reduced(completed):
                completed_assignments += 1
                assignment_counts["root_systems"] += 1
            else:
                assignment_counts["nonreduced_closures"] += 1
        assert bool(integral_assignments) == bool(brute)
        assert bool(completed_assignments) == bool(brute)
        if colour is None:
            counts["no_partition"] += 1
        else:
            counts["partition"] += 1
            # Test both assignments of the two lengths, even for dependent seeds.
            for chosen in (colour, [1 - a for a in colour]):
                roots, _ = closure(normalized_gram(gram, chosen))
                closures[len(roots)] += 1
    assert counts == {"psd": 97, "not_psd": 28, "positive_definite": 81,
                      "singular": 16, "partition": 81, "no_partition": 16}
    expected_cross_tab = {("positive_definite", True): 65,
                          ("positive_definite", False): 16,
                          ("singular", True): 16, ("singular", False): 0}
    assert all(cross_tab[key] == count for key, count in expected_cross_tab.items())
    assert closures == {6: 10, 8: 36, 10: 12, 12: 32, 18: 72}
    assert assignment_counts["tried"] == 97 * 27
    assert (assignment_counts["root_systems"] + assignment_counts["nonreduced_closures"]
            + assignment_counts["rejected_on_seeds"]
            == assignment_counts["tried"])
    print(f"Exhaustive 125 signed three-line Gram matrices: {dict(sorted(counts.items()))}")
    print("Census cross-tab (partition, no partition): "
          f"positive definite=({cross_tab['positive_definite', True]}, "
          f"{cross_tab['positive_definite', False]}), "
          f"singular=({cross_tab['singular', True]}, {cross_tab['singular', False]})")
    print(f"Both colour orientations, resulting root counts: {dict(sorted(closures.items()))}")
    print("Independent squared-length assignments in {1,2,4}: "
          f"{dict(sorted(assignment_counts.items()))}; "
          "integral seeds and verified completion exist iff a partition exists in all 97 cases")


def explicit_psi_checks():
    examples = {
        "empty": ([], 0, 0),
        "A1_squared": ([[2, 0], [0, 2]], 8, 4),
        "A1_cubed": ([[2, 0, 0], [0, 2, 0], [0, 0, 2]], 18, 6),
        "A2_plus_A1": ([[2, -1, 0], [-1, 2, 0], [0, 0, 2]], 8, 8),
        "B2": ([[2, 2], [2, 4]], 8, 8),
        "C3": ([[2, 2, 1], [2, 4, 2], [1, 2, 2]], 18, 18),
        "D4": ([[2, -1, 0, 0], [-1, 2, -1, -1],
                [0, -1, 2, 0], [0, -1, 0, 2]], 48, 24),
    }
    for name, (gram, psi_count, closure_count) in examples.items():
        psi = integral_span_roots(gram)
        generated, _ = closure(gram)
        assert len(psi) == psi_count
        assert len(generated) == closure_count
        assert set(generated) <= set(psi)
        assert sp.Matrix(list(psi)).rank() == len(gram)
        print(f"Explicit Psi, {name}: {len(psi)} roots; "
              f"reflection closure: {len(generated)} roots; all axioms verified")


def floor_log_two(x):
    """The exact integer h with 2**h <= x < 2**(h+1), also for x < 1."""
    x = Q(x)
    assert x > 0
    exponent = x.numerator.bit_length() - x.denominator.bit_length()
    if x < Q(2) ** exponent:
        exponent -= 1
    assert Q(2) ** exponent <= x < Q(2) ** (exponent + 1)
    return exponent


def g2_model():
    """The rational-coordinate G2 model in the plane x+y+z=0."""
    roots = {vec(3, [(i, 1), (j, -1)])
             for i in range(3) for j in range(3) if i != j}
    roots |= {tuple(Q(sign * (2 if j == i else -1)) for j in range(3))
              for i in range(3) for sign in (-1, 1)}
    assert len(roots) == 12
    return sorted(roots)


def orthogonal_model(components):
    """Use rational coordinates and a weighted metric for exact rescaling.

    A component (roots, scale_sq) represents sqrt(scale_sq)*roots in the
    ordinary Euclidean metric. Block weights keep every calculation rational,
    even for the sqrt(3) factor, without approximating the represented vectors.
    """
    dimensions = [len(roots[0]) for roots, _ in components]
    total_dimension = sum(dimensions)
    weights, roots, component_of_line = [], [], {}
    offset = 0
    for component, ((block, scale_sq), dimension) in enumerate(zip(components, dimensions)):
        assert scale_sq > 0
        weights.extend([Q(scale_sq)] * dimension)
        for r in block:
            embedded = (Q(0),) * offset + r + (Q(0),) * (total_dimension - offset - dimension)
            roots.append(embedded)
            component_of_line[line(embedded)] = component
        offset += dimension

    def inner(x, y):
        return sum(w * a * b for w, a, b in zip(weights, x, y))

    # Verify the entire containing Root System before sampling its line sets.
    rootset = set(roots)
    for r in roots:
        assert inner(r, r) > 0
        assert tuple(-a for a in r) in rootset
        for s in roots:
            coefficient = 2 * inner(r, s) / inner(r, r)
            assert coefficient.denominator == 1
            assert tuple(b - coefficient * a for a, b in zip(r, s)) in rootset
            if line(r) == line(s):
                assert s == r or s == tuple(-a for a in r)
    assert sp.Matrix(roots).rank() == sum(sp.Matrix(block).rank() for block, _ in components)

    representatives = sorted(component_of_line)
    root_on_line = {line(r): r for r in roots}
    squared_lengths = [inner(root_on_line[x], root_on_line[x]) for x in representatives]
    component_indices = [component_of_line[x] for x in representatives]
    angles = {(i, j): inner(x, y) ** 2 / (inner(x, x) * inner(y, y))
              for i, x in enumerate(representatives)
              for j, y in enumerate(representatives) if i < j}
    assert set(angles.values()) <= {Q(0), Q(1, 4), Q(1, 2), Q(3, 4)}
    return squared_lengths, component_indices, angles


def subset_checks():
    f4, _ = model("F", 4)
    b3, _ = model("B", 3)
    c3, _ = model("C", 3)
    b2, _ = model("B", 2)
    examples = [
        ("F4 + sqrt(3)*B3", [(f4, Q(1)), (b3, Q(3))]),
        ("C3 + G2 + (17/10)*B2", [(c3, Q(1)), (g2_model(), Q(1)),
                                   (b2, Q(289, 100))]),
    ]
    rng = Random(20260928)
    totals = Counter()
    for name, components in examples:
        lengths, component_indices, full_angles = orthogonal_model(components)
        counts = Counter()
        for x in lengths:
            assert floor_log_two(2 * x) == floor_log_two(x) + 1
            assert floor_log_two(x / 2) == floor_log_two(x) - 1
        for _ in range(3000):
            selected = sorted(rng.sample(range(len(lengths)), rng.randint(2, 9)))
            assert 2 <= len(selected) <= 9 < len(lengths)
            angles = {(i, j): full_angles[selected[i], selected[j]]
                      for i, j in combinations(range(len(selected)), 2)}
            if Q(3, 4) in angles.values():
                counts["skipped_30_degree_pair"] += 1
                continue
            computed = partition(len(selected), angles)
            assert computed is not None
            assert valid_colouring(computed, angles)
            exponents = [floor_log_two(lengths[i]) for i in selected]
            assert valid_colouring([e % 2 for e in exponents], angles)
            # Rescaling the entire system gives negative logarithms. Both an
            # even and an odd shift test the colour behaviour below length 1.
            for shift in (-4, -3):
                shifted = [floor_log_two(lengths[i] * Q(2) ** shift) for i in selected]
                assert shifted == [e + shift for e in exponents]
                assert all(e < 0 for e in shifted)
                assert valid_colouring([e % 2 for e in shifted], angles)
            counts["allowed"] += 1
            counts["allowed_with_45_degree_pair"] += Q(1, 2) in angles.values()
            counts["allowed_meeting_multiple_components"] += (
                len({component_indices[i] for i in selected}) > 1)
            if len(components) == 3:
                g2_lengths = {lengths[i] for i in selected if component_indices[i] == 1}
                counts["allowed_meeting_G2"] += bool(g2_lengths)
                counts["allowed_meeting_both_G2_lengths"] += g2_lengths == {2, 6}
        assert counts["allowed"] + counts["skipped_30_degree_pair"] == 3000
        assert counts["allowed_with_45_degree_pair"] > 0
        assert counts["allowed_meeting_multiple_components"] > 0
        if len(components) == 2:
            assert counts["allowed"] == 3000
        else:
            assert counts["skipped_30_degree_pair"] > 0
            assert counts["allowed_meeting_both_G2_lengths"] > 0
        totals.update(counts)
        print(f"3000 proper random subsets, {name}: {dict(sorted(counts.items()))}")
    assert totals["allowed"] + totals["skipped_30_degree_pair"] == 6000
    print(f"Subset totals (seed 20260928): allowed={totals['allowed']}, "
          f"skipped_30_degree_pair={totals['skipped_30_degree_pair']}; "
          "all allowed subsets pass graph and integer-log colourings")


def parity_checks():
    """An integral norm-4 vector need not preserve the whole integer span."""
    # In the A2 lattice, the first two coefficients have Gram [[2,-1],[-1,2]].
    # Adjoin an orthogonal norm-2 vector. r=e1+e3 has norm 4 but (r,e2)=-1.
    gram = [[2, -1, 0], [-1, 2, 0], [0, 0, 2]]
    r, s = (1, 0, 1), (0, 1, 0)
    signature = tuple(dot(row, r) for row in gram)
    assert dot(r, signature) == 4
    assert dot(s, signature) == -1
    assert Q(2 * dot(s, signature), dot(r, signature)) == Q(-1, 2)
    print("Parity guard: an arbitrary norm-4 lattice vector has pairing -1/2; "
          "the full norm-{2,4} shell would fail crystallographic integrality")


if __name__ == "__main__":
    print(f"Python {sys.version.split()[0]} checks: SymPy {sp.__version__}, NumPy {np.__version__}")
    model_checks()
    small_checks()
    explicit_psi_checks()
    all_three_line_checks()
    subset_checks()
    parity_checks()
    print("PASS: all exact assertions and numerical diagnostics")
