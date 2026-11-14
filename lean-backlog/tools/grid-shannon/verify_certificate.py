#!/usr/bin/env python3
"""Check the grid Shannon upper certificate using only integer arithmetic.

Run: python3 lean-backlog/tools/grid-shannon/verify_certificate.py
Python 3.10+; do not use -O. No optimizer or discovery generator is imported.
The 18 inequalities prove an upper bound, not the exact Shannon optimum.
Their soft-recovery costs, lower construction, order value and residual
triangle check are exact.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
import json


def host():
    """The 9 point rows and 6 line columns of the 3 by 3 grid."""
    points = list(product(range(3), repeat=2))
    lines = [{3*i+j for j in range(3)} for i in range(3)] + [
        {3*i+j for i in range(3)} for j in range(3)]
    cells = [(p, ell) for p in range(9) for ell in range(6) if p not in lines[ell]]
    index = {cell: i for i, cell in enumerate(cells)}
    rows = [sum(1 << i for i, (p, _) in enumerate(cells) if p == r) for r in range(9)]
    cols = [sum(1 << i for i, (_, ell) in enumerate(cells) if ell == c) for c in range(6)]
    helpers = [sum(rows[p] for p in line) for line in lines]
    assert len(cells) == 36 and sum(map(len, lines)) == 18
    assert all(R.bit_count() == 4 for R in rows)
    assert all(C.bit_count() == 6 for C in cols)
    assert all(H.bit_count() == 12 for H in helpers)
    group = set()
    for f, g, swap in product(permutations(range(3)), permutations(range(3)), (False, True)):
        pp = [3*(g[j] if swap else f[i])+(f[i] if swap else g[j]) for i, j in points]
        lp = [lines.index({pp[p] for p in line}) for line in lines]
        cp = tuple(index[pp[p], lp[ell]] for p, ell in cells)
        assert all(bool(helpers[cells[i][1]] >> j & 1) ==
                   bool(helpers[cells[cp[i]][1]] >> cp[j] & 1)
                   for i in range(36) for j in range(36))
        group.add(cp)
    assert len(group) == 72
    return lines, cells, index, rows, cols, helpers, group


def closure_path(S, helpers, cols):
    """Return the closure and a deterministic list of paid column firings."""
    path = []
    while True:
        old = S
        for ell, (H, C) in enumerate(zip(helpers, cols)):
            if H & S == H and C & ~S:
                path.append(dict(column=ell, added_mask=C & ~S))
                S |= C
        if S == old:
            return S, path


def closure(S, helpers, cols):
    return closure_path(S, helpers, cols)[0]


def move(S, perm):
    return sum(1 << perm[i] for i in range(len(perm)) if S >> i & 1)


def sector_rank(S, structure):
    # A sector consists of pairs (y_i, y_i-D), with its own independent D.
    # This is the graphic rank of K_{2,6}, and also group-difference entropy
    # for uniform independent symbols in any finite abelian group.
    return sum(sum(bool(S & pair) for pair in pairs) +
               int(any(S & pair == pair for pair in pairs)) for pairs in structure)


def verify(certificate):
    if not __debug__:
        raise RuntimeError("Assertions must be enabled; do not run with -O")
    lines, cells, index, rows, cols, helpers, group = host()
    full = (1 << len(cells))-1
    close = lambda S: closure(S, helpers, cols)
    cache = {}

    def canonical(S):
        if S not in cache:
            cache[S] = min(move(S, p) for p in group)
        return cache[S]

    assert certificate["scale"] == 5 and certificate["residual_rhs"] == 114

    # First recover the horizontal-line column from point rows 0,1,2;
    # it supplies the omitted cells of rows 3,6, completing a vertical line.
    generator = rows[0] | rows[1] | rows[2] | (rows[3] & ~cols[0]) | (rows[6] & ~cols[0])
    row_union = rows[0] | rows[1] | rows[2] | rows[3] | rows[6]
    assert generator.bit_count() == 18
    assert close(generator) == close(row_union) == 23074308095
    assert certificate["generator18"] == generator

    combined, rhs_total, semantic_rows = Counter(), 0, []
    used_orbits = set()
    paid_paths = []
    for term_number, item in enumerate(certificate["terms"], 1):
        kind, sets, weight = item["kind"], item["sets"], item["weight"]
        assert isinstance(weight, int) and weight > 0
        singleton_mask, path, start = 0, [], None
        if kind == "normalization":
            S, = sets
            assert S == 0
            terms, rhs = [(S, -1)], 0
        elif kind == "submodular":
            S, T = sets
            start = S | T
            joined, path = closure_path(start, helpers, cols)
            terms = [(S & T, 1), (joined, 1), (S, -1), (T, -1)]
            rhs = 0
        elif kind == "singleton-cap":
            S, = sets
            singleton_mask = S
            terms, rhs = [(S, 1)], S.bit_count()
        elif kind == "generator-cap":
            S, = sets
            assert S == close(generator)
            singleton_mask = start = generator
            joined, path = closure_path(start, helpers, cols)
            assert joined == S
            terms, rhs = [(S, 1)], generator.bit_count()
        else:
            raise AssertionError(kind)
        coefficients = Counter()
        for S, a in terms:
            assert 0 <= S <= full and close(S) == S
            coefficients[canonical(S)] += a
        coefficients = {S: a for S, a in coefficients.items() if a}
        for S, a in coefficients.items():
            combined[S] += weight*a
            used_orbits.add(S)
        rhs_total += weight*rhs
        semantic_rows.append(dict(kind=kind, weight=weight, sets=sets, rhs=rhs,
                                  orbit_coefficients=sorted(coefficients.items()),
                                  singleton_mask=singleton_mask, closure_path=path))
        if path:
            paid_paths.append(dict(term=term_number, weight=weight, start_mask=start, steps=path))
    assert len(semantic_rows) == 18
    assert {S: a for S, a in combined.items() if a} == {full: 5}
    assert rhs_total == 114
    orbit_table = [dict(mask=S, cells=S.bit_count(), orbit_size=len({move(S, p) for p in group}))
                   for S in sorted(used_orbits)]
    assert orbit_table == certificate["orbits"]

    # With imperfect recovery, each firing costs at most the sum of the
    # conditional entropies of its new cells given their helper set, or
    # alternatively the joint conditional entropy of its whole column.
    # Check the actual transported incidence counts, not only their totals.
    raw_singleton_weight = sum(row["weight"]*row["singleton_mask"].bit_count()
                               for row in semantic_rows)
    raw_cell_error_weight = sum(row["weight"]*step["added_mask"].bit_count()
                               for row in semantic_rows for step in row["closure_path"])
    raw_column_error_weight = sum(row["weight"]*len(row["closure_path"])
                                 for row in semantic_rows)
    assert (raw_singleton_weight, raw_cell_error_weight, raw_column_error_weight) == (114, 66, 16)
    singleton_weights, cell_errors, column_errors = [0]*36, [0]*36, [0]*6
    for perm in group:
        line_perm = [cells[perm[(C & -C).bit_length()-1]][1] for C in cols]
        for row in semantic_rows:
            for v in range(36):
                if row["singleton_mask"] >> v & 1:
                    singleton_weights[perm[v]] += row["weight"]
            for step in row["closure_path"]:
                column_errors[line_perm[step["column"]]] += row["weight"]
                for v in range(36):
                    if step["added_mask"] >> v & 1:
                        cell_errors[perm[v]] += row["weight"]
    assert set(singleton_weights) == {228}
    assert set(cell_errors) == {132}
    assert set(column_errors) == {192}
    denominator = 5*len(group)
    assert singleton_weights[0]+cell_errors[0] == denominator
    soft = dict(raw_singleton_weight=raw_singleton_weight,
                raw_new_cell_weight=raw_cell_error_weight,
                raw_column_firings=raw_column_error_weight,
                average_denominator=denominator,
                per_cell_singleton_weight=singleton_weights[0],
                per_cell_error_weight=cell_errors[0],
                per_column_error_weight=column_errors[0],
                singleton_coefficient=str(Fraction(singleton_weights[0], denominator)),
                cell_error_coefficient=str(Fraction(cell_errors[0], denominator)),
                joint_column_error_coefficient=str(Fraction(column_errors[0], denominator)),
                paths=paid_paths)
    assert soft == certificate["soft_recovery"]

    # Exact rank-21 code: three independent sectors, one for each a < b.
    # Its displayed form need not be invariant under the host group.
    sectors = []
    for a, b in combinations(range(3), 2):
        pairs = [(index[3*a+j, b], index[3*b+j, a]) for j in range(3)]
        pairs += [(index[3*i+a, 3+b], index[3*i+b, 3+a]) for i in range(3)]
        sectors.append(pairs)
    structures = Counter(tuple(sorted(tuple(sorted((1 << p[u]) | (1 << p[v])
                                                   for u, v in pairs)) for pairs in sectors))
                         for p in group)
    assert len(structures) == 6 and set(structures.values()) == {12}
    for structure in structures:
        pairs = [pair for sector in structure for pair in sector]
        assert len(pairs) == 18 and sum(pairs) == full
        assert sum(pair.bit_count() for pair in pairs) == 36
        assert sector_rank(full, structure) == 21
        assert all(sector_rank(1 << i, structure) == 1 for i in range(36))
        assert all(sector_rank(H | C, structure) == sector_rank(H, structure)
                   for H, C in zip(helpers, cols))
    for row in semantic_rows:
        lhs6 = sum(a*sum(sector_rank(S, structure) for structure in structures)
                   for S, a in row["orbit_coefficients"])
        assert lhs6 <= 6*row["rhs"]

    # The residual mutual helper graph has no triangle.
    mutual = [sum(1 << j for j in range(36) if helpers[cells[i][1]] >> j & 1 and
                  helpers[cells[j][1]] >> i & 1) for i in range(36)]
    assert not any(mutual[i] >> j & 1 and mutual[i] >> k & 1 and mutual[j] >> k & 1
                   for i, j, k in combinations(range(36), 3))

    # Row-order cost is 36 minus the sum of completed lines over prefixes.
    limits = [0, 0, 0, 1, 1, 2, 2, 3, 4]
    for A in range(512):
        if A.bit_count() < 9:
            assert sum(all(A >> p & 1 for p in line) for line in lines) <= limits[A.bit_count()]
    order = [0, 1, 2, 3, 6, 4, 5, 7, 8]
    prefix, counts = 0, []
    for p in order:
        counts.append(sum(all(prefix >> i & 1 for i in line) for line in lines))
        prefix |= 1 << p
    assert counts == limits and sum(counts) == 13
    residual_upper = Fraction(rhs_total, certificate["scale"])
    assert certificate["residual_upper"] == str(residual_upper) == "114/5"
    assert certificate["full_upper"] == str(18+residual_upper) == "204/5"
    return dict(status="PASS: exact semantic grid upper certificate",
                scaled_identity="5 h(W) <= 114", residual_upper=str(residual_upper),
                full_upper=str(18+residual_upper), known_residual_lower=21,
                known_full_lower=39, residual_order=36-sum(counts), full_order=54-sum(counts),
                certified_order_gap="1/5", exact_shannon_value="not determined",
                residual_mutual_triangles=0, proof_terms=len(semantic_rows),
                orbit_variables=len(used_orbits), lower_witness_translates=len(structures),
                soft_singleton_coefficient=soft["singleton_coefficient"],
                soft_cell_error_coefficient=soft["cell_error_coefficient"],
                soft_joint_column_error_coefficient=soft["joint_column_error_coefficient"],
                total_correlation_upper=str(Fraction(denominator, cell_errors[0])),
                entropic_total_correlation_lower=str(Fraction(36, 36-21)))


if __name__ == "__main__":
    path = Path(__file__).resolve().with_name("certificate.json")
    print(json.dumps(verify(json.loads(path.read_text())), indent=2))
