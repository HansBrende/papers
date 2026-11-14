#!/usr/bin/env python3
"""Independently replay the 33-term Fano Shannon proof, standard library only.

Run: python3 lean-backlog/tools/fano-shannon/verify_certificate.py
Do not disable assertions with -O. No solver or discovery LP is imported.
Every mask, automorphism, recovery closure and integer coefficient is checked.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
certificate = json.loads((ROOT / "certificate.json").read_text())
assert certificate["scale"] == 264
assert certificate["residual_rhs"] == 4928
points = [p for p in product((0, 1), repeat=3) if any(p)]
incident = lambda p, l: sum(x*y for x, y in zip(p, l)) % 2 == 0
lines = [{i for i, p in enumerate(points) if incident(p, l)} for l in points]
cells = [(i, j) for i, p in enumerate(points) for j, l in enumerate(points)
         if not incident(p, l)]
assert len(cells) == 28 and sum(map(len, lines)) == 21
cell_index = {p: i for i, p in enumerate(cells)}
rows = [sum(1 << k for k, (i, _) in enumerate(cells) if i == p) for p in range(7)]
cols = [sum(1 << k for k, (_, j) in enumerate(cells) if j == l) for l in range(7)]
helpers = [sum(rows[p] for p in L) for L in lines]
assert all(H.bit_count() == 12 for H in helpers)
FULL = (1 << len(cells))-1


def closure(S):
    while True:
        T = S
        for H, C in zip(helpers, cols):
            if H & S == H:
                S |= C
        if T == S:
            return S


perms = set()
for basis_images in product(points, repeat=3):
    images = [tuple(sum(v[j]*basis_images[j][i] for j in range(3)) % 2
                    for i in range(3)) for v in points]
    if len(set(images)) != 7 or (0, 0, 0) in images:
        continue
    p = [points.index(v) for v in images]
    ell = [lines.index({p[i] for i in L}) for L in lines]
    perm = tuple(cell_index[p[i], ell[j]] for i, j in cells)
    assert all((i in lines[j]) == (p[i] in lines[ell[j]])
               for i in range(7) for j in range(7))
    perms.add(perm)
assert len(perms) == 168


canonical_cache = {}
def canonical(S):
    if S not in canonical_cache:
        bits = [i for i in range(28) if S >> i & 1]
        canonical_cache[S] = min(sum(1 << perm[i] for i in bits) for perm in perms)
    return canonical_cache[S]


# Only row closures purchased by the certificate are needed; no row-order DP.
seed = {A: closure(sum(rows[p] for p in range(7) if A >> p & 1))
        for A in range(128)}

triangles = []
for P in combinations(range(7), 3):
    if set(P) in lines:
        continue
    T = []
    for p in P:
        opposite = set(P)-{p}
        ell = next(i for i, L in enumerate(lines) if opposite <= L)
        T.append(cell_index[p, ell])
    triangles.append(sum(1 << i for i in T))
assert len(triangles) == 28
triangle_rank3 = lambda S: sum(min(2, (S & T).bit_count()) for T in triangles)
assert triangle_rank3(FULL) == 56

combined = Counter()
rhs_total = Fraction(0)
semantic_rows = []
for item in certificate["terms"]:
    kind, sets = item["kind"], item["sets"]
    assert isinstance(item["weight"], int)
    mult = Fraction(item["weight"], certificate["scale"])
    assert mult > 0
    terms = []
    if kind == "nonnegative":
        S, = sets
        terms, rhs = [(S, -1)], 0
    elif kind == "row-closure-cap":
        S, A = sets
        assert 0 <= A < 128
        terms, rhs = [(S, 1)], 4*A.bit_count()+(S & ~seed[A]).bit_count()
    elif kind == "submodular":
        S, T = sets
        assert closure(S) == S and closure(T) == T
        terms, rhs = [(S & T, 1), (closure(S | T), 1), (S, -1), (T, -1)], 0
    elif kind == "increment":
        S, T = sets
        terms, rhs = [(S, 1), (T, -1)], (S & ~T).bit_count()
    elif kind == "closed-join-increment":
        S, T = sets
        terms, rhs = [(closure(S | T), 1), (S, -1)], (T & ~S).bit_count()
    else:
        raise AssertionError(kind)
    coefficients = Counter()
    for S, c in terms:
        assert 0 <= S <= FULL and closure(S) == S
        coefficients[canonical(S)] += c
        combined[canonical(S)] += mult*c
    coefficients = {S: c for S, c in coefficients.items() if c}
    # All positive rows must be tight at the explicit triangle-code entropy.
    assert sum(c*triangle_rank3(S) for S, c in coefficients.items()) == 3*rhs
    rhs_total += mult*rhs
    weight = 264*mult
    assert weight.denominator == 1
    semantic_rows.append(dict(kind=kind, masks=sets, weight264=int(weight), rhs=rhs,
                              canonical_coefficients=sorted(coefficients.items())))

combined = {S: a for S, a in combined.items() if a}
assert combined == {FULL: Fraction(1)}, combined
assert rhs_total == Fraction(56, 3)
assert rhs_total+21 == Fraction(119, 3)
assert len(semantic_rows) == 33
output = dict(status="PASS: independently reconstructed semantic dual",
              residual_bound=str(rhs_total), full_bound=str(rhs_total+21),
              scaled_identity="264 h(W) <= 4928",
              rows=semantic_rows,
              scope="Exact upper certificate plus explicit triangle-code matching lower; no optimizer")
assert certificate["residual_bound"] == str(rhs_total)
assert certificate["full_bound"] == str(rhs_total+21)
# Each nonincident cell is in three triangles. Their independent parity
# checks give the matching 3-lane code over every finite cyclic group.
assert all(sum(bool(T >> i & 1) for T in triangles) == 3 for i in range(28))
assert all(all((helpers[cells[i][1]] >> j & 1) for i in range(28) for j in range(28)
               if i != j and T >> i & 1 and T >> j & 1) for T in triangles)
# Exact row-order optimum: the number of completed lines in prefixes of
# size 0,...,6 is bounded by 0,0,0,1,1,2,4, attained starting with one line.
limits = [0,0,0,1,1,2,4]
for A in range(128):
    if A.bit_count() < 7:
        J = sum(all(A >> p & 1 for p in L) for L in lines)
        assert J <= limits[A.bit_count()]
order = sorted(lines[0])+sorted(set(range(7))-lines[0])
prefix = 0
completed = []
for p in order:
    completed.append(sum(all(prefix >> i & 1 for i in L) for L in lines))
    prefix |= 1 << p
assert completed == limits
assert 49-sum(completed) == 41
output["exact_order_bound"] = 41
output["exact_shannon_order_gap"] = "4/3"
print(json.dumps({k: v for k, v in output.items() if k != "rows"}, indent=2))
for row in semantic_rows:
    print(row["weight264"], row["kind"], row["masks"], "rhs", row["rhs"])
