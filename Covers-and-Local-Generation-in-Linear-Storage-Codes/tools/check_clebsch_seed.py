#!/usr/bin/env python3
"""Check the exact finite witness used by the rigid-seed lemma.

Usage from the paper directory: python3 tools/check_clebsch_seed.py
Uses only Python's standard library. No solver, floating-point calculation,
download, or generated proof premise is involved. This is not a Lean proof.
"""

import json
from itertools import combinations
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
    return len(pivots)


def main():
    cert = json.loads(Path(__file__).with_name("clebsch-seed-certificate.json").read_text())
    edges = []
    for u, v in combinations(range(16), 2):
        if u ^ v not in {1, 2, 4, 8, 15}:
            continue
        perm = (0, 2, 1) if (u, v) == (0, 1) else (
            (2, 1, 0) if (u, v) == (0, 2) else (0, 1, 2))
        edges.extend((3 * u + a, 3 * v + perm[a]) for a in range(3))
    edges.sort()
    require(len(edges) == len(set(edges)) == 120, "edge count")
    neighbors = [set() for _ in range(48)]
    for u, v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
    require(all(len(ns) == 5 for ns in neighbors), "degree")
    seen, todo = {0}, [0]
    while todo:
        for v in neighbors[todo.pop()]:
            if v not in seen:
                seen.add(v)
                todo.append(v)
    require(len(seen) == 48, "connectedness")
    check = [(1 << u) | sum(1 << v for v in neighbors[u]) for u in range(48)]
    basis = [int(x, 16) for x in cert["kernel_basis_hex"]]
    require(len(basis) == 26 and all(0 <= x < 1 << 48 for x in basis), "basis format")
    require(binary_rank(basis) == 26, "basis independence")
    require(all((row & x).bit_count() % 2 == 0 for row in check for x in basis), "kernel membership")
    require(binary_rank(check) == 22, "full kernel dimension")
    forms = [sum(((((x >> u) & 1) & ((y >> v) & 1)) ^
                  (((x >> v) & 1) & ((y >> u) & 1))) << e
                 for e, (u, v) in enumerate(edges)) for x, y in combinations(basis, 2)]
    ri, ci = cert["minor_row_indices"], cert["minor_column_indices"]
    require(len(ri) == len(set(ri)) == len(ci) == len(set(ci)) == 73, "minor size")
    require(all(0 <= i < 325 for i in ri) and all(0 <= j < 120 for j in ci), "minor indices")
    minor = [sum(((forms[i] >> c) & 1) << j for j, c in enumerate(ci)) for i in ri]
    require(minor == [int(x, 16) for x in cert["minor_rows_hex"]], "literal minor entries")
    inverse = [int(x, 16) for x in cert["inverse_rows_hex"]]
    require(len(inverse) == 73 and all(0 <= x < 1 << 73 for x in inverse), "inverse format")
    for i, row in enumerate(minor):
        product = 0
        for j, invrow in enumerate(inverse):
            if (row >> j) & 1:
                product ^= invrow
        require(product == 1 << i, f"minor-inverse identity, row {i}")
    cuts = [sum(int(v in edge) << e for e, edge in enumerate(edges)) for v in range(48)]
    require(binary_rank(cuts) == 47, "cut dimension")
    require(all((row & cut).bit_count() % 2 == 0 for row in forms for cut in cuts), "cut inclusion")
    print("PASS: 48 vertices, kernel dimension 26, invertible 73-square signing minor, cut dimension 47.")


if __name__ == "__main__":
    main()
