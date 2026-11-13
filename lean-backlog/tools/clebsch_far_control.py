#!/usr/bin/env python3
"""Exact diagonal far-cell control from the folded 5-cube (standard library).

This checks a conditioned far-half counterexample, not the full-array
near-credit conjecture and not a cubic/high-girth example.
"""
import argparse
from collections import Counter, deque
import json
from pathlib import Path


def binary_rref(rows, n):
    rows = list(rows)
    pivots = []
    r = 0
    for col in range(n):
        pivot = next((i for i in range(r, len(rows)) if (rows[i] >> col) & 1), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        for i in range(len(rows)):
            if i != r and ((rows[i] >> col) & 1):
                rows[i] ^= rows[r]
        pivots.append(col)
        r += 1
    return rows[:r], pivots


def kernel_basis(rows, n):
    reduced, pivots = binary_rref(rows, n)
    basis = []
    for free in range(n):
        if free in pivots:
            continue
        v = 1 << free
        for row, pivot in zip(reduced, pivots):
            if (row >> free) & 1:
                v |= 1 << pivot
        assert all((row & v).bit_count() % 2 == 0 for row in rows)
        basis.append(v)
    assert len(binary_rref(basis, n)[0]) == len(basis)
    return basis, pivots


def bfs(adjacency, source):
    dist = [-1]*len(adjacency)
    dist[source] = 0
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in adjacency[u]:
            if dist[v] == -1:
                dist[v] = dist[u]+1
                queue.append(v)
    return dist


def build():
    d, generators = 16, [1, 2, 4, 8, 15]
    neighbors = [sorted(i ^ s for s in generators) for i in range(d)]
    a = [[int(j in neighbors[i]) for j in range(d)] for i in range(d)]
    assert all(len(ns) == 5 for ns in neighbors)
    assert all(a[i][j] == a[j][i] for i in range(d) for j in range(d))
    assert all(a[i][i] == 0 for i in range(d))
    a2 = [[sum(a[i][k]*a[k][j] for k in range(d)) for j in range(d)] for i in range(d)]
    a3 = [[sum(a2[i][k]*a[k][j] for k in range(d)) for j in range(d)] for i in range(d)]
    assert all(a2[i][j] == 3*int(i == j)-2*a[i][j]+2
               for i in range(d) for j in range(d))
    assert all(a3[i][j] == 7*a[i][j]-6*int(i == j)+6
               for i in range(d) for j in range(d))
    host = [[d+j for j in neighbors[i]] for i in range(d)] + [neighbors[j] for j in range(d)]
    distances = [bfs(host, i)[d:] for i in range(d)]
    assert all(distances[i][j] == (5 if i == j else 1 if a[i][j] else 3)
               for i in range(d) for j in range(d))
    far = [[i, j] for i in range(d) for j in range(d) if distances[i][j] >= 5]
    assert far == [[i, i] for i in range(d)]

    # This explicit four-cycle distinguishes the host from the requested
    # cubic girth-ten/twelve subfamily.
    girth_four_cycle = [0, d+1, 3, d+2]
    assert all(v in host[u] for u, v in zip(girth_four_cycle,
                                          girth_four_cycle[1:]+girth_four_cycle[:1]))
    check_rows = [(1 << i) | sum(1 << j for j in neighbors[i]) for i in range(d)]
    basis, pivots = kernel_basis(check_rows, d)
    assert len(pivots) == 6 and len(basis) == 10
    for word in basis:
        for i in range(d):
            assert ((word >> i) & 1) == sum((word >> j) & 1 for j in neighbors[i]) % 2

    # At diagonal far cells the whole-row helper rule is exactly the
    # undirected Clebsch adjacency relation; every helper is mutual.
    assert all(a[j][i] == int(i in neighbors[j]) for i in range(d) for j in range(d))
    pairing = [[i, i ^ 1] for i in range(d) if i < (i ^ 1)]
    assert len(pairing) == 8
    assert sorted(v for pair in pairing for v in pair) == list(range(d))
    assert all(j in neighbors[i] and i in neighbors[j] for i, j in pairing)

    return dict(d=d, forward_window=5, reverse_window=5, generators=generators,
                neighbors=neighbors, bipartite_host_girth=4,
                girth_four_cycle=girth_four_cycle,
                distance_counts_per_row=[dict(sorted(Counter(row).items())) for row in distances],
                row_column_distances=distances, near_cells=240, far_cells=far,
                binary_check_rows=check_rows, binary_rank=6,
                binary_pivot_columns=pivots, binary_kernel_basis=basis,
                far_code_dimension=10, far_pairing_dimension=8, pairing=pairing,
                full_array_coordinates=256, frozen_near_coordinates=240,
                scope='counterexample to conditioned far-half; not to arbitrary-C full-array near-credit bound')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    receipt = build()
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2)+'\n')
    keys = ['d', 'forward_window', 'reverse_window', 'bipartite_host_girth',
            'near_cells', 'binary_rank', 'far_code_dimension', 'far_pairing_dimension']
    print(json.dumps({k: receipt[k] for k in keys}, sort_keys=True))


if __name__ == '__main__':
    main()
