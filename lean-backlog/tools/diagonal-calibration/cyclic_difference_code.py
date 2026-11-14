"""Exact controls for the cyclic two-whole-row difference code.

Standard library; no optimizer, field search, randomness, or file writes.
From the repository root:
  python3 lean-backlog/tools/diagonal-calibration/cyclic_difference_code.py
"""
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path


def graph(d):
    """Return latent vertices and oriented cell edges X[c,r]=z_u-z_v."""
    assert d >= 2
    vertices = [('z', i, j) for i, j in combinations(range(d), 2)]
    vertices += [(kind, i) for kind in ('a', 'b') for i in range(d)]
    index = {v: i for i, v in enumerate(vertices)}

    def pair(i, j):
        assert i != j
        return index['z', min(i, j), max(i, j)]

    edges = {}
    for c in range(d):
        for r in range(d):
            if r == c:
                edges[c, r] = (index['a', c], pair(c, (c+1) % d))
            elif r == (c-1) % d:
                edges[c, r] = (index['b', c], pair(c, (c+1) % d))
            else:
                edges[c, r] = (pair(c, r), pair(c, (r+1) % d))
    return vertices, edges


def graphic_rank(vertex_count, edges):
    parent = list(range(vertex_count))

    def find(v):
        while parent[v] != v:
            v = parent[v]
        return v

    result = 0
    for u, v in edges:
        u, v = find(u), find(v)
        if u != v:
            parent[u] = v
            result += 1
    return result


def decoder(d, c, r):
    """Integral signed paths in permitted rows r,r+1; loops read directly."""
    if c in (r, (r+1) % d):
        return {(c, r): 1}
    delta = (c-r) % d
    first = [(r, (r+j) % d) for j in range(1, delta)]
    second = [((r+1) % d, (r+j) % d) for j in range(delta, d)]
    return {cell: -1 for cell in first+second}


def audit(d):
    vertices, edges = graph(d)
    total = len(vertices)-1
    assert len(edges) == d*d
    assert total == d*(d+3)//2-1
    assert graphic_rank(len(vertices), edges.values()) == total
    for c in range(d):
        row = [edges[c, r] for r in range(d)]
        assert len(set(v for e in row for v in e)) == d+1
        assert graphic_rank(len(vertices), row) == d
    for (c, r), (u, v) in edges.items():
        coefficients = decoder(d, c, r)
        assert all(i in (r, (r+1) % d) for i, _ in coefficients)
        expanded = Counter()
        for cell, coefficient in coefficients.items():
            start, end = edges[cell]
            expanded[start] += coefficient
            expanded[end] -= coefficient
        assert {i: value for i, value in expanded.items() if value} == {u: 1, v: -1}
        if c not in (r, (r+1) % d):
            assert len(coefficients) == d-1
    natural_order = sum(max(r+1, (r+1) % d+1) for r in range(d))
    assert natural_order == total
    return dict(d=d, latent_vertices=len(vertices), coordinate_edges=len(edges),
                rank=total, natural_order_upper=natural_order,
                integral_recoveries_checked=len(edges), group_scope='every finite abelian group')


def compare_cyclic5():
    witness_tools = Path(__file__).resolve().parent
    from verify_cyclic5_rank_witness import witness_values
    receipt = json.loads((witness_tools/'cyclic5-rank-witness.json').read_text())
    cells, _, witness = witness_values(receipt)
    vertices, edges = graph(5)
    residual_edges = [edges[cell] for cell in cells]
    values = []
    for mask in range(1 << len(cells)):
        value = graphic_rank(len(vertices),
                             (e for i, e in enumerate(residual_edges) if mask >> i & 1))
        assert value == witness[mask]
        values.append(value)
    checksum = sha256(','.join(map(str, values)).encode()).hexdigest()
    assert len(values) == 32768 and values[-1] == 9
    return dict(subsets_compared=len(values), mismatches=0, residual_rank=values[-1],
                rank_values_sha256=checksum,
                realization='graphic; linear over every field; entropic for every alphabet size')


if __name__ == '__main__':
    print(json.dumps(dict(status='EXACT PASS', controls=[audit(d) for d in (2, 3, 4, 5, 8)],
                          cyclic5_comparison=compare_cyclic5()), indent=2))
