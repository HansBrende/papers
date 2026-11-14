#!/usr/bin/env python3
"""Verify fixed C_p:C_3 sector-code certificates; no search or dependencies.

From the repository root:
    python3 lean-backlog/tools/bounded-sector-controls/check.py

The certificates prove achievable all-alphabet cardinalities, not optimal
capacities. The known components are free coordinates, pairs and triangles.
"""
from collections import Counter, deque
from pathlib import Path
import json


def check(data):
    p, multiplier = data["p"], data["multiplier"]
    d = 3 * p
    elements = [(a, b) for b in range(3) for a in range(p)]
    index = {x: i for i, x in enumerate(elements)}
    assert multiplier != 1 and pow(multiplier, 3, p) == 1

    def mul(i, j):
        a, b = elements[i]
        c, e = elements[j]
        return index[((a + pow(multiplier, b, p) * c) % p, (b + e) % 3)]

    def inv(i):
        a, b = elements[i]
        return index[((-pow(multiplier, (-b) % 3, p) * a) % p, (-b) % 3)]

    # These explicit semidirect products have identity index zero.
    assert all(mul(i, inv(i)) == 0 == mul(inv(i), i) for i in range(d))
    helpers = {0, 1, p}  # identity, translation, dilation
    sectors = [set() for _ in range(d)]
    for g in range(d):
        for s in helpers:
            for t in helpers:
                sectors[g].add(mul(mul(inv(s), inv(g)), inv(t)))
    assert all(g in sectors[h] for g in range(d) for h in sectors[g])

    # Exhaustive shortest odd closed-walk lengths in the sector graph.
    returns = []
    for g in range(d):
        distances = {(g, 0): 0}
        queue = deque([(g, 0)])
        while queue:
            v, parity = queue.popleft()
            for u in sectors[v]:
                state = (u, 1 - parity)
                if state not in distances:
                    distances[state] = distances[v, parity] + 1
                    queue.append(state)
        returns.append(distances.get((g, 1)))
    assert Counter(returns) == {1: 6, 3: d - 6}

    loops = set(data["loop_sectors"])
    triangles = set(data["triangle_sectors"])
    assert loops == {inv(t) for t in helpers} and len(loops) == 3
    assert len(triangles) == 2 and not loops & triangles
    for g in triangles:
        translated = {mul(g, t) for t in helpers}
        mutual = {x for x in translated if inv(x) in translated}
        assert len(mutual) == 2 and 0 not in mutual
        x = min(mutual)
        assert mul(mul(x, x), x) == 0
        assert mutual == {x, inv(x)}
        # The d/3 disjoint triangles each carry a sum-zero q² code.
        cycles = {frozenset((r, mul(r, x), mul(r, mul(x, x)))) for r in range(d)}
        assert len(cycles) == d // 3 and all(len(c) == 3 for c in cycles)
        assert set().union(*cycles) == set(range(d))

    def verify_matching(key, unused):
        edges = data[key]
        assert sorted(v for g, h, _, _ in edges for v in (g, h)) == sorted(unused)
        for g, h, s, t in edges:
            assert g != h and s in helpers and t in helpers
            assert h == mul(mul(inv(s), inv(g)), inv(t))
            voltage = mul(g, s)
            # Right multiplication matches the d cells bijectively and
            # commutes with all left translations: the rule is covariant.
            assert len({mul(r, voltage) for r in range(d)}) == d
            for r in range(d):
                rp = mul(r, voltage)
                c, cp = mul(r, g), mul(rp, h)
                assert rp in {mul(c, u) for u in helpers}
                assert r in {mul(cp, u) for u in helpers}
        return len(edges)

    pairs = verify_matching("pair_matching", set(range(d)) - loops)
    triangle_pairs = verify_matching("triangle_matching", set(range(d)) - loops - triangles)
    pair_dimension = 3 * d + d * pairs
    triangle_dimension = 3 * d + 4 * d // 3 + d * triangle_pairs
    assert pair_dimension == data["expected_pair_dimension"]
    assert triangle_dimension == data["expected_triangle_dimension"]
    assert triangle_dimension == (3 * d * d + 11 * d) // 6
    return dict(d=d, cells=d * d, odd_return_histogram=dict(Counter(returns)),
                pair_dimension=pair_dimension, triangle_dimension=triangle_dimension,
                sector_block_size_at_most=2, alphabet="every finite q>=2")


if __name__ == "__main__":
    data = json.loads(Path(__file__).with_name("instances.json").read_text())
    print(json.dumps([check(row) for row in data], indent=2))
