#!/usr/bin/env python3
"""Exact controls for two-token-and-oriented-controls.md (standard library).

Run from the repository root:
    python3 lean-backlog/tools/two_token_controls.py

No numerical eigensolver or solver status is used as a proof certificate.
The Paley code is the known Gadouleau--Riis (2011), Example 9 construction.
"""
from collections import Counter, deque
from fractions import Fraction
import json


def binary_rank(rows):
    pivots = {}
    for value in rows:
        while value:
            pivot = value.bit_length() - 1
            if pivot in pivots:
                value ^= pivots[pivot]
            else:
                pivots[pivot] = value
                break
    return len(pivots)


def path_control():
    # B is the path 0-1-2-3-4-5; even vertices are row ports.
    cells = [(i, c) for i in (0, 2, 4) for c in (1, 3, 5)]
    neighbours = {
        x: [y for y in cells if abs(x[0] - y[1]) == 1
            and abs(y[0] - x[1]) == 1]
        for x in cells
    }
    start = (0, 5)
    assert neighbours[start] == [(4, 1)]
    walk = [(0, 5), (4, 1), (2, 3), (2, 3), (4, 1), (0, 5)]
    assert all(y in neighbours[x] for x, y in zip(walk, walk[1:]))
    distance = {(start, 0): 0}
    queue = deque([(start, 0)])
    while queue:
        x, parity = queue.popleft()
        for y in neighbours[x]:
            state = (y, 1 - parity)
            if state not in distance:
                distance[state] = distance[(x, parity)] + 1
                queue.append(state)
    assert distance[(start, 1)] == 5
    return dict(endpoint_degree=1, shortest_odd_closed_walk=5,
                simple_cycle_through_endpoint=False)


def paley_control():
    helpers = [{(i + s) % 7 for s in (1, 2, 4)} for i in range(7)]
    assert all(i not in helpers[i] for i in range(7))
    assert all(i not in helpers[j] for i in range(7) for j in helpers[i])
    rows = [(1 << i) | sum(1 << j for j in helpers[i]) for i in range(7)]
    assert binary_rank(rows) == 3
    words = [x for x in range(128) if all((r & x).bit_count() % 2 == 0
                                         for r in rows)]
    assert len(words) == 16
    assert Counter(x.bit_count() for x in words) == {0: 1, 3: 7, 4: 7, 7: 1}
    for x in words:
        for i in range(7):
            assert ((x >> i) & 1) == sum((x >> j) & 1 for j in helpers[i]) % 2
    # This recovery order works for arbitrary deterministic nonlinear codes.
    known = {3, 4, 5, 6}
    for i in (2, 1, 0):
        assert helpers[i] <= known
        known.add(i)
    assert known == set(range(7))
    return dict(vertices=7, oriented=True, binary_rank=3, binary_dimension=4,
                all_alphabet_upper="q^4", attained_alphabets="q=2^b, b>=1")


def spectral_control():
    d, shifts = 13, {0, 1, 3, 9}
    w = len(shifts)
    incidence = [[int((r - c) % d in shifts) for c in range(d)] for r in range(d)]
    assert all(sum(row) == w for row in incidence)
    assert all(sum(incidence[r][c] for r in range(d)) == w for c in range(d))
    gram = [[sum(incidence[r][k] * incidence[s][k] for k in range(d))
             for s in range(d)] for r in range(d)]
    assert all(gram[r][s] == 3 * int(r == s) + 1
               for r in range(d) for s in range(d))
    mutual = [[incidence[r][k] * incidence[j][c] for j in range(d) for k in range(d)]
              for r in range(d) for c in range(d)]
    assert all(sum(row) == w * w for row in mutual)
    assert all(mutual[i][j] == mutual[j][i] for i in range(d * d) for j in range(d * d))
    loops = sum(mutual[i][i] for i in range(d * d))
    assert loops == 52
    singular_upper = Fraction(7, 16)
    assert Fraction(3, 16) <= singular_upper ** 2
    fraction = (1 - singular_upper) / (2 - singular_upper)
    assert fraction == Fraction(9, 25)
    cost = d * d * fraction
    ceiling = (cost.numerator + cost.denominator - 1) // cost.denominator
    assert ceiling == 61
    return dict(cells=d * d, gram="3I+J", singular_upper=str(singular_upper),
                bipartizing_deletion_at_least=ceiling, looped_cells=loops,
                additional_deletions_at_least=ceiling - loops)


if __name__ == "__main__":
    print(json.dumps(dict(path=path_control(), paley=paley_control(),
                          spectral=spectral_control()), indent=2))
