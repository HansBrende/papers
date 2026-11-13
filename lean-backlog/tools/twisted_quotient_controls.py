#!/usr/bin/env python3
"""Exact controls for twisted-swap-controls.md; standard library only.

Run: python3 lean-backlog/tools/twisted_quotient_controls.py
Checks the constructive symmetric-block rank formula over GF(2), GF(3),
and GF(5), including zero and odd quotient ranks, and the tensor controls.
These finite checks accompany the written all-field proof, not replace it.
"""

import json
import random


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def sub(a, b, p):
    return [[(x-y) % p for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def mul(a, b, p, columns=None):
    n = len(b[0]) if b else columns
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) % p
             for j in range(n)] for i in range(len(a))]


def kron(a, b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


def rref(a, p):
    a = [[x % p for x in row] for row in a]
    pivots = []
    for j in range(len(a[0])):
        i = len(pivots)
        pivot = next((k for k in range(i, len(a)) if a[k][j]), None)
        if pivot is None:
            continue
        a[i], a[pivot] = a[pivot], a[i]
        inverse = pow(a[i][j], -1, p)
        a[i] = [x*inverse % p for x in a[i]]
        for k in range(len(a)):
            if k != i and a[k][j]:
                coefficient = a[k][j]
                a[k] = [(x-coefficient*y) % p for x, y in zip(a[k], a[i])]
        pivots.append(j)
    return a, pivots


def rank(a, p):
    return len(rref(a, p)[1])


def completion(target, p):
    """Internal-coordinate order: target is a 2 by 2 array of d by d blocks."""
    d = len(target)//2
    quotient = [[(target[i][d+j]-target[d+i][j]) % p
                 for j in range(d)] for i in range(d)]
    reduced, pivots = rref(quotient, p)
    r = len(pivots)
    k = (r+1)//2
    x = [[row[j] for j in pivots] for row in quotient]
    y = reduced[:r]
    assert mul(x, y, p, d) == quotient
    u1 = [row[:k] for row in x]
    u2 = [row[k:] + [0]*(2*k-r) for row in x]
    v1 = y[:k]
    v2 = y[k:] + [[0]*d for _ in range(2*k-r)]
    left = u1 + [[-z % p for z in row] for row in u2]
    right = [a+b for a, b in zip(v2, v1)]
    residual = mul(left, right, p, 2*d)
    decoder = sub(target, residual, p)
    assert rank(residual, p) == k
    assert all(decoder[i][d+j] == decoder[d+i][j]
               for i in range(d) for j in range(d))
    return r


def tensor_control(p, multiplicity):
    # In outer-coordinate order, U and U^-1 are the two swap blocks.
    u, ui = [[1, 1], [0, 1]], [[1, -1], [0, 1]]
    assert mul(u, ui, p) == eye(2)
    tau = [[0, 0, 1, 1], [0, 0, 0, 1],
           [1, -1, 0, 0], [0, 1, 0, 0]]
    decoder = [[-1, 0, 1, 0], [0, 0, 0, 1],
               [1, -1, 0, 0], [-1, 1, 0, -1]]
    for i in range(2):
        for j in range(2):
            assert decoder[2*i][2*j+1] == decoder[2*i+1][2*j]
    residual = sub(tau, decoder, p)
    assert residual == [[1, 0, 0, 1], [0, 0, 0, 0],
                        [0, 0, 0, 0], [1, 0, 0, 1]]
    assert rank(kron(residual, eye(multiplicity)), p) == multiplicity
    # n=2*m, d=2: nullity=3*m, compared with pairing=2*m.
    return {"p": p, "d": 2, "n": 2*multiplicity, "w": 3,
            "nullity": 3*multiplicity, "pairing": 2*multiplicity}


def main():
    rng = random.Random(20261113)
    counts = {}
    controls = []
    for p in (2, 3, 5):
        checked = 0
        for d in range(1, 9):
            for r in range(d+1):
                target = [[rng.randrange(p) for _ in range(2*d)] for _ in range(2*d)]
                for i in range(d):
                    for j in range(d):
                        target[i][d+j] = (target[d+i][j]+int(i == j and i < r)) % p
                assert completion(target, p) == r
                checked += 1
            for _ in range(8):
                completion([[rng.randrange(p) for _ in range(2*d)] for _ in range(2*d)], p)
                checked += 1
        counts[str(p)] = checked
        controls.extend(tensor_control(p, m) for m in (1, 2, 3))
    print(json.dumps({"quotient_completions": counts, "tensor_controls": controls}, indent=2))


if __name__ == "__main__":
    main()
