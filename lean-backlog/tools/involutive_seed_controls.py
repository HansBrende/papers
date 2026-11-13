#!/usr/bin/env python3
"""Exact controls for the written involutive-seed screens; not their proof.

Run from the repository root (standard library only):
    python3 lean-backlog/tools/involutive_seed_controls.py

Reuse Paper 17's Kronecker, swap and finite-field rank routines. Check
non-normal conjugates at pairing, four-term partial swaps above pairing,
and the non-involutive three-term seed. Never infer dimension from trace.
"""
import importlib.util
from pathlib import Path


def load_ops():
    repo = Path(__file__).resolve().parents[2]
    path = repo / ('Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-'
                   'Transposition-on-Tapes/tools/three_term_example.py')
    spec = importlib.util.spec_from_file_location('published_three_term', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def multiply(a, b, p):
    columns = list(zip(*b))
    return [[sum(x*y for x, y in zip(row, column)) % p
             for column in columns] for row in a]


def realign(k, s):
    return [[k[i*s+j][a*s+b] for j in range(s) for b in range(s)]
            for i in range(s) for a in range(s)]


def measure(k, s, p, ops):
    tau = ops.swap(s)
    t = multiply(tau, k, p)
    return (s*s-ops.rank_mod(ops.add(tau, k, p, -1), p),
            ops.rank_mod(realign(k, s), p),
            multiply(t, t, p) == identity(s*s))


def main():
    ops = load_ops()
    count = 0
    for p in (2, 3, 5, 7, 101):
        for s in (2, 4, 5, 6):
            a, b = ops.unit(s, 0, 1), ops.unit(s, 0, 0)
            k = ops.add(identity(s*s), ops.kron(b, a, p), p)
            k = ops.add(k, ops.kron(a, b, p), p, -1)
            assert measure(k, s, p, ops) == (s*(s+1)//2, 3, True)
            count += 1
        for m in (1, 2, 3):
            s = 2*m
            k = [[0]*(s*s) for _ in range(s*s)]
            for i in range(2):
                for j in range(2):
                    # The published kron helper assumes equal local sizes;
                    # construct the rectangular-factor-size lift explicitly.
                    a = [[int(r//m == i and c//m == j and r % m == c % m)
                          for c in range(s)] for r in range(s)]
                    b = [list(row) for row in zip(*a)]
                    k = ops.add(k, ops.kron(a, b, p), p)
            assert measure(k, s, p, ops) == (2*m*(m+1), 4, True)
            count += 1
        s = 3
        pi = [[int(i == j and a == b) for a in range(s) for b in range(s)]
              for i in range(s) for j in range(s)]
        k = ops.add(ops.swap(s), pi, p, -1)
        assert measure(k, s, p, ops) == (8, 3, False)
        count += 1
    print(f'{count} exact involution, Schmidt-rank and kernel-dimension controls passed.')


if __name__ == '__main__':
    main()
