#!/usr/bin/env python3
"""Exact diagnostics for involutive-product-spaces.md; standard library only.

Run from the repository root:
    python3 lean-backlog/tools/product_space_controls.py

The written proofs are authoritative. These controls check realignment,
the product-rank screen, its one-sided limitation, and small block cases.
They reuse Paper 17's rank routines through involutive_seed_controls.py.
"""
import random

from involutive_seed_controls import identity, load_ops, measure, multiply, realign


def span_dimension(matrices, p, ops):
    return ops.rank_mod([[value for row in a for value in row] for a in matrices], p)


def product_dimension(left, right, p, ops):
    return span_dimension([multiply(a, b, p) for a in left for b in right], p, ops)


def decoder(left, right, p, ops):
    d = len(left[0])
    result = [[0]*(d*d) for _ in range(d*d)]
    for a, b in zip(left, right):
        result = ops.add(result, ops.kron(a, b, p), p)
    return result


def main():
    ops = load_ops()
    rng = random.Random(2026111310)
    checked = 0
    for p in (2, 3, 5, 7):
        # General rank inequality, without assuming involutivity.
        for d in (2, 3, 4):
            for _ in range(3):
                aa = [[[rng.randrange(p) for _ in range(d)] for _ in range(d)] for _ in range(3)]
                bb = [[[rng.randrange(p) for _ in range(d)] for _ in range(d)] for _ in range(3)]
                k = decoder(aa, bb, p, ops)
                t = multiply(ops.swap(d), k, p)
                rank_product = ops.rank_mod(realign(multiply(t, t, p), d), p)
                assert product_dimension(bb, aa, p, ops)+product_dimension(aa, bb, p, ops) <= 9+rank_product
                checked += 1

        # An exact minimal three-term conjugate of the swap.
        for d in (2, 4, 6):
            a, b = ops.unit(d, 0, 1), ops.unit(d, 0, 0)
            aa = [identity(d), b, [[-v % p for v in row] for row in a]]
            bb = [identity(d), a, b]
            k = decoder(aa, bb, p, ops)
            assert measure(k, d, p, ops) == (d*(d+1)//2, 3, True)
            assert product_dimension(aa, bb, p, ops) == product_dimension(bb, aa, p, ops) == 3
            checked += 1

        # A dimension-five mixed product span can generate all Mat_d.
        for d in (3, 4, 5, 7):
            c = [[int(i == (j+1) % d) for j in range(d)] for i in range(d)]
            a = ops.unit(d, 0, 0)
            uu, vv = [identity(d), a, c], [identity(d), a, multiply(a, c, p)]
            assert product_dimension(vv, uu, p, ops) == 5
            assert product_dimension(uu, vv, p, ops) == 6
            powers = [identity(d)]
            for _ in range(d-1):
                powers.append(multiply(powers[-1], c, p))
            units = [multiply(multiply(ci, a, p), cj, p) for ci in powers for cj in powers]
            assert span_dimension(units, p, ops) == d*d
            checked += 1

        # One-sided quadratic-growth theorem: noncommuting 2x2 blocks,
        # arbitrary dense opposite factors, and an attained identity control.
        for m in (1, 2, 3):
            d = 2*m
            x = [[int(i < m and j == i+m) for j in range(d)] for i in range(d)]
            y = [list(row) for row in zip(*x)]
            bb = [identity(d), x, y]
            assert product_dimension(bb, bb, p, ops) == 4
            zero = [[0]*d for _ in range(d)]
            assert measure(decoder([identity(d), zero, zero], bb, p, ops), d, p, ops)[0] == d*(d+1)//2
            for _ in range(4):
                aa = [[[rng.randrange(p) for _ in range(d)] for _ in range(d)] for _ in range(3)]
                assert measure(decoder(aa, bb, p, ops), d, p, ops)[0] <= d*(d+1)//2
                checked += 1

    # The characteristic-two paired-cut inequality can be strict.
    n = ops.unit(2, 0, 1)
    k = ops.add(identity(4), ops.kron(n, n, 2), 2)
    assert measure(k, 2, 2, ops) == (2, 2, True)
    checked += 1
    print(f'{checked} exact product-space and block controls passed.')


if __name__ == '__main__':
    main()
