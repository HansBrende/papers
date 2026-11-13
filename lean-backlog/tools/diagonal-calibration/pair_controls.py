"""Independent exact controls for the two-sector GF(2) representation.

The exhaustive enumeration is in two_sector.cpp. This file checks its
expansion convention and all one-sector minima, then deterministic sample
ranks with an independent elimination direction. It does not replace the
exhaustive enumeration or bound general coupling.
"""
import json
import random

T = [1, 2, 4, 8, 15]


def rank(rows):
    rows = rows.copy()
    r = 0
    for j in reversed(range(32)):
        pivot = next((i for i in range(r, len(rows)) if rows[i] >> j & 1), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        for i in range(r + 1, len(rows)):
            if rows[i] >> j & 1:
                rows[i] ^= rows[r]
        r += 1
    return r


def matrix(g, h, masks):
    # Build via the literal whole-row helper test, rather than shifts.
    sectors = [g, h]
    cells = [(column ^ displacement, column)
             for displacement in sectors for column in range(16)]
    rows = []
    for x, (i, c) in enumerate(cells):
        value = 1 << x
        for y, (j, k) in enumerate(cells):
            mask = masks[(x // 16) * 2 + y // 16]
            shift = c ^ j
            if shift in T and mask >> T.index(shift) & 1:
                value ^= 1 << y
        rows.append(value)
    return rows


def expected(g, h, masks):
    rows = []
    for x in range(32):
        c = x % 16
        r = 1 << x
        for sector, displacement in enumerate([g, h]):
            mask = masks[2 * (x // 16) + sector]
            for t, shift in enumerate(T):
                if mask >> t & 1:
                    r ^= 1 << (16 * sector + (c ^ displacement ^ shift))
        rows.append(r)
    return rows


def main():
    random.seed(294)
    receipt = []
    for g, h in [(0, 3), (3, 5), (3, 12)]:
        minima = [min(rank([(1 << x) ^ sum(1 << (x ^ a ^ T[t])
                       for t in range(5) if m >> t & 1)
                       for x in range(16)]) for m in range(32)) for a in [g, h]]
        baseline = sum(minima)
        assert baseline == (10 if g == 0 else 8)
        samples = [(random.randrange(32), random.randrange(32),
                    random.randrange(32), random.randrange(32)) for _ in range(128)]
        for masks in samples:
            a = matrix(g, h, masks)
            assert a == expected(g, h, masks)
            assert rank(a) >= baseline
        receipt.append(dict(pair=[g, h], diagonal_minima=minima,
                            sample_expansion_checks=len(samples)))
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
