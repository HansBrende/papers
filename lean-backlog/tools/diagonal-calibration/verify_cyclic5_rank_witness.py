"""Exact compact full-Shannon witness; standard library, no LP or file writes.

From the repository root:
  python3 lean-backlog/tools/diagonal-calibration/verify_cyclic5_rank_witness.py

All 32768 subset values are reconstructed from 15 cyclic-flat orbit
representatives. Every elemental Shannon inequality and recovery equality
is checked directly. No matroid representability or code capacity is claimed.
"""
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
import hashlib
import json


def witness_values(receipt):
    d, n = 5, 15
    cells = [((c+k) % d, c) for c in range(d) for k in (2, 3, 4)]
    lookup = {v: i for i, v in enumerate(cells)}
    group = []
    for reflect in (False, True):
        for shift in range(d):
            group.append([lookup[((1-r if reflect else r)+shift) % d,
                                 ((-c if reflect else c)+shift) % d]
                          for r, c in cells])

    def image(mask, perm):
        return sum(1 << perm[i] for i in range(n) if mask >> i & 1)

    assert len({tuple(perm) for perm in group}) == 10
    assert all(sorted(perm) == list(range(n)) for perm in group)
    flats = {}
    orbit_keys = set()
    for mask, rank in receipt['cyclic_flat_orbit_representatives']:
        key = min(image(mask, perm) for perm in group)
        assert key not in orbit_keys
        orbit_keys.add(key)
        for perm in group:
            F = image(mask, perm)
            assert F not in flats or flats[F] == rank
            flats[F] = rank
    assert len(flats) == receipt['cyclic_flat_count'] == 68
    h = [min(rank+(S & ~F).bit_count() for F, rank in flats.items())
         for S in range(1 << n)]
    return cells, flats, h


def main():
    receipt = json.loads(Path(__file__).with_name('cyclic5-rank-witness.json').read_text())
    cells, flats, h = witness_values(receipt)
    n, d = len(cells), 5
    rho = [{c, (c+1) % d} for c in range(d)]
    assert h[0] == 0 and h[-1] == receipt['residual_total'] == 9
    assert all(h[1 << i] <= 1 for i in range(n))
    checked = n
    for S in range(1 << n):
        absent = [i for i in range(n) if not (S >> i & 1)]
        for i in absent:
            assert h[S] <= h[S | (1 << i)]
            checked += 1
        for i, j in combinations(absent, 2):
            assert h[S] + h[S | (1 << i) | (1 << j)] <= h[S | (1 << i)] + h[S | (1 << j)]
            checked += 1
    assert checked == 1_105_935
    for c in range(d):
        H = sum(1 << i for i, (r, _) in enumerate(cells) if r in rho[c])
        C = sum(1 << i for i, (_, col) in enumerate(cells) if col == c)
        assert h[H | C] == h[H]
    # Verify the supplied family really is the complete set of cyclic flats.
    actual = {}
    for S in range(1 << n):
        if (all(h[S | (1 << i)] > h[S] for i in range(n) if not (S >> i & 1))
                and all(h[S ^ (1 << i)] == h[S] for i in range(n) if S >> i & 1)):
            actual[S] = h[S]
    assert actual == flats

    # Independently verify the six-cell DAG and optimal row-order value.
    order = receipt['row_order']
    pos = {r: j for j, r in enumerate(order)}
    dag = [(r, c) for r in range(d) for c in range(d)
           if all(pos[i] < pos[r] for i in rho[c])]
    assert set(dag) == {tuple(v) for v in receipt['dag_cells']} and len(dag) == 6
    row_order_bounds = []
    for order in permutations(range(d)):
        pos = {r: j+1 for j, r in enumerate(order)}
        row_order_bounds.append(sum(max(pos[i] for i in rho[c]) for c in range(d)))
    assert min(row_order_bounds) == 19
    assert receipt['free_loop_count'] == sum(map(len, rho)) == 10
    assert receipt['full_total'] == h[-1]+10 == 25-len(dag) == 19
    checksum = hashlib.sha256(','.join(map(str, h)).encode()).hexdigest()
    print(json.dumps(dict(status='EXACT PASS', entropy_subsets=1 << n,
                          shannon_inequalities=checked, cyclic_flats=len(flats),
                          flat_orbits=len(receipt['cyclic_flat_orbit_representatives']),
                          cyclic_flat_size_rank_counts={f'{size},{rank}': count
                              for (size, rank), count in sorted(Counter(
                                  (F.bit_count(), rank) for F, rank in flats.items()).items())},
                          exact_residual_shannon=h[-1], exact_full_shannon=19,
                          full_order_upper=19, rank_values_sha256=checksum,
                          code_realization='not claimed'), indent=2))


if __name__ == '__main__':
    main()
