#!/usr/bin/env python3
"""Check saved Shannon certificates and the coarse-grid control, without search.

Run: python3 lean-backlog/tools/diagonal-calibration/shannon_certificates.py
Uses the neighboring receipt.json; no external dependencies or file writes.
"""
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path


def add(counter, coefficient, *sets):
    for mask in sets:
        if mask:  # h(empty)=0
            counter[mask] += coefficient


def clean(counter):
    return {mask: coefficient for mask, coefficient in counter.items() if coefficient}


def verify(case):
    d, T = case['d'], case['T']
    assert T == [1 << i for i in range(d.bit_length() - 1)]
    order = case['row_order']
    assert sorted(order) == list(range(d))
    pos = {row: j for j, row in enumerate(order)}
    A = sorted((i * d + c for i in range(d) for c in range(d)
                if all(pos[c ^ t] < pos[i] for t in T)),
               key=lambda v: (pos[v // d], v % d))
    assert set(A) == {i * d + c for i, c in case['acyclic_cells']}
    all_variables = (1 << (d * d)) - 1
    Amask = sum(1 << v for v in A)
    Bmask = all_variables ^ Amask
    B = [v for v in range(d * d) if Bmask >> v & 1]

    # Explicit unit-coefficient Shannon dual. Each singleton has h(v)<=1.
    dual = Counter()
    for v in B:
        add(dual, -1, 1 << v)
    # Subadditivity of B, expanded into I(v; earlier B)>=0.
    prefix = 0
    for v in B:
        bit = 1 << v
        add(dual, 1, bit, prefix)
        add(dual, -1, prefix | bit)
        prefix |= bit
    assert prefix == Bmask

    recovery_equalities = Counter()
    for v in A:
        _, c = divmod(v, d)
        H = sum(((1 << d) - 1) << ((c ^ t) * d) for t in T)
        assert H & ~prefix == 0 and not (H >> v & 1)
        bit = 1 << v
        # h(v|H)-h(v|prefix)>=0 by Shannon submodularity, since H<=prefix.
        add(dual, 1, H | bit, prefix)
        add(dual, -1, H, prefix | bit)
        add(recovery_equalities, 1, H | bit)
        add(recovery_equalities, -1, H)
        prefix |= bit
    assert prefix == all_variables
    expected = recovery_equalities.copy()
    add(expected, -1, all_variables)
    assert clean(dual) == clean(expected)
    # Hence the nonnegative sum is |B|-h(V)+sum_v h(v|H_v).
    # Recovery makes the last sum zero, proving h(V)<=|B|.

    # Recheck the existing all-alphabet attainment without using GF(2) rank:
    # independent free loop cells and sum-zero words on pairs or K4s.
    covered = set()
    free = pairs = k4 = dimension = 0
    for diagonal in case['diagonals']:
        g = diagonal['g']
        if diagonal['kind'] == 'loops':
            assert g in T
            cells = {(i, i ^ g) for i in range(d)}
            assert not (cells & covered)
            covered |= cells
            free += d
            dimension += d
        else:
            assert diagonal['kind'] in ('matching', 'K4 partition')
            for part in diagonal['parts']:
                assert len(part) in (2, 4)
                cells = {(i, i ^ g) for i in part}
                assert len(cells) == len(part) and not (cells & covered)
                for i, c in cells:
                    assert all(j in {c ^ t for t in T}
                               for j, _ in cells if j != i)
                covered |= cells
                dimension += len(part) - 1
                pairs += len(part) == 2
                k4 += len(part) == 4
    assert len(covered) == d * d
    assert dimension == len(B) == case['diagonal_dimension']
    assert len(A) == case['row_order_optimum_deficit']
    return dict(d=d, w=len(T), row_order=order,
                selected_cells_by_row=[sum(v // d == row for v in A) for row in order],
                acyclic_cells=len(A), complement_cells=len(B),
                singleton_inequalities=len(B),
                nontrivial_B_subadditivity_inequalities=max(0, len(B) - 1),
                recovery_submodularity_steps=len(A),
                free_loop_cells=free, pair_gadgets=pairs, K4_gadgets=k4,
                all_alphabet_attained_exponent=dimension,
                all_coefficients='unit integers; recovery equalities have coefficient -1')


def verify_coarse(d):
    full = (1 << (d * d)) - 1
    f = lambda k: d * k - k * k // 4
    h = {}
    for a, b in product(range(1 << d), repeat=2):
        cells = sum(1 << (i * d + j) for i in range(d) for j in range(d)
                    if (a >> i) & 1 or (b >> j) & 1)
        value = f((a | b).bit_count())
        assert cells not in h or h[cells] == value
        h[cells] = value
    monotone_pairs = submodular_pairs = 0
    assert h[0] == 0
    for x, hx in h.items():
        assert 0 <= hx <= x.bit_count()
        for y, hy in h.items():
            if x & y == x:
                assert hx <= hy
                monotone_pairs += 1
            assert x | y in h
            if x & y in h:
                assert hx + hy >= h[x | y] + h[x & y]
                submodular_pairs += 1
    for i in range(d):
        row = sum(1 << (i * d + j) for j in range(d))
        col = sum(1 << (j * d + i) for j in range(d))
        assert h[row | col] == h[row]
    return dict(d=d, retained_sets=len(h), monotone_pairs=monotone_pairs,
                submodular_pairs=submodular_pairs, recovery_equalities=d,
                coarse_value=h[full], matching_host_order_bound=d * (d + 1) // 2)


def main():
    raw = Path(__file__).with_name('receipt.json').read_bytes()
    cases = [case for case in json.loads(raw)
             if case['T'] == [1 << i for i in range(case['d'].bit_length() - 1)]]
    assert [case['d'] for case in cases] == [4, 8, 16]
    print(json.dumps(dict(source_sha256=hashlib.sha256(raw).hexdigest(),
                          basis_certificates=[verify(case) for case in cases],
                          coarse_controls=[verify_coarse(d) for d in (3, 4)]), indent=2))


if __name__ == '__main__':
    main()
