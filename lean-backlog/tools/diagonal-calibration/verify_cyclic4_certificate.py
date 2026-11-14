#!/usr/bin/env python3
"""Standard-library-only verifier for the one saved cyclic4 Shannon test.

No SciPy, optimizer, search for codes, or file writes. Reconstructs exactly
the 2,824 Shannon inequalities and verifies the saved rational primal/dual.
Also checks the explicit binary entropy function and all-alphabet recovery.
"""
from fractions import Fraction
from pathlib import Path
import json

from cyclic4_shannon import build


def rank(rows):
    basis = {}
    for value in rows:
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
    return len(basis)


def main():
    receipt = json.loads(Path(__file__).with_name('cyclic4-shannon-receipt.json').read_text())
    cells, helpers, inequalities, equalities, best = build()
    assert len(inequalities) == 2824
    assert len(receipt['primal']) == 256
    assert [list(v) for v in cells] == receipt['active_cells']
    assert helpers == receipt['helper_masks']
    primal = list(map(Fraction, receipt['primal']))
    for _, row, rhs in inequalities:
        assert sum(coef * primal[j] for j, coef in row.items()) <= rhs
    for _, row, rhs in equalities:
        assert sum(coef * primal[j] for j, coef in row.items()) == rhs
    rows_by_name = {json.dumps(name, sort_keys=True): (row, rhs, True)
                    for name, row, rhs in inequalities}
    rows_by_name.update({json.dumps(name, sort_keys=True): (row, rhs, False)
                         for name, row, rhs in equalities})
    combined = [Fraction(0)] * 256
    bound = Fraction(0)
    used_names = set()
    for item in receipt['dual']:
        name = json.dumps(item['constraint'], sort_keys=True)
        assert name not in used_names
        used_names.add(name)
        row, rhs, is_inequality = rows_by_name[name]
        multiplier = Fraction(item['multiplier'])
        assert not is_inequality or multiplier >= 0
        for j, coefficient in row.items():
            combined[j] += multiplier * coefficient
        bound += multiplier * rhs
    assert combined == [Fraction(0)] * 255 + [Fraction(1)]
    assert bound == primal[255] == 5
    assert best[0] == 3 and 16 - best[0] == 13
    assert receipt['exact_full_shannon'] == '13'

    # Four pair sums equal z. These generator vectors encode z and the four
    # freely chosen first endpoints over GF(2); over Z/qZ use z-u instead.
    pairs = [(0, 5), (1, 4), (2, 6), (3, 7)]
    generators = [sum(1 << j for _, j in pairs)]
    generators += [(1 << i) | (1 << j) for i, j in pairs]
    assert rank(generators) == 5
    assert all(rank(g & S for g in generators) == primal[S] for S in range(256))
    recovery = []
    for i, H in enumerate(helpers):
        pair = next(pair for pair in pairs if i in pair)
        mate = pair[0] if pair[1] == i else pair[1]
        assert H >> mate & 1
        other = next(pair for pair in pairs if all(H >> j & 1 for j in pair))
        assert i not in other
        recovery.append({'target': i, 'mate': mate, 'pair_revealing_z': other})
    print(json.dumps(dict(exact_residual_shannon=5, free_loops=8,
                          exact_full_shannon_and_all_alphabet_capacity_exponent=13,
                          largest_cell_DAG=3, inequalities_checked=2824,
                          exact_entropy_subsets_checked=256,
                          nonzero_dual_terms=len(receipt['dual']),
                          all_alphabet_recovery=recovery), indent=2))


if __name__ == '__main__':
    main()
