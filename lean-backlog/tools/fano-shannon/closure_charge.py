#!/usr/bin/env python3
"""Verify the Fano certificate's exact soft-recovery charges; no solver.

From the repository root, with assertions enabled:
  python3 lean-backlog/tools/fano-shannon/closure_charge.py
To regenerate the receipt, pass --output followed by its desired path.
Run verify_certificate.py separately to check the underlying upper proof.
Standard library only; default execution checks the saved receipt.
"""
import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
points = [v for v in product((0, 1), repeat=3) if any(v)]
incident = lambda p, l: sum(x*y for x, y in zip(points[p], points[l])) % 2 == 0
lines = [{p for p in range(7) if incident(p, l)} for l in range(7)]
cells = [(p, l) for p in range(7) for l in range(7) if not incident(p, l)]
cell_index = {cell: i for i, cell in enumerate(cells)}
rows = [sum(1 << i for i, (p, _) in enumerate(cells) if p == r) for r in range(7)]
cols = [sum(1 << i for i, (_, l) in enumerate(cells) if l == c) for c in range(7)]
helpers = [sum(rows[p] for p in L) for L in lines]
FULL = (1 << 28)-1


def derive(S):
    """Each productive step adds its whole column after all helpers are known."""
    assert 0 <= S <= FULL
    start, path = S, []
    while True:
        old = S
        for c, (H, C) in enumerate(zip(helpers, cols)):
            added = C & ~S
            if H & S == H and added:
                path.append(dict(column=c, context=S, added=added))
                S |= added
        if S == old:
            break
    assert all(H & S != H or C & S == C for H, C in zip(helpers, cols))
    used = [step['column'] for step in path]
    assert len(set(used)) == len(used)
    assert set(used) == {c for c, C in enumerate(cols) if C & (S & ~start)}
    assert sum(step['added'].bit_count() for step in path) == (S & ~start).bit_count()
    return S, path


def automorphisms():
    result = set()
    for images in product(points, repeat=3):
        moved = [tuple(sum(v[j]*images[j][i] for j in range(3)) % 2
                       for i in range(3)) for v in points]
        if len(set(moved)) != 7 or (0, 0, 0) in moved:
            continue
        pp = [points.index(v) for v in moved]
        lp = tuple(lines.index({pp[p] for p in L}) for L in lines)
        cp = tuple(cell_index[pp[p], lp[l]] for p, l in cells)
        assert all(incident(p, l) == incident(pp[p], lp[l])
                   for p in range(7) for l in range(7))
        result.add((lp, cp))
    assert len(result) == 168
    return sorted(result)


def build_receipt():
    cert = json.loads((ROOT / 'certificate.json').read_text())
    assert cert['scale'] == 264 and len(cert['terms']) == 33
    entries, singleton_prices = [], []
    weighted_steps = weighted_added = 0
    for i, term in enumerate(cert['terms'], 1):
        kind, args, weight = term['kind'], term['sets'], term['weight']
        assert isinstance(weight, int) and weight > 0
        price = 0
        if kind in ('submodular', 'closed-join-increment'):
            seed = args[0] | args[1]
            if kind == 'closed-join-increment':
                price = args[1] & ~args[0]
        elif kind == 'row-closure-cap':
            S, A = args
            assert 0 <= A < 128
            seed = sum(rows[p] for p in range(7) if A >> p & 1)
            closed, _ = derive(seed)
            price = seed | (S & ~closed)
        elif kind == 'increment':
            singleton_prices.append((weight, args[0] & ~args[1]))
            continue
        else:
            assert kind == 'nonnegative'
            continue
        singleton_prices.append((weight, price))
        end, path = derive(seed)
        if path:
            weighted_steps += weight * len(path)
            weighted_added += weight * (end & ~seed).bit_count()
            entries.append(dict(term=i, kind=kind, weight=weight, seed=seed,
                                closure=end, path=path))
    assert len(entries) == 11
    assert weighted_steps == 902 and weighted_added == 2464
    assert sum(w*S.bit_count() for w, S in singleton_prices) == 4928

    # Check the actual transported charges, not just their average totals.
    joint, individual, prices = Counter(), Counter(), Counter()
    for lp, cp in automorphisms():
        for entry in entries:
            for step in entry['path']:
                joint[lp[step['column']]] += entry['weight']
                for v in range(28):
                    if step['added'] >> v & 1:
                        individual[cp[v]] += entry['weight']
        for weight, S in singleton_prices:
            for v in range(28):
                if S >> v & 1:
                    prices[cp[v]] += weight
    denominator = 264*168
    assert [joint[c] for c in range(7)] == [21648]*7
    assert [individual[v] for v in range(28)] == [14784]*28
    assert [prices[v] for v in range(28)] == [29568]*28
    assert Fraction(21648, denominator) == Fraction(41, 84)
    assert Fraction(14784, denominator) == Fraction(1, 3)
    assert Fraction(29568, denominator) == Fraction(2, 3)
    return dict(scale=264, group_order=168, nonzero_closure_terms=11,
                weighted_column_firings=902, weighted_added_coordinates=2464,
                singleton_coefficient='2/3', per_column_error_coefficient='41/84',
                per_cell_error_coefficient='1/3', transported_denominator=denominator,
                transported_column_charge=21648, transported_cell_charge=14784,
                transported_singleton_price=29568, entries=entries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = build_receipt()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert result == json.loads((ROOT / 'closure-charge-receipt.json').read_text())
    print(json.dumps(dict(status='EXACT PASS', **{k: v for k, v in result.items()
                                                if k != 'entries'}), indent=2))


if __name__ == '__main__':
    main()
