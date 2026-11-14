#!/usr/bin/env python3
"""One full Shannon LP on the eight nonloop cells of rho(c)={c,c+1} mod4.

Uses SciPy only to propose a certificate. Every printed bound is subsequently
verified using Fraction arithmetic, including dual feasibility and a primal
witness. No other host is tested; the receipt is written beside this script.
Run from the repository root with SciPy installed:
  python3 lean-backlog/tools/diagonal-calibration/cyclic4_shannon.py
Replay the saved receipt without SciPy using verify_cyclic4_certificate.py.
"""
from fractions import Fraction
from itertools import combinations, permutations
from pathlib import Path
import json


def rat(x):
    return Fraction(float(x)).limit_denominator(1000000)


def coefficients(pairs):
    out = {}
    for i, v in pairs:
        out[i] = out.get(i, 0) + v
    return {i: v for i, v in out.items() if v}


def build():
    d = 4
    rho = [{c, (c + 1) % d} for c in range(d)]
    cells = [(i, c) for c in range(d) for i in range(d) if i not in rho[c]]
    n = len(cells)
    assert n == 8
    full = (1 << n) - 1
    helpers = [sum(1 << j for j, (i, _) in enumerate(cells) if i in rho[c])
               for _, c in cells]
    assert all(not (H >> i & 1) for i, H in enumerate(helpers))
    constraints = []
    for i in range(n):
        constraints.append(({'type': 'singleton', 'i': i}, {1 << i: 1}, 1))
    for S in range(1 << n):
        for i in range(n):
            if not (S >> i & 1):
                constraints.append(({'type': 'monotone', 'i': i, 'S': S},
                                    {S: 1, S | (1 << i): -1}, 0))
        for i, j in combinations([i for i in range(n) if not (S >> i & 1)], 2):
            ij = (1 << i) | (1 << j)
            row = coefficients([(S, 1), (S | ij, 1),
                                (S | (1 << i), -1), (S | (1 << j), -1)])
            constraints.append(({'type': 'submodular', 'i': i, 'j': j, 'S': S}, row, 0))
    equalities = [({'type': 'normalized'}, {0: 1}, 0)]
    for i, H in enumerate(helpers):
        equalities.append(({'type': 'recovery', 'i': i, 'H': H},
                           {H | (1 << i): 1, H: -1}, 0))
    orders = []
    for order in permutations(range(d)):
        pos = {v: i for i, v in enumerate(order)}
        A = [(i, c) for i in range(d) for c in range(d)
             if all(pos[j] < pos[i] for j in rho[c])]
        orders.append((len(A), order, A))
    best = max(orders)
    return cells, helpers, constraints, equalities, best


def main():
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix
    cells, helpers, inequalities, equalities, best = build()
    nvar = 1 << len(cells)
    def matrix(rows):
        ii, jj, vv = [], [], []
        for i, (_, row, _) in enumerate(rows):
            for j, value in row.items():
                ii.append(i); jj.append(j); vv.append(value)
        return csr_matrix((vv, (ii, jj)), shape=(len(rows), nvar), dtype=float)
    c = np.zeros(nvar)
    c[-1] = -1
    result = linprog(c, A_ub=matrix(inequalities),
                     b_ub=[b for _, _, b in inequalities],
                     A_eq=matrix(equalities), b_eq=[b for _, _, b in equalities],
                     bounds=[(None, None)] * nvar, method='highs')
    assert result.success, result.message
    primal = [rat(x) for x in result.x]
    dual = [rat(-x) for x in result.ineqlin.marginals]
    eq_dual = [rat(-x) for x in result.eqlin.marginals]
    assert all(y >= 0 for y in dual)
    for (_, row, rhs), y in zip(inequalities, dual):
        assert sum(coef * primal[j] for j, coef in row.items()) <= rhs
    for _, row, rhs in equalities:
        assert sum(coef * primal[j] for j, coef in row.items()) == rhs
    combined = [Fraction(0)] * nvar
    bound = Fraction(0)
    used = []
    for (name, row, rhs), multiplier in zip(inequalities + equalities, dual + eq_dual):
        if multiplier:
            used.append({'constraint': name, 'multiplier': str(multiplier)})
            for j, coef in row.items():
                combined[j] += multiplier * coef
            bound += multiplier * rhs
    assert combined == [Fraction(0)] * (nvar - 1) + [Fraction(1)]
    assert bound == primal[-1]
    receipt = dict(host='d=4, rho(c)={c,c+1 mod4}',
                   active_cells=cells, helper_masks=helpers, free_loop_cells=8,
                   full_order_bound=16-best[0], largest_row_dag=best[0],
                   attaining_row_order=best[1], selected_cells=best[2],
                   exact_residual_shannon=str(bound), exact_full_shannon=str(8+bound),
                   inequalities=len(inequalities), entropy_variables=nvar,
                   dual_nonzero=len(used), dual=used,
                   primal=[str(x) for x in primal],
                   exact_verification='All primal inequalities, recoveries, dual signs, and exact coefficient identity checked using fractions')
    output = Path(__file__).with_name('cyclic4-shannon-receipt.json')
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k not in ('dual', 'primal')}, indent=2))
    print('DUAL', json.dumps(used, indent=2))


if __name__ == '__main__':
    main()
