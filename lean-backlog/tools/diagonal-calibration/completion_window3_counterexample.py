"""Exact counterexample to the modified row-closure envelope; no LP/search.

From the repository root:
  python3 lean-backlog/tools/diagonal-calibration/completion_window3_counterexample.py

Standard library only; writes no files. The sole host is d=4, rho(c)=[4] minus {c}.
All 167 nonempty antichains give 49 intersections. Their budgets certify
the envelope on all 2^16 subsets by the short argument below.
"""
from collections import Counter
from itertools import combinations
import json

from row_closure_completion import antichains


def main():
    d = 4
    cells = [(r, c) for r in range(d) for c in range(d)]
    full = (1 << len(cells))-1
    diagonal = sum(1 << i for i, (r, c) in enumerate(cells) if r == c)
    rho = [15 ^ (1 << c) for c in range(d)]
    J = [sum(1 << c for c, H in enumerate(rho) if H & A == H)
         for A in range(1 << d)]
    g = [0]*(1 << d)
    for A in range(1, 1 << d):
        g[A] = min(g[A ^ (1 << i)] + d-J[A ^ (1 << i)].bit_count()
                   for i in range(d) if A >> i & 1)
    assert all(g[A] == [0, 4, 8, 12, 15][A.bit_count()]
               for A in range(1 << d))
    closures = [sum(1 << i for i, (r, c) in enumerate(cells)
                    if A >> r & 1 or J[A] >> c & 1) for A in range(1 << d)]

    def meet(family):
        result = full
        for A in family:
            result &= closures[A]
        return result

    def budget(family):
        result = 0
        for size in range(1, len(family)+1):
            for sub in combinations(family, size):
                union = 0
                for A in sub:
                    union |= A
                result += (1 if size % 2 else -1)*g[union]
        return result

    minima = {}
    count = 0
    for family in antichains(d):
        count += 1
        F, value = meet(family), budget(family)
        minima[F] = min(minima.get(F, value), value)
    assert count == 167 and len(minima) == 49
    clipped = {F: max(0, min(F.bit_count(), value)) for F, value in minima.items()}

    # These finite checks certify h(X)=|X|-1_{X meets the diagonal} everywhere.
    # Every term is >= |X|-1. If X avoids the diagonal, any discounted F
    # has an element outside X and hence gives a term >= |X|. Conversely,
    # the empty set and the diagonal singletons attain the two cases.
    assert clipped[0] == 0
    assert all(value >= F.bit_count()-1 for F, value in clipped.items())
    assert all(F & diagonal for F, value in clipped.items() if value < F.bit_count())
    assert all(clipped[1 << (d*i+i)] == 0 for i in range(d))

    def envelope(X):
        return min(value+(X & ~F).bit_count() for F, value in clipped.items())

    # Human-readable zero-budget certificate for {(0,0)}:
    # families {01,02,03,123} have singleton/pair/triple/full totals
    # 36, 81, 60, 15, giving 36-81+60-15=0.
    singleton_family = (3, 5, 9, 14)
    assert meet(singleton_family) == 1 and budget(singleton_family) == 0
    a, b = 1, 1 << 5
    submod = [envelope(X) for X in (0, a, b, a | b)]
    assert submod == [0, 0, 0, 1]
    H = full ^ 15  # Helper rows 1,2,3 for column 0.
    C = sum(1 << (d*r) for r in range(d))
    recovery = [envelope(H), envelope(H | C)]
    assert recovery == [11, 12]
    assert envelope(full) == g[-1] == 15
    # Actual all-alphabet code: off-diagonal freedom and one diagonal parity.
    def true_rank(X):
        return X.bit_count()-int(X & diagonal == diagonal)
    assert all(true_rank(closures[A]) == g[A] for A in range(1 << d))
    for c in range(d):
        helpers = sum(1 << i for i, (r, _) in enumerate(cells) if r != c)
        column = sum(1 << i for i, (_, col) in enumerate(cells) if col == c)
        assert true_rank(helpers | column) == true_rank(helpers)

    histogram = sorted(Counter((F.bit_count(), value, minima[F])
                               for F, value in clipped.items()).items())
    assert histogram == [((0, 0, -3), 1), ((1, 0, 0), 4), ((2, 2, 2), 6),
                         ((4, 3, 3), 5), ((5, 5, 5), 12), ((7, 6, 6), 4),
                         ((8, 8, 8), 6), ((10, 9, 9), 6), ((13, 12, 12), 4),
                         ((16, 15, 15), 1)]
    print(json.dumps(dict(status='EXACT COUNTEREXAMPLE', d=d, rho_masks=rho,
                          row_budgets_by_size=[0, 4, 8, 12, 15],
                          nonempty_antichains=count, intersection_sets=len(minima),
                          budget_histogram=histogram,
                          all_subsets_formula='|X| - int(X meets the diagonal)',
                          submodularity_values=submod, recovery_values=recovery,
                          top_value=15, true_all_alphabet_capacity_exponent=15), indent=2))


if __name__ == '__main__':
    main()
