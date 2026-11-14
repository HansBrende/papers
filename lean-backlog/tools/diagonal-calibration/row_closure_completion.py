"""Audit the row-closure completion on cyclic five; exact arithmetic, no LP.

From the repository root:
  python3 lean-backlog/tools/diagonal-calibration/row_closure_completion.py

Checks all nonempty antichain presentations. Rank domination on every
intersection and envelope equality on the defining cyclic flats certify
equality on all full-grid subsets by the proof in row spread, section 26.4.
Standard library only; writes no files.
"""
from itertools import combinations
from pathlib import Path
import json

from verify_cyclic5_rank_witness import witness_values


def antichains(n):
    """Every nonempty antichain of subsets of [n], exactly once."""
    def extend(chosen, candidates):
        for j, A in enumerate(candidates):
            new = chosen + (A,)
            yield new
            remaining = [B for B in candidates[j+1:]
                         if (A & B) != A and (A & B) != B]
            yield from extend(new, remaining)
    yield from extend((), list(range(1 << n)))


def main():
    d = 5
    cells = [(r, c) for r in range(d) for c in range(d)]
    full = (1 << len(cells))-1
    rho = [(1 << c) | (1 << ((c+1) % d)) for c in range(d)]
    J = [sum(1 << c for c, H in enumerate(rho) if H & A == H)
         for A in range(1 << d)]
    g = [0]*(1 << d)
    for A in range(1, 1 << d):
        g[A] = min(g[A ^ (1 << i)] + d - J[A ^ (1 << i)].bit_count()
                   for i in range(d) if A >> i & 1)
    by_size = [0, 5, 10, 14, 17, 19]
    assert all(g[A] == by_size[A.bit_count()] for A in range(1 << d))
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

    # Fixed obstructions: the empty intersection and a nonempty one.
    assert meet((1, 2)) == meet((1, 2, 4)) == 0
    assert budget((1, 2)) == 0 and budget((1, 2, 4)) == -1
    collision = meet((6, 11))
    assert collision == meet((11, 14, 22)) and collision.bit_count() == 8
    assert budget((6, 11)) == 7 and budget((11, 14, 22)) == 8

    receipt = json.loads(Path(__file__).with_name('cyclic5-rank-witness.json').read_text())
    residual_cells, flats, rank = witness_values(receipt)
    positions = [cells.index(cell) for cell in residual_cells]
    loops = full ^ sum(1 << i for i in positions)

    def project(F):
        return sum(1 << j for j, i in enumerate(positions) if F >> i & 1)

    def embed(S):
        return sum(1 << i for j, i in enumerate(positions) if S >> j & 1)

    def full_rank(F):
        return (F & loops).bit_count() + rank[project(F)]

    minima = {}
    count = negative = nonempty_negative = 0
    for family in antichains(d):
        count += 1
        F, value = meet(family), budget(family)
        minima[F] = min(minima.get(F, value), value)
        negative += value < 0
        nonempty_negative += bool(F) and value < 0
    assert count == 7580 and len(minima) == 919
    assert negative == 1450 and nonempty_negative == 0
    clipped = {F: max(0, min(F.bit_count(), value)) for F, value in minima.items()}

    def envelope(X):
        return min(value+(X & ~F).bit_count() for F, value in clipped.items())

    assert all(value >= full_rank(F) for F, value in clipped.items())
    assert all(embed(F) in minima and envelope(embed(F)) == value
               for F, value in flats.items())
    assert all(full_rank(closures[A]) == g[A] for A in range(1 << d))
    assert full_rank(collision) == 7 and envelope(full) == 19
    # These two envelope tests imply equality everywhere: every budget
    # dominates h, and the envelope agrees on the flats defining h by
    # h(X)=min_F(h(F)+|X\F|). See section 26.4 for both inequalities.
    print(json.dumps(dict(status='EXACT PASS', row_budgets_by_size=by_size,
                          nonempty_antichains=count, intersection_sets=len(minima),
                          negative_presentations=negative,
                          nonempty_negative_presentations=nonempty_negative,
                          nonempty_collision_budgets=[7, 8],
                          cyclic_flats_embedded_and_matched=len(flats),
                          rank_domination_checks=len(clipped), full_value=19,
                          all_full_subsets_equal_witness='by finite envelope certificate'), indent=2))


if __name__ == '__main__':
    main()
