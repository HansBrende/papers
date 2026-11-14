"""Verify the ten-grid code on the generalized quadrangle of order (2, 2).

Run from the repository root:
    python3 lean-backlog/tools/host-probe/gq_grid_control.py

The 15 points are duads of six symbols; the 15 lines are perfect matchings.
The ten unordered 3+3 partitions each select a full-line 3x3 grid. Every
nonincident cell occurs in exactly two grids. The existing integer identity
checker supplies each grid's 21-symbol code, so independent grid sources
give q**210 residual words with two q-symbol lanes per cell, for every q>=2.
This is an exact finite certificate, not a Lean formalization.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
import json

from grid_code_check import check as check_grid_code


def perfect_matchings(vertices):
    if not vertices:
        yield ()
        return
    first, *rest = vertices
    for other in rest:
        remaining = tuple(v for v in rest if v != other)
        for tail in perfect_matchings(remaining):
            yield tuple(sorted(((first, other),) + tail))


def sign_of_permutation(perm):
    return sum(perm[i] > perm[j] for i in range(3) for j in range(i + 1, 3)) % 2


def check():
    points = tuple(combinations(range(6), 2))
    lines = tuple(sorted(perfect_matchings(tuple(range(6)))))
    assert len(points) == len(lines) == 15
    assert all(len(line) == 3 for line in lines)
    assert all(sum(p in line for line in lines) == 3 for p in points)
    assert all(len(set(a) & set(b)) <= 1 for a, b in combinations(lines, 2))
    # The generalized-quadrangle axiom: the unique point on a nonincident
    # line collinear with p is its unique duad disjoint from p.
    assert all(
        sum(not (set(p) & set(q)) for q in line) == 1
        for p in points for line in lines if p not in line
    )
    residual = {(p, line) for p in points for line in lines if p not in line}
    assert len(residual) == 180

    occurrences = Counter()
    grid_count = 0
    for left in combinations(range(6), 3):
        if 0 not in left:  # One representative of every unordered partition.
            continue
        right = tuple(v for v in range(6) if v not in left)
        grid_points = {tuple(sorted((a, b))) for a in left for b in right}
        parallel = [[], []]
        for perm in permutations(range(3)):
            line = tuple(sorted(tuple(sorted((left[i], right[perm[i]])))
                                for i in range(3)))
            assert line in lines
            parallel[sign_of_permutation(perm)].append(line)
        grid_lines = set(parallel[0] + parallel[1])
        assert len(grid_points) == 9 and len(grid_lines) == 6
        assert all(set(line) <= grid_points for line in grid_lines)
        # The two parity classes are the rows and columns of the point grid.
        assert all(not (set(a) & set(b))
                   for family in parallel for a, b in combinations(family, 2))
        grid_coordinates = {}
        for i, horizontal in enumerate(parallel[0]):
            for j, vertical in enumerate(parallel[1]):
                common = set(horizontal) & set(vertical)
                assert len(common) == 1
                grid_coordinates[i, j] = next(iter(common))
        assert set(grid_coordinates.values()) == grid_points
        assert len(set(grid_coordinates.values())) == 9
        assert all(
            (grid_coordinates[i, j] in parallel[0][k]) == (i == k)
            and (grid_coordinates[i, j] in parallel[1][k]) == (j == k)
            for i in range(3) for j in range(3) for k in range(3)
        )
        grid_residual = {(p, line) for p in grid_points for line in grid_lines
                         if p not in line}
        assert len(grid_residual) == 36 and grid_residual <= residual
        occurrences.update(grid_residual)
        grid_count += 1

    assert grid_count == 10
    assert set(occurrences) == residual
    assert set(occurrences.values()) == {2}
    # This checks every integer recovery and parameter-extraction identity
    # once; the incidence identifications above transport it to all ten grids.
    check_grid_code()

    residual_sources = 10 * 21
    incident_cells = 15 * 3
    lanes = 2
    full_sources = residual_sources + lanes * incident_cells
    assert residual_sources == 210 and full_sources == 300
    result = {
        "status": "PASS",
        "points": len(points),
        "lines": len(lines),
        "residual_cells": len(residual),
        "incident_cells": incident_cells,
        "grids": grid_count,
        "grid_sources": 21,
        "lanes_per_residual_cell": lanes,
        "residual_q_symbols": residual_sources,
        "full_q_symbols": full_sources,
        "residual_exponent_in_q_squared_alphabet": residual_sources // lanes,
        "full_exponent_in_q_squared_alphabet": full_sources // lanes,
        "residual_rate": str(Fraction(residual_sources, lanes * len(residual))),
        "full_rate": str(Fraction(full_sources, lanes * len(points) * len(lines))),
        "soft_constant_lower_bound": str(Fraction(
            lanes * len(residual), lanes * len(residual) - residual_sources)),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O: this certificate uses assertions.")
    check()
