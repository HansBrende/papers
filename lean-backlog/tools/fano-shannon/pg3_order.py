#!/usr/bin/env python3
"""Exact PG(2,3) order/triangle replay; standard library, no optimizer.

Run from the repository root:
    python3 lean-backlog/tools/fano-shannon/pg3_order.py

The geometry and default receipt paths are resolved from this script.
Use --write to regenerate the receipt,
or --receipt FILE to choose another location. Do not disable assertions.
The geometry comes from the existing sibling simplex-calibration tool.
"""
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import importlib.util
from itertools import combinations
import json
from pathlib import Path


def audit():
    source = Path(__file__).resolve().parents[1] / 'simplex-calibration/plane_controls.py'
    spec = importlib.util.spec_from_file_location('plane_controls', source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    data = module.plane(3)
    d, points = data['d'], data['points']
    assert d == 13
    line_masks = [sum(1 << i for i, x in enumerate(points)
                      if sum(a*b for a, b in zip(x, line)) % 3 == 0)
                  for line in points]
    assert all(mask.bit_count() == 4 for mask in line_masks)
    assert all((a & b).bit_count() == 1
               for a, b in combinations(line_masks, 2))
    n_masks = 1 << d
    unhit = [sum(not (mask & line) for line in line_masks)
             for mask in range(n_masks)]
    completed = [sum(mask & line == line for line in line_masks)
                 for mask in range(n_masks)]

    # F(S): best sum of unhit nonempty prefixes in an order of S.
    best, pred = [0] * n_masks, [-1] * n_masks
    # Independent recurrence for min sum of line completion times.
    cost = [0] + [10**9] * (n_masks - 1)
    for mask in range(1, n_masks):
        choices = [i for i in range(d) if mask >> i & 1]
        p = min(choices, key=lambda i: (-best[mask ^ (1 << i)], i))
        pred[mask] = p
        best[mask] = unhit[mask] + best[mask ^ (1 << p)]
        k = mask.bit_count()
        cost[mask] = min(cost[mask ^ (1 << i)]
                         + k * (completed[mask] - completed[mask ^ (1 << i)])
                         for i in choices)
    mask, dp_order = n_masks - 1, []
    while mask:
        p = pred[mask]
        dp_order.append(p)
        mask ^= 1 << p
    dp_order.reverse()
    assert best[-1] == 29 and cost[-1] == 140 == d*d - best[-1]

    # Human-readable geometric optimizer in the affine chart first coordinate=1.
    geometric_points = [(1,1,1), (1,1,2), (1,2,1), (1,2,2),
                        (1,1,0), (1,2,0), (1,0,0), (1,0,1), (1,0,2)]
    geometric_points += [p for p in points if p[0] == 0]
    geometric_order = [points.index(p) for p in geometric_points]
    assert sorted(geometric_order) == list(range(d))
    prefix, profile = 0, []
    for p in geometric_order:
        prefix |= 1 << p
        profile.append(unhit[prefix])
    expected = [9,6,4,3,2,2,1,1,1,0,0,0,0]
    maxima = [max(unhit[mask] for mask in range(n_masks)
                  if mask.bit_count() == k) for k in range(1,d+1)]
    assert profile == maxima == expected and sum(profile) == best[-1]

    position = {p:i for i,p in enumerate(geometric_order)}
    dag = [(p,l) for p,l in data['cells']
           if all(position[p] < position[q] for q in range(d)
                  if line_masks[l] >> q & 1)]
    assert len(dag) == 29
    assert all(position[p] < position[q] for p,l in dag for q,m in dag
               if line_masks[l] >> q & 1)

    triangles = data['triangles']
    degrees = Counter(i for tri in triangles for i in tri)
    assert len(triangles) == 234
    assert set(degrees) == set(range(117)) and set(degrees.values()) == {6}
    assert len(data['cells']) == 117 and len(data['loops']) == 52
    packing_weight = Fraction(1,6)
    assert all(sum(packing_weight for tri in triangles if i in tri) == 1
               for i in range(117))
    residual_code_rate_symbols = 2 * len(triangles) * packing_weight
    assert residual_code_rate_symbols == 78

    # C68's incidence descriptions, on the residual 117 coordinates.
    closures = [sum(1 << i for i,(p,m) in enumerate(data['cells'])
                    if line_masks[l] >> p & 1 or m == l) for l in range(d)]
    triangle_masks = [sum(1 << i for i in tri) for tri in triangles]
    for a,b in combinations(range(d),2):
        meet = closures[a] & closures[b]
        contained = [tri for tri in triangle_masks if meet & tri == tri]
        assert meet.bit_count() == 15 and len(contained) == 9
        union = 0
        for tri in contained:
            union |= tri
        assert union == meet
    for tri, mask in zip(triangles, triangle_masks):
        lines = [data['cells'][i][1] for i in tri]
        assert len(set(lines)) == 3
        assert closures[lines[0]] & closures[lines[1]] & closures[lines[2]] == mask

    return {
        'host': 'PG(2,3), rows points, columns lines, dot-product incidence',
        'method': 'two exact integer subset recurrences, all 8192 masks; no optimizer',
        'points': points,
        'lines': [[i for i in range(d) if mask >> i & 1] for mask in line_masks],
        'all_cells': 169, 'loop_cells': 52, 'residual_cells': 117,
        'maximum_acyclic_size': 29, 'total_order_value': 140,
        'residual_order_value': 88,
        'dp_optimal_point_order': dp_order,
        'geometric_optimal_point_order': geometric_order,
        'geometric_order_points': geometric_points,
        'maximum_unhit_lines_by_prefix_size': maxima,
        'geometric_acyclic_cells': dag,
        'bellman_table_sha256': sha256(json.dumps(best, separators=(',', ':')).encode()).hexdigest(),
        'mutual_triangles': 234, 'triangles_per_residual_cell': 6,
        'uniform_fractional_triangle_weight': '1/6',
        'residual_triangle_code_normalized_dimension': 78,
        'total_triangle_code_normalized_dimension': 130,
        'code_lane_count': 6,
        'binary_total_dimension_with_six_lanes': 780,
        'order_minus_triangle_code': 10,
        'residual_two_line_closure_intersection_size': 15,
        'triangles_in_each_two_line_closure_intersection': 9,
        'triangle_code_entropy_of_that_intersection': '27/2',
        'scope': 'Order/MAIS exact. Triangle packing gives a six-lane code lower bound; '
                 'no PG(2,3) Shannon upper or exact scalar capacity is proved.'
    }


def main():
    if not __debug__:
        raise SystemExit('Run without -O: exact checks use assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path,
                        default=Path(__file__).resolve().with_name('pg3-order-receipt.json'))
    parser.add_argument('--write', action='store_true', help='Regenerate the exact receipt.')
    args = parser.parse_args()
    receipt = json.loads(json.dumps(audit()))
    if args.write:
        args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    else:
        assert json.loads(args.receipt.read_text()) == receipt, 'Receipt mismatch'
    print(json.dumps({k:receipt[k] for k in
                      ('maximum_acyclic_size', 'total_order_value',
                       'residual_order_value', 'mutual_triangles',
                       'triangles_per_residual_cell',
                       'total_triangle_code_normalized_dimension',
                       'order_minus_triangle_code')}, indent=2))


if __name__ == '__main__':
    main()
