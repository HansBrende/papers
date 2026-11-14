#!/usr/bin/env python3
"""Exact row entropies for existing binary diagonal/folded-cube codes.

No solver or numerical tolerances. Inactive coordinates are fixed zero.
Run: python3 row_synergy.py --verify row-synergy-receipt.json
Run without --verify to recompute; --output writes a compact receipt.
Do not disable assertions with -O.
"""
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path


from controls import binary_rank as rank


def kernel_basis(check, n):
    pivots = {}
    for row in check:
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
    generators = []
    for free in range(n):
        if free in pivots:
            continue
        vector = 1 << free
        for p in sorted(pivots):
            if (pivots[p] & vector).bit_count() % 2:
                vector ^= 1 << p
        assert all((row & vector).bit_count() % 2 == 0 for row in check)
        generators.append(vector)
    assert rank(generators) == n - rank(check)
    return generators


def entropies(check, n, row_masks, ambient_cells, loop_cells):
    full = (1 << n) - 1
    assert sum(mask.bit_count() for mask in row_masks) == n
    assert sum(row_masks) == full
    generators = kernel_basis(check, n)
    k, check_rank = len(generators), rank(check)

    def entropy(mask):
        return rank(vector & mask for vector in generators)

    rows = []
    for mask in row_masks:
        rest = full ^ mask
        h_row = entropy(mask)
        residual = k - entropy(rest)
        # Independent parity-check formulations of projection and shortening.
        assert h_row == mask.bit_count() - check_rank + rank(row & rest for row in check)
        assert residual == mask.bit_count() - rank(row & mask for row in check)
        rows.append((h_row, residual))
    row_sum = sum(x[0] for x in rows)
    residual_sum = sum(x[1] for x in rows)
    synergy = 2 * k - row_sum - residual_sum
    # Check the order-based definition, not just the order-free formula.
    before = 0
    ordered_synergies = []
    for mask, (h_row, residual) in zip(row_masks, rows):
        after = full ^ (before | mask)
        h_given_before = entropy(before | mask) - entropy(before)
        h_given_after = entropy(after | mask) - entropy(after)
        ordered_synergies.append(h_given_before + h_given_after - h_row - residual)
        before |= mask
    assert sum(ordered_synergies) == synergy
    assert residual_sum <= loop_cells
    slack = ambient_cells - row_sum
    assert 2 * k == ambient_cells - slack + residual_sum + synergy
    return {
        "active_coordinates": n, "ambient_grid_cells": ambient_cells,
        "dimension": k, "check_rank": check_rank,
        "row_entropies": [x[0] for x in rows],
        "row_residual_entropies": [x[1] for x in rows],
        "row_entropy_sum": row_sum, "row_entropy_slack": slack,
        "row_residual_entropy_sum": residual_sum,
        "active_loop_cells": loop_cells,
        "active_loop_allowance_minus_residual": loop_cells - residual_sum,
        "total_synergy": synergy,
        "synergy_by_increasing_row_order": ordered_synergies,
    }


def incidence_distances(d, T):
    dist = [None] * (2 * d)
    dist[d] = 0  # Column port of 0; row port g represents displacement g.
    queue = deque([d])
    while queue:
        v = queue.popleft()
        side, i = divmod(v, d)
        for t in T:
            u = (1 - side) * d + (i ^ t)
            if dist[u] is None:
                dist[u] = dist[v] + 1
                queue.append(u)
    return dist[:d]


def global_control(case):
    d, T = case["d"], case["T"]
    check = case["whole_binary_check_rows"]
    n = d * d
    assert rank(check) == case["whole_binary_rank"]
    row_masks = [((1 << d) - 1) << (i * d) for i in range(d)]
    result = entropies(check, n, row_masks, n, d * len(T))
    result.update(d=d, T=T, saved_dimension=case["diagonal_dimension"],
                  ambient_host_loop_cells=d * len(T))
    assert result["dimension"] == case["diagonal_dimension"]
    distances = incidence_distances(d, T)
    result["near_three_cells"] = d * sum(t is not None and t <= 3 for t in distances)
    result["diagonals"] = []
    for desc in case["diagonals"]:
        g = desc["g"]
        local = []
        for i in range(d):
            original = check[i * d + (i ^ g)]
            assert all(((q // d) ^ (q % d)) == g
                       for q in range(n) if (original >> q) & 1)
            local.append(sum(((original >> (j * d + (j ^ g))) & 1) << j
                             for j in range(d)))
        # Use d active cells, one per row, with all other grid cells fixed.
        stats = entropies(local, d, [1 << i for i in range(d)], n,
                          d if g in T else 0)
        assert stats["dimension"] == desc["dimension"]
        stats.update(g=g, kind=desc["kind"], incidence_distance=distances[g],
                     ambient_host_loop_cells=d * len(T))
        result["diagonals"].append(stats)
    for key in ("dimension", "row_entropy_sum", "row_residual_entropy_sum", "total_synergy"):
        assert result[key] == sum(s[key] for s in result["diagonals"])
    result["near_three_synergy"] = sum(s["total_synergy"] for s in result["diagonals"]
                                      if s["incidence_distance"] is not None
                                      and s["incidence_distance"] <= 3)
    result["other_diagonal_synergy"] = result["total_synergy"] - result["near_three_synergy"]
    return result


def folded_control(j):
    assert j >= 1 and j % 2 == 1
    n = 1 << (j - 1)
    T = [1 << i for i in range(j - 1)] + [n - 1]
    check = []
    for i in range(n):
        row = 1 << i
        for t in T:
            row ^= 1 << (i ^ t)
        check.append(row)
    assert rank(check) == (n - (1 << ((j - 1) // 2))) // 2
    result = entropies(check, n, [1 << i for i in range(n)], n * n,
                       n if j == 1 else 0)
    distance = incidence_distances(n, T)[0]
    assert distance == j
    triangle = any(a != b and (a ^ b) in T for a in T for b in T if a and b)
    assert triangle == (j == 3)
    result.update(j=j, d=n, T=T, active_diagonal_incidence_distance=distance,
                  ambient_host_loop_cells=n * len(T),
                  active_support_has_triangle=triangle)
    if j >= 3:
        assert result["total_synergy"] == (1 << ((j - 1) // 2))
        assert result["row_entropy_sum"] == n
        assert result["row_residual_entropy_sum"] == 0
    return result


def compact(result):
    host_keys = ("d", "T", "dimension", "row_entropy_sum", "row_entropy_slack",
                 "row_residual_entropy_sum", "total_synergy", "near_three_cells",
                 "near_three_synergy", "other_diagonal_synergy")
    folded_keys = ("j", "d", "dimension", "row_entropy_sum", "row_entropy_slack",
                   "row_residual_entropy_sum", "total_synergy",
                   "active_diagonal_incidence_distance", "active_support_has_triangle")
    return {
        "method": result["method"], "source_sha256": result["source_sha256"],
        "full_hosts": [{key: item[key] for key in host_keys} for item in result["full_hosts"]],
        "folded_diagonal_codes": [{key: item[key] for key in folded_keys}
                                  for item in result["folded_diagonal_codes"]],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify", type=Path)
    args = parser.parse_args()
    source = Path(__file__).with_name("receipt.json")
    raw = source.read_bytes()
    result = compact({
        "method": "Exact GF(2) elimination, generator projections, independent check-matrix shortening, chain-rule crosscheck",
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "full_hosts": [global_control(case) for case in json.loads(raw)],
        "folded_diagonal_codes": [folded_control(j) for j in (1, 3, 5, 7, 9)],
    })
    if args.verify:
        assert result == json.loads(args.verify.read_text()), "Receipt mismatch"
        print("Verified all four full hosts and five folded-diagonal controls.")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    if not args.verify:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
