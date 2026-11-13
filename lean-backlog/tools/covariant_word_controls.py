#!/usr/bin/env python3
"""Exact D8 controls: scalar-monomial baselines and Cayley distance.

Only standard-library arithmetic is used. Keep this file beside
twisted_a5_controls.py. Run with --output receipt.json for full certificates;
the default prints a compact summary without writing a file.
"""

from collections import Counter, deque
from itertools import combinations
from math import factorial
from pathlib import Path
import json
import argparse

from twisted_a5_controls import (make_a5, bounded_local_census, compose, inverse,
                                 cycles, permutation_module, matrix_rank, difference,
                                 identity, mmul)


def bfs(generators, starts):
    distance = {g: 0 for g in starts}
    words = {g: [] for g in starts}
    queue = deque(starts)
    while queue:
        g = queue.popleft()
        for label, s in generators:
            h = compose(g, s)
            if h not in distance:
                distance[h] = distance[g]+1
                words[h] = words[g]+[label]
                queue.append(h)
    # The distance function is certified by the BFS construction and the
    # one-step inequalities on every edge, independently of shortest words.
    for g in distance:
        for _, s in generators:
            assert distance[compose(g, s)] <= distance[g]+1
    return distance, words


def cycle_lengths(g):
    seen, lengths = set(), []
    for i in range(len(g)):
        if i in seen:
            continue
        j, length = i, 0
        while j not in seen:
            seen.add(j)
            length += 1
            j = g[j]
        lengths.append(length)
    return tuple(sorted(lengths, reverse=True))


def standard_max_eigenmultiplicity(g):
    """Characteristic-zero multiplicity, via the permutation cycle lengths."""
    lengths = cycle_lengths(g)
    candidates = [(len(lengths)-1, 1)]
    candidates += [(sum(length % q == 0 for length in lengths), q)
                   for q in range(2, len(g)+1)]
    return max(candidates)[0]


def scalar_monomial_baseline(elements, n, multiplicity):
    """Twice the exact baseline; keep odd n arithmetic integral."""
    return sum(max(n, 2*multiplicity(g)) for g in elements)


def distance_census_a5():
    instance = make_a5()
    elements = instance["elements"]
    e, a, b = (elements[i] for i in instance["sigma"])
    sym = [("a", a), ("b", b), ("B", inverse(b))]
    directed = sym[:2]
    de, we = bfs(sym, [e])
    ds, _ = bfs(sym, [e, a, b])
    dss, _ = bfs(sym, [e, a, b, inverse(b)])
    dd, _ = bfs(directed, [e, a, b])
    sectors = {}
    for n in (4, 5):
        census = bounded_local_census(instance, n)
        action = elements if n == 4 else instance["action6"]
        baseline2 = sum(max(n, 2*standard_max_eigenmultiplicity(g)) for g in action)
        assert baseline2 == 2*census["identity_pairing_total"]
        gains = []
        for orbit in census["orbits"]:
            if orbit["attained_local"] <= orbit["identity_pairing"]:
                continue
            gs = [elements[i] for i in orbit["indices"]]
            gains.append({**orbit, "distance_from_identity": [de[g] for g in gs],
                          "symmetric_distance_from_Sigma": [ds[g] for g in gs],
                          "symmetric_distance_from_symmetric_Sigma": [dss[g] for g in gs],
                          "directed_distance_from_Sigma": [dd[g] for g in gs],
                          "shortest_symmetric_words": [we[g] for g in gs]})
        sectors[str(n)] = {"scalar_monomial_baseline": census["identity_pairing_total"],
                            "attained_local_total": census["attained_local_total"], "gains": gains}
    return {"symmetric_alphabet": "a,b,b^-1", "directed_alphabet": "a,b",
            "symmetric_diameter": max(de.values()),
            "distance_histogram": dict(sorted(Counter(de.values()).items())),
            "sectors": sectors}


def double_transpositions(m):
    e = tuple(range(m))
    result = set()
    for i, j, k, l in combinations(range(m), 4):
        for pairs in (((i,j),(k,l)), ((i,k),(j,l)), ((i,l),(j,k))):
            p = list(e)
            for r, s in pairs:
                p[r], p[s] = p[s], p[r]
            result.add(tuple(p))
    return sorted(result)


def a7_control():
    m, n = 7, 6
    e = tuple(range(m))
    a = (1, 0, 3, 2, 4, 5, 6)
    b = tuple(list(range(1,m))+[0])
    sym = [("a", a), ("b", b), ("B", inverse(b))]
    de, we = bfs(sym, [e])
    assert len(de) == factorial(m)//2
    ds, _ = bfs(sym, [e, a, b])
    dss, _ = bfs(sym, [e, a, b, inverse(b)])
    dd, wd = bfs(sym[:2], [e])
    dds, _ = bfs(sym[:2], [e,a,b])
    elements = sorted(de)
    a_matrix = permutation_module(a)
    helper_rank = matrix_rank([sum(mat, ()) for mat in
                               (identity(n), a_matrix, permutation_module(b))])
    assert helper_rank == 3
    records = []
    for t in double_transpositions(m):
        g = compose(a, t)
        if g == inverse(g):
            continue
        gi = inverse(g)
        u, ui, tm = map(permutation_module, (g, gi, t))
        assert mmul(u, ui) == identity(n)
        r1, r2 = difference(u, a_matrix), difference(ui, a_matrix)
        assert r1 == mmul(a_matrix, difference(tm, identity(n)))
        assert r2 == mmul(difference(tm, identity(n)), a_matrix)
        assert matrix_rank(r1) == matrix_rank(r2) == 2
        maxmult = standard_max_eigenmultiplicity(g)
        baseline = max(n, 2*maxmult)
        nullity = 2*n-4
        records.append({"t": cycles(t), "g": cycles(g), "g_inverse": cycles(gi),
                        "permutation_t": t, "permutation_g": g,
                        "cycle_type_g": cycle_lengths(g),
                        "identity_distance": [de[g], de[gi]],
                        "symmetric_distance_from_Sigma": [ds[g], ds[gi]],
                        "symmetric_distance_from_symmetric_Sigma": [dss[g], dss[gi]],
                        "directed_distance_from_identity": [dd[g], dd[gi]],
                        "directed_distance_from_Sigma": [dds[g], dds[gi]],
                        "shortest_symmetric_words": [we[g], we[gi]],
                        "shortest_directed_words": [wd[g], wd[gi]],
                        "maximum_eigenmultiplicity": maxmult,
                        "scalar_monomial_pair_baseline": baseline,
                        "helper_pair_nullity": nullity,
                        "gain_over_scalar_monomial": nullity-baseline,
                        "A": a_matrix, "U": u, "U_inverse": ui,
                        "residual_ranks": [matrix_rank(r1), matrix_rank(r2)]})
    positive = [r for r in records if r["gain_over_scalar_monomial"] > 0]
    positive.sort(key=lambda r:(min(r["symmetric_distance_from_symmetric_Sigma"]),
                               min(r["symmetric_distance_from_Sigma"]),r["g"]),reverse=True)
    witness = next(r for r in positive if r["t"] == "(1 6)(2 3)")
    assert min(witness["symmetric_distance_from_symmetric_Sigma"]) == max(
        min(r["symmetric_distance_from_symmetric_Sigma"]) for r in positive)
    # Explicit normal-space faithfulness certificate: no nonidentity element
    # acts by a scalar in the standard representation.
    for g in elements:
        mat = permutation_module(g)
        scalar = all(mat[i][j] == (mat[0][0] if i == j else 0)
                     for i in range(n) for j in range(n))
        assert scalar == (g == e)
    baseline2 = scalar_monomial_baseline(elements, n, standard_max_eigenmultiplicity)
    assert baseline2 % 2 == 0
    baseline = baseline2//2
    types = {}
    for g in elements:
        key = str(cycle_lengths(g))
        if key not in types:
            types[key] = {"count":0,"maximum_eigenmultiplicity":standard_max_eigenmultiplicity(g)}
        types[key]["count"] += 1
    # Count each inverse pair once for the compatible patches. Every g from
    # the involution construction has inverse a*(a*t*a), also in this list.
    seen = set()
    simultaneous_gain = 0
    positive_pair_count = 0
    for r in positive:
        g = tuple(r["permutation_g"])
        if g in seen:
            continue
        seen.update((g,inverse(g)))
        simultaneous_gain += r["gain_over_scalar_monomial"]
        positive_pair_count += 1
    return {"group_order": len(elements), "helper_space_dimension": helper_rank,
            "Sigma": [cycles(x) for x in (e,a,b)],
            "symmetric_alphabet": "a,b,b^-1", "directed_alphabet": "a,b",
            "symmetric_diameter": max(de.values()), "directed_diameter": max(dd.values()),
            "symmetric_distance_histogram": dict(sorted(Counter(de.values()).items())),
            "cycle_type_counts": types,
            "noncommuting_double_transpositions": len(records),
            "positive_inverse_pairs": positive_pair_count,
            "global_scalar_monomial_baseline": baseline,
            "global_sector_lower_after_one_far_patch": baseline+witness["gain_over_scalar_monomial"],
            "global_sector_lower_after_all_involution_patches": baseline+simultaneous_gain,
            "farthest_witness": witness,
            "positive_displacement_distance_histogram": dict(sorted(Counter(min(r["symmetric_distance_from_Sigma"])
                                                                            for r in positive).items())),
            "scope": "Attained lower bounds only; no global optimum or full regular-representation gain claimed."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write the full JSON certificate")
    args = parser.parse_args()
    receipt = {"A5": distance_census_a5(), "A7": a7_control()}
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2)+"\n")
    a7 = receipt["A7"]
    summary = {"A5": {"symmetric_diameter": receipt["A5"]["symmetric_diameter"],
                       "sectors": {n: {k:v for k,v in s.items() if k != "gains"}
                                   for n,s in receipt["A5"]["sectors"].items()}},
               "A7": {k:a7[k] for k in ("group_order","helper_space_dimension","Sigma","symmetric_diameter",
                       "directed_diameter","positive_inverse_pairs","global_scalar_monomial_baseline",
                       "global_sector_lower_after_one_far_patch",
                       "global_sector_lower_after_all_involution_patches")},
               "A7_farthest": {k:a7["farthest_witness"][k] for k in
                               ("t","g","identity_distance","symmetric_distance_from_Sigma",
                                "symmetric_distance_from_symmetric_Sigma","residual_ranks",
                                "scalar_monomial_pair_baseline","helper_pair_nullity")}}
    print(json.dumps(summary,indent=2))


if __name__ == "__main__":
    main()
