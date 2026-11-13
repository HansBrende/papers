#!/usr/bin/env python3
"""Exact rational A5 twisted-swap test instances; no third-party dependencies.

Permutation product p*q means p after q. Matrices act on column vectors.
The 4- and 5-dimensional rational modules are sum-zero permutation modules.
Run this file for exact structural checks and a bounded local-copy census.
"""

from collections import Counter
from itertools import permutations, product
from math import gcd
from functools import reduce
import argparse
import json


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def identity(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def mmul(a, b):
    return tuple(tuple(sum(x*y for x, y in zip(row, col))
                       for col in zip(*b)) for row in a)


def transpose(a):
    return tuple(zip(*a))


def matrix_rank(a):
    """Exact rank over Q by integer elimination with gcd row normalization."""
    if not a:
        return 0
    rows = [list(row) for row in a]
    rank = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        p = rows[rank][col]
        for i in range(rank+1, len(rows)):
            q = rows[i][col]
            if q:
                rows[i] = [p*x-q*y for x, y in zip(rows[i], rows[rank])]
                g = reduce(gcd, rows[i], 0)
                if g:
                    rows[i] = [x//g for x in rows[i]]
        rank += 1
        if rank == len(rows):
            break
    return rank


def flat(a):
    return tuple(x for row in a for x in row)


def difference(a, b):
    return tuple(tuple(x-y for x, y in zip(ar, br)) for ar, br in zip(a, b))


def coefficient_residual(a, basis, numerators, denominator=1):
    """Denominator-cleared residual a - sum(c_s basis_s)."""
    n = len(a)
    return tuple(tuple(denominator*a[i][j]
                       - sum(c*b[i][j] for c, b in zip(numerators, basis))
                       for j in range(n)) for i in range(n))


def permutation_module(p):
    """Restriction to sum-zero, basis e_i - e_last."""
    n = len(p)-1
    return tuple(tuple(int(p[j] == i)-int(p[n] == i)
                       for j in range(n)) for i in range(n))


def order(p):
    e = tuple(range(len(p)))
    q, k = p, 1
    while q != e:
        q, k = compose(q, p), k+1
    return k


def cycles(p):
    unseen = set(range(len(p)))
    result = []
    while unseen:
        start = min(unseen)
        c, x = [], start
        while x in unseen:
            unseen.remove(x)
            c.append(x+1)
            x = p[x]
        if len(c) > 1:
            result.append("("+" ".join(map(str, c))+")")
    return "".join(result) or "e"


def make_a5():
    elements = [p for p in permutations(range(5))
                if sum(p[i] > p[j] for i in range(5) for j in range(i+1, 5)) % 2 == 0]
    index = {p: i for i, p in enumerate(elements)}
    e = tuple(range(5))
    a = (1, 0, 3, 2, 4)  # (1 2)(3 4)
    b = (2, 1, 4, 3, 0)  # (1 3 5)
    multiplication = [[index[compose(p, q)] for q in elements] for p in elements]
    inverses = [index[inverse(p)] for p in elements]
    sigma = [index[p] for p in (e, a, b)]
    reached, queue = {index[e]}, [index[e]]
    while queue:
        g = queue.pop()
        for s in sigma[1:]:
            h = multiplication[g][s]
            if h not in reached:
                reached.add(h)
                queue.append(h)
    assert len(elements) == len(reached) == 60
    subgroups = set()
    for g in elements:
        if order(g) == 5:
            powers, x = [], e
            for _ in range(5):
                powers.append(index[x])
                x = compose(g, x)
            subgroups.add(tuple(sorted(powers)))
    subgroups = sorted(subgroups)
    assert len(subgroups) == 6
    subgroup_index = {h: i for i, h in enumerate(subgroups)}
    actions = []
    for gi in range(60):
        actions.append(tuple(subgroup_index[tuple(sorted(
            multiplication[multiplication[gi][h]][inverses[gi]] for h in subgroup))]
                             for subgroup in subgroups))
    reps = {4: [permutation_module(p) for p in elements],
            5: [permutation_module(p) for p in actions]}
    return {"elements": elements, "index": index, "multiplication": multiplication,
            "inverses": inverses, "sigma": sigma, "reps": reps,
            "sylow5": subgroups, "action6": actions}


def inversion_orbits(instance):
    return [(i,) if i == j else (i, j)
            for i, j in enumerate(instance["inverses"]) if i <= j]


def verify(instance):
    reps = instance["reps"]
    table = instance["multiplication"]
    for n, matrices in reps.items():
        gram = tuple(tuple(1+int(i == j) for j in range(n)) for i in range(n))
        assert matrices[0] == identity(n)
        for i, a in enumerate(matrices):
            assert mmul(a, matrices[instance["inverses"][i]]) == identity(n)
            assert mmul(mmul(transpose(a), gram), a) == gram
            for j, b in enumerate(matrices):
                assert mmul(a, b) == matrices[table[i][j]]
        characters = [sum(a[i][i] for i in range(n)) for a in matrices]
        assert sum(c*c for c in characters) == 60
        assert sum(characters) == 0


def bounded_local_census(instance, n, radius=2, denominator=2):
    """Search individual U_g versus W; only attained lower bounds, no optimum claim.

    For each inversion pair use either ordinary pairing, or two independent W
    approximants to the two off-diagonal U blocks. Fixed points use one W fit.
    All ranks are exact. Coefficients are generated in [-radius,radius]/den.
    Always include the three basis vectors, even for a zero search radius.
    """
    matrices = instance["reps"][n]
    basis = [matrices[s] for s in instance["sigma"]]
    basis_rank = matrix_rank([flat(a) for a in basis])
    assert basis_rank == 3
    coefficients = {((1, 0, 0), 1), ((0, 1, 0), 1), ((0, 0, 1), 1), ((0, 0, 0), 1)}
    for den in range(1, denominator+1):
        for nums in product(range(-radius, radius+1), repeat=3):
            common = reduce(gcd, nums, den)
            coefficients.add((tuple(x//common for x in nums), den//common))
    coefficients = sorted(coefficients, key=lambda x: (sum(abs(v) for v in x[0])/x[1], x[1], x[0]))
    best = []
    for gi, u in enumerate(matrices):
        candidates = []
        for nums, den in coefficients:
            nullity = n-matrix_rank(coefficient_residual(u, basis, nums, den))
            candidates.append((nullity, nums, den))
        max_nullity = max(c[0] for c in candidates)
        winner = next(c for c in candidates if c[0] == max_nullity)
        best.append({"g": gi, "cycles": cycles(instance["elements"][gi]),
                     "nullity": winner[0], "numerators": winner[1], "denominator": winner[2]})
    orbits = []
    pairing_total = local_total = copy_total = 0
    exactly_in_W = [i for i, u in enumerate(matrices)
                    if matrix_rank([flat(a) for a in basis]+[flat(u)]) == basis_rank]
    for orbit in inversion_orbits(instance):
        if len(orbit) == 1:
            g = orbit[0]
            pairing = n-matrix_rank(difference(matrices[g], identity(n)))
            local = best[g]["nullity"]
            copying = n if g in exactly_in_W else pairing
        else:
            pairing = n
            local = max(n, sum(best[g]["nullity"] for g in orbit))
            copying = 2*n if all(g in exactly_in_W for g in orbit) else n
        pairing_total += pairing
        local_total += local
        copy_total += copying
        orbits.append({"indices": orbit, "cycles": [cycles(instance["elements"][g]) for g in orbit],
                       "identity_pairing": pairing, "exact_block_copying": copying,
                       "attained_local": local, "fits": [best[g] for g in orbit]})
    return {"dimension": n, "W_rank": basis_rank, "num_coefficients": len(coefficients),
            "identity_pairing_total": pairing_total, "exact_block_copying_total": copy_total,
            "attained_local_total": local_total, "exactly_in_W": exactly_in_W,
            "characters_by_order": {str(k): sorted({sum(a[i][i] for i in range(n))
                                            for a, p in zip(matrices, instance["elements"]) if order(p) == k})
                                     for k in (1, 2, 3, 5)},
            "orbits": orbits, "best_fits": best}


def numpy_instance(n=4, orthonormal=True, subset=None):
    """Return (tau, W_basis, ordered_group_indices), numpy imported only here.

    A subset must be closed under inversion. Orthonormal=True conjugates all
    representation matrices by the same Cholesky factor of I+J.
    """
    import numpy as np
    instance = make_a5()
    indices = list(range(60)) if subset is None else list(subset)
    location = {g: i for i, g in enumerate(indices)}
    assert len(location) == len(indices)
    assert all(instance["inverses"][g] in location for g in indices)
    matrices = np.array(instance["reps"][n], dtype=float)
    if orthonormal:
        p = np.linalg.cholesky(np.eye(n)+np.ones((n, n))).T
        matrices = np.array([p @ a @ np.linalg.inv(p) for a in matrices])
    tau = np.zeros((n*len(indices), n*len(indices)))
    for i, g in enumerate(indices):
        j = location[instance["inverses"][g]]
        tau[i*n:(i+1)*n, j*n:(j+1)*n] = matrices[g]
    return tau, matrices[instance["sigma"]], indices


def sparse_orbit_witness(instance, census):
    """Sparse (s,row,col,numerator,denominator) entries attaining the census.

    s=0,1,2 indexes (e,a,b), not an arbitrary group element. Each inverse pair
    either retains diagonal identity or uses the two recorded W approximants.
    No interactions between distinct inversion orbits occur.
    """
    entries = []
    for orbit in census["orbits"]:
        indices = orbit["indices"]
        if orbit["attained_local"] > orbit["identity_pairing"]:
            for fit in orbit["fits"]:
                g = fit["g"]
                h = instance["inverses"][g]
                for s, num in enumerate(fit["numerators"]):
                    if num:
                        entries.append((s, g, h, num, fit["denominator"]))
        else:
            entries.extend((0, g, g, 1, 1) for g in indices)
    return sorted(entries)


def shared_triangle_certificate(instance):
    """Actual d^2-coordinate certificate; valid over every field.

    Outside displacement a,b,b^-1: K=I. At a: copy R_a. On (b,b^-1):
    K=[[0,R_b],[-I-R_b,0]]. The sole residual block is I+R_b+R_b^2.
    """
    d = len(instance["elements"])
    table = instance["multiplication"]
    inv = instance["inverses"]
    _, a, b = instance["sigma"]
    binv = inv[b]
    excluded = {a, b, binv}
    assert len(excluded) == 3 and table[a][a] == 0
    assert table[table[b][b]][b] == 0 and binv != b
    outside = {(r, g) for r in range(d) for g in range(d) if g not in excluded}
    seen = set()
    outside_cycles = Counter()
    for v in sorted(outside):
        if v in seen:
            continue
        r, g = v
        w = (table[r][g], inv[g])
        assert w in outside
        assert (table[w[0]][w[1]], inv[w[1]]) == v
        cycle = {v, w}
        seen.update(cycle)
        outside_cycles[len(cycle)] += 1
    assert seen == outside
    bcycles = []
    seen = set()
    for r in range(d):
        if r in seen:
            continue
        cycle = (r, table[r][b], table[table[r][b]][b])
        assert len(set(cycle)) == 3 and table[cycle[2]][b] == r
        seen.update(cycle)
        bcycles.append(cycle)
    assert len(seen) == d
    # Each b-cycle contributes a 3x3 all-ones block to Q, hence rank one
    # in every characteristic. We also check Q over Q directly.
    q = tuple(tuple(sum(int(c == x) for x in (r, table[r][b], table[r][binv]))
                    for c in range(d)) for r in range(d))
    assert matrix_rank(q) == len(bcycles)
    outside_nullity = sum(outside_cycles.values())
    pair_nullity = 2*d-len(bcycles)
    full_nullity = outside_nullity+d+pair_nullity
    sparse_entries = [(0, g, g, 1, 1) for g in range(d) if g not in excluded]
    sparse_entries += [(1, a, a, 1, 1), (2, b, binv, 1, 1),
                       (0, binv, b, -1, 1), (2, binv, b, -1, 1)]
    sector_checks = {}
    for n, matrices in instance["reps"].items():
        baseline = sum(n if len(o) == 2 else n-matrix_rank(difference(matrices[o[0]], identity(n)))
                       for o in inversion_orbits(instance))
        a_gain = matrix_rank(difference(matrices[a], identity(n)))
        b_residual = coefficient_residual(matrices[binv],
                                         [identity(n), matrices[a], matrices[b]], (-1, 0, -1))
        b_gain = n-matrix_rank(b_residual)
        sector_checks[str(n)] = {"identity_baseline": baseline,
                                  "a_gain": a_gain, "b_gain": b_gain,
                                  "shared_construction_nullity": baseline+a_gain+b_gain}
    return {"coordinate_dimension": d*d, "field_scope": "every field",
            "outside_tau_cycles": dict(outside_cycles), "outside_nullity": outside_nullity,
            "a_block_nullity": d, "b_right_cosets": bcycles,
            "b_residual_rank": len(bcycles), "b_pair_nullity": pair_nullity,
            "full_nullity": full_nullity, "identity_nullity": d*(d+1)//2,
            "gain": full_nullity-d*(d+1)//2,
            "sector_checks": sector_checks, "sparse_kappa_entries": sorted(sparse_entries)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="a5_instances_receipt.json")
    parser.add_argument("--radius", type=int, default=2)
    parser.add_argument("--denominator", type=int, default=2)
    args = parser.parse_args()
    instance = make_a5()
    verify(instance)
    report = {"group_order": 60, "sigma": [cycles(instance["elements"][s]) for s in instance["sigma"]],
              "sigma_indices": instance["sigma"], "order_census": dict(Counter(map(order, instance["elements"]))),
              "exact_checks": "all 3600 multiplication identities, inverse and invariant-Gram identities, character inner products",
              "representations": {str(n): bounded_local_census(instance, n, args.radius, args.denominator) for n in (4, 5)},
              "shared_triangle_construction": shared_triangle_certificate(instance)}
    for census in report["representations"].values():
        census["sparse_kappa_entries"] = sparse_orbit_witness(instance, census)
    with open(args.output, "w") as f:
        json.dump(report, f, indent=2)
        f.write("\n")
    print(json.dumps({**{k: v for k, v in report.items() if k not in ("representations", "shared_triangle_construction")},
                      "shared_triangle_construction": {k: v for k, v in report["shared_triangle_construction"].items()
                                                       if k not in ("b_right_cosets", "sparse_kappa_entries")},
                      "representations": {n: {k: v for k, v in r.items() if k not in ("orbits", "best_fits", "sparse_kappa_entries")}
                                          for n, r in report["representations"].items()}}, indent=2))


if __name__ == "__main__":
    main()
