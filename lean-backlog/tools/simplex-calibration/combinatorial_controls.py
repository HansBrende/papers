#!/usr/bin/env python3
"""Exact small projective-plane controls; standard library only.

This certifies explicit simplex/pair packings, not arbitrary code capacity.
"""
from itertools import combinations, product
import argparse
import json
from pathlib import Path
import time


# Compact indices in the lexicographically ordered list of nonloop cells.
# Independently checked against the companion plane_controls.py witness.
FANO_PACKING = [
    [2, 4, 18], [0, 6, 22], [1, 9, 12], [3, 19, 20],
    [5, 10, 26], [7, 16, 23], [8, 15, 21], [13, 17, 25],
    [11, 27], [14, 24],
]


def normalized(v, q):
    a = next(x % q for x in v if x % q)
    inv = pow(a, -1, q)
    return tuple((x * inv) % q for x in v)


def dot(v, w, q):
    return sum(a * b for a, b in zip(v, w)) % q


def cross(v, w, q):
    return normalized((v[1]*w[2]-v[2]*w[1], v[2]*w[0]-v[0]*w[2],
                       v[0]*w[1]-v[1]*w[0]), q)


def plane(q):
    pts = sorted({normalized(v, q) for v in product(range(q), repeat=3) if any(v)})
    d = len(pts)
    ids = {v: i for i, v in enumerate(pts)}
    incidence = [[dot(p, l, q) == 0 for l in pts] for p in pts]
    loops = [i*d+j for i in range(d) for j in range(d) if incidence[i][j]]
    nonloops = [i*d+j for i in range(d) for j in range(d) if not incidence[i][j]]
    compact = {v: i for i, v in enumerate(nonloops)}
    triangles = []
    for a, b, c in combinations(range(d), 3):
        opposite = (cross(pts[b], pts[c], q), cross(pts[a], pts[c], q),
                    cross(pts[a], pts[b], q))
        if dot(pts[a], opposite[0], q):
            triangles.append(tuple(sorted((a*d+ids[opposite[0]], b*d+ids[opposite[1]],
                                           c*d+ids[opposite[2]]))))
    triangles = sorted(set(triangles))
    pairs = []
    for a, b in combinations(nonloops, 2):
        p, l = divmod(a, d)
        p2, l2 = divmod(b, d)
        if incidence[p][l2] and incidence[p2][l]:
            pairs.append((a, b))
    masks = [sum(1 << compact[v] for v in t) for t in triangles]
    pair_masks = [sum(1 << compact[v] for v in t) for t in pairs]
    # Multiplication by alpha with alpha^3=alpha+1 gives a Singer action here.
    point_map = [ids[normalized((v[2], v[0]+v[2], v[1]), q)] for v in pts]
    line_map = []
    for l in range(d):
        p, p2 = [i for i in range(d) if incidence[i][l]][:2]
        line_map.append(ids[cross(pts[point_map[p]], pts[point_map[p2]], q)])
    cell_map = {p*d+l: point_map[p]*d+line_map[l] for p in range(d) for l in range(d)}
    assert all(incidence[p][l] == incidence[point_map[p]][line_map[l]]
               for p in range(d) for l in range(d))
    return dict(q=q, d=d, points=pts, incidence=incidence, loops=loops,
                nonloops=nonloops, triangles=triangles, pairs=pairs, masks=masks,
                pair_masks=pair_masks, compact=compact, point_map=point_map,
                line_map=line_map, cell_map=cell_map)


def gf2_nullspace(rows, n):
    piv = {}
    for r in rows:
        while r:
            p = r.bit_length()-1
            if p in piv:
                r ^= piv[p]
            else:
                piv[p] = r
                break
    basis = []
    for f in range(n):
        if f in piv:
            continue
        v = 1 << f
        for p in sorted(piv):
            if (piv[p] & v).bit_count() % 2:
                v |= 1 << p
        assert all((r & v).bit_count() % 2 == 0 for r in rows)
        basis.append(v)
    return basis


def rank_mod(matrix, p):
    a = [[x % p for x in row] for row in matrix]
    rank = 0
    for j in range(len(a[0]) if a else 0):
        pivot = next((i for i in range(rank, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        z = pow(a[rank][j], -1, p)
        a[rank] = [(x*z) % p for x in a[rank]]
        for i in range(rank+1, len(a)):
            z = a[i][j]
            if z:
                a[i] = [(x-z*y) % p for x, y in zip(a[i], a[rank])]
        rank += 1
    return rank


def projector_controls(P):
    q, d = P['q'], P['d']
    projectors = {}
    for cell in P['nonloops']:
        i, j = divmod(cell, d)
        p, line = P['points'][i], P['points'][j]
        scale = pow(dot(p, line, q), -1, q)
        a = [[(scale*x*y) % q for y in line] for x in p]
        assert rank_mod(a, q) == 1
        projectors[cell] = a

    def matrix_sum(cells):
        return [[sum(projectors[v][i][j] for v in cells) % q
                 for j in range(3)] for i in range(3)]

    zero = [[0]*3 for _ in range(3)]
    identity = [[int(i == j) for j in range(3)] for i in range(3)]
    assert matrix_sum(P['nonloops']) == zero
    assert all(matrix_sum(t) == identity for t in P['triangles'])
    cap = len(P['nonloops']) // 3
    # If cap is nonzero in F_q, fewer than three rank-one leftovers cannot
    # sum to -cap I_3. Here q is prime (the script only instantiates 2 and 3).
    improved_cap = cap-int(cap % q != 0)
    return dict(total_projector_sum=zero, simplex_projector_sum=identity,
                counting_triangle_upper=cap, projector_triangle_upper=improved_cap)


def check_clique_code(P, groups):
    """Check the displayed code, not a capacity upper bound for all codes."""
    d, n = P['d'], len(P['nonloops'])
    flat = [v for group in groups for v in group]
    assert len(flat) == n and set(flat) == set(P['nonloops'])
    matrix = [[0]*n for _ in range(n)]
    for group in groups:
        for a in group:
            p, line = divmod(a, d)
            for b in group:
                p2, _ = divmod(b, d)
                assert a == b or P['incidence'][p2][line]
                matrix[P['compact'][a]][P['compact'][b]] = 1
    ranks = {str(p): rank_mod(matrix, p) for p in (2, 3, 5)}
    assert set(ranks.values()) == {len(groups)}
    return dict(groups=groups, exact_ranks_over_prime_fields=ranks,
                number_of_disjoint_checks=len(groups),
                total_code_dimension=d*d-len(groups),
                dimension_upper_for_disjoint_cliques=d*d-(n+2)//3)


def vector_simplex_code(P):
    """One lane per incident triangle; each lane occurs in one parity check."""
    incident = {v: [i for i, t in enumerate(P['triangles']) if v in t]
                for v in P['nonloops']}
    degrees = {len(ts) for ts in incident.values()}
    assert len(degrees) == 1
    delta = degrees.pop()
    checks = [[v*delta+incident[v].index(i) for v in t]
              for i, t in enumerate(P['triangles'])]
    flat = [bit for check in checks for bit in check]
    assert len(flat) == len(set(flat)) == len(P['nonloops'])*delta
    assert set(flat) == {v*delta+lane for v in P['nonloops'] for lane in range(delta)}
    for check in checks:
        for bit in check:
            cell = bit//delta
            _, line = divmod(cell, P['d'])
            for other in check:
                other_cell = other//delta
                other_row, _ = divmod(other_cell, P['d'])
                assert other == bit or P['incidence'][other_row][line]
    total_bits = P['d']**2*delta
    exact_binary_rank = total_bits-len(gf2_nullspace(
        [sum(1 << b for b in check) for check in checks], total_bits))
    assert exact_binary_rank == len(checks)
    return dict(lanes_per_entry=delta, total_base_symbols=total_bits,
                parity_checks=checks, exact_binary_rank=exact_binary_rank,
                all_field_rank_from_disjoint_support=len(checks),
                base_symbol_code_dimension=total_bits-len(checks),
                normalized_entry_dimension_numerator=total_bits-len(checks),
                normalized_entry_dimension_denominator=delta)


def singer_orbits(P):
    triangles = P['triangles']
    masks = P['masks']
    tid = {t: i for i, t in enumerate(triangles)}
    perm = [tid[tuple(sorted(P['cell_map'][v] for v in t))] for t in triangles]
    seen, orbits = set(), []
    for i in range(len(triangles)):
        if i in seen:
            continue
        orbit, j = [], i
        while j not in seen:
            seen.add(j)
            orbit.append(j)
            j = perm[j]
        assert j == i
        union = 0
        disjoint = True
        for j in orbit:
            disjoint &= not bool(union & masks[j])
            union |= masks[j]
        orbits.append(dict(indices=orbit, mask=union, disjoint=disjoint))
    return orbits


def find_packing(masks, n, target, seconds=20):
    """Exact branch search, returning a witness or a completed exhaustive no.

    A vertex is either covered by one selected edge through it or uncovered.
    The latter branch is bounded by the exact remaining uncovered allowance.
    A timeout is not an upper certificate.
    """
    by_vertex = [[i for i, m in enumerate(masks) if (m >> v) & 1] for v in range(n)]
    start = time.monotonic()
    nodes = 0
    dead = set()

    def visit(available, left, chosen):
        nonlocal nodes
        nodes += 1
        if time.monotonic()-start > seconds:
            raise TimeoutError
        if left == 0:
            return chosen
        if available.bit_count() < 3*left:
            return None
        key = (available, left)
        if key in dead:
            return None
        options = None
        selected = None
        bits = available
        while bits:
            bit = bits & -bits
            v = bit.bit_length()-1
            candidates = [i for i in by_vertex[v] if masks[i] & available == masks[i]]
            if options is None or len(candidates) < len(options):
                selected, options = v, candidates
                if not options:
                    break
            bits ^= bit
        for i in options:
            ans = visit(available ^ masks[i], left-1, chosen+[i])
            if ans is not None:
                return ans
        if available.bit_count() > 3*left:
            ans = visit(available ^ (1 << selected), left, chosen)
            if ans is not None:
                return ans
        dead.add(key)
        return None

    try:
        ans = visit((1 << n)-1, target, [])
        return dict(status='witness' if ans is not None else 'exhaustive_no',
                    indices=ans, nodes=nodes, seconds=time.monotonic()-start)
    except TimeoutError:
        return dict(status='timeout', indices=None, nodes=nodes,
                    seconds=time.monotonic()-start)


def audit(q, seconds):
    P = plane(q)
    n = len(P['nonloops'])
    orbits = singer_orbits(P)
    orbit_packing = None
    for r in range(1, 5):
        for subset in combinations([o for o in orbits if o['disjoint']], r):
            if sum(len(o['indices']) for o in subset)*3 != n:
                continue
            union = 0
            good = True
            for o in subset:
                if union & o['mask']:
                    good = False
                    break
                union |= o['mask']
            if good:
                orbit_packing = sum([o['indices'] for o in subset], [])
                break
        if orbit_packing:
            break
    nullspace = gf2_nullspace(P['masks'], n)
    forbidden_one_holes = []
    all_mask = (1 << n)-1
    for hole in range(n):
        target = all_mask ^ (1 << hole)
        witness = next((v for v in nullspace if (target & v).bit_count() % 2), None)
        if witness is not None:
            forbidden_one_holes.append(dict(hole=P['nonloops'][hole],
                                           parity_support=[P['nonloops'][v] for v in range(n)
                                                           if (witness >> v) & 1]))
    search = (dict(status='singer_witness', indices=orbit_packing) if orbit_packing else
              find_packing(P['masks'], n, n//3, seconds))
    receipt = {k: P[k] for k in ('q', 'd', 'points', 'loops', 'nonloops', 'triangles', 'pairs',
                                'point_map', 'line_map')}
    receipt.update(triangle_degree=sorted({sum(bool(m & (1 << v)) for m in P['masks'])
                                          for v in range(n)}),
                   singer_orbit_sizes=[len(o['indices']) for o in orbits],
                   singer_disjoint_orbits=sum(o['disjoint'] for o in orbits),
                   binary_parity_dimension=len(nullspace),
                   forbidden_one_holes=forbidden_one_holes, search=search)
    receipt['projector_controls'] = projector_controls(P)
    if search['indices'] is not None:
        receipt['packing'] = [P['triangles'][i] for i in search['indices']]
        covered = sum((P['masks'][i] for i in search['indices']), 0)
        assert covered.bit_count() == 3*len(search['indices'])
        receipt['uncovered'] = [P['nonloops'][v] for v in range(n) if not (covered >> v) & 1]
    if q == 2:
        groups = [[P['nonloops'][i] for i in group] for group in FANO_PACKING]
        assert all(tuple(sorted(g)) in (P['triangles'] if len(g) == 3 else P['pairs'])
                   for g in groups)
        receipt['maximum_triangle_packing'] = 8
    else:
        groups = receipt['packing']
        receipt['maximum_triangle_packing'] = len(groups)
        receipt['singer_seed_triangles'] = [P['triangles'][o['indices'][0]]
                                           for o in orbits
                                           if set(o['indices']) <= set(search['indices'])]
    receipt['clique_code'] = check_clique_code(P, groups)
    receipt['vector_simplex_code'] = vector_simplex_code(P)
    assert receipt['maximum_triangle_packing'] == receipt['projector_controls']['projector_triangle_upper']
    assert receipt['clique_code']['total_code_dimension'] == receipt['clique_code']['dimension_upper_for_disjoint_cliques']
    summary = {k: receipt[k] for k in ('q', 'd', 'triangle_degree', 'singer_disjoint_orbits',
                                      'binary_parity_dimension', 'maximum_triangle_packing')}
    summary.update(loops=len(P['loops']), nonloops=n, triangles=len(P['triangles']),
                   pairs=len(P['pairs']), forbidden_one_holes=len(forbidden_one_holes),
                   disjoint_clique_dimension=receipt['clique_code']['total_code_dimension'],
                   vector_dimension=(str(receipt['vector_simplex_code']['base_symbol_code_dimension'])
                                     + '/' + str(receipt['vector_simplex_code']['lanes_per_entry'])),
                   search_status=search['status'])
    print(json.dumps(summary, sort_keys=True), flush=True)
    return receipt


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--seconds', type=float, default=20)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    results = [audit(q, args.seconds) for q in (2, 3)]
    if args.output:
        args.output.write_text(json.dumps(results, indent=2)+'\n')
