#!/usr/bin/env python3
"""Checks of the order bounds for one-class relations and of the lemma on mutual helpers.

A one-class relation of window w on the positions (c, r) of a d x d matrix has maps i_m, j_m on Z/d and
the helpers (i_m(r), c + j_m(r)), 1 <= m <= w.  A set of positions is acyclic if the helper relation has
no directed cycle inside it (a position that is its own helper is a cycle); a storage code over q symbols
has at most q^(d^2 - |A|) elements for every acyclic set A.

Usage:  python3 order_bounds_check.py        (standard library only; about 15 seconds)

Part 1  Ranking lemma.  For every multigraph with n <= 5 vertices and n edges (loops allowed) the ranking
        that repeatedly puts a vertex of least degree on top has cost at most n(n+1)/2 + n - 1, where the
        cost is the sum over the edges of the larger rank.  For n <= 4 the least cost over all rankings is
        computed for every such multigraph; its maximum is n(n+1)/2 + n - 1, so the lemma is sharp there.
Part 2  Rows.  For random relations (d = 3..9, window 1..4) and random rankings phi, the positions with
        phi(c) > max_m phi(i_m(r)) are acyclic and their complement has sum_r max_m phi(i_m(r)) elements.
Part 3  Window two.  The exact least number of positions that meet every cycle (all subsets, d = 3 and 4)
        of random relations of window 2 is at most the cost of the greedy ranking, which is at most
        d(d+1)/2 + d - 1.  Control: with all nine maps at d = 3 the value is 9, above the window-two bound.
Part 4  Columns.  For random relations and random functions psi (ties allowed), the positions with
        psi(r) > max_m psi(c + j_m(r)) are acyclic.  For random d in 20..400, random u, j0, B and offsets
        with u (j - j0) mod d in [-B, B], the set for psi(e) = u (e - j0) mod d has at least
        d^2/2 - 2 (B + gcd(u, d)) d positions.  The same for rows: with a random permutation pi and row
        maps with u (i_m(r) - pi(r) - b0) mod d in [-B, B], the set {phi(c) > max_m phi(i_m(r))} for
        phi(x) = u (x - b0) mod d has at least that many positions.  Control: offsets outside the allowed
        set break the bound in some case.
Part 5  Few offsets.  For random d in 50..3000 and s = 1, 2, 3 random differences, a multiplier
        u <= N^s with all u t mod d within d/N of 0 exists for N = floor(d^(1/(s+1))) (found by search),
        and 2 (floor(d/N) + gcd(u, d)) d <= 6 d^(2 - 1/(s+1)).
Part 6  Mutual helpers.  For random relations, the number of quadruples (p, p', m, m') with p' the m-th
        helper of p and p the m'-th helper of p' equals the sum over types (u, v) of n(u, v) n(v, u), and
        every such p' is (r - u, c + v) for the type (u, v) of (r, m).  For eps = 1/2 and 1, the set T of
        the types (u, v) with n(u, v), n(v, u) >= eps d / (2w) has at most 2 w^2 / eps elements and fewer
        than eps d^2 quadruples have a type outside it.
Part 7  Transitive triangles.  For random relations, some with a planted constant row map, the number of
        quadruples (p, m, m', m'') in which the m'-th helper of p is the m''-th helper of the m-th helper
        of p equals the sum, over (m, m', m'') and x, of |a^-1(x)| |b^-1(x)| with
        a(r) = (i_m'(r), j_m'(r) - j_m(r) - i_m(r)) and b(r') = (i_m''(r'), j_m''(r') - r'), and in every
        quadruple found a(r) = b(r') for the columns r of p and r' of its m-th helper.  The positions that
        are their own helpers number at most w d.  (The size of the set in the last statement of the
        proposition is not tested: at these sizes its bound exceeds d^2.)
Part 8  The two local codes named after the proposition on mutual helpers.  The binary code of length 7
        in which the entry at p is the sum of the entries at p + 1, p + 2, p + 4 (modulo 7) has dimension 4,
        and its helper relation, a tournament, has a transitive triangle; so has the parity code on a
        triangle, of dimension 2.
Part 9  Sharpness.  (i) For the cycle on n vertices, n <= 7, every ranking has cost at least
        n(n+1)/2 + n - 1 (all rankings).  (ii) The relation at d = 3 with (i_1, j_1) = (1,2), (0,1), (0,2)
        and (i_2, j_2) = (2,1), (1,0), (2,0) at r = 0, 1, 2 has six positions that are their own helpers and
        three that help one another; the least hitting set of its cycles has 8 = d(d+1)/2 + d - 1 positions,
        and the 2^8 binary matrices whose entries at the three positions sum to zero form a storage code.
        (iii) For d = 4 and 6, the matrices with X[c][r] = X[r][c] for c - r even and X[c][r] = X[r-1][c+1]
        for c - r odd form a storage code on the relation with helpers (r, c) and (r - 1, c + 1), with
        d^2/2 + d free entries; at d = 4 the least hitting set has exactly 12 positions.  (iv) Whole rows:
        when every position of column r has all positions of the rows r and r + 1 as helpers, the least
        hitting set at d = 4 has 13 = d(d+1)/2 + d - 1 positions.
"""
import itertools
import math
import random


def relation(d, maps):
    return [sorted({i[r] * d + (c + j[r]) % d for (i, j) in maps}) for c in range(d) for r in range(d)]


def is_acyclic(hs, alive):
    alive = set(alive)
    for v in alive:
        if v in hs[v]:
            return False
    indeg = {v: 0 for v in alive}
    out = {v: [w for w in hs[v] if w in alive] for v in alive}
    for v in alive:
        for w in out[v]:
            indeg[w] += 1
    stack = [v for v in alive if indeg[v] == 0]
    seen = 0
    while stack:
        v = stack.pop()
        seen += 1
        for w in out[v]:
            indeg[w] -= 1
            if indeg[w] == 0:
                stack.append(w)
    return seen == len(alive)


def least_hitting(hs):
    """Exact least number of vertices meeting every cycle, by a table over all subsets."""
    n = len(hs)
    mask = [sum(1 << w for w in hs[v]) for v in range(n)]
    acyclic = bytearray(1 << n)
    acyclic[0] = 1
    best = 0
    for s in range(1, 1 << n):
        t = s
        while t:
            low = t & -t
            v = low.bit_length() - 1
            # v may be removed last if none of its helpers lies in s (v itself included)
            if not (mask[v] & s) and acyclic[s ^ low]:
                acyclic[s] = 1
                break
            t ^= low
        if acyclic[s]:
            k = bin(s).count("1")
            if k > best:
                best = k
    return n - best


def greedy_rank(n, edges):
    alive = set(range(n))
    live = [set(e) for e in edges]
    phi = [0] * n
    cost = 0
    for k in range(n, 0, -1):
        deg = {v: 0 for v in alive}
        for e in live:
            if e is not None:
                for v in e:
                    deg[v] += 1
        v = min(alive, key=lambda x: (deg[x], x))
        phi[v] = k
        cost += k * deg[v]
        live = [None if (e is None or v in e) else e for e in live]
        alive.remove(v)
    return phi, cost


def cost_of(phi, edges):
    return sum(max(phi[v] for v in e) for e in edges)


def part1():
    cases = 0
    sharp = {}
    for n in range(1, 6):
        pairs = [(a, b) for a in range(n) for b in range(a, n)]
        worst = 0
        for es in itertools.combinations_with_replacement(pairs, n):
            phi, cost = greedy_rank(n, es)
            assert sorted(phi) == list(range(1, n + 1)) and cost == cost_of(phi, es)
            assert cost <= n * (n + 1) // 2 + n - 1, (n, es, cost)
            cases += 1
            if n <= 4:
                best = min(cost_of(p, es) for p in itertools.permutations(range(1, n + 1)))
                assert best <= cost
                worst = max(worst, best)
        if n <= 4:
            assert worst == n * (n + 1) // 2 + n - 1
            sharp[n] = worst
    print(f"part 1: greedy ranking within the bound on all {cases} multigraphs with n <= 5 vertices and n edges;"
          f" largest optimum for n <= 4: {sharp}")


def rand_maps(d, w, rng):
    return [([rng.randrange(d) for _ in range(d)], [rng.randrange(d) for _ in range(d)]) for _ in range(w)]


def part2():
    rng = random.Random(2)
    n = 0
    for d in range(3, 10):
        for w in range(1, 5):
            for _ in range(40):
                maps = rand_maps(d, w, rng)
                phi = list(range(1, d + 1))
                rng.shuffle(phi)
                A = {c * d + r for c in range(d) for r in range(d) if phi[c] > max(phi[i[r]] for (i, _) in maps)}
                assert is_acyclic(relation(d, maps), A)
                assert d * d - len(A) == sum(max(phi[i[r]] for (i, _) in maps) for r in range(d))
                n += 1
    print(f"part 2: the row set is acyclic with the stated size in {n} random cases")


def rank_value(d, maps):
    return greedy_rank(d, [tuple(sorted({i[r] for (i, _) in maps})) for r in range(d)])[1]


def part3():
    rng = random.Random(3)
    worst = {}
    for d, trials in ((3, 300), (4, 30)):
        w = None
        for t in range(trials):
            maps = rand_maps(d, 2, rng)
            if t % 3 == 0:                      # include the pairing, where the bound is nearly attained
                maps[0] = (list(range(d)), [0] * d)
            v = least_hitting(relation(d, maps))
            rv = rank_value(d, maps)
            assert v <= rv <= d * (d + 1) // 2 + d - 1, (d, maps, v, rv)
            w = v if w is None else max(w, v)
        worst[d] = w
    # control: the table can report values above the window-two bound.  With all d^2 pairs (i, j) as maps
    # every position is its own helper, and every position must be hit.
    d = 3
    full = [([i] * d, [j] * d) for i in range(d) for j in range(d)]
    assert least_hitting(relation(d, full)) == d * d > d * (d + 1) // 2 + d - 1
    print(f"part 3: exact values at window 2 never exceed the greedy ranking cost; largest found {worst}"
          f" (bounds 8 and 13); control with window 9 at d = 3 gives 9")


def centred(x, d):
    x %= d
    return x if 2 * x <= d else x - d


def count_set(d, offs, u, j0):
    psi = [u * (e - j0) % d for e in range(d)]
    return sum(1 for r in range(d) for c in range(d) if psi[r] > max(psi[(c + j) % d] for j in offs[r]))


def part4():
    rng = random.Random(4)
    n = 0
    for d in range(3, 10):
        for w in range(1, 5):
            for _ in range(40):
                maps = rand_maps(d, w, rng)
                psi = [rng.randrange(2 * d) for _ in range(d)]
                A = {c * d + r for c in range(d) for r in range(d)
                     if psi[r] > max(psi[(c + j[r]) % d] for (_, j) in maps)}
                assert is_acyclic(relation(d, maps), A)
                n += 1
    m = 0
    broken = False
    for _ in range(300):
        d = rng.randrange(20, 401)
        u = rng.randrange(1, d)
        g = math.gcd(u, d)
        j0 = rng.randrange(d)
        B = rng.randrange(0, max(1, d // 6))
        allowed = [j for j in range(d) if abs(centred(u * (j - j0), d)) <= B]
        w = rng.randrange(1, 5)
        offs = [[rng.choice(allowed) for _ in range(w)] for _ in range(d)]
        assert count_set(d, offs, u, j0) >= d * d / 2 - 2 * (B + g) * d, (d, u, j0, B)
        # the same count for rows: i_m(r) = pi(r) + b with u (b - b0) mod d in [-B, B]
        pi = list(range(d))
        rng.shuffle(pi)
        phi = [u * (x - j0) % d for x in range(d)]
        top = [max(phi[(pi[r] + j) % d] for j in offs[r]) for r in range(d)]
        rows = sum(1 for c in range(d) for r in range(d) if phi[c] > top[r])
        assert rows >= d * d / 2 - 2 * (B + g) * d, (d, u, j0, B)
        m += 1
        if B < d // 20:
            free = [[rng.randrange(d) for _ in range(4)] for _ in range(d)]
            if count_set(d, free, u, j0) < d * d / 2 - 2 * (B + g) * d:
                broken = True
    assert broken, "control: arbitrary offsets never broke the bound"
    print(f"part 4: the column set is acyclic in {n} random cases; the counts for columns and rows hold in {m} cases;"
          f" control with arbitrary offsets breaks it")


def part5():
    rng = random.Random(5)
    n = 0
    for _ in range(400):
        s = rng.randrange(1, 4)
        d = rng.randrange(50, 3001)
        N = 1
        while (N + 1) ** (s + 1) <= d:
            N += 1
        diffs = [rng.randrange(1, d) for _ in range(s)]
        u = next((u for u in range(1, N ** s + 1) if all(abs(centred(u * t, d)) * N <= d for t in diffs)), None)
        assert u is not None and u < d, (d, s, diffs)
        assert 2 * (d // N + math.gcd(u, d)) * d <= 6 * d ** (2 - 1.0 / (s + 1)) + 1e-6
        n += 1
    print(f"part 5: a multiplier exists and the exponent is within 6 d^(2 - 1/(s+1)) in {n} random cases")


def part6():
    rng = random.Random(6)
    n = 0
    total = 0
    for d in range(3, 12):
        for w in range(1, 5):
            for t in range(20):
                maps = rand_maps(d, w, rng)
                if t % 2 == 0:                  # plant translation-swaps so that mutual helpers occur
                    u, v = rng.randrange(d), rng.randrange(d)
                    maps[0] = ([(r - u) % d for r in range(d)], [v] * d)
                    if w > 1:
                        maps[1] = ([(r - v) % d for r in range(d)], [u] * d)
                types = {}
                for r in range(d):
                    for m, (i, j) in enumerate(maps):
                        types[(r, m)] = ((r - i[r]) % d, j[r])
                count = {}
                for ty in types.values():
                    count[ty] = count.get(ty, 0) + 1
                expected = sum(k * count.get((v, u), 0) for (u, v), k in count.items())
                quads = 0
                for c in range(d):
                    for r in range(d):
                        for m, (i, j) in enumerate(maps):
                            c2, r2 = i[r], (c + j[r]) % d
                            for m2, (i2, j2) in enumerate(maps):
                                if i2[r2] == c and (c2 + j2[r2]) % d == r:
                                    quads += 1
                                    u, v = types[(r, m)]
                                    assert (c2, r2) == ((r - u) % d, (c + v) % d)
                                    assert types[(r2, m2)] == (v, u)
                assert quads == expected, (d, w, quads, expected)
                for eps in (0.5, 1.0):
                    theta = eps / (2 * w)
                    T = {ty for ty, k in count.items()
                         if k >= theta * d and count.get((ty[1], ty[0]), 0) >= theta * d}
                    assert len(T) <= 2 * w * w / eps
                    outside = sum(k * count.get((v, u), 0) for (u, v), k in count.items() if (u, v) not in T)
                    assert outside < eps * d * d, (d, w, eps, outside)
                total += quads
                n += 1
    print(f"part 6: the count of mutual-helper quadruples equals the sum over types in {n} random relations"
          f" ({total} quadruples in all)")


def part7():
    rng = random.Random(7)
    n = 0
    total = 0
    for d in range(3, 11):
        for w in range(1, 4):
            for t in range(15):
                maps = rand_maps(d, w, rng)
                if t % 2 == 0:                  # a constant row map makes transitive triangles frequent
                    row, k = rng.randrange(d), rng.randrange(d)
                    maps[-1] = ([row] * d, [(r + k) % d for r in range(d)])
                expected = 0
                for m, (i, j) in enumerate(maps):
                    for m1, (i1, j1) in enumerate(maps):
                        a = {}
                        for r in range(d):
                            x = (i1[r], (j1[r] - j[r] - i[r]) % d)
                            a[x] = a.get(x, 0) + 1
                        for m2, (i2, j2) in enumerate(maps):
                            for r2 in range(d):
                                expected += a.get((i2[r2], (j2[r2] - r2) % d), 0)
                quads = 0
                loops = 0
                for c in range(d):
                    for r in range(d):
                        if any(i[r] == c and (c + j[r]) % d == r for (i, j) in maps):
                            loops += 1
                        for (i, j) in maps:
                            q = (i[r], (c + j[r]) % d)
                            for (i1, j1) in maps:
                                s_ = (i1[r], (c + j1[r]) % d)
                                for (i2, j2) in maps:
                                    if (i2[q[1]], (q[0] + j2[q[1]]) % d) == s_:
                                        quads += 1
                                        r2 = q[1]
                                        assert ((i1[r], (j1[r] - j[r] - i[r]) % d)
                                                == (i2[r2], (j2[r2] - r2) % d))
                assert quads == expected, (d, w, quads, expected)
                assert loops <= w * d
                total += quads
                n += 1
    print(f"part 7: the count of transitive-triangle quadruples equals the sum over values in {n} random relations"
          f" ({total} quadruples in all); loops number at most w d")


def gf2_rank(rows):
    rows = list(rows)
    rank = 0
    while rows:
        pivot = rows.pop()
        if pivot:
            rank += 1
            low = pivot & -pivot
            rows = [x ^ pivot if x & low else x for x in rows]
    return rank


def has_transitive_triangle(helpers):
    n = len(helpers)
    return any(x in helpers[y] and y in helpers[z] and x in helpers[z]
               for x in range(n) for y in range(n) for z in range(n) if len({x, y, z}) == 3)


def part8():
    ham = [{(p + 1) % 7, (p + 2) % 7, (p + 4) % 7} for p in range(7)]
    checks = [(1 << p) | sum(1 << q for q in ham[p]) for p in range(7)]
    assert 7 - gf2_rank(checks) == 4
    assert all((q in ham[p]) != (p in ham[q]) for p in range(7) for q in range(7) if p != q)   # a tournament
    assert has_transitive_triangle(ham)
    tri = [{1, 2}, {0, 2}, {0, 1}]
    assert 3 - gf2_rank([0b111, 0b111, 0b111]) == 2 and has_transitive_triangle(tri)
    print("part 8: the code of length 7 has dimension 4 on a tournament with a transitive triangle;"
          " the triangle code has dimension 2 and a transitive triangle")


def is_storage_code(d, hs, matrices):
    """Pairwise test: two matrices that agree at the helpers of a position agree at the position."""
    for v in range(d * d):
        seen = {}
        for x in matrices:
            key = tuple(x[h] for h in hs[v])
            if seen.setdefault(key, x[v]) != x[v]:
                return False
    return True


def part9():
    # (i) cycles
    for n in range(1, 8):
        edges = [(k, (k + 1) % n) for k in range(n)]
        best = min(cost_of(p, edges) for p in itertools.permutations(range(1, n + 1)))
        assert best == n * (n + 1) // 2 + n - 1, (n, best)
    # (ii) d = 3
    d = 3
    maps = [([1, 0, 0], [2, 1, 2]), ([2, 1, 2], [1, 0, 0])]
    hs = relation(d, maps)
    loops = [v for v in range(9) if v in hs[v]]
    tri = [v for v in range(9) if v not in loops]
    assert len(loops) == 6 and len(tri) == 3 and all(set(hs[v]) == set(tri) - {v} for v in tri)
    assert least_hitting(hs) == 8 == d * (d + 1) // 2 + d - 1
    code = [x for x in itertools.product(range(2), repeat=9) if sum(x[v] for v in tri) % 2 == 0]
    assert len(code) == 2 ** 8 and is_storage_code(d, hs, code)
    # (iii) even d
    for d in (4, 6):
        ident, zero = list(range(d)), [0] * d
        maps = [(ident, zero), ([(r - 1) % d for r in range(d)], [1] * d)]
        hs = relation(d, maps)
        partner = {}
        for c in range(d):
            for r in range(d):
                partner[c * d + r] = r * d + c if (c - r) % 2 == 0 else ((r - 1) % d) * d + (c + 1) % d
        assert all(partner[partner[v]] == v and partner[v] in hs[v] for v in partner)
        free = sorted(v for v in partner if v <= partner[v])
        assert len(free) == d * d // 2 + d
        rng = random.Random(9)
        sample = []
        for _ in range(4096 if d == 4 else 3000):
            x = [0] * (d * d)
            for v in free:
                x[v] = x[partner[v]] = rng.randrange(2)
            sample.append(tuple(x))
        if d == 4:                                   # all 2^12 matrices of the set
            sample = []
            for bits in itertools.product(range(2), repeat=len(free)):
                x = [0] * 16
                for v, b in zip(free, bits):
                    x[v] = x[partner[v]] = b
                sample.append(tuple(x))
            assert len(set(sample)) == 2 ** 12 and least_hitting(hs) == 12
        assert is_storage_code(d, hs, sample)
    # (iv) whole rows
    d = 4
    hs = [sorted({r * d + e for e in range(d)} | {((r + 1) % d) * d + e for e in range(d)})
          for c in range(d) for r in range(d)]
    assert least_hitting(hs) == 13 == d * (d + 1) // 2 + d - 1
    print("part 9: the cycle is extremal for the ranking lemma (n <= 7); the bound of window two is attained at"
          " d = 3; codes with d^2/2 + d free entries at d = 4, 6; whole rows at d = 4 need 13 positions")


if __name__ == "__main__":
    part1()
    part2()
    part3()
    part4()
    part5()
    part6()
    part7()
    part8()
    part9()
    print("ALL CHECKS PASSED")
