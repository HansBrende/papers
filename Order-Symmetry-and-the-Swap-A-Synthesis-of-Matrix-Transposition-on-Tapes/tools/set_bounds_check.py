#!/usr/bin/env python3
"""Small-instance checks of Proposition "Two bounds for sets" and of two remarks that go with it.

A recovery relation on the d*d positions of a matrix gives every position a set of helpers.  A set S of
d x d matrices over an alphabet of q symbols is a storage code on it if any two matrices of S that agree
at all helpers of a position agree at that position.  The proposition says:

  (a) if every helper of a position in row c lies in a column j with g(j) > c, then |S| <= q^(sum of g)
      (the form with rows and columns exchanged is this statement for the transposed relation, and is
      not checked separately);
  (b) if every position has exactly one helper f(position), then |S| <= q^(number of cycles of f), and
      for f(c, r) = (pi_J(r), rho_J(r) + c), J the class of c among M classes, |S| <= q^((d^2 + M d)/2).

Both are instances of the acyclic-set bound: |S| <= q^|I| when the relation has no directed cycle (loops
included) outside the set I.  The key step of the proofs, "two codewords that agree on I are equal", uses
the two words only, and it holds for all pairs exactly when the relation is acyclic outside I.  The script
does the following.

  1. d = 2, q = 2, every one of the 16^4 recovery relations, exact largest code (a largest clique of the
     graph of pairs that form a code): against q^|I| for every I with no cycle outside it; against the
     bound of (a) for every g whose hypothesis holds; and against the bound of (b), which is attained,
     for the 4^4 relations with one helper each.
  2. The key step over all pairs of matrices, for 40 random relations at d = 3, q = 2 and 60 at d = 2,
     q = 3 that satisfy the hypothesis of (a) (random g), and as many for (b); and, on random relations
     and random sets I, that the key step holds exactly when there is no cycle outside I.
  3. At sizes up to d = 12: for the cyclic band of half-width B (every 2B <= d) with the g of the text,
     the hypothesis of (a) for every possible helper, the count of the exponent, and no cycle outside I
     for 20 random relations each; and the second statement of (b), the count of cycles, for random
     class maps at d <= 8.
  4. Controls, which must fail: (a) with rows in place of columns in the hypothesis; the cyclic band with
     the g of a line, at d = 3, where the set of all matrices is a code and exceeds that bound.
  5. The remark on the perfect shuffle: the differences pi(c) - c take d - 1 values for even d <= 64,
     and at d = 4 over two symbols two columns share a decoder exactly when their differences agree.
  6. The remark on marker rows: for the block-symmetric matrices over two symbols with M blocks of side m
     and k = ceil(log2 M) marker rows 0, m, ..., (k-1)m that spell the block of the column, the number of
     matrices is 2^((d^2 + M d)/2 - k d), and one function for every coordinate r serves all rows c when
     it reads the k marker entries and the M entries that the M classes would read: over all matrices of
     the set at d = 4 (M = 2 and M = 4), and over 300 random ones at d = 16, M = 8 (window 11, 2^144
     matrices).  Control, which must fail: the same without the marker entries, at d = 4, M = 2.

Usage, from the paper's directory:  python3 tools/set_bounds_check.py
Standard library only; under a minute.  It prints a summary and exits with status 1 if a check fails.
"""
import itertools
import random
import sys


def matrices(d, q):
    return list(itertools.product(range(q), repeat=d * d))


def pair_is_code(x, y, helpers):
    """Do the two matrices x != y form a storage code on the relation?"""
    for v, hs in enumerate(helpers):
        if x[v] != y[v] and all(x[u] == y[u] for u in hs):
            return False
    return True


def largest_code(d, q, helpers):
    """Exact largest storage code: a largest clique, by a simple branch and bound."""
    ms = matrices(d, q)
    n = len(ms)
    adj = [0] * n
    for a in range(n):
        for b in range(a + 1, n):
            if pair_is_code(ms[a], ms[b], helpers):
                adj[a] |= 1 << b
                adj[b] |= 1 << a
    best = 0

    def grow(size, cand):
        nonlocal best
        if size > best:
            best = size
        while cand and size + bin(cand).count("1") > best:
            v = cand.bit_length() - 1
            cand &= ~(1 << v)
            grow(size + 1, cand & adj[v])

    grow(0, (1 << n) - 1)
    return best


def staircase(d, g):
    """The set I = {(i, j): i < g(j)}, as indices i*d + j."""
    return [i * d + j for j in range(d) for i in range(d) if i < g[j]]


def hypothesis_a(d, helpers, g):
    return all(g[u % d] > v // d for v, hs in enumerate(helpers) for u in hs)


def acyclic_outside(n, helpers, index_set):
    """True if the relation has no directed cycle (loops included) among the positions outside index_set."""
    inside = set(index_set)
    state = {}
    for s in range(n):
        if s in inside or s in state:
            continue
        stack = [(s, iter(helpers[s]))]
        state[s] = 1
        while stack:
            v, it = stack[-1]
            for u in it:
                if u in inside:
                    continue
                if state.get(u) == 1:
                    return False
                if u not in state:
                    state[u] = 1
                    stack.append((u, iter(helpers[u])))
                    break
            else:
                state[v] = 2
                stack.pop()
    return True


def key_step(d, q, helpers, index_set):
    """True if no two distinct matrices that agree on index_set form a code."""
    inside = set(index_set)
    rest = [v for v in range(d * d) if v not in inside]
    tails = list(itertools.product(range(q), repeat=len(rest)))
    for base in itertools.product(range(q), repeat=len(index_set)):
        words = []
        for tail in tails:
            x = [0] * (d * d)
            for v, s in zip(index_set, base):
                x[v] = s
            for v, s in zip(rest, tail):
                x[v] = s
            words.append(tuple(x))
        for a in range(len(words)):
            for b in range(a + 1, len(words)):
                if pair_is_code(words[a], words[b], helpers):
                    return False
    return True


def cycles_of(f):
    """One position on every cycle of the map f on range(len(f))."""
    chosen, state = [], [0] * len(f)
    for s in range(len(f)):
        path, v = [], s
        while state[v] == 0:
            state[v] = 1
            path.append(v)
            v = f[v]
        if state[v] == 1:
            chosen.append(v)
        for u in path:
            state[u] = 2
    return chosen


def random_relation_a(d, g, rng, max_helpers):
    helpers = []
    for v in range(d * d):
        pool = [i * d + j for j in range(d) if g[j] > v // d for i in range(d)]
        k = rng.randint(0, min(max_helpers, len(pool)))
        helpers.append(tuple(rng.sample(pool, k)))
    return helpers


def band_g(d, B):
    return [d if j < B else min(d, j + B + 1) for j in range(d)]


def fail(msg):
    print("FAILED:", msg)
    sys.exit(1)


def part1():
    d, q, n = 2, 2, 4
    subsets = [tuple(u for u in range(n) if m >> u & 1) for m in range(16)]
    gs = list(itertools.product(range(d + 1), repeat=d))
    acyclic_cases = cases_a = attained = 0
    for hel in itertools.product(subsets, repeat=n):
        best = largest_code(d, q, hel)
        for index_set in subsets:
            if acyclic_outside(n, hel, index_set):
                acyclic_cases += 1
                if best > q ** len(index_set):
                    fail(f"acyclic-set bound at d=2, q=2: relation {hel}, I={index_set}")
        for g in gs:
            if hypothesis_a(d, hel, g):
                cases_a += 1
                if best > q ** sum(g):
                    fail(f"(a) at d=2, q=2: relation {hel}, g={g}: code {best}")
                attained += best == q ** sum(g)
    print(f"1. d=2, q=2, all 65536 relations, exact largest code: the acyclic-set bound holds in all "
          f"{acyclic_cases} cases (relation, I);")
    print(f"   (a) holds in all {cases_a} cases (relation, g), with equality in {attained}")
    for f in itertools.product(range(n), repeat=n):
        hel = [(f[v],) for v in range(n)]
        if largest_code(d, q, hel) != q ** len(cycles_of(list(f))):
            fail(f"(b) at d=2, q=2: f={f}")
    print("   (b): the largest code is exactly q^(number of cycles) for all 256 one-helper relations")


def part2(rng):
    for d, q, trials in ((3, 2, 40), (2, 3, 60)):
        n = d * d
        for _ in range(trials):
            g = [rng.randint(0, d) for _ in range(d)]
            hel = random_relation_a(d, g, rng, 4)
            if not hypothesis_a(d, hel, g):
                fail("generator")
            if not key_step(d, q, hel, staircase(d, g)):
                fail(f"(a) key step at d={d}, q={q}: g={g}, relation {hel}")
            f = [rng.randrange(n) for _ in range(n)]
            if not key_step(d, q, [(f[v],) for v in range(n)], cycles_of(f)):
                fail(f"(b) key step at d={d}, q={q}: f={f}")
        agree = both = 0
        for _ in range(trials):
            hel = [tuple(rng.sample(range(n), rng.randint(0, 2))) for _ in range(n)]
            index_set = sorted(rng.sample(range(n), rng.randint(n - 4, n - 1)))
            ks, ac = key_step(d, q, hel, index_set), acyclic_outside(n, hel, index_set)
            if ks != ac:
                fail(f"key step and acyclicity differ at d={d}, q={q}: {hel}, I={index_set}")
            agree += 1
            both += ks
        print(f"2. d={d}, q={q}: the key step holds over all pairs for {trials} random relations of (a) and "
              f"{trials} of (b); on {agree} random pairs (relation, I) it holds exactly when there is no "
              f"cycle outside I ({both} with, {agree - both} without)")


def part3(rng):
    bands = 0
    for d in range(2, 13):
        for B in range(0, d // 2 + 1):
            g = band_g(d, B)
            if sum(g) != d * (d + 1) // 2 + 2 * B * d - B * (2 * B + 1):
                fail(f"exponent of the cyclic band at d={d}, B={B}")
            for c in range(d):
                for e in range(-B, B + 1):
                    if not g[(c + e) % d] > c:
                        fail(f"hypothesis of the cyclic band at d={d}, B={B}, row {c}, offset {e}")
            index_set = staircase(d, g)
            for _ in range(20):
                hel = []
                for v in range(d * d):
                    c = v // d
                    pool = [i * d + (c + e) % d for e in range(-B, B + 1) for i in range(d)]
                    hel.append(tuple(rng.sample(pool, rng.randint(1, min(4, len(pool))))))
                if not acyclic_outside(d * d, hel, index_set):
                    fail(f"cyclic band at d={d}, B={B}: a cycle outside I")
            bands += 1
    print(f"3. cyclic band, d <= 12, every B with 2B <= d ({bands} pairs): the hypothesis of (a) holds for "
          f"every possible helper, the exponent is d(d+1)/2 + 2Bd - B(2B+1), and 20 random relations each "
          f"have no cycle outside I")
    maps = 0
    for d in range(2, 9):
        for _ in range(300):
            M = rng.randint(1, d)
            cls = [rng.randrange(M) for _ in range(d)]
            M_used = len(set(cls))
            pi = {J: [rng.randrange(d) for _ in range(d)] for J in set(cls)}
            rho = {J: [rng.randrange(d) for _ in range(d)] for J in set(cls)}
            f = [pi[cls[c]][r] * d + (rho[cls[c]][r] + c) % d for c in range(d) for r in range(d)]
            if 2 * len(cycles_of(f)) > d * d + M_used * d:
                fail(f"count of cycles at d={d}: classes {cls}")
            maps += 1
    print(f"   (b), second statement: 2z <= d^2 + Md for {maps} random class maps at d <= 8")


def part4():
    d, q = 2, 2
    hel = [(v,) for v in range(d * d)]       # every position is its own helper
    wrong_bound = q ** (d * (d + 1) // 2)    # (a) for g(i) = i + 1 read on the rows of the helpers
    best = largest_code(d, q, hel)
    if best <= wrong_bound:
        fail("control 1 did not fail")
    print(f"4. control, rows in place of columns in the hypothesis of (a): a code of {best} > {wrong_bound} "
          f"matrices (as expected)")
    d, q, B = 3, 2, 1
    hel = [(v,) for v in range(d * d)]       # allowed in the cyclic band: at d = 3 every column is within 1
    g_line = [min(d, j + B + 1) for j in range(d)]
    ms = matrices(d, q)
    if not all(pair_is_code(ms[a], ms[b], hel) for a in range(len(ms)) for b in range(a + 1, len(ms))):
        fail("control 2: the set of all matrices is not a code")
    if len(ms) <= q ** sum(g_line):
        fail("control 2 did not fail")
    print(f"   control, cyclic band at d=3, B=1 with the g of a line: all {len(ms)} matrices form a code, "
          f"more than {q ** sum(g_line)} (as expected)")


def part5():
    for d in range(2, 65, 2):
        pi = [c // 2 if c % 2 == 0 else c // 2 + d // 2 for c in range(d)]
        if sorted(pi) != list(range(d)):
            fail("pi is not a permutation")
        if len({(pi[c] - c) % d for c in range(d)}) != d - 1:
            fail(f"shuffle differences at d={d}")
    d = 4
    pi = [c // 2 if c % 2 == 0 else c // 2 + d // 2 for c in range(d)]
    ms = matrices(d, 2)
    for c in range(d):
        for e in range(c + 1, d):
            # The decoder of column c maps the view sigma^c X to column pi(c) of X.
            # Columns c and e share a decoder exactly if equal views always come with equal outputs.
            seen, shared = {}, True
            for col in (c, e):
                for x in ms:
                    view = tuple(x[i * d + (j + col) % d] for i in range(d) for j in range(d))
                    out = tuple(x[i * d + pi[col]] for i in range(d))
                    if seen.setdefault(view, out) != out:
                        shared = False
                        break
                if not shared:
                    break
            if shared != ((pi[c] - c) % d == (pi[e] - e) % d):
                fail(f"shared decoders of the shuffle at d=4: columns {c}, {e}")
    print("5. perfect shuffle: pi(c) - c takes d - 1 values for even d <= 64; at d = 4 two columns share a "
          "decoder exactly when their differences agree")


def marker_set(d, M, k, rng=None, samples=None):
    """The block-symmetric d x d matrices over two symbols whose rows 0, m, ..., (k-1)m spell the block
    of the column; all of them if samples is None, else that many random ones.  Returns (matrices, log2
    of the number of matrices in the whole set)."""
    m = d // M
    free = [(s, t, a, b) for s in range(M) for t in range(M) for a in range(m) for b in range(a, m)
            if not (a == 0 and s < k)]

    def build(values):
        x = [[0] * d for _ in range(d)]
        for (s, t, a, b), v in zip(free, values):
            x[s * m + a][t * m + b] = v
            x[s * m + b][t * m + a] = v
        for s in range(k):
            for c in range(d):
                bit = (c // m) >> s & 1
                x[s * m][c] = bit
                x[s * m + c % m][(c // m) * m] = bit
        return x

    if samples is None:
        words = [build(v) for v in itertools.product(range(2), repeat=len(free))]
    else:
        words = [build([rng.randrange(2) for _ in free]) for _ in range(samples)]
    return words, len(free)


def one_function(d, M, k, words, markers=True):
    """True if, for every coordinate r, one function of the entries read gives X[c][r] for all rows c
    and all the given matrices: the k marker entries (s*m, c), and the entries (s*m + l, (t - s)*m + c)
    for all classes s, where r = t*m + l."""
    m = d // M
    for r in range(d):
        t, l = divmod(r, m)
        seen = {}
        for x in words:
            for c in range(d):
                view = tuple(x[s * m][c] for s in range(k)) if markers else ()
                view += tuple(x[s * m + l][((t - s) * m + c) % d] for s in range(M))
                if seen.setdefault(view, x[c][r]) != x[c][r]:
                    return False
    return True


def part6(rng):
    for d, M, k in ((4, 2, 1), (4, 4, 2)):
        words, log_size = marker_set(d, M, k)
        if log_size != (d * d + M * d) // 2 - k * d or len({tuple(map(tuple, x)) for x in words}) != 2 ** log_size:
            fail(f"size of the marker set at d={d}, M={M}")
        if not one_function(d, M, k, words):
            fail(f"marker rows at d={d}, M={M}: no single function")
    d, M, k = 16, 8, 3
    words, log_size = marker_set(d, M, k, rng, 300)
    if log_size != d * d // 2 + d:
        fail("size of the marker set at d=16, M=8")
    if not one_function(d, M, k, words):
        fail("marker rows at d=16, M=8: no single function on the sample")
    all_words, _ = marker_set(4, 2, 0)
    if one_function(4, 2, 0, all_words, markers=False):
        fail("control 3 did not fail")
    print(f"6. marker rows: one function for all rows on the whole set at d=4 (M=2: 2^8 matrices, M=4: 2^8), "
          f"and on 300 random matrices of the set of 2^{log_size} at d=16, M=8, window {M + k}; without "
          f"markers no single function serves the block-symmetric matrices at d=4, M=2 (as expected)")


def main():
    rng = random.Random(17)
    part1()
    part2(rng)
    part3(rng)
    part4()
    part5()
    part6(rng)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
