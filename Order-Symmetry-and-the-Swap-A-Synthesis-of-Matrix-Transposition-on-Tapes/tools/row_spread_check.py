#!/usr/bin/env python3
"""Checks for the propositions on whole rows and stages at the end of the section on sets of matrices
(the order bound for whole rows; stages; expanding row relations).

Usage (needs NumPy; about ten seconds; the random choices are seeded):
    python3 tools/row_spread_check.py

Setting.  A row relation rho gives, for every column r of a d x d matrix, the set rho[r] of rows that the
entries of column r may be computed from.  H_rho is the digraph on the positions (c, r) in which (c, r) has
the helpers (i, c') for all i in rho[r] and all c'.

    sigma(rho) = min over bijections phi: rows -> {1..d} of  sum_r max phi(rho[r])      (max of {} = 0).

Parts.
 1. sigma by dynamic programming over subsets of rows agrees with brute force over all orders (d <= 6).
 2. Exactness: d^2 - sigma(rho) is the largest acyclic set of H_rho (exhaustive over subsets of positions,
    d <= 4).
 3. Blocks: sigma = (d^2 + sum of squared block sizes)/2 for full blocks and a bijection; the upper bound
    (d^2 + s d)/2 for rows inside blocks of at most s rows and arbitrary maps; the block-symmetric set of
    matrices is a code of exactly that size (q = 2, d = 4), also after a permutation of the columns; a control.
 4. Stages, part (a): coset stages compose to the predicted coset, sigma = (d^2 + 2^dim d)/2 for full cosets,
    and containment and the bound for arbitrary (often singular) linear parts and partial cosets.
 5. Degree: sigma <= w d (d+1)/(w+1) on random relations, equality for the complement of the identity, and
    the code of the matrices with even diagonal at d = 4.
 6. Expanding row relations, part (a): the inequality with the exact expansion constant, by enumeration.
 7. Gather passes: a simulation, with rows as units, that uses only the marking strings of the domain and the
    range of each increasing injection, moves both heads forward only and gathers the prescribed rows; head
    moves are counted.  Exact sigma of some unions of monotone maps at d = 16 and of the T-fold compositions
    of the shuffle parents with and without the row itself (the numbers quoted in the text).  Sizes this small
    say nothing about growth.
 8. Orders: sum_r max phi(rho[r]) <= d(d+1)/2 + d * (sum of one-sided stretches between layouts) on random
    pipelines (the step used for heights).
 9. Stages, part (b), the step of the proof: random pipelines of scans with small buffers in affine row
    orders, row-local maps, affine row permutations and butterflies, as operators on arrays of d = 8 symbols.
    Whenever two inputs have the same advice (the buffer states at the multiples of 2^k) and agree on the
    predicted coset of r, the outputs agree at r.  Control: inputs that agree on the coset but have different
    advice do give different outputs.
10. Stages, part (c): random pipelines over two copies whose stages mix copies arranged by digit permutations
    or free one digit; every row read has at most Omega more ones than the output row, and the order by the
    number of ones gives d(d+1)/2 + (W - 1) d.  The bound is below d^2 only for small Omega at these sizes.

Not checked here: the bound for scans itself with its last inequality, the cited part on expanders, the
proposition on products of bounded pieces, and the count for partial transposes.
"""
import itertools
import random
import sys
from fractions import Fraction

import numpy as np

SEED = 20261111
rng = random.Random(SEED)


# ---------------------------------------------------------------- basic tools
def masks_of(rho, d):
    out = []
    for r in range(d):
        m = 0
        for i in rho[r]:
            m |= 1 << i
        out.append(m)
    return out


def n_table(rho, d):
    """n[A] = number of columns r with rho[r] contained in the set A of rows."""
    n = np.zeros(1 << d, dtype=np.int64)
    for m in masks_of(rho, d):
        n[m] += 1
    for i in range(d):
        v = n.reshape(-1, 2, 1 << i)
        v[:, 1, :] += v[:, 0, :]
    return n


def popcounts(d):
    idx = np.arange(1 << d, dtype=np.int64)
    pc = np.zeros(1 << d, dtype=np.int64)
    for i in range(d):
        pc += (idx >> i) & 1
    return idx, pc


def sigma(rho, d, n=None):
    """min over chains {} = A_0 < A_1 < ... < A_{d-1} of sum_j (d - n(A_j))."""
    if n is None:
        n = n_table(rho, d)
    idx, pc = popcounts(d)
    big = 10 ** 12
    g = np.full(1 << d, big, dtype=np.int64)
    g[0] = 0
    h = g.copy()
    h[0] = d - n[0]
    for k in range(1, d + 1):
        layer = idx[pc == k]
        best = np.full(len(layer), big, dtype=np.int64)
        for i in range(d):
            bit = 1 << i
            sel = (layer & bit) != 0
            sub = layer[sel] ^ bit
            best[sel] = np.minimum(best[sel], h[sub])
        g[layer] = best
        h[layer] = best + d - n[layer]
    return int(g[(1 << d) - 1])


def sigma_brute(rho, d):
    best = None
    for perm in itertools.permutations(range(d)):
        phi = [0] * d
        for rank, row in enumerate(perm):
            phi[row] = rank + 1
        val = sum(max((phi[i] for i in rho[r]), default=0) for r in range(d))
        if best is None or val < best:
            best = val
    return best


def random_relation(d, w, with_identity=False):
    rho = []
    for r in range(d):
        s = set(rng.sample(range(d), w))
        if with_identity:
            s.add(r)
        rho.append(s)
    return rho


# ---------------------------------------------------------------- part 1
def part1():
    count = 0
    for d in range(2, 7):
        for w in range(0, min(d, 4) + 1):
            for _ in range(6 if d < 6 else 3):
                rho = [set(rng.sample(range(d), rng.randint(0, w))) for _ in range(d)]
                assert sigma(rho, d) == sigma_brute(rho, d), (d, rho)
                count += 1
    print(f"part 1: subset DP = brute force over all orders on {count} random relations, d <= 6")


# ---------------------------------------------------------------- part 2
def mais_H(rho, d):
    """Largest acyclic induced subgraph of H_rho, exhaustively (positions p = c*d + r)."""
    N = d * d
    helper = []
    for p in range(N):
        c, r = divmod(p, d)
        m = 0
        for i in rho[r]:
            for c2 in range(d):
                m |= 1 << (i * d + c2)
        helper.append(m)
    loop = [(helper[p] >> p) & 1 for p in range(N)]
    acyc = bytearray(1 << N)
    acyc[0] = 1
    best = 0
    for S in range(1, 1 << N):
        # S is acyclic iff some p in S has no helper in S and S - p is acyclic
        T = S
        ok = 0
        while T:
            low = T & -T
            p = low.bit_length() - 1
            if not loop[p] and (helper[p] & S) == 0 and acyc[S ^ low]:
                ok = 1
                break
            T ^= low
        acyc[S] = ok
        if ok:
            b = bin(S).count("1")
            if b > best:
                best = b
    return best


def part2():
    count = 0
    for d in (2, 3):
        for _ in range(12):
            rho = [set(rng.sample(range(d), rng.randint(0, d))) for _ in range(d)]
            assert mais_H(rho, d) == d * d - sigma(rho, d), (d, rho)
            count += 1
    d = 4
    for rho in ([{0}, {1}, {2}, {3}], [{1}, {2}, {3}, {0}], [{1, 2}, {2, 3}, {3, 0}, {0, 1}],
                [{1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}], [{0, 1}, {0, 1}, {2, 3}, {2, 3}],
                [{1}, {0, 2}, {3}, {1, 2}]):
        assert mais_H(rho, d) == d * d - sigma(rho, d), rho
        count += 1
    for _ in range(14):
        rho = [set(rng.sample(range(d), rng.randint(0, 3))) for _ in range(d)]
        assert mais_H(rho, d) == d * d - sigma(rho, d), rho
        count += 1
    print(f"part 2: largest acyclic set of H_rho = d^2 - sigma(rho) on {count} relations, d <= 4 "
          "(exhaustive over subsets of positions)")


# ---------------------------------------------------------------- part 3
def is_code(S, rho, d):
    """Every column r is a function of the rows rho[r] on the set S (matrices as tuples of row tuples)."""
    for r in range(d):
        rows = sorted(rho[r])
        seen = {}
        for X in S:
            key = tuple(X[i] for i in rows)
            col = tuple(X[c][r] for c in range(d))
            if seen.setdefault(key, col) != col:
                return False
    return True


def part3():
    # sigma formula for full blocks of arbitrary sizes, composed with a bijection
    count = 0
    for d in range(3, 13):
        for _ in range(4):
            sizes = []
            left = d
            while left:
                s = rng.randint(1, left)
                sizes.append(s)
                left -= s
            rows = list(range(d))
            rng.shuffle(rows)
            blocks, pos = [], 0
            for s in sizes:
                blocks.append(set(rows[pos:pos + s]))
                pos += s
            block_of = {i: b for b in blocks for i in b}
            pi = list(range(d))
            rng.shuffle(pi)
            rho = [set(block_of[pi[r]]) for r in range(d)]
            assert 2 * sigma(rho, d) == d * d + sum(s * s for s in sizes), (d, sizes)
            count += 1
    # upper bound (d^2 + s d)/2 when every rho(r) lies inside a block of at most s rows (any map, sub-blocks)
    upper = 0
    for d in range(3, 13):
        for _ in range(6):
            s_max = rng.randint(1, d)
            rows = list(range(d))
            rng.shuffle(rows)
            blocks, pos = [], 0
            while pos < d:
                sz = rng.randint(1, min(s_max, d - pos))
                blocks.append(rows[pos:pos + sz])
                pos += sz
            rho = []
            for r in range(d):
                b = rng.choice(blocks)
                rho.append(set(rng.sample(b, rng.randint(0, len(b)))))
            assert 2 * sigma(rho, d) <= d * d + max(len(b) for b in blocks) * d, (d, blocks, rho)
            upper += 1
    count += upper
    # the block-symmetric code at d = 4, blocks {0,1}, {2,3}: X[c][r] = X[r][c] across blocks, free inside
    d = 4
    blk = [0, 0, 1, 1]
    free = [(c, r) for c in range(d) for r in range(d) if blk[c] <= blk[r]]
    S = []
    for bits in itertools.product((0, 1), repeat=len(free)):
        X = [[0] * d for _ in range(d)]
        for (c, r), b in zip(free, bits):
            X[c][r] = b
            if blk[c] < blk[r]:
                X[r][c] = b
        S.append(tuple(tuple(row) for row in X))
    rho = [{0, 1}, {0, 1}, {2, 3}, {2, 3}]
    assert len(set(S)) == 2 ** 12 and sigma(rho, d) == 12
    assert is_code(S, rho, d)
    # after a permutation of the columns the relation is rho(r) = block(pi(r)) and the size is the same
    pi = [2, 0, 3, 1]                       # column r of the new matrix is column pi[r] of the old one
    S2 = [tuple(tuple(X[c][pi[r]] for r in range(d)) for c in range(d)) for X in S]
    rho2 = [rho[pi[r]] for r in range(d)]
    assert is_code(S2, rho2, d) and sigma(rho2, d) == 12 and len(set(S2)) == 2 ** 12
    # control: the same set is not a code for the relation that reads one row only
    assert not is_code(S, [{0}, {1}, {2}, {3}], d)
    print(f"part 3: sigma = (d^2 + sum s^2)/2 on {count - upper} full block relations and the upper bound on "
          f"{upper} relations with sub-blocks and arbitrary maps (d <= 12); block-symmetric code "
          "of size 2^12 = 2^sigma at d = 4, also with permuted columns; control passed")


# ---------------------------------------------------------------- part 4
def rank_f2(vecs):
    basis = []
    for v in vecs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def span_f2(vecs):
    out = {0}
    for v in vecs:
        out |= {x ^ v for x in out}
    return out


def random_gl(n):
    while True:
        cols = [rng.randrange(1, 1 << n) for _ in range(n)]
        if rank_f2(cols) == n:
            return cols


def apply_lin(cols, x):
    y = 0
    for k, c in enumerate(cols):
        if (x >> k) & 1:
            y ^= c
    return y


def part4():
    count = 0
    for n in (3, 4):
        d = 1 << n
        for _ in range(8):
            T = rng.randint(1, 3)
            stages = []
            for _ in range(T):
                P = random_gl(n)
                a = rng.randrange(d)
                t = rng.randint(0, 1)
                V = [rng.randrange(1, d) for _ in range(t)]
                stages.append((P, a, V))
            # stage s: output row r reads the input rows pi_s(r) + span(V_s); the last stage is applied last
            def read(stage, r):
                P, a, V = stage
                base = apply_lin(P, r) ^ a
                return {base ^ v for v in span_f2(V)}
            rho = []
            for r in range(d):
                cur = {r}
                for stage in reversed(stages):
                    cur = set().union(*(read(stage, x) for x in cur))
                rho.append(cur)
            # the predicted coset: pi = pi_1 o ... o pi_T, V = V_1 + P_1 V_2 + P_1 P_2 V_3 + ...
            gens = []
            for s, (P, a, V) in enumerate(stages):
                for v in V:
                    x = v
                    for (P2, _, _) in reversed(stages[:s]):
                        x = apply_lin(P2, x)
                    gens.append(x)
            Vspan = span_f2(gens)
            dimV = rank_f2(gens)
            assert dimV <= sum(len(V) for (_, _, V) in stages)
            for r in range(d):
                base = r
                for stage in reversed(stages):
                    base = apply_lin(stage[0], base) ^ stage[1]
                assert rho[r] == {base ^ v for v in Vspan}, "composition is not the predicted coset"
            assert 2 * sigma(rho, d) == d * d + (1 << dimV) * d
            count += 1
    # singular linear parts and partial cosets: containment in the predicted coset and the bound
    sing = 0
    for n in (3, 4):
        d = 1 << n
        for _ in range(40):
            T = rng.randint(1, 3)
            stages = []
            for _ in range(T):
                P = [rng.randrange(1 << n) for _ in range(n)]          # any matrix, often singular
                a = rng.randrange(d)
                V = [rng.randrange(1, d) for _ in range(rng.randint(0, 1))]
                keep = [{v for v in span_f2(V) if rng.random() < 0.7} for _ in range(d)]
                stages.append((P, a, V, keep))
            rho = []
            for r in range(d):
                cur = {r}
                for (P, a, V, keep) in reversed(stages):
                    cur = set().union(*({apply_lin(P, x) ^ a ^ v for v in keep[x]} for x in cur))
                rho.append(cur)
            gens = []
            for s_, (P, a, V, keep) in enumerate(stages):
                for v in V:
                    x = v
                    for (P2, _, _, _) in reversed(stages[:s_]):
                        x = apply_lin(P2, x)
                    gens.append(x)
            Vspan, dimV = span_f2(gens), rank_f2(gens)
            for r in range(d):
                base = r
                for (P, a, V, keep) in reversed(stages):
                    base = apply_lin(P, base) ^ a
                assert rho[r] <= {base ^ v for v in Vspan}
            assert 2 * sigma(rho, d) <= d * d + (1 << dimV) * d
            sing += 1
    print(f"        and {sing} pipelines with arbitrary (often singular) linear parts and partial cosets: "
          "containment and the bound")
    print(f"part 4: {count} random pipelines of affine coset stages (d = 8, 16): the composed relation is "
          "the predicted coset and sigma = (d^2 + 2^dim d)/2")


# ---------------------------------------------------------------- part 5
def part5():
    count = 0
    for d in range(3, 15):
        for w in range(1, min(d, 5) + 1):
            for _ in range(2):
                rho = random_relation(d, w)
                assert (w + 1) * sigma(rho, d) <= w * d * (d + 1), (d, w)
                count += 1
    for d in range(2, 13):
        rho = [set(range(d)) - {r} for r in range(d)]
        assert sigma(rho, d) == d * d - 1
    # parity code on the diagonal, d = 4: all entries off the diagonal free, the diagonal has even weight
    d = 4
    S = []
    off = [(c, r) for c in range(d) for r in range(d) if c != r]
    for bits in itertools.product((0, 1), repeat=len(off) + d - 1):
        X = [[0] * d for _ in range(d)]
        for (c, r), b in zip(off, bits):
            X[c][r] = b
        diag = bits[len(off):]
        for k in range(d - 1):
            X[k][k] = diag[k]
        X[d - 1][d - 1] = sum(diag) % 2
        S.append(tuple(tuple(row) for row in X))
    rho = [set(range(d)) - {r} for r in range(d)]
    assert len(set(S)) == 2 ** 15 and is_code(S, rho, d)
    print(f"part 5: sigma <= w d (d+1)/(w+1) on {count} random relations (d <= 14); complement of the "
          "identity has sigma = d^2 - 1 (d <= 12), attained by a code of size 2^15 at d = 4")


# ---------------------------------------------------------------- part 6
def expansion(rho, d):
    """min over nonempty sets S of at most d/2 columns of |N(S)|/|S| (exact, as a Fraction)."""
    m = masks_of(rho, d)
    nb = np.zeros(1 << d, dtype=np.int64)
    for i in range(d):
        nb[1 << i: 1 << (i + 1)] = nb[0: 1 << i] | m[i]
    idx, pc = popcounts(d)
    pcn = np.zeros(1 << d, dtype=np.int64)
    for i in range(d):
        pcn += (nb >> i) & 1
    best = None
    for k in range(1, d // 2 + 1):
        v = int(pcn[pc == k].min())
        f = Fraction(v, k)
        if best is None or f < best:
            best = f
    return best


def part6():
    rows = []
    for d, w in ((10, 2), (12, 2), (12, 3), (14, 2), (14, 3), (16, 2), (16, 3), (18, 3)):
        for _ in range(3):
            rho = random_relation(d, w, with_identity=True)
            ratio = expansion(rho, d)            # = 1 + eps
            assert ratio >= 1
            n = n_table(rho, d)
            idx, pc = popcounts(d)
            Nj = [int(n[pc == j].max()) for j in range(d)]
            s = sigma(rho, d, n)
            chain_bound = sum(d - Nj[j] for j in range(d))
            lemma = d * (d + 1) // 2 + sum(j - int(Fraction(j) / ratio) for j in range(d // 2 + 1))
            assert all(Nj[j] <= j for j in range(d))
            assert s >= chain_bound >= lemma, (d, w, s, chain_bound, lemma)
            rows.append((d, w + 1, float(ratio) - 1, lemma, chain_bound, s, d * (d + 1) // 2))
    print("part 6: expansion lemma on random relations containing the identity")
    print("        d  deg   eps   lemma  levelwise  sigma  d(d+1)/2")
    for row in rows[::3]:
        print("       %2d   %d   %.3f   %4d     %4d    %4d    %4d" % row)


# ---------------------------------------------------------------- part 7
def split_increasing(f):
    """Split a non-decreasing partial map (dict r -> f(r)) into strictly increasing injections."""
    parts = []
    for r in sorted(f):
        for g in parts:
            last = max(g)
            if g[last] < f[r]:
                g[r] = f[r]
                break
        else:
            parts.append({r: f[r]})
    return parts


def gather_passes(maps, d, ell):
    """Row-level simulation of the gather passes for strictly increasing partial injections.

    For each map the machine has two marking strings of d bits: dom[r] = 1 iff f is defined at r, ran[i] = 1 iff
    i is a value of f.  It does not use the values of f.  In a pass the work head visits the slots r = 0, 1, ...
    in order; at a marked slot the input head advances to the next marked row of the range and that row is copied
    into field m of the slot.  Both heads only move forward within a pass.  Returns (slots, steps), where steps
    counts head moves in cells (a row has ell cells), rewinds included."""
    w = len(maps)
    tape = list(range(d))                       # the row under the input head, identified by its index
    slots = [[None] * w for _ in range(d)]
    steps = 0
    for m, f in enumerate(maps):
        dom = [1 if r in f else 0 for r in range(d)]
        ran = [0] * d
        for v in f.values():
            ran[v] = 1
        head_in = 0
        for r in range(d):
            if dom[r]:
                while not ran[head_in]:
                    head_in += 1
                    steps += ell                 # skip an unmarked row
                slots[r][m] = tape[head_in]      # copy: both heads move over one row
                head_in += 1
                steps += 2 * ell
                steps += (w - 1) * ell           # the work head passes the other fields of the slot
            else:
                steps += w * ell
        steps += head_in * ell + d * w * ell     # rewind both heads
    return slots, steps


def random_monotone_map(d, k):
    dom = sorted(rng.sample(range(d), k))
    ran = sorted(rng.sample(range(d), k))
    return dict(zip(dom, ran))


def part7():
    d, ell = 16, 16 * 4
    ident = {r: r for r in range(d)}
    half = {r: r // 2 for r in range(d)}
    half2 = {r: r // 2 + d // 2 for r in range(d)}
    third = {r: (2 * r) // 3 for r in range(d)}
    named = {
        "r/2, r/2 + d/2 (shuffle parents)": [half, half2],
        "id": [ident],
        "id, r/2, r/2 + d/2": [ident, half, half2],
        "id, r/2, r/2 + d/2, 2r/3": [ident, half, half2, third],
    }
    print("part 7: unions of monotone maps at d = 16 (exact sigma; d(d+1)/2 = 136, degree-two ceiling 151)")
    for name, maps in named.items():
        inj = [g for f in maps for g in split_increasing(f)]
        for g in inj:
            keys = sorted(g)
            assert all(g[a] < g[b] for a, b in zip(keys, keys[1:]))
        slots, steps = gather_passes(inj, d, ell)
        w = len(inj)
        rho = [{f[r] for f in maps if r in f} for r in range(d)]
        # the rows gathered by the marking strings are the rows the maps prescribe
        assert all({x for x in slots[r] if x is not None} == rho[r] for r in range(d))
        assert all(slots[r][m] == inj[m].get(r) for r in range(d) for m in range(w))
        assert steps <= 2 * w * (w + 2) * d * ell
        print(f"        {name:34s} sigma = {sigma(rho, d)}   increasing injections (passes) = {w}, "
              f"head moves = {steps / (d * ell):.1f} d*ell")
    # the T-fold composition of the shuffle parents is a coset relation; with the row itself added it is not
    par = [{r // 2, r // 2 + d // 2} for r in range(d)]
    withid = [{r} | par[r] for r in range(d)]
    for rel, expect in ((par, [144, 160, 192, 256]), (withid, [161, 192, 221])):
        cur = [{r} for r in range(d)]
        got = []
        for T in range(len(expect)):
            cur = [set().union(*(rel[x] for x in c)) for c in cur]
            got.append(sigma(cur, d))
        assert got == expect, got
    print("        T-fold compositions at d = 16: shuffle parents 144, 160, 192, 256 = (d^2 + 2^T d)/2; "
          "with the row itself 161, 192, 221")
    best = 0
    for trial in range(400):
        maps = [ident] + [random_monotone_map(d, rng.randint(d // 2, d)) for _ in range(3)]
        rho = [{f[r] for f in maps if r in f} for r in range(d)]
        best = max(best, sigma(rho, d))
    print(f"        best of 400 random unions of id and three increasing injections: sigma = {best}")
    assert best <= 4 * d * (d + 1) // 5


# ---------------------------------------------------------------- part 8
def part8():
    count = 0
    for d in (6, 8, 10):
        for _ in range(10):
            T = rng.randint(1, 3)
            rels = [random_relation(d, rng.randint(1, 2)) for _ in range(T)]
            lay = []
            for _ in range(T + 1):
                p = list(range(1, d + 1))
                rng.shuffle(p)
                lay.append(p)
            # stage s maps arrays laid out by lay[s-1] to arrays laid out by lay[s]; rels[s-1] is its relation
            beta = []
            for s in range(1, T + 1):
                b = max(max(lay[s - 1][i] for i in rels[s - 1][r]) - lay[s][r] for r in range(d))
                beta.append(max(b, 0))
            rho = []
            for r in range(d):
                cur = {r}
                for s in range(T, 0, -1):
                    cur = set().union(*(rels[s - 1][x] for x in cur))
                rho.append(cur)
            total = sum(max(lay[0][i] for i in rho[r]) for r in range(d))
            assert total <= d * (d + 1) // 2 + d * sum(beta)
            count += 1
    print(f"part 8: sum_r max phi(rho(r)) <= d(d+1)/2 + d * (sum of the one-sided stretches) on {count} random "
          "pipelines with random layouts")


# ---------------------------------------------------------------- part 9
def random_affine_bijection(n):
    return random_gl(n), rng.randrange(1 << n)


def part9():
    n, d, OM = 3, 8, 4                      # rows are symbols of an alphabet with OM elements
    checked = controls = pipelines = 0
    attempts = 0
    while pipelines < 40 and attempts < 2000:
        attempts += 1
        k = rng.choice((1, 2))
        T = rng.randint(2, 4)
        stages = []
        for _ in range(T):
            kind = rng.choice(("scan", "scan", "perm", "local", "fly"))
            if kind == "perm":
                stages.append(("perm", random_affine_bijection(n)))
            elif kind == "local":
                stages.append(("local", [[rng.randrange(OM) for _ in range(OM)] for _ in range(d)]))
            elif kind == "fly":
                v = rng.randrange(1, d)
                stages.append(("fly", v, [[[rng.randrange(OM) for _ in range(OM)] for _ in range(OM)]
                                          for _ in range(d)]))
            else:
                nb = rng.choice((2, 4))     # number of buffer states
                lam = random_affine_bijection(n)
                f = [[[rng.randrange(OM) for _ in range(OM)] for _ in range(nb)] for _ in range(d)]
                g = [[[rng.randrange(nb) for _ in range(OM)] for _ in range(nb)] for _ in range(d)]
                stages.append(("scan", lam, f, g))

        def lam_of(lam, x):
            return apply_lin(lam[0], x) ^ lam[1]

        def run(X):
            advice = []
            cur = list(X)
            for st in stages:               # stages[0] is applied first
                if st[0] == "perm":
                    cur = [cur[lam_of(st[1], r)] for r in range(d)]
                elif st[0] == "local":
                    cur = [st[1][r][cur[r]] for r in range(d)]
                elif st[0] == "fly":
                    cur = [st[2][r][cur[r]][cur[r ^ st[1]]] for r in range(d)]
                else:
                    _, lam, f, g = st
                    inv = {lam_of(lam, r): r for r in range(d)}
                    out = [0] * d
                    beta = 0
                    for j in range(d):
                        if j and j % (1 << k) == 0:
                            advice.append(beta)
                        r = inv[j]
                        out[r] = f[j][beta][cur[r]]
                        beta = g[j][beta][cur[r]]
                    cur = out
            return cur, tuple(advice)

        def coset(r):
            cur = {r}
            for st in reversed(stages):
                if st[0] == "perm":
                    cur = {lam_of(st[1], x) for x in cur}
                elif st[0] == "fly":
                    cur = cur | {x ^ st[1] for x in cur}
                elif st[0] == "scan":
                    lam = st[1]
                    cur = {y for y in range(d) for x in cur
                           if (lam_of(lam, y) >> k) == (lam_of(lam, x) >> k)}
            return cur

        cosets = [coset(r) for r in range(d)]
        u_scans = sum(1 for st in stages if st[0] == "scan")
        t_fly = sum(1 for st in stages if st[0] == "fly")
        assert all(len(c) <= 1 << (t_fly + u_scans * k) for c in cosets)       # dimension at most t + u k
        if not any(st[0] == "scan" for st in stages) or all(len(c) == d for c in cosets):
            continue
        pipelines += 1
        for _ in range(3000):
            X = [rng.randrange(OM) for _ in range(d)]
            r = rng.randrange(d)
            if len(cosets[r]) == d:
                continue
            Y = [X[i] if i in cosets[r] else rng.randrange(OM) for i in range(d)]
            if Y == X:
                continue
            (KX, aX), (KY, aY) = run(X), run(Y)
            if aX == aY:
                assert KX[r] == KY[r], "same advice, same coset rows, different output row"
                checked += 1
            elif KX[r] != KY[r]:
                controls += 1
    assert pipelines == 40 and checked > 1000 and controls > 1000
    print(f"part 9: {pipelines} random pipelines with scans (d = 8, k = 1, 2): {checked} pairs with equal advice "
          f"and equal coset rows gave equal output rows; control: {controls} pairs with different advice gave "
          "different output rows")


# ---------------------------------------------------------------- part 10
def part10():
    count = exact = nontrivial = 0
    for n in range(4, 11):
        d = 1 << n
        wt = [bin(x).count("1") for x in range(d)]
        for _ in range(10):
            T = rng.randint(1, 4)
            # rows of an intermediate array are pairs (track, r); the height is wt[r] on both tracks
            stages = []
            for s_ in range(T):
                perms = []
                for _a in range(2):
                    pm = list(range(n))
                    rng.shuffle(pm)
                    perms.append(pm)
                kind = rng.choice(("mix", "mix", "digit"))
                stages.append((kind, perms, rng.randrange(n)))

            def permute(x, pm):
                y = 0
                for k_ in range(n):
                    if (x >> k_) & 1:
                        y |= 1 << pm[k_]
                return y

            def reads(stage, track, r):
                kind, perms, k_ = stage
                out = {(0, permute(r, perms[0])), (1, permute(r, perms[1]))}     # mix two arranged tracks
                if kind == "digit":                                           # also free one digit
                    out |= {(a, x ^ (1 << k_)) for (a, x) in out}
                return out

            omega = sum(1 for st in stages if st[0] == "digit")
            rho = []
            for r in range(d):
                cur = {(0, r)}
                for st in reversed(stages):
                    cur = set().union(*(reads(st, a, x) for (a, x) in cur))
                rows = {x for (_, x) in cur}          # the first stage reads X on both tracks (two copies of X)
                assert all(wt[x] <= wt[r] + omega for x in rows)
                rho.append(rows)
            order = sorted(range(d), key=lambda x: (wt[x], x))
            phi = [0] * d
            for rank, x in enumerate(order):
                phi[x] = rank + 1
            levels = [0] * (n + 1)
            for x in range(d):
                levels[wt[x]] += 1
            W = max(sum(levels[w:w + omega + 1]) for w in range(n + 1))
            total = sum(max(phi[x] for x in rho[r]) for r in range(d))
            assert total <= d * (d + 1) // 2 + (W - 1) * d
            if d * (d + 1) // 2 + (W - 1) * d < d * d:
                nontrivial += 1
            if n == 4:
                assert sigma(rho, d) <= d * (d + 1) // 2 + (W - 1) * d
                exact += 1
            count += 1
    print(f"part 10: {count} random two-track pipelines of digit permutations and single-digit stages, n = 4..10: "
          f"rows read have at most Omega more ones, and the order by ones gives the bound of the part on heights "
          f"(the bound is below d^2 in {nontrivial} of them; {exact} at n = 4 with the exact sigma)")


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
    part10()
    print("all checks passed")
    sys.exit(0)
