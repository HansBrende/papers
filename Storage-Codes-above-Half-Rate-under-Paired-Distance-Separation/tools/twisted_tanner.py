"""twisted_tanner.py -- the twisted Goren-Oort Tanner code over F_49 on X = Gamma+(lambda0)\\T, p = 7, lambda0 | 11.

An independent numerical check of Theorem G (paper/sections/arithmetic.tex): dim T_tw(X_1) >= (k - 1)^2 c_1 with
c_1 = 11, for the twisted datum of weight k (binary forms of degree m = k (p - 1) = 6k) at p = 7 on the first congruence
quotient for a prime above 11. Pure Python and numpy; self-contained (the icosian and finite-field code is adapted from
../Luck-Approximation-Fails-in-Positive-Characteristic/tools/icosian_graph.py and gf.py).

Setting. E = Q(sqrt 5), theta = (1 + sqrt 5)/2, O_E = Z[theta]. I is the icosian ring (the maximal order of the
quaternion algebra over E ramified only at the two infinite places, class number 1); its norm-one units form 2I (120
elements). p = 7 is inert: O_E/7 = F_49 = F_7[t]/(t^2 - t - 1) with theta -> t, and I/7I = M_2(F_49) through
i -> (3 2; 2 -3), j -> (0 1; -1 0) (red7). ell = 11 splits; lambda0 = (11, theta - 4) and I/lambda0 I = M_2(F_11)
through theta -> 4, i -> (1 3; 3 -1), j -> (0 1; -1 0), the splitting of icosian_graph.py (red11).
Gamma+ = I[1/7]^1/{+-1} maps onto G = PSL2(F_11) (660 elements). alpha0 in I has reduced norm 7; H0 = image of 2I and
H1 = image of alpha0 2I alpha0^-1 (60 elements each). X = Gamma+(lambda0)\\T has even vertices G/H0 and odd
vertices G/H1 (11 each) and 550 edges; it is 50-regular, with every even-odd pair joined by 4 or 5 edges (ell = 11 < 4p,
so X_1 is not simple).

Edges. The 6000 icosians of reduced norm 7 form 50 classes beta 2I (right multiplication by units), one for each edge at
the even base vertex: beta mod 7 has rank one and the 50 images are the 50 points of P^1(F_49). For an even vertex v
(representative h_v in G) and a class representative beta:
  1. delta1 = alpha0 conj(beta)/7 in I[1/7]^1, g = h_v delta1^-1 (mod lambda0); w = the odd vertex with g in h_w H1;
     tbar = g^-1 h_w in H1; s in 2I with alpha0 s alpha0^-1 = +-tbar (mod lambda0); M = s^-1 = conj(s).
  2. B = beta mod 7 (rank one), C = conj(beta) mod 7, Mb = M mod 7; x in F_49^2 with a = B x != 0; y with det(a, y) = 1.
  3. b = sigma(Mb C y), where sigma(z) = z^7 coordinatewise (Frobenius of F_49).
  4. The equation f_v(a) - f_w(b) = 0, where f(z) = sum_r c_r z1^(m-r) z2^r.
Unknowns: one binary form of degree m at each of the 22 vertices. The Tanner code (evaluation at the 50 points of each
star is injective for m <= 48) is the solution space; dim = 22 (m + 1) - rank, computed exactly over F_49.
Rescaling a by c rescales y by 1/c and b by c^-7, so an equation is multiplied by c^m (c^(8m) = 1 in F_49): the model
does not depend on x, y. Weights k > p - 2 = 5 (up to k = 8, m = 48) are outside Theorem G and are reported as data.

Variants (controls):
  tw        the model above.
  untw      b = Mb C y, no Frobenius. Rescaling a by c changes an equation by c^(2m): the model is well defined only if
            48 | 2m, i.e. k = 4 = (p + 1)/2 or k = 8 (the "standard at both parities" datum; Remark rem:forced).
  badnorm   tw with det(a, y) = 2. Every b is multiplied by sigma(2) = 2, every odd side by 2^m = 1: the same equations.
  badnormw  tw with det(a, y) = w, w a generator of F_49^*: every odd side is multiplied by w^(7m), one scalar for all
            edges, absorbed by rescaling the odd forms; the dimension cannot change.
  projnorm  tw with a and b rescaled independently so that their first nonzero coordinate is 1 (the det(a, y) = 1 rule
            dropped): an edge-dependent normalization. At k = 4 it differs from tw by signs, since c^24 = +-1.
  rand      tw with f_v(a) - r_e f_w(b) = 0, r_e uniformly random in F_49^* for each edge (seed 12345 in the table;
            five more seeds in the checks).

Checks (assertions; any failure stops the run): F_49 and both splittings satisfy their relations; 2I has 120 elements
and is closed; red7 and red11 are multiplicative (products of units, and of norm-7 elements with units); conj maps to
the adjugate; the icosians of norm 7 are found by an exact search over (1/2 O_E)^4 with membership in
I = Z-span of {u, theta u : u in 2I}: there are 6000, in 50 classes of 120, with rank-one reductions whose images are
the 50 distinct points of P^1(F_49); |H0| = |H1| = 60 and s -> alpha0 s alpha0^-1 is 2:1 from 2I onto H1; the images
used generate PSL2(F_11); in every run every vertex has exactly 50 edges, with 50 distinct points of P^1(F_49).
Comparisons (reported, and summarized as ALL CHECKS PASSED or FAILURES):
  - the dimension of tw is unchanged under random x, y, random class representatives beta, random coset representatives
    h_v, h_w, alpha0 from each of the two orbits of A5 on the 50 edges at the even base vertex (sizes 20 and 30), and
    everything random at once;
  - the equations of tw and badnorm (rows up to scalars) are unchanged under random x, y and class representatives; for
    untw they change exactly when 48 does not divide 2m;
  - the equations computed from the odd side coincide with the even-side ones, row by row up to scalars, for every m:
    for the 50 classes nu at the odd base vertex alpha0 Lambda0, the even endpoint is alpha0 nu/7 Lambda0 in G/H0
    (coset of g' = h_w alpha0 nu/7), u in 2I with u = +-g'^-1 h_v, and a = u^-1 adj(nu) y', b = sigma(nu x') with
    det(nu x', y') = 1;
  - rank over F_49 = half the rank over F_7 of the regular representation (independent elimination).

Usage:  python3 tools/twisted_tanner.py [K ...] [--no-checks]
        default K = 2 3 4 5; needs numpy (e.g.  uv run --with numpy python tools/twisted_tanner.py 1 2 3 4 5 6 7 8).
        --no-checks prints the table only (about 3 s for K = 2..5).

Expected output (K = 1..8, about 30 s with the checks):
   k   m 22(m+1)-550 (k-1)^2*11 |        tw      untw   badnorm  badnormw  projnorm      rand
   1   6        -396          0 |         0         0         0         0         0         0
   2  12        -264         11 |        22         0        22        22         0         0
   3  18        -132         44 |        44         0        44        44         0         0
   4  24           0         99 |       111        60       111       111         1         1
   5  30         132        176 |       176       132       176       176       132       132
   6  36         264        275 |       286       264       286       286       264       264
   7  42         396        396 |       396       396       396       396       396       396
   8  48         528        539 |       529       529       529       529       529       528
  (rand at k = 4 is 1 for seed 12345 and 0 for seeds 1..5; untw is 60 at k = 4 under all changes of choices.)
  ALL CHECKS PASSED
"""
import itertools
import sys
import time

import numpy as np

P, ELL = 7, 11
NV = (ELL * (ELL * ELL - 1) // 2) // 60          # 11 vertices of each parity
NCLS = P * P + 1                                   # 50 edges at each vertex


# ----------------------------------------------------------------------------- F_49
class F49:
    """F_49 = F_7[t]/(t^2 - t - 1); a + b t is encoded as a + 7 b (so F_7 = {0..6} and theta -> t = 7)."""

    def __init__(self):
        q = 49
        a, b = np.arange(q) % 7, np.arange(q) // 7
        A, B, C, D = a[:, None], b[:, None], a[None, :], b[None, :]
        self.add = (((A + C) % 7) + 7 * ((B + D) % 7)).astype(np.uint8)
        # (a + b t)(c + d t) = ac + bd + (ad + bc + bd) t, using t^2 = t + 1
        self.mul = (((A * C + B * D) % 7) + 7 * ((A * D + B * C + B * D) % 7)).astype(np.uint8)
        self.neg = (((-a) % 7) + 7 * ((-b) % 7)).astype(np.uint8)
        self.sub = self.add[np.arange(q)[:, None], self.neg[None, :]]
        self.inv = np.zeros(q, dtype=np.uint8)
        for x in range(1, q):
            self.inv[x] = int(np.flatnonzero(self.mul[x] == 1)[0])
        # Frobenius: (a + b t)^7 = a + b t^7 = a + b (1 - t)
        self.frob = (((a + b) % 7) + 7 * ((-b) % 7)).astype(np.uint8)
        self.pow = np.ones((q, q), dtype=np.uint8)            # pow[x, e] = x^e for e = 0..48 (0^0 = 1)
        for e in range(1, q):
            self.pow[:, e] = self.mul[self.pow[:, e - 1], np.arange(q)]
        t = 7
        assert int(self.mul[t, t]) == int(self.add[t, 1]), "t^2 = t + 1"
        assert all(int(self.pow[x, 7]) == int(self.frob[x]) for x in range(q))
        assert int(self.frob[t]) != t and all(int(self.frob[x]) == x for x in range(7))
        X, Y, Z = np.meshgrid(np.arange(q), np.arange(q), np.arange(q), indexing="ij")   # field axioms
        assert np.array_equal(self.mul[X, self.add[Y, Z]], self.add[self.mul[X, Y], self.mul[X, Z]])
        assert np.array_equal(self.mul[X, self.mul[Y, Z]], self.mul[self.mul[X, Y], Z])
        assert all(int(self.mul[x, self.inv[x]]) == 1 for x in range(1, q))
        orders = [next(e for e in range(1, q) if self.pow[x, e] == 1) for x in range(1, q)]
        self.gen = 1 + orders.index(48)                         # a generator of F_49^*

    # small helpers on Python ints
    def m(self, x, y):
        return int(self.mul[x, y])

    def a(self, x, y):
        return int(self.add[x, y])

    def mat(self, X, Y):
        """2x2 matrices as 4-tuples (x00, x01, x10, x11)."""
        m, a = self.m, self.a
        return (a(m(X[0], Y[0]), m(X[1], Y[2])), a(m(X[0], Y[1]), m(X[1], Y[3])),
                a(m(X[2], Y[0]), m(X[3], Y[2])), a(m(X[2], Y[1]), m(X[3], Y[3])))

    def vec(self, X, v):
        m, a = self.m, self.a
        return (a(m(X[0], v[0]), m(X[1], v[1])), a(m(X[2], v[0]), m(X[3], v[1])))

    def det(self, u, v):
        return int(self.sub[self.mul[u[0], v[1]], self.mul[u[1], v[0]]])

    def scal(self, c, v):
        return tuple(self.m(c, x) for x in v)

    def fr(self, v):
        return tuple(int(self.frob[x]) for x in v)

    def proj(self, v):
        """first nonzero coordinate scaled to 1"""
        c = v[0] if v[0] else v[1]
        return self.scal(int(self.inv[c]), v)

    def rank(self, M):
        """rank of a matrix over F_49 by Gaussian elimination (row echelon form)."""
        R = np.array(M, dtype=np.uint8)
        nr, nc = R.shape
        r = 0
        for c in range(nc):
            if r == nr:
                break
            nz = np.flatnonzero(R[r:, c])
            if nz.size == 0:
                continue
            i = r + int(nz[0])
            if i != r:
                R[[r, i]] = R[[i, r]]
            R[r, c:] = self.mul[self.inv[R[r, c]], R[r, c:]]
            rows = r + 1 + np.flatnonzero(R[r + 1:, c])
            if rows.size:
                f = R[rows, c]
                R[rows, c:] = self.sub[R[rows, c:], self.mul[f[:, None], R[r, c:][None, :]]]
            r += 1
        return r


# ----------------------------------------------------------------------------- Z[theta] and quaternions (exact)
# An element (a + b theta)/2 of 1/2 Z[theta] is stored as the integer pair (a, b); a quaternion q = w + x i + y j + z k
# with coefficients in 1/2 Z[theta] is stored as the 4-tuple of pairs of 2q ("scaled"). theta^2 = theta + 1.
def zm(x, y):
    return (x[0] * y[0] + x[1] * y[1], x[0] * y[1] + x[1] * y[0] + x[1] * y[1])


def zs(*terms):
    return (sum(t[0] for t in terms), sum(t[1] for t in terms))


def zn(x):
    return (-x[0], -x[1])


def qmul_raw(p, q):
    w1, x1, y1, z1 = p
    w2, x2, y2, z2 = q
    w = zs(zm(w1, w2), zn(zm(x1, x2)), zn(zm(y1, y2)), zn(zm(z1, z2)))
    x = zs(zm(w1, x2), zm(x1, w2), zm(y1, z2), zn(zm(z1, y2)))
    y = zs(zm(w1, y2), zn(zm(x1, z2)), zm(y1, w2), zm(z1, x2))
    z = zs(zm(w1, z2), zm(x1, y2), zn(zm(y1, x2)), zm(z1, w2))
    return (w, x, y, z)


def qmul(p, q):
    """scaled product: 2(pq) = (2p)(2q)/2."""
    r = qmul_raw(p, q)
    assert all(c[0] % 2 == 0 and c[1] % 2 == 0 for c in r)
    return tuple((c[0] // 2, c[1] // 2) for c in r)


def qconj(q):
    return (q[0], zn(q[1]), zn(q[2]), zn(q[3]))


def qneg(q):
    return tuple(zn(c) for c in q)


def qnrd(q):
    """reduced norm of the quaternion whose scaled form is q, as a pair (A, B) meaning A + B theta."""
    s = zs(*(zm(c, c) for c in q))
    assert s[0] % 4 == 0 and s[1] % 4 == 0
    return (s[0] // 4, s[1] // 4)


def qmul_np(Pa, u):
    """scaled products p u for an array Pa of scaled quaternions (N, 4, 2) and one scaled quaternion u."""
    def z(x, y):
        return np.stack([x[:, 0] * y[0] + x[:, 1] * y[1], x[:, 0] * y[1] + x[:, 1] * y[0] + x[:, 1] * y[1]], axis=1)
    w1, x1, y1, z1 = Pa[:, 0], Pa[:, 1], Pa[:, 2], Pa[:, 3]
    w2, x2, y2, z2 = u
    R = np.stack([z(w1, w2) - z(x1, x2) - z(y1, y2) - z(z1, z2),
                  z(w1, x2) + z(x1, w2) + z(y1, z2) - z(z1, y2),
                  z(w1, y2) - z(x1, z2) + z(y1, w2) + z(z1, x2),
                  z(w1, z2) + z(x1, y2) - z(y1, x2) + z(z1, w2)], axis=1)
    assert np.all(R % 2 == 0)
    return R // 2


def perm_parity(p):
    return sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j]) % 2


def icosians():
    """the 120 units of 2I (scaled form), with checks."""
    U = set()
    for pos in range(4):
        for s in (1, -1):
            q = [(0, 0)] * 4
            q[pos] = (2 * s, 0)
            U.add(tuple(q))
    for sg in itertools.product((1, -1), repeat=4):
        U.add(tuple((s, 0) for s in sg))
    vals0 = [(0, 0), (1, 0), (-1, 1), (0, 1)]       # 0, 1/2, theta^-1/2, theta/2 (scaled by 2)
    for perm in itertools.permutations(range(4)):
        if perm_parity(perm):
            continue
        for sg in itertools.product((1, -1), repeat=3):
            vals = [vals0[0]] + [(s * v[0], s * v[1]) for s, v in zip(sg, vals0[1:])]
            q = [None] * 4
            for i in range(4):
                q[perm[i]] = vals[i]
            U.add(tuple(q))
    U = sorted(U)
    assert len(U) == 120
    Us = set(U)
    assert all(qnrd(u) == (1, 0) for u in U)
    assert all(qmul(a, b) in Us for a in U for b in U), "2I not closed"
    return U


def hnf(rows):
    """echelon basis (integer row operations) of the Z-span of integer vectors."""
    rows = [list(r) for r in rows]
    n = len(rows[0])
    r = 0
    for col in range(n):
        while True:
            nz = [i for i in range(r, len(rows)) if rows[i][col]]
            if not nz:
                break
            i0 = min(nz, key=lambda i: abs(rows[i][col]))
            rows[r], rows[i0] = rows[i0], rows[r]
            piv = rows[r][col]
            clean = True
            for i in range(r + 1, len(rows)):
                if rows[i][col]:
                    f = rows[i][col] // piv
                    rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
                    clean &= rows[i][col] == 0
            if clean:
                break
        if r < len(rows) and rows[r][col]:
            if rows[r][col] < 0:
                rows[r] = [-x for x in rows[r]]
            r += 1
    return rows[:r]


def in_lattice(basis, X):
    """X: (N, n) integer array; True where the row lies in the Z-span of the echelon basis (full rank)."""
    X = X.copy()
    ok = np.ones(len(X), dtype=bool)
    for row in basis:
        c = next(j for j, x in enumerate(row) if x)
        ok &= X[:, c] % row[c] == 0
        X -= np.outer(X[:, c] // row[c], np.array(row, dtype=np.int64))
    return ok & np.all(X == 0, axis=1)


def norm_p_elements(U, p):
    """all icosians of reduced norm p (scaled form): exact search over (1/2 Z[theta])^4, then membership in I."""
    th, th2 = (1 + 5 ** 0.5) / 2, (1 - 5 ** 0.5) / 2
    bound = 4 * p + 1e-9                    # each scaled coordinate c has sigma_i(c)^2 <= 4p at both embeddings
    coords = [(a, b) for a in range(-30, 31) for b in range(-30, 31)
              if (a + b * th) ** 2 <= bound and (a + b * th2) ** 2 <= bound]
    sq = {c: zm(c, c) for c in coords}      # (2c)^2 in Z[theta]
    pairs = {}
    for c1 in coords:
        for c2 in coords:
            pairs.setdefault(zs(sq[c1], sq[c2]), []).append((c1, c2))
    cand = []
    for key, lst in pairs.items():
        other = pairs.get((4 * p - key[0], -key[1]))
        if other:
            for c12 in lst:
                for c34 in other:
                    cand.append(c12 + c34)
    # membership: I = O_E-span of 2I = Z-span of {u, theta u}
    gens = []
    for u in U:
        gens.append([x for c in u for x in c])
        gens.append([x for c in u for x in (c[1], c[0] + c[1])])   # theta (a + b theta) = b + (a + b) theta
    basis = hnf(gens)
    assert len(basis) == 8
    X = np.array([[x for c in q for x in c] for q in cand], dtype=np.int64)
    ok = in_lattice(basis, X)
    assert all(in_lattice(basis, np.array(gens, dtype=np.int64)))
    out = sorted(q for q, o in zip(cand, ok) if o)
    assert all(qnrd(q) == (p, 0) for q in out)
    index = abs(int(round(np.linalg.det(np.array(basis, dtype=float)))))
    return out, len(cand), index


# ----------------------------------------------------------------------------- reductions mod 7 and mod lambda0
I7 = (3, 2, 2, 4)            # (3 2; 2 -3) over F_7
J7 = (0, 1, 6, 0)            # (0 1; -1 0)
IL = (1, 3, 3, 10)           # (1 3; 3 -1) over F_11 (icosian_graph.fl_data(11))
JL = (0, 1, 10, 0)
PHIL = 4                     # theta mod lambda0
INV2_7, INV2_11, INV7_11 = 4, 6, 8


class Red7:
    def __init__(self, F):
        self.F = F
        self.K7 = F.mat(I7, J7)
        one, mone = (1, 0, 0, 1), (6, 0, 0, 6)
        assert F.mat(I7, I7) == mone and F.mat(J7, J7) == mone and F.mat(self.K7, self.K7) == mone
        assert F.mat(I7, J7) == tuple(int(F.neg[x]) for x in F.mat(J7, I7))

    def coef(self, c):
        """(a + b theta)/2 -> F_49 with theta -> t."""
        return (INV2_7 * c[0]) % 7 + 7 * ((INV2_7 * c[1]) % 7)

    def __call__(self, q):
        F = self.F
        w, x, y, z = (self.coef(c) for c in q)
        out = []
        for e in range(4):
            v = F.m(w, (1, 0, 0, 1)[e])
            v = F.a(v, F.m(x, I7[e]))
            v = F.a(v, F.m(y, J7[e]))
            v = F.a(v, F.m(z, self.K7[e]))
            out.append(v)
        return tuple(out)


def m11(X, Y):
    return ((X[0] * Y[0] + X[1] * Y[2]) % 11, (X[0] * Y[1] + X[1] * Y[3]) % 11,
            (X[2] * Y[0] + X[3] * Y[2]) % 11, (X[2] * Y[1] + X[3] * Y[3]) % 11)


KL = m11(IL, JL)


def n11(X):
    """sign normalization: the class of X in PSL2(F_11)."""
    X = tuple(x % 11 for x in X)
    f = next(x for x in X if x)
    return X if f <= 5 else tuple((-x) % 11 for x in X)


def inv11(X):
    return n11((X[3], -X[1], -X[2], X[0]))         # determinant 1


def det11(X):
    return (X[0] * X[3] - X[1] * X[2]) % 11


def red11(q):
    w, x, y, z = (((c[0] + PHIL * c[1]) * INV2_11) % 11 for c in q)
    return tuple((w * (1, 0, 0, 1)[e] + x * IL[e] + y * JL[e] + z * KL[e]) % 11 for e in range(4))


def scal11(c, X):
    return tuple((c * x) % 11 for x in X)


# ----------------------------------------------------------------------------- the global data
class Setup:
    def __init__(self, verbose=True):
        t0 = time.time()
        F = self.F = F49()
        self.red7 = r7 = Red7(F)
        mone = (10, 0, 0, 10)
        assert m11(IL, IL) == mone and m11(JL, JL) == mone and m11(KL, KL) == mone
        assert m11(IL, JL) == tuple((-x) % 11 for x in m11(JL, IL))
        assert (PHIL * PHIL - PHIL - 1) % 11 == 0
        U = self.U = icosians()
        # reductions are ring homomorphisms (on products of units)
        for a in U[::7]:
            for b in U[::11]:
                assert F.mat(r7(a), r7(b)) == r7(qmul(a, b))
                assert m11(red11(a), red11(b)) == red11(qmul(a, b))
            assert F.mat(r7(a), r7(qconj(a))) == (1, 0, 0, 1)
        # norm-7 icosians and their classes beta 2I
        N7, ncand, index = norm_p_elements(U, P)
        self.N7 = N7
        assert len(N7) == 120 * (P * P + 1), len(N7)
        arr = np.array(N7, dtype=np.int64)                              # (6000, 4, 2)
        enc = lambda A: ((A + 32).reshape(len(A), 8) * (64 ** np.arange(8))).sum(1)
        keys = np.stack([enc(qmul_np(arr, np.array(u))) for u in U], axis=1)
        canon = keys.min(axis=1)
        own = enc(arr)
        assert set(own.tolist()) >= set(canon.tolist())
        cls_keys, cls_of = np.unique(canon, return_inverse=True)
        assert len(cls_keys) == NCLS and all(np.bincount(cls_of) == 120)
        self.classes = [[N7[i] for i in np.flatnonzero(cls_of == c)] for c in range(NCLS)]
        self.cls_index = {N7[i]: int(cls_of[i]) for i in range(len(N7))}
        # reductions mod 7: rank one, image line constant on classes, the 50 lines distinct
        lines = []
        for cl in self.classes:
            L = set()
            for beta in cl:
                Bb = r7(beta)
                assert any(Bb) and F.det((Bb[0], Bb[2]), (Bb[1], Bb[3])) == 0
                col = (Bb[0], Bb[2]) if (Bb[0] or Bb[2]) else (Bb[1], Bb[3])
                L.add(F.proj(col))
                # conj -> adjugate
                Cb = r7(qconj(beta))
                assert Cb == (Bb[3], int(F.neg[Bb[1]]), int(F.neg[Bb[2]]), Bb[0])
            assert len(L) == 1
            lines.append(L.pop())
        assert len(set(lines)) == NCLS
        for beta in N7[::97]:
            for u in U[::13]:
                assert F.mat(r7(beta), r7(u)) == r7(qmul(beta, u))
                assert m11(red11(beta), red11(u)) == red11(qmul(beta, u))
        self.lines = lines
        # PSL2(F_11), H0
        self.G = sorted({n11((a, b, c, d)) for a in range(11) for b in range(11) for c in range(11)
                         for d in range(11) if (a * d - b * c) % 11 == 1})
        assert len(self.G) == 660
        self.H0map = {}
        for u in U:
            self.H0map.setdefault(n11(red11(u)), u)
        assert len(self.H0map) == 60
        # left action of 2I on the classes: orbits of A5 on the edges at the base vertex
        orb, seen = [], set()
        for c in range(NCLS):
            if c in seen:
                continue
            o = {self.cls_index[qmul(u, self.classes[c][0])] for u in U}
            seen |= o
            orb.append(sorted(o))
        self.orbits = orb
        self.info = dict(ncand=ncand, index=index, orbits=sorted(len(o) for o in orb), time=time.time() - t0)
        if verbose:
            print(f"setup: F_49 and splittings ok; |2I| = 120; norm-7 search: {ncand} candidates in (1/2 O_E)^4, "
                  f"[ (1/2 O_E)^4 : I ] = {index}, {len(N7)} icosians of norm 7 in {NCLS} classes of 120, "
                  f"images = {len(set(lines))} distinct points of P^1(F_49); A5-orbits on the 50 edges: "
                  f"{self.info['orbits']}; {time.time() - t0:.1f}s", flush=True)


# ----------------------------------------------------------------------------- the edges of X and their points
class Frame:
    """alpha0-dependent data: H1, cosets, representatives."""

    def __init__(self, S, alpha0, rng=None):
        F = S.F
        assert qnrd(alpha0) == (P, 0)
        self.alpha0 = alpha0
        self.A11 = red11(alpha0)
        A11c = red11(qconj(alpha0))
        assert m11(self.A11, scal11(INV7_11, A11c)) == (1, 0, 0, 1)
        self.H1map, fib = {}, {}
        for s in S.U:
            t = n11(m11(m11(self.A11, red11(s)), scal11(INV7_11, A11c)))
            self.H1map.setdefault(t, s)
            fib.setdefault(t, set()).add(s)
        assert len(self.H1map) == 60 and all(len(v) == 2 and qneg(min(v)) in v for v in fib.values())
        H0, H1 = list(S.H0map), list(self.H1map)

        def cosets(H):
            canon = {g: min(n11(m11(g, h)) for h in H) for g in S.G}
            ids = sorted(set(canon.values()))
            idx = {c: n for n, c in enumerate(ids)}
            members = [[] for _ in ids]
            for g in S.G:
                members[idx[canon[g]]].append(g)
            return {g: idx[canon[g]] for g in S.G}, members

        self.cos0, mem0 = cosets(H0)
        self.cos1, mem1 = cosets(H1)
        assert len(mem0) == NV and len(mem1) == NV
        if rng is None:
            self.rep0 = [min(m) for m in mem0]
            self.rep1 = [min(m) for m in mem1]
        else:
            self.rep0 = [m[rng.integers(len(m))] for m in mem0]
            self.rep1 = [m[rng.integers(len(m))] for m in mem1]
        # the group generated by H0, H1 and the elements delta1 used below is PSL2(F_11)
        gens = H0[:5] + H1[:5] + [n11(m11(self.A11, scal11(INV7_11, red11(qconj(cl[0]))))) for cl in S.classes]
        grp, frontier = {n11((1, 0, 0, 1))}, [n11((1, 0, 0, 1))]
        while frontier:
            new = []
            for x in frontier:
                for g in gens:
                    y = n11(m11(x, g))
                    if y not in grp:
                        grp.add(y)
                        new.append(y)
            frontier = new
        assert len(grp) == 660


def rand_vec(F, rng, nonzero_under=None):
    while True:
        x = (int(rng.integers(49)), int(rng.integers(49)))
        if x == (0, 0):
            continue
        if nonzero_under is None or any(F.vec(nonzero_under, x)):
            return x


def solve_y(F, a, target, rng=None):
    """y with det(a, y) = target (random up to multiples of a if rng is given)."""
    if rng is None:
        y0 = (0, 1) if F.det(a, (0, 1)) else (1, 0)
    else:
        while True:
            y0 = (int(rng.integers(49)), int(rng.integers(49)))
            if F.det(a, y0):
                break
    c = F.m(target, int(F.inv[F.det(a, y0)]))
    y = F.scal(c, y0)
    if rng is not None:                                   # y + lam a: same determinant
        lam = int(rng.integers(49))
        y = tuple(F.a(yy, F.m(lam, aa)) for yy, aa in zip(y, a))
    assert F.det(a, y) == target
    return y


def edges_even(S, Fr, variant="tw", rng_beta=None, rng_xy=None, rng_r=None):
    """the 550 equations f_v(a) - r f_w(b) = 0 from the even side: lists (v, w, a, b, r)."""
    F, r7 = S.F, S.red7
    target = {"badnorm": 2, "badnormw": F.gen}.get(variant, 1)
    out = []
    for v in range(NV):
        hv = Fr.rep0[v]
        for c in range(NCLS):
            cl = S.classes[c]
            beta = cl[0] if rng_beta is None else cl[rng_beta.integers(len(cl))]
            cb = qconj(beta)
            D = scal11(INV7_11, m11(Fr.A11, red11(cb)))          # delta1 = alpha0 conj(beta)/7 mod lambda0
            assert det11(D) == 1
            g = n11(m11(hv, inv11(D)))
            w = Fr.cos1[g]
            tb = n11(m11(inv11(g), Fr.rep1[w]))
            s = Fr.H1map[tb]                                     # alpha0 s alpha0^-1 = +-tbar
            Mb = r7(qconj(s))
            Bb, Cb = r7(beta), r7(cb)
            if rng_xy is None:
                x = (1, 0) if any(F.vec(Bb, (1, 0))) else (0, 1)
            else:
                x = rand_vec(F, rng_xy, Bb)
            a = F.vec(Bb, x)
            y = solve_y(F, a, target, rng_xy)
            b = F.vec(F.mat(Mb, Cb), y)
            assert any(b)
            if variant != "untw":
                b = F.fr(b)
            if variant == "projnorm":
                a, b = F.proj(a), F.proj(b)
            r = 1 if variant != "rand" else 1 + int(rng_r.integers(48))
            out.append((v, w, a, b, r))
    check_stars(S, out)
    return out


def edges_odd(S, Fr, rng_nu=None, rng_xy=None):
    """the same equations computed from the odd side (twisted model)."""
    F, r7 = S.F, S.red7
    out = []
    for w in range(NV):
        hw = Fr.rep1[w]
        for c in range(NCLS):
            cl = S.classes[c]
            nu = cl[0] if rng_nu is None else cl[rng_nu.integers(len(cl))]
            D = scal11(INV7_11, m11(Fr.A11, red11(nu)))          # alpha0 nu / 7 in I[1/7]^1
            assert det11(D) == 1
            g = n11(m11(hw, D))
            v = Fr.cos0[g]
            tb = n11(m11(inv11(g), Fr.rep0[v]))
            u = S.H0map[tb]                                      # u = +-tbar
            Nb, adjN, Uinv = r7(nu), r7(qconj(nu)), r7(qconj(u))
            if rng_xy is None:
                x = (1, 0) if any(F.vec(Nb, (1, 0))) else (0, 1)
            else:
                x = rand_vec(F, rng_xy, Nb)
            b2 = F.vec(Nb, x)
            y = solve_y(F, b2, 1, rng_xy)
            a = F.vec(F.mat(Uinv, adjN), y)
            out.append((v, w, a, F.fr(b2), 1))
    check_stars(S, out)
    return out


def check_stars(S, E):
    F = S.F
    deg0, deg1 = [0] * NV, [0] * NV
    pts0, pts1 = [set() for _ in range(NV)], [set() for _ in range(NV)]
    for v, w, a, b, r in E:
        deg0[v] += 1
        deg1[w] += 1
        pts0[v].add(F.proj(a))
        pts1[w].add(F.proj(b))
    assert deg0 == [NCLS] * NV and deg1 == [NCLS] * NV, (deg0, deg1)
    assert all(len(s) == NCLS for s in pts0) and all(len(s) == NCLS for s in pts1)


# ----------------------------------------------------------------------------- the linear system
def system(S, E, m):
    F = S.F
    n = m + 1
    ev = np.array([e[0] for e in E])
    ow = np.array([e[1] for e in E])
    A = np.array([e[2] for e in E], dtype=np.int64)
    B = np.array([e[3] for e in E], dtype=np.int64)
    r = np.array([e[4] for e in E], dtype=np.int64)
    rr = np.arange(n)
    monA = F.mul[F.pow[A[:, :1], m - rr], F.pow[A[:, 1:], rr]]
    monB = F.mul[F.pow[B[:, :1], m - rr], F.pow[B[:, 1:], rr]]
    negB = F.neg[F.mul[r[:, None], monB]]
    M = np.zeros((len(E), 2 * NV * n), dtype=np.uint8)
    rows = np.arange(len(E))[:, None]
    M[rows, ev[:, None] * n + rr] = monA
    M[rows, (NV + ow[:, None]) * n + rr] = negB
    return M


def dim_T(S, E, m):
    M = system(S, E, m)
    return M.shape[1] - S.F.rank(M)


def row_set(S, E, m):
    """the rows of the system, each scaled so that its first nonzero entry is 1, as a sorted list."""
    F = S.F
    M = system(S, E, m)
    first = M[np.arange(len(M)), (M != 0).argmax(axis=1)]
    Mn = F.mul[F.inv[first][:, None], M]
    return sorted(map(bytes, Mn))


def rank_f7(M):
    """rank over F_7 of the regular representation of a matrix over F_49 (each entry a + b t becomes the 2x2 block
    (a b; b a+b) of multiplication by a + b t on the basis 1, t); it is twice the rank over F_49."""
    a, b = M.astype(np.int64) % 7, M.astype(np.int64) // 7
    nr, nc = M.shape
    A = np.zeros((2 * nr, 2 * nc), dtype=np.int64)
    A[0::2, 0::2], A[0::2, 1::2], A[1::2, 0::2], A[1::2, 1::2] = a, b, b, (a + b) % 7
    inv = [0] + [pow(x, 5, 7) for x in range(1, 7)]
    r = 0
    for c in range(2 * nc):
        if r == 2 * nr:
            break
        nz = np.flatnonzero(A[r:, c])
        if nz.size == 0:
            continue
        i = r + int(nz[0])
        if i != r:
            A[[r, i]] = A[[i, r]]
        A[r, c:] = A[r, c:] * inv[int(A[r, c])] % 7
        rows = r + 1 + np.flatnonzero(A[r + 1:, c])
        if rows.size:
            A[rows, c:] = (A[rows, c:] - A[rows, c][:, None] * A[r, c:][None, :]) % 7
        r += 1
    return r


# ----------------------------------------------------------------------------- main
def main(Ks, checks=True):
    t0 = time.time()
    S = Setup()
    # alpha0: 2 + i + j + k, and the least element of the least class in the other A5-orbit of edges at the base vertex
    alphaA = ((4, 0), (2, 0), (2, 0), (2, 0))
    assert alphaA in S.cls_index
    oA = next(o for o in S.orbits if S.cls_index[alphaA] in o)
    oB = next(o for o in S.orbits if o is not oA)
    alphaB = S.classes[oB[0]][0]
    print(f"alpha0_A = 2+i+j+k (its edge lies in the A5-orbit of size {len(oA)}); alpha0_B = {fmt_q(alphaB)} "
          f"(orbit of size {len(oB)})", flush=True)
    FrA = Frame(S, alphaA)
    ms = [6 * k for k in Ks]
    print("PSL2(F_11) is generated by the images used; |H0| = |H1| = 60; 11 + 11 vertices; every star has 50 edges "
          "with distinct points (checked in every run below)", flush=True)

    # --- the table
    variants = ["tw", "untw", "badnorm", "badnormw", "projnorm", "rand"]
    table = {}
    for var in variants:
        t1 = time.time()
        E = edges_even(S, FrA, var, rng_r=np.random.default_rng(12345))
        for k, m in zip(Ks, ms):
            table[(k, var)] = dim_T(S, E, m)
        print(f"  variant {var:9s}: " + "  ".join(f"k={k}:{table[(k, var)]}" for k in Ks) +
              f"   ({time.time() - t1:.1f}s)", flush=True)
    print()
    hdr = f"{'k':>2} {'m':>3} {'22(m+1)-550':>11} {'(k-1)^2*11':>10} | " + " ".join(f"{v:>9}" for v in variants)
    print(hdr)
    print("-" * len(hdr))
    for k, m in zip(Ks, ms):
        print(f"{k:>2} {m:>3} {22 * (m + 1) - 550:>11} {(k - 1) ** 2 * 11:>10} | " +
              " ".join(f"{table[(k, v)]:>9}" for v in variants))
    print("(22(m+1)-550: count of unknowns minus equations; (k-1)^2*11: the bound of Theorem G, valid for 2 <= k <= 5)")
    print(flush=True)
    if not checks:
        print(f"total {time.time() - t0:.1f}s")
        return table, None

    fails = []
    R = lambda seed: np.random.default_rng(seed)

    def run(label, Fr, variant="tw", **seeds):
        t1 = time.time()
        kw = {"rng_r": R(777)}
        kw.update({key: R(val) for key, val in seeds.items()})
        E = edges_even(S, Fr, variant, **kw)
        dims = [dim_T(S, E, m) for m in ms]
        print(f"  {label:62s} " + " ".join(f"{d:>4}" for d in dims) + f"   ({time.time() - t1:.1f}s)", flush=True)
        return dims

    rng = R(11)
    alphaA2 = qmul(qmul(S.U[rng.integers(120)], alphaA), S.U[rng.integers(120)])
    FrB, FrA2 = Frame(S, alphaB), Frame(S, alphaA2)
    print("Independence of the twisted model; dims for k = " + " ".join(f"{k:>4}" for k in Ks))
    ref = [table[(k, "tw")] for k in Ks]
    for label, Fr, seeds in [
            ("tw  random x, y (seed 1)", FrA, dict(rng_xy=1)),
            ("tw  random x, y (seed 2)", FrA, dict(rng_xy=2)),
            ("tw  random class representatives beta (seed 3)", FrA, dict(rng_beta=3)),
            ("tw  random class representatives beta (seed 4)", FrA, dict(rng_beta=4)),
            ("tw  random coset representatives h_v, h_w (seed 5)", Frame(S, alphaA, R(5)), {}),
            ("tw  random coset representatives h_v, h_w (seed 6)", Frame(S, alphaA, R(6)), {}),
            ("tw  alpha0_B (other A5-orbit)", FrB, {}),
            (f"tw  alpha0_A' = u alpha0_A u' = {fmt_q(alphaA2)}", FrA2, {}),
            ("tw  alpha0_B, random h, beta, x, y (seeds 7, 8, 9)", Frame(S, alphaB, R(7)), dict(rng_beta=8, rng_xy=9)),
            ("tw  alpha0_A, random h, beta, x, y (seeds 10, 11, 12)", Frame(S, alphaA, R(10)),
             dict(rng_beta=11, rng_xy=12))]:
        dims = run(label, Fr, "tw", **seeds)
        if dims != ref:
            fails.append(f"tw depends on the choices: {label}: {dims} != {ref}")
    print("Equations (rows up to scalars) unchanged under random x, y and class representatives (seeds 31, 32)")
    for var in ("tw", "badnorm", "untw"):
        E0 = edges_even(S, FrA, var)
        E1 = edges_even(S, FrA, var, rng_xy=R(31), rng_beta=R(32))
        same = [row_set(S, E0, m) == row_set(S, E1, m) for m in ms]
        note = "  (untw: expected only where 48 | 2m, i.e. k = 4, 8)" if var == "untw" else ""
        print(f"  {var:62s} " + " ".join(f"{'yes' if s_ else 'no':>4}" for s_ in same) + note, flush=True)
        if var != "untw" and not all(same):
            fails.append(f"{var}: equations depend on x, y or on the class representatives")
        if var == "untw" and any(s_ != (k % 4 == 0) for k, s_ in zip(Ks, same)):
            fails.append("untw: dependence on x, y does not match the prediction 48 | 2m")
    E0, E1 = edges_even(S, FrA, "tw"), edges_even(S, FrA, "badnorm")
    if any(row_set(S, E0, m) != row_set(S, E1, m) for m in ms):
        fails.append("badnorm equations differ from tw")
    print("Controls under the same changes (not expected to be invariant unless well defined)")
    untw = [run("untw default", FrA, "untw"),
            run("untw random x, y (seed 1)", FrA, "untw", rng_xy=1),
            run("untw random x, y (seed 2)", FrA, "untw", rng_xy=2),
            run("untw random h_v, h_w (seed 5), beta (seed 3)", Frame(S, alphaA, R(5)), "untw", rng_beta=3),
            run("untw alpha0_B", FrB, "untw"),
            run("untw alpha0_B, random h, beta, x, y (seeds 7, 8, 9)", Frame(S, alphaB, R(7)), "untw",
                rng_beta=8, rng_xy=9)]
    if 4 in Ks and len({d[Ks.index(4)] for d in untw}) != 1:
        fails.append("untw at k = 4 (where it is well defined) depends on the choices")
    run("projnorm random h_v, h_w (seed 5)", Frame(S, alphaA, R(5)), "projnorm")
    run("projnorm alpha0_B", FrB, "projnorm")
    for seed in (1, 2, 3, 4, 5):
        E = edges_even(S, FrA, "rand", rng_r=R(seed))
        print(f"  {'rand gauge (seed ' + str(seed) + ')':62s} " + " ".join(f"{dim_T(S, E, m):>4}" for m in ms),
              flush=True)

    print("Cross-check: the equations computed from the odd side equal those from the even side (rows up to scalars)")
    for label, Fr, se, so in [("alpha0_A, default choices", FrA, {}, {}),
                              ("alpha0_B, random h, beta, nu, x, y", Frame(S, alphaB, R(21)),
                               dict(rng_xy=22, rng_beta=23), dict(rng_xy=24, rng_nu=25))]:
        Ee = edges_even(S, Fr, "tw", **{key: R(val) for key, val in se.items()})
        Eo = edges_odd(S, Fr, **{key: R(val) for key, val in so.items()})
        same = [row_set(S, Ee, m) == row_set(S, Eo, m) for m in ms]
        print(f"  {label:62s} " + " ".join(f"{'yes' if s_ else 'NO':>4}" for s_ in same), flush=True)
        if not all(same):
            fails.append(f"odd-side equations differ: {label}")

    print("Cross-check of the elimination: rank over F_7 of the regular representation = 2 * rank over F_49 (tw)")
    t1 = time.time()
    E = edges_even(S, FrA, "tw")
    okr = []
    for m in ms:
        M = system(S, E, m)
        okr.append(rank_f7(M) == 2 * S.F.rank(M))
    print(f"  {'tw default':62s} " + " ".join(f"{'yes' if o else 'NO':>4}" for o in okr) +
          f"   ({time.time() - t1:.1f}s)", flush=True)
    if not all(okr):
        fails.append("rank over F_7 != 2 rank over F_49")
    print()
    print("ALL CHECKS PASSED" if not fails else "FAILURES:\n  " + "\n  ".join(fails))
    print(f"total {time.time() - t0:.1f}s")
    return table, fails


def fmt_q(q):
    """a scaled quaternion as (w, x, y, z) with entries (a + b th)/2, th = theta."""
    def c(z):
        a, b = z
        if b == 0:
            return f"{a}/2" if a % 2 else f"{a // 2}"
        if a == 0:
            return f"{b}th/2"
        return f"({a}{'+' if b > 0 else '-'}{abs(b)}th)/2"
    return "(" + ", ".join(c(z) for z in q) + ")"


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    Ks = [int(a) for a in args] or [2, 3, 4, 5]
    assert all(1 <= k and 6 * k <= 48 for k in Ks), "need m = 6k <= 48 (evaluation on P^1(F_49) injective)"
    main(Ks, checks="--no-checks" not in sys.argv)
