"""Exhaustive and randomized checks of Theorem TP (the translate pigeonhole) and of the results around it.

Usage (from the paper's root directory; needs numpy):

    python3 tools/exhaustive_pigeonhole_checks.py            # all sections
    python3 tools/exhaustive_pigeonhole_checks.py n3 n4      # only the named sections

What it checks.  Over small finite fields, the statements of the paper's section "Symmetry: the translate
pigeonhole": Lemma (pigeonhole against a translate); Proposition (for the swap, the best case is the pairing value);
Theorem TP and the steps of its proof; Proposition (equal pieces: the bound is attained); Theorem (the line form of
Theorem TP); Theorem (twist classes) with Corollary (modulation frequencies); and, in one case, the copy rules of
Proposition (copy rules, every partition).  It also produces the numbers quoted in Remark (numerical: what the exact
value does not say) and in Remark (numerical: on a line, other shifts fail).  Every check of a statement of the paper
is an assertion; a line marked informational only prints a count and asserts nothing.  Sections marked exhaustive
decide their question; greedy extension, hill climbing and sampling give lower bounds on the largest code only.  A
run takes about 40 seconds on one core, prints its results and writes no files; it ends with a line "CHECKS FINISHED
... no assertion failed", or stops at the first failed assertion.  All random choices come from fixed seeds.

Conventions.  The side length, called d in the paper, is n here.
  X is n x n over GF(p); vec index of entry (i, j) is i*n + j.
  tau X = X^T.   (A (x) B) X = A X B^T, i.e. numpy.kron(A, B) on vec(X).
  sigma = rot(n, 1):  (sigma x)[c] = x[c+1 mod n].   P_J = diagonal mask of the class J.
  Class-uniform rule:  X[c][r] = sum_{i,j} calA[J(c)][i][r][j] * X[i][(j + c) mod n]      (x_c = sum_i calA_{J,i} sigma^c x_i).
  A "family" is a list of labels (sets of rows sharing one decoder) and selection maps v_c: F^{n^2} -> F^m;
  a subspace XS is a code of the family iff for every label
        sum_{c in label} v_c(X_c) = 0  (X_c in XS)   implies   sum_c row_c(X_c) = 0.
  (Then a decoder exists; K_from_code solves for it and the kernel of tau - K is recomputed from scratch.)
  "Chain bound": the bound floor((s n^2 + n chi)/(s + 1)) of Theorem TP for a set D0 of s + 1 shifts (Delta_0 in the
  paper); "best chain bound": its minimum over the sets of shifts that contain 0 (all of them in the sections
  convention, n3 and n4; sets of at most four shifts, three in odd characteristic, in the section search).
  H_delta is the space {X : x_{c+delta} = sigma^delta x_c whenever c and c+delta lie in one class}.  The pairing
  value is n(n+1)/2.

Sections:
  n2          n = 2, exhaustive over rules (all K of the family): Theorem TP with one class over GF(2) and GF(3); the
              line form with one class (all rules over GF(2), a sample over GF(3)); the twist family of one
              modulation frequency (all rules over GF(3), a sample over GF(5)).
  pigeonhole  Lemma (pigeonhole against a translate): exhaustive N = 2 (GF(2), GF(3)), exhaustive (S, T) N = 3 GF(2),
              structured random instances.
  swapfloor   Proposition (for the swap, the best case is the pairing value): rank(tau - 1); dim ker[tau, T] >= n
              (exhaustive n = 2 GF(2)); non-derogatory and derogatory G.
  convention  The class-uniform rule equals sum A (x) (P_J sigma^d); the steps of the proof of Theorem TP on real
              codes; Proposition (equal pieces: the bound is attained).
  n3          n = 3, exhaustive over all subspaces of GF(2)^9 of dimension >= 7 (rules on a cycle, rules on a line,
              and masks before the rotation); GF(3): all hyperplanes.  Remark (numerical: on a line, other shifts
              fail).
  n4          n = 4 over GF(2): is the bound attained?  Exhaustive over all codes containing H_delta; count and
              orbits of the extremal codes; no extremal code extends by one dimension; unequal pieces {0},{1,2,3}
              over GF(2) and GF(3); all copy rules for these pieces.  Remark (numerical: what the exact value does
              not say).
  search      Greedy and structured search, n = 4..6, GF(2), GF(3), GF(5), unequal intervals, non-interval classes;
              Theorem (the line form of Theorem TP) and the step dim(X cap T^-1 X) <= Mn of its proof on two-sided
              rules on a line; masks before the rotation.
  twist       Theorem (twist classes): Weyl families (Corollary (modulation frequencies)), dihedral families,
              nilpotent q-commuting families; hill climbing.
  tm          The chain bounds for the Thue-Morse colouring and for a random two-colouring of Z_n, with one and with
              two shifts (compare the open problem on classes with no almost-period).
"""
import itertools
import random
import sys
import time

import numpy as np


# ----------------------------------------------------------------------------------------------------------------
# GF(p) linear algebra
# ----------------------------------------------------------------------------------------------------------------
def rref(M, p):
    M = np.array(M, dtype=np.int64) % p
    rows, cols = M.shape
    r = 0
    piv = []
    for c in range(cols):
        if r == rows:
            break
        nz = np.nonzero(M[r:, c])[0]
        if nz.size == 0:
            continue
        k = r + int(nz[0])
        if k != r:
            M[[r, k]] = M[[k, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        if inv != 1:
            M[r] = (M[r] * inv) % p
        col = M[:, c].copy()
        col[r] = 0
        idx = np.nonzero(col)[0]
        if idx.size:
            M[idx] = (M[idx] - np.outer(col[idx], M[r])) % p
        piv.append(c)
        r += 1
    return M[:r], piv


def rank(M, p):
    M = np.asarray(M)
    if M.size == 0:
        return 0
    return len(rref(M, p)[1])


def nullspace(M, p):
    """Rows: a basis of {x : M x = 0}."""
    M = np.array(M, dtype=np.int64) % p
    cols = M.shape[1]
    R, piv = rref(M, p)
    ps = set(piv)
    free = [c for c in range(cols) if c not in ps]
    B = np.zeros((len(free), cols), dtype=np.int64)
    for t, f in enumerate(free):
        B[t, f] = 1
        for k, pc in enumerate(piv):
            B[t, pc] = (-R[k, f]) % p
    return B


def solve_right(S, L, p):
    """Find Y (m x k) with S Y = L (S: E x m, L: E x k); None if inconsistent.  Free unknowns are set to 0."""
    S = np.array(S, dtype=np.int64) % p
    L = np.array(L, dtype=np.int64) % p
    m = S.shape[1]
    R, piv = rref(np.hstack([S, L]), p)
    Y = np.zeros((m, L.shape[1]), dtype=np.int64)
    for k, pc in enumerate(piv):
        if pc >= m:
            return None
        Y[pc] = R[k, m:]
    assert not ((S @ Y - L) % p).any()
    return Y


def swap(n):
    S = np.zeros((n * n, n * n), dtype=np.int64)
    for r in range(n):
        for c in range(n):
            S[r * n + c, c * n + r] = 1
    return S


def rot(n, d=1):
    M = np.zeros((n, n), dtype=np.int64)
    for c in range(n):
        M[c, (c + d) % n] = 1
    return M


def mask(n, J):
    M = np.zeros((n, n), dtype=np.int64)
    for c in J:
        M[c, c] = 1
    return M


def comm(A, B, p):
    return (A @ B - B @ A) % p


def rnd(rng, shape, p):
    return np.array([rng.randrange(p) for _ in range(int(np.prod(shape)))], dtype=np.int64).reshape(shape)


def gauss_binom(N, d, q):
    num = den = 1
    for i in range(d):
        num *= q ** (N - i) - 1
        den *= q ** (i + 1) - 1
    return num // den


# ----------------------------------------------------------------------------------------------------------------
# Lemma (pigeonhole against a translate)
# ----------------------------------------------------------------------------------------------------------------
def rank2(a, b, c, d, p):
    if (a * d - b * c) % p:
        return 2
    return 1 if (a or b or c or d) else 0


def test_pigeonhole():
    t0 = time.time()
    # (i) exhaustive, N = 2, all triples (tau, K, T) over GF(2) and GF(3)
    for p in (2, 3):
        mats = list(itertools.product(range(p), repeat=4))
        eq = 0
        for tau in mats:
            for K in mats:
                s = tuple((x - y) % p for x, y in zip(tau, K))
                D = 2 - rank2(*s, p)
                if D == 0:
                    continue        # bound is trivially true
                for T in mats:
                    def cm(Mx):
                        a, b, c, d = Mx
                        e, f, g, h = T
                        return ((b * g - f * c) % p, (a * f + b * h - e * b - f * d) % p,
                                (c * e + d * g - g * a - h * c) % p, (c * f - g * b) % p)
                    kt = 2 - rank2(*cm(tau), p)
                    rc = rank2(*cm(K), p)
                    assert 2 * D <= 2 + kt + rc, (p, tau, K, T)
                    eq += (2 * D == 2 + kt + rc)
        print(f"(Lemma) exhaustive N=2 GF({p}): all {len(mats)**3} triples (tau,K,T) satisfy the bound; equality in {eq} triples")
    # (ii) exhaustive (S, T), N = 3, GF(2): rank[S,T] <= 2 rank S  (this is the Lemma, written for S = tau - K)
    allm = np.array([[(x >> k) & 1 for k in range(9)] for x in range(512)], dtype=np.int64).reshape(512, 3, 3)
    rk = np.array([rank(allm[x], 2) for x in range(512)])
    code = (1 << np.arange(9)).reshape(3, 3)
    worst = 0
    for s in range(512):
        C = (allm[s][None] @ allm - allm @ allm[s][None]) % 2
        idx = (C * code[None]).sum(axis=(1, 2))
        assert (rk[idx] <= 2 * rk[s]).all()
        worst = max(worst, int((rk[idx] - 2 * rk[s]).max()))
    print(f"(Lemma) exhaustive N=3 GF(2): rank[S,T] <= 2 rank S for all 262144 pairs (max of rank[S,T] - 2 rank S = {worst})")
    # (iii) structured random: planted kernel, adversarial T
    rng = random.Random(20261109)
    cnt = 0
    tight = 0
    for p in (2, 3, 5):
        for N in (4, 5, 6, 8, 9, 10):
            I = np.eye(N, dtype=np.int64)
            for trial in range(150):
                tau = rnd(rng, (N, N), p)
                if trial % 2:
                    tau = swap(3) if N == 9 else (swap(2) if N == 4 else tau)
                D0 = rng.randrange(1, N + 1)
                Xb = rnd(rng, (D0, N), p)                      # planted code = row space of Xb
                Q = nullspace(Xb, p)                           # rows q with q.x = 0 on the code
                Rm = rnd(rng, (N, Q.shape[0]), p)
                K = (tau + Rm @ Q) % p if Q.shape[0] else tau.copy()
                kind = trial % 5
                if kind == 0:
                    T = rnd(rng, (N, N), p)
                elif kind == 1:                                # T preserves the planted code
                    Bc = np.vstack([Xb, rnd(rng, (N, N), p)])
                    Rr, piv = rref(Bc.T, p)
                    basis = Bc[piv[:N]] if len(piv) >= N else None
                    if basis is None or rank(basis, p) < N:
                        T = rnd(rng, (N, N), p)
                    else:
                        d = rank(Xb, p)
                        blk = rnd(rng, (N, N), p)
                        blk[:d, d:] = 0
                        # T^T acts on row vectors: choose T with T(code) inside code
                        Binv = np.array(solve_right(basis, I, p))
                        T = (basis.T @ blk.T @ Binv.T) % p
                elif kind == 2:                                # T commutes with K
                    T = (K @ K + rng.randrange(p) * K + rng.randrange(p) * I) % p
                elif kind == 3:                                # T commutes with tau
                    T = (tau @ tau + rng.randrange(p) * tau) % p
                else:                                          # rank-one T
                    T = (rnd(rng, (N, 1), p) @ rnd(rng, (1, N), p)) % p
                D = N - rank(tau - K, p)
                kt = N - rank(comm(tau, T, p), p)
                rc = rank(comm(K, T, p), p)
                sharp = N - rank(comm(tau - K, T, p), p)       # dim ker [tau - K, T]
                assert 2 * D - N <= sharp <= kt + rc, (p, N, D, sharp, kt, rc)
                tight += (2 * D == N + kt + rc)
                cnt += 1
    print(f"(Lemma) structured random: {cnt} instances GF(2),GF(3),GF(5), N<=10, planted kernels; no violation of "
          f"2D-N <= dim ker[tau-K,T] <= dim ker[tau,T] + rank[K,T]; the Lemma is tight in {tight}   [{time.time()-t0:.1f}s]")


# ----------------------------------------------------------------------------------------------------------------
# Proposition (for the swap, the best case is the pairing value)
# ----------------------------------------------------------------------------------------------------------------
def companion(coeffs, p):
    n = len(coeffs)
    G = np.zeros((n, n), dtype=np.int64)
    for i in range(1, n):
        G[i, i - 1] = 1
    for i in range(n):
        G[i, n - 1] = (-coeffs[i]) % p
    return G


def centralizer_dim(G, p):
    n = G.shape[0]
    I = np.eye(n, dtype=np.int64)
    return n * n - rank(np.kron(G, I) - np.kron(I, G.T), p)


def test_swapfloor():
    t0 = time.time()
    for p in (2, 3, 5, 7):
        for n in range(2, 7):
            tau = swap(n)
            assert rank(tau - np.eye(n * n, dtype=np.int64), p) == n * (n - 1) // 2, (p, n)
    print("(swap floor) rank(tau - 1) = n(n-1)/2 for n = 2..6 over GF(2), GF(3), GF(5), GF(7)  (characteristic 2 included)")
    # exhaustive n = 2, GF(2): all 65536 T.  tau swaps coordinates 1 and 2 of the 4 coordinates.
    perm = [0, 2, 1, 3]

    def colperm(row):
        return (row & 1) | ((row >> 2 & 1) << 1) | ((row >> 1 & 1) << 2) | (row & 8)

    def rk4(rows):
        r = 0
        rows = list(rows)
        for bit in range(4):
            pv = next((k for k in range(r, 4) if rows[k] >> bit & 1), None)
            if pv is None:
                continue
            rows[r], rows[pv] = rows[pv], rows[r]
            for k in range(4):
                if k != r and rows[k] >> bit & 1:
                    rows[k] ^= rows[r]
            r += 1
        return r
    hist = {}
    for T in itertools.product(range(16), repeat=4):
        C = [T[perm[r]] ^ colperm(T[r]) for r in range(4)]     # (tau T - T tau), row r
        k = 4 - rk4(C)
        hist[k] = hist.get(k, 0) + 1
    assert min(hist) == 2
    print(f"(swap floor) exhaustive n=2 GF(2): dim ker[tau,T] over all 65536 T: histogram {dict(sorted(hist.items()))} (min = n = 2)")
    # non-derogatory G: all companion matrices; derogatory: compare with the centraliser dimension
    for p, n in ((2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (5, 2), (5, 3), (2, 5), (3, 4)):
        tau = swap(n)
        I = np.eye(n, dtype=np.int64)
        polys = list(itertools.product(range(p), repeat=n))
        if len(polys) > 130:
            polys = random.Random(1).sample(polys, 130)
        for cf in polys:
            G = companion(cf, p)
            T = np.kron(I, G) % p
            k = n * n - rank(comm(tau, T, p), p)
            assert k == n, (p, n, cf, k)
            # the kernel as in the proof of the Proposition: {X : X G^T = G X}
            k2 = n * n - rank(np.kron(I, G) - np.kron(G, I), p)
            assert k2 == n
    print("(swap floor) dim ker[tau, 1(x)G] = n for every companion matrix G tested (GF(2) n<=5, GF(3) n<=4, GF(5) n<=3); "
          "kernel = {X : X G^T = G X} confirmed")
    rng = random.Random(7)
    for p in (2, 3, 5):
        for n in (2, 3, 4):
            tau = swap(n)
            I = np.eye(n, dtype=np.int64)
            for _ in range(40):
                G = rnd(rng, (n, n), p)
                if rng.random() < 0.4:      # make derogatory matrices likely: block scalar / low rank
                    G = (rng.randrange(p) * I + rnd(rng, (n, 1), p) @ rnd(rng, (1, n), p) * (rng.random() < 0.5)) % p
                k = n * n - rank(comm(tau, np.kron(I, G) % p, p), p)
                assert k == centralizer_dim(G, p) >= n
                k = n * n - rank(comm(tau, np.kron(G, I) % p, p), p)
                assert k == centralizer_dim(G, p)
    print("(swap floor) dim ker[tau, 1(x)G] = dim ker[tau, G(x)1] = dim centraliser(G) on 360 random G (derogatory ones included)")
    # hill climbing: try to push dim ker[tau, T] below n
    least = {}
    for p in (2, 3, 5):
        for n in (3, 4):
            tau = swap(n)
            N = n * n
            best = N
            for start in range(4):
                T = rnd(rng, (N, N), p)
                cur = N - rank(comm(tau, T, p), p)
                for it in range(250):
                    T2 = T.copy()
                    for _ in range(rng.randrange(1, 4)):
                        T2[rng.randrange(N), rng.randrange(N)] = rng.randrange(p)
                    k = N - rank(comm(tau, T2, p), p)
                    if k <= cur:
                        T, cur = T2, k
                best = min(best, cur)
            assert best >= n
            least[(p, n)] = best
    print(f"(swap floor) hill climbing on T to minimise dim ker[tau,T]: least found {least} (never below n)   [{time.time()-t0:.1f}s]")


# ----------------------------------------------------------------------------------------------------------------
# Families and the code criterion
# ----------------------------------------------------------------------------------------------------------------
def sel_cyclic(n):
    return (lambda c: [i * n + (c + d) % n for i in range(n) for d in range(n)]), n * n


def sel_line2(n):
    """Two-sided window on a line: offsets d = j - c in (-n, n), no wrap-around."""
    return (lambda c: [(i * n + c + d) if 0 <= c + d < n else None
                       for i in range(n) for d in range(-(n - 1), n)]), n * (2 * n - 1)


def sel_line1(n):
    """One-sided truncated shift: x_c = sum_i calA_{J,i} S^c x_i, (S x)[j] = x[j+1], zero beyond the end."""
    return (lambda c: [(i * n + c + d) if c + d < n else None for i in range(n) for d in range(n)]), n * n


class Family:
    def __init__(self, n, labels, sel=None, m=None, E=None, name=""):
        self.n, self.labels, self.name = n, [list(l) for l in labels], name
        if E is None:
            E = {}
            for lab in self.labels:
                for c in lab:
                    Ec = np.zeros((m, n * n), dtype=np.int64)
                    for t, q in enumerate(sel(c)):
                        if q is not None:
                            Ec[t, q] = 1
                    E[c] = Ec
        self.E = E
        self.m = next(iter(E.values())).shape[0]

    @staticmethod
    def from_span(n, Bs, name=""):
        """All rows share one decoder; K = sum_t A_t (x) B_t with arbitrary A_t.  v_c(X) = (X B_t^T e_c)_t."""
        E = {}
        for c in range(n):
            Ec = np.zeros((len(Bs) * n, n * n), dtype=np.int64)
            for t, B in enumerate(Bs):
                for i in range(n):
                    Ec[t * n + i, i * n:(i + 1) * n] = B[c]
            E[c] = Ec
        return Family(n, [list(range(n))], E=E, name=name)

    def is_code(self, B, p):
        n = self.n
        B = np.asarray(B, dtype=np.int64) % p
        if B.shape[0] == 0:
            return True
        for lab in self.labels:
            S = np.vstack([B @ self.E[c].T for c in lab]) % p
            L = np.vstack([B[:, c * n:(c + 1) * n] for c in lab])
            if rank(S, p) != rank(np.hstack([S, L]), p):
                return False
        return True

    def K_from_code(self, B, p):
        """Solve for the decoders and return K (n^2 x n^2) with tau X = K X on the code; None if not a code."""
        n = self.n
        B = np.asarray(B, dtype=np.int64) % p
        K = np.zeros((n * n, n * n), dtype=np.int64)
        for lab in self.labels:
            S = np.vstack([B @ self.E[c].T for c in lab]) % p
            L = np.vstack([B[:, c * n:(c + 1) * n] for c in lab])
            Y = solve_right(S, L, p)
            if Y is None:
                return None
            dec = Y.T                                   # n x m ; x_c = dec @ v_c(X)
            for c in lab:
                rowsK = (dec @ self.E[c]) % p           # row r: functional giving X[c][r]
                for r in range(n):
                    K[r * n + c] = rowsK[r]
        return K


class Fam2:
    """GF(2) bitmask version of a Family (same criterion, independent implementation of the elimination)."""

    def __init__(self, fam):
        n = fam.n
        self.n, self.labels, self.m = n, fam.labels, fam.m
        self.maskv = (1 << fam.m) - 1
        self.col = {}
        for lab in fam.labels:
            for c in lab:
                E = fam.E[c] % 2
                col = [0] * (n * n)
                for q in range(n * n):
                    v = 0
                    for t in np.nonzero(E[:, q])[0]:
                        v |= 1 << int(t)
                    col[q] = v
                for r in range(n):
                    col[c * n + r] |= 1 << (fam.m + r)
                self.col[c] = col
        self.tab = None

    def build_tables(self):
        N = self.n * self.n
        self.tab = {}
        for c, col in self.col.items():
            t = [0] * (1 << N)
            for x in range(1, 1 << N):
                low = x & -x
                t[x] = t[x ^ low] ^ col[low.bit_length() - 1]
            self.tab[c] = t

    def img(self, c, x):
        if self.tab is not None:
            return self.tab[c][x]
        v = 0
        col = self.col[c]
        while x:
            low = x & -x
            v ^= col[low.bit_length() - 1]
            x ^= low
        return v

    def prefix(self, basis):
        """Pivot tables after inserting `basis`; None if `basis` is not a code."""
        state = []
        mv = self.maskv
        for lab in self.labels:
            piv = {}
            for c in lab:
                for b in basis:
                    v = self.img(c, b)
                    while True:
                        lo = v & mv
                        if not lo:
                            if v:
                                return None
                            break
                        h = lo.bit_length()
                        if h in piv:
                            v ^= piv[h]
                        else:
                            piv[h] = v
                            break
            state.append(piv)
        return state

    def is_code(self, basis, state=None):
        mv = self.maskv
        for k, lab in enumerate(self.labels):
            piv = dict(state[k]) if state is not None else {}
            for c in lab:
                for b in basis:
                    v = self.img(c, b)
                    while True:
                        lo = v & mv
                        if not lo:
                            if v:
                                return False
                            break
                        h = lo.bit_length()
                        if h in piv:
                            v ^= piv[h]
                        else:
                            piv[h] = v
                            break
        return True


def cyclic_family(n, classes):
    f, m = sel_cyclic(n)
    return Family(n, classes, f, m, name=f"cyclic {classes}")


def line2_family(n, classes):
    f, m = sel_line2(n)
    return Family(n, classes, f, m, name=f"line(two-sided) {classes}")


def line1_family(n, classes):
    f, m = sel_line1(n)
    return Family(n, classes, f, m, name=f"line(one-sided) {classes}")


def span_family_PJ_sigma(n, classes):
    """B in span{P_J sigma^d}: mask applied after the rotation (mask on the OUTPUT index c)."""
    Bs = [(mask(n, J) @ rot(n, d)) for J in classes for d in range(n)]
    return Family.from_span(n, Bs, name=f"span P_J sigma^d {classes}")


def span_family_sigma_PJ(n, classes):
    """B in span{sigma^d P_J}: mask applied before the rotation (mask on the INPUT index j)."""
    Bs = [(rot(n, d) @ mask(n, J)) for J in classes for d in range(n)]
    return Family.from_span(n, Bs, name=f"span sigma^d P_J {classes}")


def chi_cyclic(n, classes, shifts):
    cls = {c: k for k, J in enumerate(classes) for c in J}
    diffs = {(a - b) % n for a in shifts for b in shifts if a != b}
    par = list(range(n))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for c in range(n):
        for d in diffs:
            e = (c + d) % n
            if cls[c] == cls[e]:
                par[find(c)] = find(e)
    return len({find(c) for c in range(n)})


def best_chain_bound(n, classes, smax=None):
    """min over shift sets D0 containing 0 of floor((s n^2 + n chi)/(s+1)); returns (bound, D0, chi)."""
    smax = smax or n - 1
    best = (n * n, (0,), n)
    for s in range(1, smax + 1):
        for sh in itertools.combinations(range(1, n), s):
            ch = chi_cyclic(n, classes, (0,) + sh)
            b = (s * n * n + n * ch) // (s + 1)
            if b < best[0]:
                best = (b, (0,) + sh, ch)
    return best


def vec_bits(x, N):
    return np.array([(x >> q) & 1 for q in range(N)], dtype=np.int64)


def bits_of(v):
    return sum(int(b) << q for q, b in enumerate(v))


def sym_basis(n):
    B = []
    for i in range(n):
        for j in range(i, n):
            v = np.zeros(n * n, dtype=np.int64)
            v[i * n + j] = 1
            v[j * n + i] = 1
            B.append(v)
    return np.array(B)


def block_sym_basis(n, M):
    m = n // M
    B = []
    for I in range(M):
        for J in range(M):
            for k in range(m):
                for l in range(k, m):
                    v = np.zeros(n * n, dtype=np.int64)
                    v[(I * m + k) * n + J * m + l] = 1
                    v[(I * m + l) * n + J * m + k] = 1
                    B.append(v)
    return np.array(B)


def intervals(n, M):
    m = n // M
    return [list(range(k * m, (k + 1) * m)) for k in range(M)]


def coarse_transposition_tensor(n, M, p):
    """K = sum_{I,I'} A_{I,I'} (x) (P_I sigma^{(I'-I)m}), built directly as a sum of Kronecker products."""
    m = n // M
    K = np.zeros((n * n, n * n), dtype=np.int64)
    for I in range(M):
        for I2 in range(M):
            A = np.zeros((n, n), dtype=np.int64)       # A[r][i]: r in block I2, i = I*m + (r mod m)
            for l in range(m):
                A[I2 * m + l, I * m + l] = 1
            B = mask(n, range(I * m, (I + 1) * m)) @ rot(n, ((I2 - I) * m) % n)
            K += np.kron(A, B)
    return K % p


# ----------------------------------------------------------------------------------------------------------------
# Theorem TP: conventions and proof steps
# ----------------------------------------------------------------------------------------------------------------
def rule_to_K(n, classes, calA, p):
    """calA[J][i] is an n x n matrix (rows r, columns j).  K[(r,c),(i,j')] = calA[J(c)][i][r][(j'-c) mod n]."""
    cls = {c: k for k, J in enumerate(classes) for c in J}
    K = np.zeros((n * n, n * n), dtype=np.int64)
    for r in range(n):
        for c in range(n):
            for i in range(n):
                for j in range(n):
                    K[r * n + c, i * n + (j + c) % n] = calA[cls[c]][i][r][j]
    return K % p


def rule_to_tensor(n, classes, calA, p):
    K = np.zeros((n * n, n * n), dtype=np.int64)
    for k, J in enumerate(classes):
        for d in range(n):
            A = np.array([[calA[k][i][r][d] for i in range(n)] for r in range(n)], dtype=np.int64)
            K += np.kron(A, mask(n, J) @ rot(n, d))
    return K % p


def check_proof_steps(n, classes, K, p, shift_sets, tag):
    """On ker(tau - K): dimension of the multi-translate intersection, covariance on edges, dim <= n chi."""
    tau = swap(n)
    I = np.eye(n, dtype=np.int64)
    Sm = (tau - K) % p
    X = nullspace(Sm, p)
    D = X.shape[0]
    cls = {c: k for k, J in enumerate(classes) for c in J}
    out = []
    for sh in shift_sets:
        s = len(sh) - 1
        stack = [Sm] + [(Sm @ np.kron(I, rot(n, d))) % p for d in sh if d]
        Xp = nullspace(np.vstack(stack), p)
        dp = Xp.shape[0]
        ch = chi_cyclic(n, classes, sh)
        assert dp >= (s + 1) * D - s * n * n, (tag, sh, dp, D)
        assert dp <= n * ch, (tag, sh, dp, ch)
        assert (s + 1) * D <= s * n * n + n * ch
        diffs = {(a - b) % n for a in sh for b in sh if a != b}
        for v in Xp:
            Xm = v.reshape(n, n)
            for c in range(n):
                for d in diffs:
                    c2 = (c + d) % n
                    if cls[c] == cls[c2]:
                        # x_{c'} = sigma^{c'-c} x_c :  X[c'][j] = X[c][j + (c'-c)]
                        assert all(Xm[c2][j] == Xm[c][(j + d) % n] for j in range(n)), (tag, sh, c, c2)
        out.append((sh, dp, ch))
    return D, out


def test_convention():
    t0 = time.time()
    rng = random.Random(3)
    cnt = 0
    for p in (2, 3, 5):
        for n in (2, 3, 4, 5):
            for trial in range(6):
                M = rng.randrange(1, n + 1)
                colr = [rng.randrange(M) for _ in range(n)]
                classes = [[c for c in range(n) if colr[c] == k] for k in range(M)]
                classes = [J for J in classes if J]
                dens = rng.choice([0.1, 0.3, 1.0])
                calA = [[[[rng.randrange(p) if rng.random() < dens else 0 for _ in range(n)] for _ in range(n)]
                         for _ in range(n)] for _ in classes]
                K1 = rule_to_K(n, classes, calA, p)
                K2 = rule_to_tensor(n, classes, calA, p)
                assert (K1 == K2).all()
                # kernel vectors satisfy the rule written out with explicit rotations
                X = nullspace(swap(n) - K1, p)
                cls = {c: k for k, J in enumerate(classes) for c in J}
                for v in X:
                    Xm = v.reshape(n, n)
                    for c in range(n):
                        for r in range(n):
                            val = sum(calA[cls[c]][i][r][j] * Xm[i][(j + c) % n] for i in range(n) for j in range(n))
                            assert (val - Xm[c][r]) % p == 0
                # the two formulations of the family agree as code criteria
                f1 = cyclic_family(n, classes)
                f2 = span_family_PJ_sigma(n, classes)
                for _ in range(4):
                    Bt = rnd(rng, (rng.randrange(1, n * n), n * n), p)
                    assert f1.is_code(Bt, p) == f2.is_code(Bt, p)
                if X.shape[0]:
                    assert f1.is_code(X, p) and f2.is_code(X, p)
                bound = best_chain_bound(n, classes)[0]
                assert X.shape[0] <= bound
                cnt += 1
    print(f"(TP) convention: class-uniform rule == sum_(J,d) A_(J,d) (x) (P_J sigma^d) [mask AFTER rotation, on the output "
          f"index] on {cnt} random rules; kernels obey the rule and the chain bound; label criterion == span criterion")
    # block-symmetric code: tensor form, exact dimension, proof steps
    for p in (2, 3, 5):
        for n, M in ((4, 2), (6, 2), (6, 3), (8, 2), (8, 4), (9, 3), (6, 6), (5, 1), (6, 1)):
            if p > 2 and n > 6:
                continue
            classes = intervals(n, M)
            K = coarse_transposition_tensor(n, M, p)
            fam = cyclic_family(n, classes)
            Xk = nullspace(swap(n) - K, p)
            D = Xk.shape[0]
            assert D == (n * n + M * n) // 2 == block_sym_basis(n, M).shape[0]
            assert rank(np.vstack([Xk, block_sym_basis(n, M)]), p) == D          # same space
            assert fam.is_code(Xk, p)
            Kc = fam.K_from_code(Xk, p)                 # decoder re-solved from the code alone
            assert Kc is not None and n * n - rank(swap(n) - Kc, p) >= D
            shsets = [(0, 1), (0, n - 1)] + ([(0, 1, 2)] if n > 2 else []) + ([(0, 2)] if n > 2 else [])
            D2, info = check_proof_steps(n, classes, K, p, shsets, ("blocksym", n, M, p))
            assert D2 == D
            if p == 2:
                print(f"(TP) n={n} M={M}: coarse transposition (tensor form) has kernel = block-symmetric, D = {D} = "
                      f"(n^2+Mn)/2; D0={{0,1}}: dim X' = {info[0][1]}, n*chi = {n*info[0][2]}")
    print(f"(TP) Proposition (equal pieces: the bound is attained): block-symmetric checks passed over GF(2), GF(3), GF(5)   [{time.time()-t0:.1f}s]")


# ----------------------------------------------------------------------------------------------------------------
# enumeration of subspaces
# ----------------------------------------------------------------------------------------------------------------
def subspaces_gf2(N, d):
    """All d-dimensional subspaces of GF(2)^N as RREF bases (lists of ints)."""
    for piv in itertools.combinations(range(N), d):
        ps = set(piv)
        free = [(k, j) for k in range(d) for j in range(piv[k] + 1, N) if j not in ps]
        base = [1 << piv[k] for k in range(d)]
        for bits in range(1 << len(free)):
            rows = base[:]
            t = 0
            b = bits
            while b:
                if b & 1:
                    k, j = free[t]
                    rows[k] |= 1 << j
                b >>= 1
                t += 1
            yield rows


def max_code_dim_exhaustive(f2, N, dims, stop_at_first=False):
    """For each d in dims (descending): count d-dimensional codes.  Returns {d: count}."""
    res = {}
    for d in dims:
        cnt = 0
        ex = None
        for basis in subspaces_gf2(N, d):
            if f2.is_code(basis):
                cnt += 1
                if ex is None:
                    ex = basis
        res[d] = (cnt, ex)
        if cnt and stop_at_first:
            break
    return res


def test_n3():
    t0 = time.time()
    n, N = 3, 9
    assert sum(1 for _ in subspaces_gf2(N, 7)) == gauss_binom(N, 7, 2) == 43435
    sym = [bits_of(v) for v in sym_basis(n)]
    parts = {"M=1 {012}": [[0, 1, 2]], "M=2 {0}{12}": [[0], [1, 2]], "M=2 {01}{2}": [[0, 1], [2]],
             "M=2 {02}{1}": [[0, 2], [1]], "M=3": [[0], [1], [2]]}
    print("(TP) n=3, GF(2), EXHAUSTIVE over all subspaces of dimension 9, 8 (511) and 7 (43435):")
    results = {}
    for kind, mk in (("cyclic", cyclic_family), ("line two-sided", line2_family), ("line one-sided", line1_family),
                     ("masks before rotation (sigma^d P_J)", span_family_sigma_PJ)):
        for pname, classes in parts.items():
            fam = mk(n, classes)
            f2 = Fam2(fam)
            f2.build_tables()
            full = f2.is_code([1 << q for q in range(N)])
            if full:
                mx, cnt = 9, 1
            else:
                r = max_code_dim_exhaustive(f2, N, (8, 7), stop_at_first=True)
                if r.get(8, (0,))[0]:
                    mx, cnt = 8, r[8][0]
                elif r[7][0]:
                    mx, cnt = 7, r[7][0]
                else:
                    assert f2.is_code(sym), "symmetric matrices should be a code"
                    mx, cnt = 6, None
            M = len(classes)
            if kind == "cyclic":
                b, sh, ch = best_chain_bound(n, classes)
                bnd = f"best chain bound {b} (D0={sh}, chi={ch})"
                assert mx <= b, (kind, pname, mx, b)
            elif kind.startswith("masks"):
                b = (n * n + M * n) // 2
                bnd = f"(n^2+Mn)/2 = {b}"
            else:
                b = (n * n + M * n) // 2
                bnd = f"(n^2+Mn)/2 = {b}; for comparison (n^2+(M+1)n-M)/2 = {(n*n+(M+1)*n-M)//2}"
            results[(kind, pname)] = mx
            cs = f", number of codes of that dimension: {cnt}" if cnt is not None else " (symmetric matrices; no 7-dim code exists)"
            flag = "" if mx <= b else "   <-- EXCEEDS (n^2+Mn)/2"
            print(f"   {kind:36s} {pname:12s}: exact max code dim = {mx}{cs}; {bnd}{flag}")
    print(f"   [{time.time()-t0:.1f}s]")
    # The picture at n = 3: cyclic = chain bound in every case; one-sided line = n(n+1)/2 always;
    # two-sided line = (n^2+Mn)/2 for INTERVAL classes, but 8 > 7 for the non-interval classes {0,2},{1}
    # (Remark (numerical: on a line, other shifts fail)).
    assert results[("line two-sided", "M=1 {012}")] == 6 and results[("line two-sided", "M=2 {01}{2}")] == 7
    assert results[("line two-sided", "M=2 {0}{12}")] == 7
    assert all(results[("line one-sided", pn)] == 6 for pn in parts)
    assert all(results[("masks before rotation (sigma^d P_J)", pn)] <= (9 + 3 * len(parts[pn])) // 2 for pn in parts)
    # verify the exceeding instance from scratch through K: two-sided line, classes {0,2},{1}, delta = 2
    pname = "M=2 {02}{1}"
    if results[("line two-sided", pname)] == 8:
        classes = parts[pname]
        fam = line2_family(n, classes)
        f2 = Fam2(fam)
        f2.build_tables()
        ex = next(b for b in subspaces_gf2(N, 8) if f2.is_code(b))
        B = np.array([vec_bits(x, N) for x in ex])
        K = fam.K_from_code(B, 2)
        D = N - rank(swap(n) - K, 2)
        assert D == 8
        # K = sum_{J,d} A_{J,d} (x) (P_J S_d), S_d the truncated shift by d (no wrap-around): rebuild and compare
        Kt = np.zeros_like(K)
        for J in classes:
            for d in range(-(n - 1), n):
                Sd = np.zeros((n, n), dtype=np.int64)
                for c in J:
                    if 0 <= c + d < n:
                        Sd[c, c + d] = 1
                A = np.zeros((n, n), dtype=np.int64)
                for r in range(n):
                    for i in range(n):
                        vals = {int(K[r * n + c, i * n + c + d]) for c in J if 0 <= c + d < n}
                        assert len(vals) <= 1          # the decoder depends on (class, offset) only
                        A[r, i] = vals.pop() if vals else 0
                Kt += np.kron(A, Sd)
        assert ((Kt - K) % 2 == 0).all()
        print(f"   two-sided line, classes {{0,2}},{{1}}, n=3: K = sum_(J,d) A_(J,d) (x) (P_J * truncated shift^d) rebuilt as a "
              f"Kronecker sum; dim ker(tau-K) = {D} > 7 = floor((n^2 + n*chi)/2) with delta=2, chi=2.")
        print(f"      the code is the hyperplane orthogonal to {nullspace(nullspace(swap(n) - K, 2), 2)[0].reshape(n, n).tolist()}")
    # GF(3): all hyperplanes (9841) for the M = 2 partitions (bound 7, so no 8-dimensional code may exist)
    p = 3
    t1 = time.time()
    hyp = []
    for h in itertools.product(range(3), repeat=9):
        nzs = [x for x in h if x]
        if nzs and nzs[0] == 1:
            hyp.append(h)
    assert len(hyp) == (3 ** 9 - 1) // 2
    for kind, mk in (("cyclic", cyclic_family), ("line two-sided", line2_family)):
        for pname in ("M=2 {01}{2}", "M=1 {012}"):
            fam = mk(n, parts[pname])
            cnt = 0
            for h in hyp:
                B = nullspace(np.array([h]), p)
                if fam.is_code(B, p):
                    cnt += 1
            print(f"   GF(3) {kind:16s} {pname}: 8-dimensional codes among all 9841 hyperplanes: {cnt}")
            if kind == "cyclic":
                assert cnt == 0
    print(f"   [{time.time()-t1:.1f}s]")


# ----------------------------------------------------------------------------------------------------------------
# n = 4, GF(2)
# ----------------------------------------------------------------------------------------------------------------
def set_partitions(elems):
    if not elems:
        yield []
        return
    first, rest = elems[0], elems[1:]
    for part in set_partitions(rest):
        for k in range(len(part)):
            yield part[:k] + [[first] + part[k]] + part[k + 1:]
        yield [[first]] + part


def H_delta_basis(n, classes, delta, p=2):
    """Basis of {X : x_{c+delta} = sigma^delta x_c whenever c, c+delta lie in one class}."""
    cls = {c: k for k, J in enumerate(classes) for c in J}
    rows = []
    for c in range(n):
        c2 = (c + delta) % n
        if cls[c] == cls[c2]:
            for j in range(n):
                v = np.zeros(n * n, dtype=np.int64)
                v[c2 * n + j] += 1
                v[c * n + (j + delta) % n] -= 1
                rows.append(v % p)
    if not rows:
        return np.eye(n * n, dtype=np.int64)
    return nullspace(np.array(rows), p)


def test_n4():
    t0 = time.time()
    n, N = 4, 16
    print("(TP) n=4, GF(2): all 15 set partitions of Z_4; exact attainment test where the best bound is "
          "(n^2 + n chi)/2 with one shift delta (then D = bound forces the code to contain H_delta):")
    seen = set()
    ext_info = {}
    for part in set_partitions(list(range(n))):
        classes = sorted(sorted(J) for J in part)
        # canonical form up to rotation of Z_4
        canon = min(tuple(sorted(tuple(sorted((c + t) % n for c in J)) for J in classes)) for t in range(n))
        if canon in seen:
            continue
        seen.add(canon)
        classes = [list(J) for J in canon]
        b, sh, ch = best_chain_bound(n, classes)
        fam = cyclic_family(n, classes)
        f2 = Fam2(fam)
        line = f"   classes {classes}: best chain bound {b} (D0={sh}, chi={ch})"
        if b == N:
            full = f2.is_code([1 << q for q in range(N)])
            print(line + f"; full space is a code: {full}")
            continue
        if len(sh) == 2 and (N + n * ch) % 2 == 0 and ch >= 2:
            delta = sh[1]
            Hb = H_delta_basis(n, classes, delta)
            assert Hb.shape[0] == n * ch
            Hbits = [bits_of(v) for v in Hb]
            st = f2.prefix(Hbits)
            assert st is not None, "H_delta must itself be a code"
            # complement of H
            comp = []
            cur = np.array(Hb)
            for q in range(N):
                e = np.zeros(N, dtype=np.int64)
                e[q] = 1
                if rank(np.vstack([cur, e]), 2) > cur.shape[0]:
                    cur = np.vstack([cur, e])
                    comp.append(1 << q)
            qd = len(comp)
            assert qd == N - n * ch and qd % 2 == 0
            lift = [0] * (1 << qd)
            for x in range(1, 1 << qd):
                low = x & -x
                lift[x] = lift[x ^ low] ^ comp[low.bit_length() - 1]
            f2.build_tables()
            cnt = 0
            tot = 0
            exts = []
            for ub in subspaces_gf2(qd, qd // 2):
                tot += 1
                if f2.is_code([lift[u] for u in ub], st):
                    cnt += 1
                    exts.append(tuple(ub))
            print(line + f"; codes of dimension {b} (all contain H_delta): {cnt} of {tot} candidates"
                  + ("  -> bound ATTAINED" if cnt else "  -> bound NOT attained; exact max <= " + str(b - 1)))
            ext_info[canon] = (classes, delta, Hb, comp, lift, exts, f2, st)
        else:
            print(line + "; (not decided exhaustively here; see the section search)")
    # Upper bound at n = 4 on the most dangerous candidates: NO extremal code extends by one dimension.
    # (All subspaces of dimension bound+1 that contain an extremal code are tested: 15 per extremal code.)
    t1 = time.time()
    tested = 0
    for canon, (classes, delta, Hb, comp, lift, exts, f2, st) in ext_info.items():
        Hbits = [bits_of(v) for v in Hb]
        qd = len(comp)
        for ub in exts:
            basis = Hbits + [lift[u] for u in ub]
            st2 = f2.prefix(basis)
            assert st2 is not None
            pivs = {(u & -u).bit_length() - 1 for u in ub}
            nonp = [q for q in range(qd) if q not in pivs]
            for msk in range(1, 1 << len(nonp)):
                w = 0
                for t, q in enumerate(nonp):
                    if msk >> t & 1:
                        w |= 1 << q
                assert not f2.is_code([lift[w]], st2), (classes, ub, w)
                tested += 1
    print(f"   upper bound at n=4: none of the {tested} subspaces of dimension bound+1 containing an extremal code is a code"
          f"   [{time.time()-t1:.1f}s]")
    # uniqueness of the extremal code for {01}{23}
    canon = ((0, 1), (2, 3))
    classes, delta, Hb, comp, lift, exts, f2, st = ext_info[canon]
    # Q-coordinates: q1 = x_1 - sigma x_0 (bits 0..3), q2 = x_3 - sigma x_2 (bits 4..7)
    def qimage(v):          # v: vec of X (length 16) -> 8-bit element of Q
        X = v.reshape(4, 4)
        q1 = [(X[1][j] + X[0][(j + 1) % 4]) % 2 for j in range(4)]
        q2 = [(X[3][j] + X[2][(j + 1) % 4]) % 2 for j in range(4)]
        return sum(int(b) << k for k, b in enumerate(q1 + q2))

    def rref_bits(vs):
        piv = {}
        for v in vs:
            while v:
                l = (v & -v).bit_length() - 1
                if l in piv:
                    v ^= piv[l]
                else:
                    piv[l] = v
                    break
        # full reduction
        keys = sorted(piv)
        for a in keys:
            for b in keys:
                if a != b and piv[b] >> a & 1:
                    piv[b] ^= piv[a]
        return tuple(piv[k] for k in keys)
    # coordinate-free: push every extremal code to Q = F^16 / H through qimage (kernel H, bijective on the complement)
    extset = {rref_bits([qimage(vec_bits(lift[u], 16)) for u in ub]) for ub in exts}
    assert len(extset) == len(exts) and all(len(u) == 4 for u in extset)
    bs = rref_bits([qimage(v) for v in block_sym_basis(4, 2)])
    assert len(bs) == 4 and bs in extset
    # symmetries acting on Q = R^2, R = GF(2)[x]/(x^4-1): unit multiplications on each class, class swap
    def mulx(q, which):     # sigma on one R-coordinate: (sigma x)[j] = x[j+1]
        lo, hi = q & 15, q >> 4
        def s(a):
            return ((a >> 1) | ((a & 1) << 3)) & 15
        return (s(lo) if which == 0 else lo) | ((s(hi) if which == 1 else hi) << 4)

    def mulu(q, which):     # multiplication by x + x^2 + x^3 (a unit of order 2)
        a = mulx(q, which)
        b = mulx(a, which)
        c = mulx(b, which)
        part = lambda z: (z & 15) if which == 0 else (z >> 4)
        val = part(a) ^ part(b) ^ part(c)
        return (q & (0xF0 if which == 0 else 0x0F)) | (val if which == 0 else val << 4)

    def swp(q):
        return (q >> 4) | ((q & 15) << 4)

    def rev(q):             # reflection j -> -j on both coordinates (sigma -> sigma^-1)
        def r(a):
            return sum(((a >> j) & 1) << ((-j) % 4) for j in range(4))
        return r(q & 15) | (r(q >> 4) << 4)
    gens = [lambda q: mulx(q, 0), lambda q: mulx(q, 1), lambda q: mulu(q, 0), lambda q: mulu(q, 1), swp, rev]
    par = {u: u for u in extset}

    def find(u):
        while par[u] != u:
            par[u] = par[par[u]]
            u = par[u]
        return u
    closed = True
    for u in list(extset):
        for g in gens:
            w = rref_bits([g(v) for v in u])
            if w not in extset:
                closed = False
                continue
            par[find(u)] = find(w)
    orbits = {}
    for u in extset:
        orbits.setdefault(find(u), []).append(u)
    sizes = sorted(len(o) for o in orbits.values())
    print(f"   extremal (12-dim) codes for {{01}}{{23}}: {len(extset)}; block-symmetric is one of them; under the group "
          f"generated by unit multiplications of R on each class, the class swap and the reflection (closed on the set: "
          f"{closed}) they fall into {len(orbits)} orbits; orbit of block-symmetric has size "
          f"{len(orbits[find(bs)])}; largest orbit {sizes[-1]}")
    assert len(orbits) > 1
    # Unequal pieces {0},{1,2,3}: the bound 12 is attained although no coarse transposition of square blocks exists.
    # Codes containing H = {x_2 = sigma x_1, x_3 = sigma x_2} in the chart U = {x_0 = x_1 = 0, x_3 = Gamma x_2}:
    # with Delta = Gamma - sigma and C = [Delta, sigma] the code condition is "C invertible and C Delta = sigma C"
    # (used here only to list candidates).  Brute force over all Delta in M_4(GF(p)), p = 2, 3; every solution is
    # re-verified by the code criterion.
    classes = [[0], [1, 2, 3]]
    fam = cyclic_family(n, classes)
    for p in (2, 3):
        t1 = time.time()
        sg = rot(n, 1)
        total = p ** N
        pw = p ** np.arange(N, dtype=np.int64)
        Hb = H_delta_basis(n, classes, 1, p)
        nsol = 0
        for start in range(0, total, 400000):
            idx = np.arange(start, min(total, start + 400000), dtype=np.int64)
            Dl = ((idx[:, None] // pw[None, :]) % p).reshape(-1, n, n)
            C = (Dl @ sg - sg @ Dl) % p
            ok = ~((C @ Dl - sg @ C) % p).reshape(len(idx), -1).any(axis=1)
            for k in np.nonzero(ok)[0]:
                if rank(C[k], p) < n:
                    continue
                Gam = (Dl[k] + sg) % p
                U = []
                for j in range(n):
                    X = np.zeros((n, n), dtype=np.int64)
                    X[2, j] = 1
                    X[3] = Gam[:, j]
                    U.append(X.reshape(-1))
                B = np.vstack([Hb, np.array(U)]) % p
                assert rank(B, p) == 12 and fam.is_code(B, p)
                if nsol == 0:
                    K = fam.K_from_code(B, p)
                    assert N - rank(swap(n) - K, p) == 12
                nsol += 1
        assert nsol > 0
        print(f"   classes {{0}},{{1,2,3}} over GF({p}): {nsol} codes of dimension 12 = (n^2+Mn)/2 of the form H + graph(Gamma) "
              f"(each verified by the criterion; one through its K)   [{time.time()-t1:.1f}s]")
    bm = best_copy_rule(4, [[0], [1, 2, 3]])
    assert bm == 11
    print(f"   classes {{0}},{{1,2,3}}: best COPY rule (all 16^4 copy rules for the class of three rows): {bm} < 12; "
          f"the extremal codes are not transpositions of entries")
    print(f"   [{time.time()-t0:.1f}s]")


def best_copy_rule(n, classes):
    """Largest code of a class-uniform COPY rule (every output entry copies one stored entry; compare
    Proposition (copy rules, every partition)):
    X[c][r] = X[i][(s + c) mod n] with (i, s) depending on (class of c, r) only.  Exhaustive; small cases only.
    The code dimension is the number of connected components of the copy graph."""
    cells = [(c, r) for c in range(n) for r in range(n)]
    opts = [(i, s) for i in range(n) for s in range(n)]
    fixed, free = {}, []
    for k, J in enumerate(classes):
        for r in range(n):
            if len(J) == 1:
                fixed[(k, r)] = (J[0], (r - J[0]) % n)        # X[c][r] = X[c][r]: a singleton class is unconstrained
            else:
                free.append((k, r))
    best = 0
    for combo in itertools.product(opts, repeat=len(free)):
        ch = dict(fixed)
        ch.update(zip(free, combo))
        par = {x: x for x in cells}

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for (k, r), (i, s_) in ch.items():
            for c in classes[k]:
                a, b = find((c, r)), find((i, (s_ + c) % n))
                if a != b:
                    par[a] = b
        best = max(best, len({find(x) for x in cells}))
    return best


# ----------------------------------------------------------------------------------------------------------------
# searches
# ----------------------------------------------------------------------------------------------------------------
def greedy2(f2, N, seed, rng, tries, weights=(1, 2, 3)):
    basis = list(seed)
    st = f2.prefix(basis)
    assert st is not None
    red = {}

    def reduce(v):
        while v:
            h = v.bit_length()
            if h in red:
                v ^= red[h]
            else:
                return v
        return 0
    for b in basis:
        v = reduce(b)
        if v:
            red[v.bit_length()] = v
    for _ in range(tries):
        w = rng.choice(weights)
        x = 0
        for _ in range(w):
            x ^= 1 << rng.randrange(N)
        if rng.random() < 0.15:
            x = rng.getrandbits(N)
        v = reduce(x)
        if not v:
            continue
        if f2.is_code([x], st):
            basis.append(x)
            red[v.bit_length()] = v
            st = f2.prefix(basis)
    return basis


def greedy_p(fam, p, seed, rng, tries):
    N = fam.n ** 2
    B = np.array(seed, dtype=np.int64).reshape(-1, N) % p
    assert fam.is_code(B, p)
    for _ in range(tries):
        x = np.zeros(N, dtype=np.int64)
        for _ in range(rng.choice((1, 2, 2, 3))):
            x[rng.randrange(N)] = rng.randrange(1, p)
        if rng.random() < 0.15:
            x = rnd(rng, (N,), p)
        B2 = np.vstack([B, x])
        if rank(B2, p) == B.shape[0]:
            continue
        if fam.is_code(B2, p):
            B = B2
    return B


def test_search():
    t0 = time.time()
    rng = random.Random(99)
    print("(TP) searches (lower bounds from greedy extension, GF(2); seeds: 0, symmetric, H_delta); every code found is "
          "re-verified through its K (kernel of tau - K recomputed) and checked against the chain bound:")
    cases = []
    for n in (4, 5, 6):
        for classes in ([[0], list(range(1, n))], [[0, 1], list(range(2, n))], [list(range(n))],
                        [[0, 1], [2, 3], list(range(4, n))] if n >= 5 else [[0], [1], [2, 3]],
                        [list(range(0, n, 2)), list(range(1, n, 2))],
                        [[0, 1, 3], [c for c in range(n) if c not in (0, 1, 3)]] if n >= 5 else [[0, 2, 3], [1]],
                        [[0, 2], [c for c in range(n) if c not in (0, 2)]]):
            if all(classes) and classes not in [c for (m_, c) in cases if m_ == n]:
                cases.append((n, classes))
    for n, classes in cases:
        N = n * n
        fam = cyclic_family(n, classes)
        f2 = Fam2(fam)
        b, sh, ch = best_chain_bound(n, classes, smax=min(3, n - 1))
        best = 0
        bestB = None
        seeds = [[], [bits_of(v) for v in sym_basis(n)]]
        for d in range(1, n):
            Hb = [bits_of(v) for v in H_delta_basis(n, classes, d)]
            if len(Hb) < N and f2.prefix(Hb) is not None:
                seeds.append(Hb)
        tries = 500 if n <= 5 else 250
        for seed in seeds:
            for rep in range(2 if n <= 5 else 1):
                B = greedy2(f2, N, seed, rng, tries)
                if len(B) > best:
                    best, bestB = len(B), B
        Bm = np.array([vec_bits(x, N) for x in bestB])
        K = fam.K_from_code(Bm, 2)
        D = N - rank(swap(n) - K, 2)
        assert D >= best and D <= b, (n, classes, D, b)
        D2, info = check_proof_steps(n, classes, K, 2, [sh, (0, 1)], ("search", n, classes))
        print(f"   n={n} classes {classes}: best found {D} (pairing {n*(n+1)//2}); chain bound {b} (D0={sh}, chi={ch})"
              + ("  ATTAINED" if D == b else ""))
    print(f"   [{time.time()-t0:.1f}s]")
    # odd characteristic, small n
    t1 = time.time()
    for p in (3, 5):
        for n, classes in ((3, [[0, 1], [2]]), (4, [[0, 1], [2, 3]]), (4, [[0], [1, 2, 3]]), (4, [[0, 2], [1, 3]]),
                           (5, [[0, 1], [2, 3, 4]])):
            if p == 5 and n == 5:
                continue
            N = n * n
            fam = cyclic_family(n, classes)
            b, sh, ch = best_chain_bound(n, classes, smax=2)
            best = None
            for d in range(1, n):
                Hb = H_delta_basis(n, classes, d, p)
                if Hb.shape[0] < N and fam.is_code(Hb, p):
                    B = greedy_p(fam, p, Hb, rng, 120 if n <= 4 else 60)
                    if best is None or B.shape[0] > best.shape[0]:
                        best = B
            B = greedy_p(fam, p, sym_basis(n), rng, 80)
            if best is None or B.shape[0] > best.shape[0]:
                best = B
            K = fam.K_from_code(best, p)
            D = N - rank(swap(n) - K, p)
            assert best.shape[0] <= D <= b
            check_proof_steps(n, classes, K, p, [sh, (0, 1)], ("searchp", p, n, classes))
            print(f"   GF({p}) n={n} classes {classes}: best found {D}; chain bound {b}" + ("  ATTAINED" if D == b else ""))
    print(f"   [{time.time()-t1:.1f}s]")
    # two-sided line family (windows on a line, no wrap-around), INTERVAL classes: Theorem (the line form of
    # Theorem TP).  Its proof gives dim (X cap T^-1 X) <= M n for T = truncated column shift, hence
    # D <= (n^2 + M n)/2.  Check both on codes.
    t2 = time.time()

    def line_steps(n, classes, K, p):
        I = np.eye(n, dtype=np.int64)
        Sh = np.zeros((n, n), dtype=np.int64)
        for j in range(n - 1):
            Sh[j, j + 1] = 1                         # (X Sh^T)[i][j] = X[i][j+1], zero in the last column
        Sm = (swap(n) - K) % p
        D = n * n - rank(Sm, p)
        dp = n * n - rank(np.vstack([Sm, (Sm @ np.kron(I, Sh)) % p]), p)
        assert dp >= 2 * D - n * n
        assert dp <= len(classes) * n, (n, classes, dp)
        assert 2 * D <= n * n + len(classes) * n, (n, classes, D)
        return D, dp
    for n, classes in ((3, [[0, 1, 2]]), (4, [[0, 1, 2, 3]]), (5, [list(range(5))]), (4, [[0, 1], [2, 3]]),
                       (4, [[0], [1, 2, 3]]), (5, [[0, 1], [2, 3, 4]]), (6, [list(range(6))]), (6, [[0, 1, 2], [3, 4, 5]]),
                       (6, [[0, 1], [2, 3], [4, 5]]), (6, [[0, 1, 2, 3], [4, 5]])):
        N = n * n
        M = len(classes)
        fam = line2_family(n, classes)
        f2 = Fam2(fam)
        best = 0
        bestB = None
        seeds = [[], [bits_of(v) for v in sym_basis(n)]]
        if M > 1 and n % M == 0 and classes == intervals(n, M):
            seeds.append([bits_of(v) for v in block_sym_basis(n, M)])
        for seed in seeds:
            if f2.prefix(seed) is None:
                continue
            for rep in range(3):
                B = greedy2(f2, N, seed, rng, 500 if n <= 5 else 300)
                Kb = fam.K_from_code(np.array([vec_bits(x, N) for x in B]).reshape(-1, N), 2)
                line_steps(n, classes, Kb, 2)
                if len(B) > best:
                    best, bestB = len(B), B
        Bm = np.array([vec_bits(x, N) for x in bestB])
        K = fam.K_from_code(Bm, 2)
        D, dp = line_steps(n, classes, K, 2)
        cyc = (N + M * n) // 2
        # random sparse two-sided line rules over GF(2), GF(3): same checks
        for p in (2, 3):
            for trial in range(20):
                Kr = np.zeros((N, N), dtype=np.int64)
                dec = {(k, r, i, d): (rng.randrange(1, p) if rng.random() < 0.25 else 0)
                       for k in range(M) for r in range(n) for i in range(n) for d in range(-(n - 1), n)}
                for k, J in enumerate(classes):
                    for c in J:
                        for r in range(n):
                            for i in range(n):
                                for j in range(n):
                                    Kr[r * n + c, i * n + j] = dec[(k, r, i, j - c)]
                line_steps(n, classes, Kr, p)
        print(f"   two-sided LINE family n={n} interval classes {classes}: best found {D} <= (n^2+Mn)/2 = {cyc}"
              + ("  ATTAINED" if D == cyc else "") + f"; dim(X cap T^-1 X) = {dp} <= Mn = {M*n}")
    print(f"   [{time.time()-t2:.1f}s]")
    # masks BEFORE the rotation (B in span{sigma^d P_J}, mask on the input index): K^T then has its second factors in
    # span{P_J sigma^d} and rank(tau - K) = rank(tau - K^T), so Theorem TP gives the same bound
    t3 = time.time()
    for n, classes in ((4, [[0, 1], [2, 3]]), (4, [[0], [1, 2, 3]]), (5, [[0, 1], [2, 3, 4]]), (6, [[0, 1, 2], [3, 4, 5]])):
        N = n * n
        M = len(classes)
        fam = span_family_sigma_PJ(n, classes)
        f2 = Fam2(fam)
        best = 0
        seeds = [[], [bits_of(v) for v in sym_basis(n)]]
        if n % M == 0 and classes == intervals(n, M):
            seeds.append([bits_of(v) for v in block_sym_basis(n, M)])
        for seed in seeds:
            if f2.prefix(seed) is None:
                continue
            for rep in range(3):
                B = greedy2(f2, N, seed, rng, 400)
                Kb = fam.K_from_code(np.array([vec_bits(x, N) for x in B]).reshape(-1, N), 2)
                D = N - rank(swap(n) - Kb, 2)
                assert 2 * D <= N + M * n, (n, classes, D)
                best = max(best, D)
        print(f"   masks-before-rotation family n={n} classes {classes}: best found {best} <= (n^2+Mn)/2 = {(N+M*n)//2}")
    print(f"   [{time.time()-t3:.1f}s]")


# ----------------------------------------------------------------------------------------------------------------
# Theorem (twist classes)
# ----------------------------------------------------------------------------------------------------------------
def prim_root_of_unity(p, n):
    assert (p - 1) % n == 0
    for g in range(2, p):
        w = pow(g, (p - 1) // n, p)
        if all(pow(w, k, p) != 1 for k in range(1, n)):
            return w
    if n == 1:
        return 1
    if n == 2:
        return p - 1
    raise ValueError


def h_dim(G, Gp, p):
    """dim {P : G^T P = P G'}."""
    n = G.shape[0]
    I = np.eye(n, dtype=np.int64)
    # vec(G^T P) = kron(G^T, I) vec(P);  vec(P G') = kron(I, G'^T) vec(P)
    return n * n - rank(np.kron(G.T, I) - np.kron(I, Gp.T), p)


def intertwiners(G, Gp, p):
    """Basis (as n x n matrices) of {Bt : G Bt = Bt G'}."""
    n = G.shape[0]
    I = np.eye(n, dtype=np.int64)
    ns = nullspace(np.kron(G, I) - np.kron(I, Gp.T), p)
    return [v.reshape(n, n) for v in ns]


def twist_instance_check(n, p, G, Gps, BTs_by_class, As_by_class, tag):
    """BTs_by_class[k]: list of B_a^T ; As_by_class[k]: list of A_a.  Returns (D, bound_numerator, s)."""
    s = len(Gps)
    for k in range(s):
        for l in range(s):
            assert not comm(Gps[k], Gps[l], p).any(), "G' must commute"
        for BT in BTs_by_class[k]:
            assert not ((G @ BT - BT @ Gps[k]) % p).any(), ("hypothesis", tag)
    K = np.zeros((n * n, n * n), dtype=np.int64)
    for k in range(s):
        for A, BT in zip(As_by_class[k], BTs_by_class[k]):
            K += np.kron(A, BT.T)
    K %= p
    D = n * n - rank(swap(n) - K, p)
    hs = [h_dim(G, Gp, p) for Gp in Gps]
    assert (s + 1) * D <= s * n * n + sum(hs), (tag, D, s, hs)
    return D, hs, K


def hill_climb_A(n, p, BTs, rng, iters, start=None):
    """Maximise dim ker(tau - sum_a A_a (x) B_a) over the A_a; BTs = list of B_a^T."""
    tau = swap(n)
    Bk = [BT.T % p for BT in BTs]
    As = [np.zeros((n, n), dtype=np.int64) for _ in BTs] if start is None else [a.copy() for a in start]

    def val(As_):
        K = sum(np.kron(A, B) for A, B in zip(As_, Bk)) % p
        return n * n - rank(tau - K, p)
    cur = val(As)
    for _ in range(iters):
        a = rng.randrange(len(As))
        i, j = rng.randrange(n), rng.randrange(n)
        old = As[a][i, j]
        As[a][i, j] = rng.randrange(p)
        v = val(As)
        if v >= cur:
            cur = v
        else:
            As[a][i, j] = old
    return cur, As


def test_twist():
    t0 = time.time()
    rng = random.Random(4242)
    # ---- Weyl families
    print("(twist) Weyl families over GF(p), n | p-1:  B_a^T = Z^k * circulant, k in a set S of s frequencies, G = sigma")
    for p, n in ((3, 2), (5, 2), (5, 4), (7, 2), (7, 3), (7, 6), (11, 5), (13, 3), (13, 4)):
        w = prim_root_of_unity(p, n)
        Z = np.diag([pow(w, i, p) for i in range(n)]).astype(np.int64)
        sg = rot(n, 1)
        # sign convention: sigma Z = w^e Z sigma
        e = next(e for e in range(n) if not ((sg @ Z - pow(w, e, p) * Z @ sg) % p).any())
        tau = swap(n)
        worst = {}
        for s in range(1, min(n, 3) + 1):
            subsets = list(itertools.combinations(range(n), s))
            rng.shuffle(subsets)
            for S in subsets[:4]:
                Gps = [(pow(w, e * k, p) * sg) % p for k in S]
                hs = [h_dim(sg, Gp, p) for Gp in Gps]
                assert hs == [n] * s, (p, n, S, hs)            # h_k = n
                Zk = [np.linalg.matrix_power(Z, k) % p for k in S]
                basisBT = [[(Zk[t] @ rot(n, d)) % p for d in range(n)] for t in range(s)]
                bound = (s * n * n + s * n) // (s + 1)
                best = 0
                # (a) random A, random circulants
                for trial in range(4):
                    BTs, As = [], []
                    for t in range(s):
                        m_ = rng.randrange(1, 3)
                        bt, as_ = [], []
                        for _ in range(m_):
                            cf = [rng.randrange(p) for _ in range(n)]
                            bt.append(sum(cf[d] * basisBT[t][d] for d in range(n)) % p)
                            as_.append(rnd(rng, (n, n), p) if trial else np.eye(n, dtype=np.int64))
                        BTs.append(bt)
                        As.append(as_)
                    D, _, _ = twist_instance_check(n, p, sg, Gps, BTs, As, ("weyl", p, n, S))
                    best = max(best, D)
                # (b) truncated swap: expand tau in the Weyl basis and keep the frequencies in S
                allBT = [(np.linalg.matrix_power(Z, k) @ rot(n, d)) % p for k in range(n) for d in range(n)]
                # solve tau = sum_t A_t (x) B_t  with B_t = allBT[t]^T :  n^2 unknown n x n matrices
                # tau[(r,c),(i,j)] = sum_t A_t[r][i] B_t[c][j]  ->  for fixed (r,i): matrix (c,j) = sum_t A_t[r][i] B_t
                Bmat = np.array([BT.T.reshape(-1) for BT in allBT]).T % p     # n^2 x n^2, columns = vec(B_t)
                A_all = np.zeros((n * n, n, n), dtype=np.int64)
                ok = True
                for r in range(n):
                    for i in range(n):
                        target = np.zeros((n, n), dtype=np.int64)
                        target[i, r] = 1                                     # tau[(r,c),(i,j)] = [c==i][j==r]
                        sol = solve_right(Bmat, target.reshape(-1, 1), p)
                        if sol is None:
                            ok = False
                            break
                        A_all[:, r, i] = sol[:, 0]
                    if not ok:
                        break
                assert ok
                BTs = [[allBT[k * n + d] for d in range(n)] for k in S]
                As = [[A_all[k * n + d] for d in range(n)] for k in S]
                D, _, Ktr = twist_instance_check(n, p, sg, Gps, BTs, As, ("weyl-trunc", p, n, S))
                best = max(best, D)
                # (c) hill climbing on the A's (from 0, and from the truncated swap)
                if n <= 4:
                    flat = [bt for t in range(s) for bt in basisBT[t]]
                    for start in (None, [a for t in range(s) for a in As[t]]):
                        v, Af = hill_climb_A(n, p, flat, rng, 250 if n <= 3 else 150, start)
                        Asn = [Af[t * n:(t + 1) * n] for t in range(s)]
                        D, _, _ = twist_instance_check(n, p, sg, Gps, basisBT, Asn, ("weyl-hc", p, n, S))
                        assert D == v
                        best = max(best, D)
                # (d) subspace-side greedy on the same family, seeded with the twisted-symmetric codes X^T = Z^-k X Z^k
                if n <= 4:
                    flatB = [bt.T % p for t in range(s) for bt in basisBT[t]]
                    fam = Family.from_span(n, flatB)
                    for k in S:
                        Zm = np.linalg.matrix_power(Z, (n - k) % n) % p
                        seed = nullspace(tau - np.kron(Zm, np.linalg.matrix_power(Z, k) % p), p)
                        assert seed.shape[0] == n * (n + 1) // 2 and fam.is_code(seed, p)
                        Bg = greedy_p(fam, p, seed, rng, 60 if n <= 3 else 40)
                        Kg = fam.K_from_code(Bg, p)
                        Dg = n * n - rank(tau - Kg, p)
                        assert Dg >= Bg.shape[0] and (s + 1) * Dg <= s * n * n + s * n, (p, n, S, Dg)
                        best = max(best, Dg)
                slack = bound - best
                worst[s] = slack if s not in worst else min(worst[s], slack)
        print(f"   GF({p}) n={n}: sigma Z = w^{e} Z sigma, so G'_k = w^({e}k) sigma; h_k = n for all k; "
              f"s = 1..{min(n,3)}: no violation; least slack (bound - best D found) by s: {worst}")
    # ---- dihedral families: B^T in span{sigma^d} + span{rho sigma^d}, G = sigma, G'_1 = sigma, G'_2 = sigma^-1
    print("(twist) dihedral families: classes {circulants}, {reflection * circulants}; G = sigma, G' = sigma, sigma^-1")
    for p, n in ((3, 3), (3, 4), (5, 3), (5, 4), (2, 3), (2, 5), (3, 5)):
        sg = rot(n, 1)
        rho = np.zeros((n, n), dtype=np.int64)
        for c in range(n):
            rho[c, (-c) % n] = 1
        Gps = [sg, rot(n, n - 1)]
        base = [[rot(n, d) for d in range(n)], [(rho @ rot(n, d)) % p for d in range(n)]]
        hs = [h_dim(sg, Gp, p) for Gp in Gps]
        best = 0
        flat = base[0] + base[1]
        for rep in range(2):
            v, Af = hill_climb_A(n, p, flat, rng, 200 if n <= 4 else 80,
                                 None if rep else [np.eye(n, dtype=np.int64)] + [np.zeros((n, n), dtype=np.int64)] * (2 * n - 1))
            D, hs2, _ = twist_instance_check(n, p, sg, Gps, base, [Af[:n], Af[n:]], ("dihedral", p, n))
            best = max(best, D)
        # subspace-side greedy on the same family
        fam = Family.from_span(n, [bt.T for bt in flat])
        B = greedy_p(fam, p, sym_basis(n), rng, 60)
        K = fam.K_from_code(B, p)
        Dg = n * n - rank(swap(n) - K, p)
        assert 3 * Dg <= 2 * n * n + sum(hs)
        best = max(best, Dg)
        print(f"   GF({p}) n={n}: h = {hs}; bound floor((2n^2 + h1 + h2)/3) = {(2*n*n + sum(hs))//3}; best D found {best} "
              f"(pairing {n*(n+1)//2})")
    # ---- generic twist classes: G' = polynomials in one matrix, B^T random intertwiners
    print("(twist) generic twist classes: G random (often nilpotent/unipotent/diagonalisable with repeated spectrum), "
          "G'_k = f_k(G0) commuting, B^T random intertwiners, A random or hill-climbed")
    cnt = 0
    tight = 0
    for p in (2, 3, 5):
        for n in (2, 3, 4):
            I = np.eye(n, dtype=np.int64)
            for trial in range(40):
                kind = trial % 4
                if kind == 0:       # nilpotent Jordan block and scalar multiples (q-commutation)
                    G = np.zeros((n, n), dtype=np.int64)
                    for i in range(n - 1):
                        G[i, i + 1] = 1
                    Gps = [(c * G) % p for c in rng.sample(range(1, p), min(p - 1, rng.randrange(1, 3)))]
                elif kind == 1:     # G conjugate to powers of itself: unipotent shift, G' = G^a
                    G = rot(n, 1)
                    Gps = [np.linalg.matrix_power(G, a) % p for a in rng.sample(range(1, n + 1), min(n, rng.randrange(1, 3)))]
                elif kind == 2:     # diagonal G with repeated eigenvalues, G' diagonal
                    G = np.diag([rng.randrange(p) for _ in range(n)]).astype(np.int64)
                    Gps = [np.diag([rng.randrange(p) for _ in range(n)]).astype(np.int64) for _ in range(rng.randrange(1, 3))]
                else:               # random G, G' = polynomials in G
                    G = rnd(rng, (n, n), p)
                    Gps = [(G @ G) % p, G.copy()][:rng.randrange(1, 3)]
                s = len(Gps)
                BTs, As = [], []
                for k in range(s):
                    basis = intertwiners(G, Gps[k], p)
                    bt, as_ = [], []
                    for _ in range(rng.randrange(1, 3)):
                        if basis:
                            Bt = sum(rng.randrange(p) * b for b in basis) % p
                        else:
                            Bt = np.zeros((n, n), dtype=np.int64)
                        bt.append(Bt)
                        as_.append(rnd(rng, (n, n), p))
                    BTs.append(bt)
                    As.append(as_)
                D, hs, _ = twist_instance_check(n, p, G, Gps, BTs, As, ("generic", p, n, trial))
                # hill-climb the A's with the full intertwiner bases
                flatB, sizes = [], []
                for k in range(s):
                    basis = intertwiners(G, Gps[k], p)
                    flatB += basis
                    sizes.append(len(basis))
                if flatB and n <= 3:
                    v, Af = hill_climb_A(n, p, flatB, rng, 120)
                    As2, pos = [], 0
                    for k in range(s):
                        As2.append(Af[pos:pos + sizes[k]])
                        pos += sizes[k]
                    BT2 = []
                    pos = 0
                    for k in range(s):
                        BT2.append(flatB[pos:pos + sizes[k]])
                        pos += sizes[k]
                    D2, hs, _ = twist_instance_check(n, p, G, Gps, BT2, As2, ("generic-hc", p, n, trial))
                    D = max(D, D2)
                tight += ((s + 1) * D + s >= s * n * n + sum(hs))    # floor of the bound attained
                cnt += 1
    print(f"   {cnt} instances over GF(2), GF(3), GF(5), n <= 4: no violation; floor of the bound attained in {tight}")
    # ---- is commutation of the G' needed?  (informational)
    viol = 0
    tot = 0
    for p in (2, 3):
        for n in (2, 3):
            for trial in range(150):
                G = rnd(rng, (n, n), p)
                Gps = [rnd(rng, (n, n), p) for _ in range(2)]
                if not comm(Gps[0], Gps[1], p).any():
                    continue
                bases = [intertwiners(G, Gp, p) for Gp in Gps]
                if not bases[0] or not bases[1]:
                    continue
                flatB = bases[0] + bases[1]
                v, Af = hill_climb_A(n, p, flatB, rng, 60)
                hs = [h_dim(G, Gp, p) for Gp in Gps]
                tot += 1
                viol += (3 * v > 2 * n * n + sum(hs))
    print(f"   (informational) non-commuting G'_1, G'_2: {viol} of {tot} hill-climbed instances exceed the formula "
          f"(the commutation hypothesis is used in the proof; this shows whether it is needed)   [{time.time()-t0:.1f}s]")


# ----------------------------------------------------------------------------------------------------------------
# Thue-Morse / random colourings
# ----------------------------------------------------------------------------------------------------------------
def test_tm():
    t0 = time.time()
    rng = random.Random(5)
    print("(colourings) chain bounds for two-colourings of Z_n, rate = (s n^2 + n chi)/((s+1) n^2):")
    for n in (64, 128, 256):
        tm = [bin(c).count("1") & 1 for c in range(n)]
        for name, col in (("Thue-Morse", tm), ("random", [rng.randrange(2) for _ in range(n)])):
            classes = [[c for c in range(n) if col[c] == k] for k in (0, 1)]
            best1 = min(((n * n + n * chi_cyclic(n, classes, (0, d))) / (2 * n * n), d, chi_cyclic(n, classes, (0, d)))
                        for d in range(1, n))
            best2 = (2.0, None, None)
            pairs = [(a, b) for a in range(1, n) for b in range(a + 1, n)]
            if len(pairs) > 6000:
                pairs = rng.sample(pairs, 6000) + [(1, 3), (1, 2), (2, 3), (1, n - 1), (3, n - 3), (1, n - 3)]
            for a, b in pairs:
                ch = chi_cyclic(n, classes, (0, a, b))
                r = (2 * n * n + n * ch) / (3 * n * n)
                if r < best2[0]:
                    best2 = (r, (a, b), ch)
            print(f"   n={n} {name:10s}: one shift: best rate {best1[0]:.4f} (delta={best1[1]}, chi={best1[2]}); "
                  f"two shifts: best rate {best2[0]:.4f} (shifts {best2[1]}, chi={best2[2]})")
    print(f"   [{time.time()-t0:.1f}s]")


# ----------------------------------------------------------------------------------------------------------------
# n = 2: exhaustive over RULES (all K of the family), GF(2), GF(3); GF(5) for the twist family
# ----------------------------------------------------------------------------------------------------------------
def test_n2():
    t0 = time.time()
    n = 2
    tau = swap(n)
    for p in (2, 3):
        # (TP) cyclic, one class: K = A_0 (x) 1 + A_1 (x) sigma, all p^8 pairs (A_0, A_1); line: + corner terms
        hist = {}
        mats = [np.array(m, dtype=np.int64).reshape(2, 2) for m in itertools.product(range(p), repeat=4)]
        kr = [[np.kron(A, B) for A in mats] for B in (np.eye(2, dtype=np.int64), rot(2, 1))]
        for a0 in range(len(mats)):
            for a1 in range(len(mats)):
                D = 4 - rank(tau - kr[0][a0] - kr[1][a1], p)
                hist[D] = hist.get(D, 0) + 1
        assert max(hist) == 3
        print(f"(n=2) GF({p}) (TP) one class, all {len(mats)**2} rules K = A0 (x) 1 + A1 (x) sigma: histogram of "
              f"dim ker(tau-K) = {dict(sorted(hist.items()))}; max = 3 = (n^2+n)/2")
    # two-sided line, one class, n = 2: B in span{1, E01, E10}: three free A's (p^12 rules): GF(2) exhaustive, GF(3) sampled
    for p, exhaustive in ((2, True), (3, False)):
        mats = [np.array(m, dtype=np.int64).reshape(2, 2) for m in itertools.product(range(p), repeat=4)]
        Bs = [np.eye(2, dtype=np.int64), np.array([[0, 1], [0, 0]]), np.array([[0, 0], [1, 0]])]
        kr = [[np.kron(A, B) for A in mats] for B in Bs]
        rng = random.Random(12)
        triples = itertools.product(range(len(mats)), repeat=3) if exhaustive else \
            ((rng.randrange(len(mats)), rng.randrange(len(mats)), rng.randrange(len(mats))) for _ in range(20000))
        mx = 0
        cnt = 0
        for a, b, c in triples:
            mx = max(mx, 4 - rank(tau - kr[0][a] - kr[1][b] - kr[2][c], p))
            cnt += 1
        assert mx == 3
        print(f"(n=2) GF({p}) two-sided line, one class (Toeplitz B): {'all' if exhaustive else 'sampled'} {cnt} rules, max dim = {mx}")
    # (twist) Weyl, n = 2, one frequency k: B^T in span{Z^k, Z^k sigma}; all rules; bound (n^2+n)/2 = 3
    for p in (3, 5):
        w = p - 1
        Z = np.diag([1, w]).astype(np.int64)
        mats = [np.array(m, dtype=np.int64).reshape(2, 2) for m in itertools.product(range(p), repeat=4)]
        if p == 5:
            mats_s = random.Random(3).sample(mats, 120)
        else:
            mats_s = mats
        for k in (0, 1):
            Zk = np.linalg.matrix_power(Z, k)
            Bt = [Zk % p, (Zk @ rot(2, 1)) % p]
            kr = [[np.kron(A, bt.T) % p for A in mats_s] for bt in Bt]
            mx = 0
            for a0 in range(len(mats_s)):
                for a1 in range(len(mats_s)):
                    mx = max(mx, 4 - rank(tau - kr[0][a0] - kr[1][a1], p))
            assert mx <= 3
            print(f"(n=2) GF({p}) (twist) Weyl, frequency k={k}: {'all' if p == 3 else 'sampled'} {len(mats_s)**2} rules, "
                  f"max dim ker(tau-K) = {mx} <= 3")
    print(f"   [{time.time()-t0:.1f}s]")


SECTIONS = {"n2": test_n2, "pigeonhole": test_pigeonhole, "swapfloor": test_swapfloor, "convention": test_convention,
            "n3": test_n3, "n4": test_n4, "search": test_search, "twist": test_twist, "tm": test_tm}

if __name__ == "__main__":
    todo = sys.argv[1:] or list(SECTIONS)
    T0 = time.time()
    for name in todo:
        SECTIONS[name]()
        sys.stdout.flush()
    print(f"CHECKS FINISHED: sections {todo} in {time.time()-T0:.1f}s; no assertion failed")
