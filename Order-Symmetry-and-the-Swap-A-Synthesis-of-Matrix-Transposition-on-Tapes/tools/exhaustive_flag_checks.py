"""Exhaustive and randomized checks of Theorem FL (the flag bound) and of its corollaries.

Usage (from the paper's root directory; needs numpy):

    python3 tools/exhaustive_flag_checks.py              # all sections, in order
    python3 tools/exhaustive_flag_checks.py T3 T9        # only the named sections

What it checks.  For K = sum_a A_a (x) B_a acting on n x n matrices over a small finite field, the script computes
the dimension of the swap code ker(SWAP - K) = {X : X^T = sum_a A_a X B_a^T} exactly and compares it with the bounds
of the paper's section "Order: the flag bound": Theorem FL, Proposition (the bound is attained for every profile),
Corollary (a pair of flags), Corollary (at most two terms), Corollary (one triangularizable side), Corollary (all
affine index maps in characteristic p), Corollary (blocks and expansion) and Remark (entries of b bits).  It also
produces the numbers quoted in Remark (numerical: the bound is not always tight) and in Remark (two is sharp).
Sections marked ALL or COMPLETE are exhaustive; block ascent, annealing and random sampling give lower bounds on
the largest kernel only.  A run takes about a minute and a half on four cores (T5 and T6 start four worker
processes), prints its results and writes no files.  It ends with a summary line, and its exit status is 0 unless a
bound of the paper is violated.  All random choices come from fixed seeds, one generator per section.  T4 stops its
GF(5) sample after 20 seconds, so the number of GF(5) pairs decided there depends on the machine.

Conventions.  The side length, called d in the paper, is n here.  vec(X)[i*n + j] = X[i][j];  SWAP vec(X) = vec(X^T);
(A (x) B) vec(X) = vec(A X B^T).  The A_a are the first factors and the B_a the second factors.  The profile of the
B_a along a flag W_1 < ... < W_n is g(i) = dim sum_a B_a(W_i); "the flag bound" is sum_i g(i), minimized over the
flags named in each section.  The pairing value is n(n+1)/2, and h = n(n-1)/2.
Row (i,k) of M = SWAP - sum_a A_a (x) B_a is the equation  X[k][i] = sum_a sum_{j,l} A_a[i][j] B_a[k][l] X[j][l].
It involves only row i of every A_a, so M is a stack of n blocks, block i being a function of
alpha_i = (row i of A_1, ..., row i of A_K).  This makes exhaustive and pruned searches over the A_a cheap.

Sections:
  T1   Theorem FL, the mechanism of its proof: in bases adapted to the flag, restriction to the index set I is
       injective on the kernel (planted staircase instances with large kernels, random flags, GF(2), GF(3), GF(5),
       GF(7), GF(10007)).  Proposition (the bound is attained for every profile) on the planted instances.
       Exchange of the two sides, and transposition.
  T2   n = 2 over GF(2): ALL 65536 operators K, minimal supports, all flags over GF(2) and GF(4), four profiles
       (B, B^T, A, A^T).
  T3   n = 3 over GF(2): ALL spans of at most two second factors up to GL_3 x GL_3, ALL 2^18 pairs (A_1, A_2):
       exact maximum of dim ker, against Corollary (at most two terms) (the value 6) and against the flag bound
       over GF(2)-, GF(4)- and GF(8)-flags; these are the numbers of Remark (numerical: the bound is not always
       tight).  Cross-validation of the pruned decision procedure against brute force.  One term, exhaustive at
       n = 4.
  T4   Corollary (at most two terms) at n = 3 over GF(3), COMPLETE: exact pruned decision (is rank <= 2 reachable?)
       over all 3^18 (A_1, A_2), for every B-pair up to equivalence (B_1 = diag(I_r, 0) of maximal rank in the span).
       GF(5): the same on a sample (all 155 regular classes are listed; a time cut keeps a mixed sample).
  T5   Corollary (at most two terms) at n = 4 over GF(2), COMPLETE: exact pruned decision (is rank <= 5 reachable?)
       over all 2^32 (A_1, A_2), for every B-pair up to equivalence (74 classes), plus redundant Kronecker-singular
       and random pairs.  Theorem FL on the same classes.  Three terms at n = 4 exceed the pairing value (Remark
       (two is sharp)).  n = 5 by block ascent.
  T6   Corollary (one triangularizable side), parts (a) and (b), and Theorem FL with adversarial first factors:
       exact decisions at n = 3 (commutative algebras incl. the fields GF(8) and GF(27), whose flag lives only over
       an extension) and at n = 4 with three second factors, block-coordinate ascent with exhaustive block moves at
       n = 4 (circulants, Sylow-2 spans, staircase subspaces), annealing at n = 8.
  T7   Corollary (blocks and expansion) for decimations, and interval masks: exact g(i) on the character flag over
       GF(p), p = 1 mod n, and over GF(2^k); all tie orders; non-coprime multipliers; both conventions (read map /
       write map).  Corollary (all affine index maps in characteristic p): the flag ker (R - 1)^i for n a power of
       the characteristic.
  T8   Rotations and one interval mask generate M_n(F); control with a periodic mask.
  T9   Sharp instances (the operator L' = SWAP - vec(1) vec(1)^T of Remark (two is sharp), called the dual pairing
       here; Klein four; partial transposes; block swap): minimum of the flag bound over ALL flags of GF(p)^n, four
       profiles, against dim ker.  The block formula of Corollary (blocks and expansion).
  T10  Corollary (blocks and expansion): the arithmetic of the expansion bound and of the bound for K terms; the
       hypothesis c >= 1 is needed (projection example).
  T11  Coordinate flags.  For first factors E_{i'i}, (i, i') in a row pattern Q, the least profile sum over
       coordinate flags is compared with the count n(n+1)/2 + min_{c,d} beta^-(c, d), where
       beta^-(c, d) = sum_i max(0, d(i) - min_{i' in Q(i)} c(i')) for orders c, d of the rows.
  T12  Realignment R: R(SWAP) = SWAP, rank one <-> Kronecker product, the Kronecker rank h of L', sampled rank-2
       perturbations of the swap.
  T13  Remark (entries of b bits): the bound b * sum g with first factors acting on V (x) F^b.
"""
import itertools, sys, time, math
import numpy as np

FAIL = []          # violations of statements of the paper (they would be counterexamples)
REMARKS = []       # facts about hypotheses exhibited by the run (not violations)

def claim(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("   *** VIOLATION:", msg, flush=True)
    return cond

# ----------------------------------------------------------------------------------------------------------
# dense linear algebra mod p
# ----------------------------------------------------------------------------------------------------------
def rref_mod(M, p):
    M = np.array(M, dtype=np.int64) % p
    if M.ndim == 1:
        M = M.reshape(1, -1)
    rows, cols = M.shape
    piv = []
    r = 0
    for c in range(cols):
        if r == rows:
            break
        nz = np.nonzero(M[r:, c])[0]
        if nz.size == 0:
            continue
        i = r + int(nz[0])
        if i != r:
            M[[r, i]] = M[[i, r]]
        M[r] = (M[r] * pow(int(M[r, c]), -1, p)) % p
        for i in np.nonzero(M[:, c])[0]:
            if i != r:
                M[i] = (M[i] - M[i, c] * M[r]) % p
        piv.append(c)
        r += 1
    return M[:r], piv

def rank_mod(M, p):
    M = np.array(M, dtype=np.int64)
    if M.size == 0:
        return 0
    return len(rref_mod(M, p)[1])

def nullspace_mod(M, p):
    R, piv = rref_mod(M, p)
    cols = np.array(M).shape[1]
    free = [c for c in range(cols) if c not in set(piv)]
    N = np.zeros((len(free), cols), dtype=np.int64)
    for t, f in enumerate(free):
        N[t, f] = 1
        for r, c in enumerate(piv):
            N[t, c] = (-R[r, f]) % p
    return N

def inv_mod(M, p):
    n = M.shape[0]
    aug = np.concatenate([np.array(M, dtype=np.int64) % p, np.eye(n, dtype=np.int64)], axis=1)
    R, piv = rref_mod(aug, p)
    assert piv[:n] == list(range(n)), "singular"
    return R[:, n:] % p

def rand_invertible(n, p, rng):
    while True:
        Q = rng.integers(0, p, size=(n, n))
        if rank_mod(Q, p) == n:
            return Q

def swap_matrix(n):
    S = np.zeros((n*n, n*n), dtype=np.int64)
    for i in range(n):
        for j in range(n):
            S[i*n + j, j*n + i] = 1
    return S

def kron_sum(As, Bs, p):
    n = As[0].shape[0]
    K = np.zeros((n*n, n*n), dtype=np.int64)
    for A, B in zip(As, Bs):
        K = (K + np.kron(np.array(A) % p, np.array(B) % p)) % p
    return K

def kerdim(As, Bs, p):
    n = As[0].shape[0]
    return n*n - rank_mod((swap_matrix(n) - kron_sum(As, Bs, p)) % p, p)

def E(n, i, j):
    M = np.zeros((n, n), dtype=np.int64); M[i, j] = 1
    return M

def realign(L, n):
    """R(L)[(o1,i1),(o2,i2)] = L[(o1,o2),(i1,i2)]."""
    return np.array(L).reshape(n, n, n, n).transpose(0, 2, 1, 3).reshape(n*n, n*n)

def supports(Kop, n, p):
    """Minimal second-factor span (row space of R(K)) and first-factor span (column space), as lists of n x n."""
    R = realign(Kop, n) % p
    rb, _ = rref_mod(R, p)
    ra, _ = rref_mod(R.T, p)
    return [v.reshape(n, n) for v in ra], [v.reshape(n, n) for v in rb]

def profile(Bs, F, p):
    """g(1..n) for the flag W_i = span of the first i columns of F."""
    n = F.shape[0]
    out = []
    for i in range(1, n+1):
        if not Bs:
            out.append(0); continue
        img = np.concatenate([(np.array(B) @ F[:, :i]) % p for B in Bs], axis=1)
        out.append(rank_mod(img.T, p))
    return out

def all_flags(n, p):
    """All complete flags of GF(p)^n, each as an n x n matrix whose first i columns span W_i."""
    vecs = [np.array(v, dtype=np.int64) for v in itertools.product(range(p), repeat=n)]
    def rec(basis):
        if len(basis) == n:
            yield np.array(basis).T
            return
        seen = set()
        Rb, piv = rref_mod(np.array(basis), p) if basis else (np.zeros((0, n), dtype=np.int64), [])
        for v in vecs:
            w = v.copy()
            for r, c in enumerate(piv):          # reduce modulo the current span
                if w[c]:
                    w = (w - w[c] * Rb[r]) % p
            if not w.any():
                continue
            lead = int(w[np.nonzero(w)[0][0]])
            w = (w * pow(lead, -1, p)) % p        # normalise
            key = tuple(int(x) for x in w)
            if key in seen:
                continue
            seen.add(key)
            yield from rec(basis + [w])
    yield from rec([])

_FLAG_CACHE = {}
def flags_cached(n, p):
    if (n, p) not in _FLAG_CACHE:
        _FLAG_CACHE[(n, p)] = list(all_flags(n, p))
    return _FLAG_CACHE[(n, p)]

def min_flag_bound(Bs, n, p):
    """min over all flags of GF(p)^n of sum_i g(i) for the tuple Bs."""
    best = n*n
    for F in flags_cached(n, p):
        best = min(best, sum(profile(Bs, F, p)))
    return best

# ----------------------------------------------------------------------------------------------------------
# GF(2) bit-packed tools
# ----------------------------------------------------------------------------------------------------------
def xor_basis(rows):
    basis = {}
    for v in rows:
        v = int(v)
        while v:
            hb = v.bit_length() - 1
            b = basis.get(hb)
            if b is None:
                basis[hb] = v
                break
            v ^= b
    return basis

def rank_bits(rows):
    return len(xor_basis(rows))

def batch_rank2(rows, nbits, init=None):
    """Vectorised GF(2) rank.  rows: list of uint32 arrays broadcastable to one shape.
    init = (basis list of nbits arrays, rank array) continues an earlier elimination."""
    shapes = [np.shape(r) for r in rows]
    if init is not None:
        shapes += [np.shape(b) for b in init[0]] + [np.shape(init[1])]
    shape = np.broadcast_shapes(*shapes)
    if init is None:
        basis = [np.zeros(shape, np.uint32) for _ in range(nbits)]
        rank = np.zeros(shape, np.int16)
    else:
        basis = [np.broadcast_to(np.asarray(b, dtype=np.uint32), shape).copy() for b in init[0]]
        rank = np.broadcast_to(np.asarray(init[1], dtype=np.int16), shape).copy()
    for r0 in rows:
        r = np.broadcast_to(np.asarray(r0, dtype=np.uint32), shape).copy()
        for b in range(nbits - 1, -1, -1):
            has = ((r >> np.uint32(b)) & np.uint32(1)).astype(bool)
            if not has.any():
                continue
            bb = basis[b]
            hb = bb != 0
            r ^= np.where(has & hb, bb, np.uint32(0))
            new = has & ~hb
            if new.any():
                basis[b] = np.where(new, r, bb)
                rank += new
                r = np.where(new, np.uint32(0), r)
    return rank, basis

def mat_to_rows(B):
    """n x n 0/1 matrix -> list of row bitmasks (bit l = column l)."""
    return [int(sum(int(B[k][l]) << l for l in range(len(B)))) for k in range(len(B))]

def block_tables(Bs_rows, n, i):
    """T[k][alpha] = bitmask (over X-entries j*n + l) of row (i,k) of M = SWAP + sum_a A_a (x) B_a over GF(2),
    alpha bit (a*n + j) = A_a[i][j]."""
    T = []
    for k in range(n):
        t = np.array([1 << (k*n + i)], dtype=np.uint32)
        for a in range(len(Bs_rows)):
            for j in range(n):
                v = np.uint32(Bs_rows[a][k] << (j*n))
                t = np.concatenate([t, t ^ v])
        T.append(t)
    return T

def alpha_to_As(alphas, K, n):
    As = [np.zeros((n, n), dtype=np.int64) for _ in range(K)]
    for i, al in enumerate(alphas):
        for a in range(K):
            for j in range(n):
                As[a][i, j] = (int(al) >> (a*n + j)) & 1
    return As

_FLAG2 = {}
def min_flag_bound2(Bs, n, flags=None):
    """GF(2): min over flags (default: ALL flags of GF(2)^n) of sum_i g(i), for the tuples Bs and Bs^T (bitsets)."""
    if flags is None:
        if n not in _FLAG2:
            _FLAG2[n] = [[int(sum(int(F[r, c]) << r for r in range(n))) for c in range(n)] for F in flags_cached(n, 2)]
        flags = _FLAG2[n]
    best = n*n
    for tr in (False, True):
        cols = []                                         # cols[a][l] = bitmask of column l of B_a (or of B_a^T)
        for B in Bs:
            M = np.array(B).T if tr else np.array(B)
            cols.append([int(sum(int(M[r, l]) << r for r in range(n))) for l in range(n)])
        for fl in flags:
            basis = {}; tot = 0
            for f in fl:
                for cl in cols:
                    v = 0; l = 0; ff = f
                    while ff:
                        if ff & 1:
                            v ^= cl[l]
                        ff >>= 1; l += 1
                    while v:
                        hb = v.bit_length() - 1
                        b = basis.get(hb)
                        if b is None:
                            basis[hb] = v; break
                        v ^= b
                tot += len(basis)
                if tot >= best:
                    break
            best = min(best, tot)
    return best

# ----------------------------------------------------------------------------------------------------------
# batched rank mod p for stacks of small matrices
# ----------------------------------------------------------------------------------------------------------
def batch_rank_p(M, p):
    M = (np.array(M, dtype=np.int16) % p)
    N, r, c = M.shape
    rank = np.zeros(N, dtype=np.int64)
    inv = np.array([0] + [pow(x, -1, p) for x in range(1, p)], dtype=np.int16)
    idx = np.arange(N)
    rowidx = np.arange(r)[None, :]
    for col in range(c):
        cand = (M[:, :, col] != 0) & (rowidx >= rank[:, None])
        has = cand.any(axis=1)
        if not has.any():
            continue
        sel = idx[has]
        pr = cand.argmax(axis=1)[has]
        rr = rank[has]
        tmp = M[sel, pr].copy(); M[sel, pr] = M[sel, rr]; M[sel, rr] = tmp
        pv = M[sel, rr, col]
        prow = (M[sel, rr] * inv[pv][:, None]) % p
        M[sel, rr] = prow
        factor = M[sel, :, col].copy()
        factor[np.arange(sel.size), rr] = 0
        M[sel] = (M[sel] - factor[:, :, None] * prow[:, None, :]) % p
        rank[has] += 1
    return rank

# ----------------------------------------------------------------------------------------------------------
# GF(2^k)
# ----------------------------------------------------------------------------------------------------------
class GF2k:
    POLY = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 6: 0b1000011}
    def __init__(self, k):
        self.k = k; self.q = 1 << k
        poly = self.POLY[k]
        self.exp = [0] * (2 * self.q); self.log = [0] * self.q
        x = 1
        for i in range(self.q - 1):
            self.exp[i] = x; self.log[x] = i
            x <<= 1
            if x & self.q:
                x ^= poly
        assert x == 1, "polynomial not primitive"
        for i in range(self.q - 1, 2 * self.q):
            self.exp[i] = self.exp[i - (self.q - 1)]
    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[self.log[a] + self.log[b]]
    def inv(self, a):
        return self.exp[(self.q - 1 - self.log[a]) % (self.q - 1)]
    def pw(self, a, e):
        if a == 0:
            return 0 if e else 1
        return self.exp[(self.log[a] * e) % (self.q - 1)]
    def rank(self, M):
        M = [list(row) for row in M]
        rows = len(M); cols = len(M[0]) if rows else 0
        r = 0
        for c in range(cols):
            piv = next((i for i in range(r, rows) if M[i][c]), None)
            if piv is None:
                continue
            M[r], M[piv] = M[piv], M[r]
            iv = self.inv(M[r][c])
            M[r] = [self.mul(iv, x) for x in M[r]]
            for i in range(rows):
                if i != r and M[i][c]:
                    f = M[i][c]
                    M[i] = [x ^ self.mul(f, y) for x, y in zip(M[i], M[r])]
            r += 1
            if r == rows:
                break
        return r

# ----------------------------------------------------------------------------------------------------------
# T1  Theorem FL: mechanism and sharpness
# ----------------------------------------------------------------------------------------------------------
def adapted(Bs, F, p):
    """Profile g and a basis F' adapted to the chain U_i = sum_a B_a(W_i)."""
    n = F.shape[0]
    cols = []
    g = []
    for i in range(n):
        for B in Bs:
            v = (np.array(B) @ F[:, i]) % p
            if rank_mod(np.array(cols + [v]), p) > len(cols):
                cols.append(v)
        g.append(len(cols))
    for j in range(n):
        e = np.zeros(n, dtype=np.int64); e[j] = 1
        if len(cols) < n and rank_mod(np.array(cols + [e]), p) > len(cols):
            cols.append(e)
    return g, np.array(cols).T % p

def mechanism_ok(As, Bs, F, p):
    """Checks dim ker <= sum g AND that p|_I is injective on ker, as the proof claims.  Returns (ker, sum g, ok)."""
    n = F.shape[0]
    M = (swap_matrix(n) - kron_sum(As, Bs, p)) % p
    Nk = nullspace_mod(M, p)
    g, Fp = adapted(Bs, F, p)
    assert g == profile(Bs, F, p)
    Fpi = inv_mod(Fp, p); FiT = inv_mod(F, p).T % p
    idx = [(a, b) for b in range(n) for a in range(g[b])]         # I = {(a', b') : a' < g(b'+1)}
    if Nk.shape[0] == 0:
        return 0, sum(g), True
    rows = []
    for v in Nk:
        X = v.reshape(n, n)
        P = (Fpi @ X @ FiT) % p                                   # X = F' P F^T
        rows.append([int(P[a, b]) for (a, b) in idx])
    inj = (rank_mod(np.array(rows, dtype=np.int64).reshape(Nk.shape[0], len(idx)), p) == Nk.shape[0]) if idx else False
    return Nk.shape[0], sum(g), (Nk.shape[0] <= sum(g)) and inj

def staircase_instance(n, g, p, rng, hide=True, drop=0.0, noise=0):
    """K0 = sum_{k < g[i]} E_ik (x) E_ki has kernel = staircase {X : X[k][i] = 0 for k >= g[i]}, dim sum g.
    Hidden by (A, B) -> (Q^-T A P, P^-1 B Q^T).  The planted flag basis is Q^-T."""
    As, Bs = [], []
    for i in range(n):
        for k in range(g[i]):
            if rng.random() < drop:
                continue
            As.append(E(n, i, k)); Bs.append(E(n, k, i))
    for _ in range(noise):                                         # extra random terms inside the staircase
        B = np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            for k in range(g[i]):
                B[k, i] = rng.integers(0, p)
        As.append(rng.integers(0, p, size=(n, n))); Bs.append(B)
    if not As:
        As, Bs = [np.zeros((n, n), dtype=np.int64)], [np.zeros((n, n), dtype=np.int64)]
    if hide:
        P = rand_invertible(n, p, rng); Q = rand_invertible(n, p, rng)
        QiT = inv_mod(Q, p).T % p; Pi = inv_mod(P, p)
        As = [(QiT @ A @ P) % p for A in As]; Bs = [(Pi @ B @ Q.T) % p for B in Bs]
        Fpl = QiT
    else:
        Fpl = np.eye(n, dtype=np.int64)
    return As, Bs, Fpl

def T1(rng):
    print("== T1  Theorem FL: mechanism (p|_I injective on the kernel) and sharpness on planted staircases")
    tot = 0; bad = 0; sharp = 0; nontrivial = 0
    for p in (2, 3, 5, 7, 10007):
        for n in (3, 4, 5, 6):
            reps = 14 if n <= 5 else 6
            for _ in range(reps):
                g = sorted(int(x) for x in rng.integers(0, n + 1, size=n))
                kind = rng.integers(3)
                As, Bs, Fpl = staircase_instance(n, g, p, rng, hide=True,
                                                 drop=(0.0 if kind == 0 else 0.25),
                                                 noise=(0 if kind < 2 else 2))
                flags = [Fpl, np.eye(n, dtype=np.int64)] + [rand_invertible(n, p, rng) for _ in range(3)]
                for t, F in enumerate(flags):
                    ker, sg, ok = mechanism_ok(As, Bs, F, p)
                    tot += 1
                    if not ok:
                        bad += 1
                        claim(False, f"T1 Theorem FL fails: p={p} n={n} g={g} flag#{t} ker={ker} sum g={sg}")
                    if ker > 0:
                        nontrivial += 1
                    if t == 0 and kind == 0:
                        claim(sg == sum(g), f"T1 planted profile mismatch p={p} n={n}")
                        if ker == sg:
                            sharp += 1
                        else:
                            claim(False, f"T1 planted staircase kernel {ker} != sum g {sg}")
                # exchanged roles: tau (tau - K) tau = tau - sum B (x) A
                ker1 = kerdim(As, Bs, p); ker2 = kerdim(Bs, As, p)
                claim(ker1 == ker2, "T1 exchange of roles changes the kernel dimension")
                # transposition: rank(tau - K) = rank(tau - K^T)
                ker3 = kerdim([A.T for A in As], [B.T for B in Bs], p)
                claim(ker1 == ker3, "T1 transposition changes the kernel dimension")
    print(f"   {tot} (instance, flag) pairs, {nontrivial} with non-zero kernel, violations {bad}; "
          f"planted staircases attaining sum g exactly: {sharp}")

# ----------------------------------------------------------------------------------------------------------
# T2  n = 2 over GF(2): every operator
# ----------------------------------------------------------------------------------------------------------
def T2(rng):
    print("== T2  n = 2, GF(2): all 65536 operators K; flags over GF(2) and GF(4); profiles B, B^T, A, A^T")
    n = 2
    gf4 = GF2k(2); w = 2                      # w = primitive element of GF(4)
    lines = [(1, 0), (0, 1), (1, 1), (1, w), (1, gf4.mul(w, w))]
    def tr(b):                                 # transpose of a 2x2 matrix coded as 4 bits (bit k*2+l)
        return (b & 0b1001) | ((b >> 1) & 1) << 2 | ((b >> 2) & 1) << 1
    def span(gens):
        el = {0}
        for g_ in gens:
            el |= {e ^ g_ for e in el}
        return frozenset(el)
    def bound_of(space):                       # min over the 5 lines of g(1) + g(2)
        mats = [b for b in space if b]
        if not mats:
            return 0
        g2 = rank_bits([((b >> 0) & 1) | ((b >> 2) & 1) << 1 for b in mats] +
                       [((b >> 1) & 1) | ((b >> 3) & 1) << 1 for b in mats])     # span of all columns
        best = 99
        for (x, y) in lines:
            vs = []
            for b in mats:
                b00, b01, b10, b11 = b & 1, (b >> 1) & 1, (b >> 2) & 1, (b >> 3) & 1
                vs.append([(x if b00 else 0) ^ (y if b01 else 0), (x if b10 else 0) ^ (y if b11 else 0)])
            best = min(best, gf4.rank(vs) + g2)
        return best
    cache = {}
    def bnd(space):
        if space not in cache:
            cache[space] = min(bound_of(space), bound_of(frozenset(tr(b) for b in space)))
        return cache[space]
    swap_rows = [1 << (k*n + i) for i in range(n) for k in range(n)]          # row (i,k) has its 1 at (k,i)
    viol = 0; tight = 0; hist = {}; c2max = 0
    for code in range(1 << 16):
        Krows = [(code >> (4*r)) & 15 for r in range(4)]                     # row r = (o1,o2), bit c = (i1,i2)
        ker = 4 - rank_bits([Krows[r] ^ swap_rows[r] for r in range(4)])
        # realignment: R[(o1,i1)][(o2,i2)] = K[(o1,o2)][(i1,i2)]
        Rrows = [0] * 4
        for o1 in range(2):
            for o2 in range(2):
                for i1 in range(2):
                    for i2 in range(2):
                        if (Krows[o1*2 + o2] >> (i1*2 + i2)) & 1:
                            Rrows[o1*2 + i1] |= 1 << (o2*2 + i2)
        Rcols = [sum(((Rrows[r] >> c) & 1) << r for r in range(4)) for c in range(4)]
        b = min(bnd(span(Rrows)), bnd(span(Rcols)))
        if rank_bits(Rrows) <= 2:
            c2max = max(c2max, ker)
        if ker > b:
            viol += 1
            if viol <= 3:
                claim(False, f"T2 Theorem FL violated at n=2: K code {code}, ker {ker}, flag bound {b}")
        if ker == b:
            tight += 1
        hist[(ker, b)] = hist.get((ker, b), 0) + 1
    print(f"   violations {viol} / 65536; bound attained by {tight} operators; (ker, bound) histogram: "
          + ", ".join(f"{k}:{v}" for k, v in sorted(hist.items())))
    claim(c2max <= 3, "T2 Corollary (at most two terms) violated at n = 2")
    print(f"   Corollary (at most two terms) at n = 2: largest kernel among all operators of Kronecker rank <= 2 is {c2max} (bound 3)")

# ----------------------------------------------------------------------------------------------------------
# T3  n = 3 over GF(2): all spans of <= 2 second factors, all first factors
# ----------------------------------------------------------------------------------------------------------
def int_to_mat(b, n):
    return np.array([[(b >> (k*n + l)) & 1 for l in range(n)] for k in range(n)], dtype=np.int64)

def mat_to_int(B):
    n = len(B)
    return int(sum(int(B[k][l]) << (k*n + l) for k in range(n) for l in range(n)))

def max_ker_exhaustive_n3(Bints):
    """Exact max over all A_1..A_K in M_3(GF(2)) (K = len(Bints) <= 2) of dim ker(SWAP - sum A (x) B)."""
    n = 3
    Bs_rows = [mat_to_rows(int_to_mat(b, n)) for b in Bints]
    NA = 1 << (len(Bints) * n)
    rows = []
    for i in range(n):
        T = block_tables(Bs_rows, n, i)
        shape = [1, 1, 1]; shape[i] = NA
        rows += [t.reshape(shape) for t in T]
    rank, _ = batch_rank2(rows, n*n)
    m = int(rank.min())
    arg = np.unravel_index(int(rank.argmin()), rank.shape)
    return n*n - m, arg

def ext_points(gf, n):
    pts = []
    for v in itertools.product(range(gf.q), repeat=n):
        nz = [x for x in v if x]
        if nz and nz[0] == 1:
            pts.append(list(v))
    return pts

def min_flag_bound_ext3(Bs, gf, stop_at=None):
    """n = 3: min over all flags of GF(2^k)^3 of sum g, for Bs (over GF(2)) and for the transposes."""
    pts = ext_points(gf, 3)
    best = 9
    for tr in (False, True):
        Ms = [np.array(B).T if tr else np.array(B) for B in Bs]
        g3 = rank_mod(np.concatenate(Ms, axis=1).T, 2)
        def app(M, w):
            out = []
            for k in range(3):
                x = 0
                for l in range(3):
                    if M[k][l]:
                        x ^= w[l]
                out.append(x)
            return out
        imgs = [[app(M, w) for M in Ms] for w in pts]
        r1 = [gf.rank(im) for im in imgs]
        for a in range(len(pts)):
            if r1[a] + r1[a] + g3 >= best:                # g2 >= g1
                continue
            for b in range(len(pts)):
                if b == a:
                    continue
                g2 = gf.rank(imgs[a] + imgs[b])
                best = min(best, r1[a] + g2 + g3)
                if stop_at is not None and best <= stop_at:
                    return best
    return best

def T3(rng):
    print("== T3  n = 3, GF(2): all spans of <= 2 second factors up to GL_3 x GL_3, all 2^18 (A_1, A_2)")
    n = 3
    cyc = np.array([[0, 1, 0], [0, 0, 1], [1, 0, 0]]); t12 = np.eye(3, dtype=np.int64) + E(3, 0, 1)
    t21 = np.eye(3, dtype=np.int64) + E(3, 1, 0)
    tabs = []
    for G in (cyc, t12, t21):
        tabs.append([mat_to_int((G @ int_to_mat(b, 3)) % 2) for b in range(512)])
        tabs.append([mat_to_int((int_to_mat(b, 3) @ G) % 2) for b in range(512)])
    # 1-dimensional spans: orbits = rank 1, 2, 3
    reps = [(mat_to_int(np.diag([1]*r + [0]*(3 - r))),) for r in (1, 2, 3)]
    # 2-dimensional spans
    keys = {}
    for b1 in range(1, 512):
        for b2 in range(b1 + 1, 512):
            k = tuple(sorted((b1, b2, b1 ^ b2)))
            if k not in keys:
                keys[k] = len(keys)
    parent = list(range(len(keys)))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for k, idx in keys.items():
        for tb in tabs:
            k2 = tuple(sorted(tb[b] for b in k))
            a, b = find(idx), find(keys[k2])
            if a != b:
                parent[a] = b
    orbit = {}
    for k, idx in keys.items():
        orbit.setdefault(find(idx), []).append(k)
    print(f"   {len(keys)} two-dimensional spans in {len(orbit)} orbits; plus 3 one-dimensional orbits")
    reps += [(v[0][0], v[0][1]) for v in orbit.values()]
    worst = 0; viol = 0; summary = []; xval = 0; ext = []
    gf4 = GF2k(2); gf8 = GF2k(3)
    for rep in reps:
        mk, arg = max_ker_exhaustive_n3(rep)
        Bs = [int_to_mat(b, 3) for b in rep]
        fb = min(min_flag_bound(Bs, 3, 2), min_flag_bound([B.T for B in Bs], 3, 2))
        # independent recomputation of the maximiser with the dense code
        As = alpha_to_As(arg, len(rep), 3)
        assert kerdim(As, Bs, 2) == mk, "bit-packed and dense kernels disagree"
        if len(rep) <= 2 and mk > 6:
            viol += 1; claim(False, f"T3 Corollary (at most two terms) violated: B = {rep}, max ker {mk} > 6, alpha = {arg}")
        if mk > fb:
            viol += 1; claim(False, f"T3 Theorem FL violated: B = {rep}, max ker {mk} > flag bound {fb}")
        worst = max(worst, mk)
        fb4 = fb8 = None
        if mk < fb:                                        # flags over extension fields: still valid bounds; sharper?
            fb4 = min(fb, min_flag_bound_ext3(Bs, gf4, stop_at=mk - 1))
            claim(mk <= fb4, f"T3 Theorem FL violated with a GF(4)-flag: B = {rep}, max ker {mk} > {fb4}")
            if mk < fb4:
                fb8 = min(fb4, min_flag_bound_ext3(Bs, gf8, stop_at=mk - 1))
                claim(mk <= fb8, f"T3 Theorem FL violated with a GF(8)-flag: B = {rep}, max ker {mk} > {fb8}")
        ext.append((len(rep), mk, fb, fb4, fb8))
        summary.append((len(rep), mk, fb))
        for rstar in range(0, 9):                       # pruned decision == brute force, every threshold
            res, wit = decide_low_rank_2(Bs, 3, rstar)
            assert res == (9 - mk <= rstar), ("decision procedure disagrees with brute force", rep, rstar, res, mk)
            if res:
                assert 9 - kerdim(alpha_to_As(wit, len(rep), 3), Bs, 2) <= rstar
        xval += 9
    hist = {}
    for s in summary:
        hist[s] = hist.get(s, 0) + 1
    print(f"   exact max of dim ker over all first factors, per orbit: largest {worst} (two-term bound 6); violations {viol}")
    print(f"   cross-validation: the pruned decision procedure of T5/T6 agrees with brute force in all {xval} (orbit, threshold) cases")
    print("   (terms, max ker, min flag bound over GF(2)-flags incl. transposes): count  ->  "
          + ", ".join(f"{k}:{v}" for k, v in sorted(hist.items())))
    notsharp = [e for e in ext if e[1] < e[2]]
    print("   orbits where no GF(2)-flag attains the exact maximum (terms, max ker, GF(2) bound, with GF(4)-flags, with GF(8)-flags): "
          + ", ".join(str(e) for e in notsharp))
    final = [min(x for x in e[2:] if x is not None) for e in ext]
    print(f"   after extension-field flags the flag bound equals the exact maximum in {sum(1 for e, f in zip(ext, final) if e[1] == f)} "
          f"of {len(ext)} orbits (no flag over GF(2), GF(4) or GF(8) ever goes below the exact maximum)")
    # K = 1 exhaustive at n = 4 (all A, B = diag(I_r, 0)) and the exact value r(r+1)/2
    n = 4
    for r in range(0, 5):
        B = np.diag([1]*r + [0]*(n - r))
        Bs_rows = [mat_to_rows(B)]
        rows = []
        for i in range(n):
            T = block_tables(Bs_rows, n, i)
            shape = [1]*n; shape[i] = 16
            rows += [t.reshape(shape) for t in T]
        rank, _ = batch_rank2(rows, n*n)
        mk = n*n - int(rank.min())
        claim(mk <= r*(r+1)//2, f"T3 one term, n=4, rank B = {r}: max ker {mk} > r(r+1)/2 (flag bound)")
        print(f"   one term, n = 4, B of rank {r}: exact max ker over all 2^16 A = {mk}; flag bound r(r+1)/2 = {r*(r+1)//2}")

# ----------------------------------------------------------------------------------------------------------
# T4  Corollary (at most two terms) at n = 3 over GF(3): exact pruned decision
# ----------------------------------------------------------------------------------------------------------
def gf_blocks(Bs, n, p, i):
    """All block-i matrices (p^(K n), n, n^2) of M = SWAP - sum A (x) B over GF(p); alpha index in base p."""
    K = len(Bs)
    NA = p ** (K * n)
    base = np.zeros((n, n*n), dtype=np.int16)
    for k in range(n):
        base[k, k*n + i] = 1
    dirs = []
    for a in range(K):
        for j in range(n):
            D = np.zeros((n, n*n), dtype=np.int16)
            for k in range(n):
                D[k, j*n:(j+1)*n] = Bs[a][k]
            dirs.append(D)
    digits = np.array(list(itertools.product(range(p), repeat=K*n)), dtype=np.int16)   # (NA, K n)
    blocks = (base[None] - np.tensordot(digits, np.array(dirs), axes=(1, 0))) % p
    return blocks, digits

def decide_low_rank_p(Bs, n, p, rstar, chunk=300_000, work_cap=60_000_000):
    """Is there (A_a) with rank(SWAP - sum A (x) B) <= rstar (< n)?  Exact via block pruning.  n = 3 only.
    Returns (True, witness, sizes) / (False, None, sizes) / (None, None, sizes) when the work cap is hit."""
    assert n == 3 and rstar < n
    blocks = []; L = []
    for i in range(n):
        bl, dg = gf_blocks(Bs, n, p, i)
        rk = batch_rank_p(bl, p)
        keep = np.nonzero(rk <= rstar)[0]
        blocks.append(bl[keep]); L.append(dg[keep])
    sizes = [len(x) for x in L]
    if min(sizes) == 0:
        return False, None, sizes
    n0, n1, n2 = sizes
    if n0 * n1 > work_cap:
        return None, None, sizes
    surv = []
    step = max(1, chunk // n1)
    for lo in range(0, n0, step):
        hi = min(n0, lo + step)
        i0 = np.repeat(np.arange(lo, hi), n1); i1 = np.tile(np.arange(n1), hi - lo)
        rk = batch_rank_p(np.concatenate([blocks[0][i0], blocks[1][i1]], axis=1), p)
        k = np.nonzero(rk <= rstar)[0]
        if k.size:
            surv.append(np.stack([i0[k], i1[k]], axis=1))
    if not surv:
        return False, None, sizes
    surv = np.concatenate(surv)
    if len(surv) * n2 > work_cap:
        return None, None, sizes
    step = max(1, chunk // n2)
    for lo in range(0, len(surv), step):
        hi = min(len(surv), lo + step)
        s_ = np.repeat(np.arange(lo, hi), n2); j2 = np.tile(np.arange(n2), hi - lo)
        st = np.concatenate([blocks[0][surv[s_, 0]], blocks[1][surv[s_, 1]], blocks[2][j2]], axis=1)
        rk = batch_rank_p(st, p)
        h = np.nonzero(rk <= rstar)[0]
        if h.size:
            h = h[0]
            return True, (L[0][surv[s_[h], 0]], L[1][surv[s_[h], 1]], L[2][j2[h]]), sizes
    return False, None, sizes

def digits_to_As(wit, K, n):
    As = [np.zeros((n, n), dtype=np.int64) for _ in range(K)]
    for i, dg in enumerate(wit):
        for a in range(K):
            for j in range(n):
                As[a][i, j] = int(dg[a*n + j])
    return As

def similarity_class_reps(n, p):
    """One representative per conjugacy class of M_n(GF(p)) (orbit search; n = 3, p = 3: 39 classes)."""
    N = p ** (n*n)
    def dec(c):
        return np.array([(c // p**t) % p for t in range(n*n)], dtype=np.int64).reshape(n, n)
    def enc(M):
        return int(sum(int(x) * p**t for t, x in enumerate(np.array(M).reshape(-1))))
    gens = [np.roll(np.eye(n, dtype=np.int64), 1, axis=0), (np.eye(n, dtype=np.int64) + E(n, 0, 1)) % p,
            (np.eye(n, dtype=np.int64) + E(n, 1, 0)) % p, np.diag([2 % p if p > 2 else 1] + [1]*(n-1))]
    gi = [inv_mod(G, p) for G in gens]
    seen = np.zeros(N, dtype=bool); reps = []
    for c in range(N):
        if seen[c]:
            continue
        reps.append(dec(c)); seen[c] = True
        stack = [c]
        while stack:
            x = stack.pop(); X = dec(x)
            for G, Gi in zip(gens, gi):
                y = enc((G @ X @ Gi) % p)
                if not seen[y]:
                    seen[y] = True; stack.append(y)
    return reps

def companion_p(coeffs, p):
    """Companion matrix of x^d + c_{d-1} x^{d-1} + ... + c_0 over GF(p); coeffs = [c_0, ..., c_{d-1}]."""
    d = len(coeffs)
    C = np.zeros((d, d), dtype=np.int64)
    for i in range(d - 1):
        C[i + 1, i] = 1
    for i in range(d):
        C[i, d - 1] = (-coeffs[i]) % p
    return C

def rational_forms_n3(p):
    out = []
    for c in itertools.product(range(p), repeat=3):
        out.append(companion_p(list(c), p))
    for a_ in range(p):
        for b_ in range(p):                              # invariant factors (x - a), (x - a)(x - b)
            out.append(block_diag(np.array([[a_]]), companion_p([(a_*b_) % p, (-(a_ + b_)) % p], p)))
    for a_ in range(p):
        out.append((a_ * np.eye(3, dtype=np.int64)) % p)
    return out

def low_rank_pencil_partners(D, r, p):
    """All B2 in M_3(GF(p)) such that every GF(p)-combination B2 + c D has rank <= r (D = diag(I_r, 0))."""
    allB = np.array(list(itertools.product(range(p), repeat=9)), dtype=np.int16).reshape(-1, 3, 3)
    ok = np.ones(len(allB), dtype=bool)
    for c in range(p):
        ok &= batch_rank_p((allB + c * D[None]) % p, p) <= r
    return allB[ok].astype(np.int64)

def T4(rng, budget5=20.0):
    print("== T4  Corollary (at most two terms) at n = 3 over GF(3) (COMPLETE) and GF(5) (sample): exact decision 'is rank <= 2 reachable?'")
    n = 3; I3 = np.eye(3, dtype=np.int64)
    # WLOG B_1 has maximal rank r in the GF(p)-span and B_1 = diag(I_r, 0).  r = 3: B_2 up to conjugacy.
    # r < 3: every B_2 whose combinations with B_1 all have rank <= r (no further reduction is used).
    for p in (3, 5):
        t0 = time.time()
        pairs = []
        reps = similarity_class_reps(3, 3) if p == 3 else rational_forms_n3(5)
        if p == 3:
            assert len(reps) == 39 and len(rational_forms_n3(3)) == 39
        for C in reps:
            pairs.append(("r=3 (I, C)", I3, C))
        fam = {}
        for r in (2, 1):
            D = np.diag([1]*r + [0]*(3 - r))
            fam[r] = low_rank_pencil_partners(D, r, p)
            sel = range(len(fam[r])) if p == 3 else rng.permutation(len(fam[r]))[:(60 if r == 2 else 25)]
            for t in sel:
                pairs.append((f"r={r}", D, fam[r][t]))
        if p == 5:
            for _ in range(20):
                pairs.append(("random", rng.integers(0, p, size=(3, 3)), rng.integers(0, p, size=(3, 3))))
            pairs = [pairs[t] for t in rng.permutation(len(pairs))]           # so that a time cut keeps a mixed sample
        cnt = {}; und = 0; done = 0; maxL = 0; found = 0
        for name, B1, B2 in pairs:
            if p == 5 and time.time() - t0 > budget5:
                break
            res, wit, sizes = decide_low_rank_p([B1 % p, B2 % p], n, p, 2)
            done += 1; maxL = max(maxL, max(sizes))
            if res is None:
                und += 1
            elif res:
                found += 1
                kd = kerdim(digits_to_As(wit, 2, 3), [B1 % p, B2 % p], p)
                claim(False, f"T4 Corollary (at most two terms) violated over GF({p}): B1={B1.tolist()} B2={B2.tolist()} ker={kd}")
            cnt[name] = cnt.get(name, 0) + 1
        tag = "COMPLETE" if (p == 3 and done == len(pairs) and und == 0) else "sample"
        print(f"   GF({p}) [{tag}]: families r=2: {len(fam[2])} pairs, r=1: {len(fam[1])} pairs; decided {done} of {len(pairs)} "
              f"({', '.join(f'{k}: {v}' for k, v in cnt.items())}); undecided {und}; largest candidate list per block {maxL}; "
              f"B-pairs where rank <= 2 is reachable: {found}; {time.time() - t0:.1f}s")

# ----------------------------------------------------------------------------------------------------------
# T5  Corollary (at most two terms) at n = 4 over GF(2): exact pruned decision
# ----------------------------------------------------------------------------------------------------------
def decide_low_rank_2(Bs, n, rstar, chunk=1_500_000, cap=4_000_000, work_cap=400_000_000):
    """Is there (A_a) over GF(2) with rank(SWAP + sum A (x) B) <= rstar?  Exact: partial stacks of blocks
    0..t are kept only while their rank is <= rstar (a necessary condition for the full stack).
    Returns (True, alphas) / (False, None) / (None, None) if a cap was hit."""
    nb = n*n
    Bs_rows = [mat_to_rows(B) for B in Bs]
    tabs = [block_tables(Bs_rows, n, i) for i in range(n)]
    single = [batch_rank2(tabs[i], nb) for i in range(n)]            # (rank, basis) per block
    ok1 = [np.nonzero(single[i][0] <= rstar)[0] for i in range(n)]
    if any(o.size == 0 for o in ok1):
        return False, None
    sol = [ok1[0]]
    basis = [b[ok1[0]] for b in single[0][1]]
    rank = single[0][0][ok1[0]]
    for t in range(1, n):
        cand = ok1[t]; S = sol[0].size
        if S * cand.size > work_cap:
            return None, None
        step = max(1, chunk // cand.size)
        new_sol = [[] for _ in range(t + 1)]; new_basis = [[] for _ in range(nb)]; new_rank = []
        total = 0
        for lo in range(0, S, step):
            hi = min(S, lo + step)
            ii = np.repeat(np.arange(lo, hi), cand.size); jj = np.tile(np.arange(cand.size), hi - lo)
            rk, bs = batch_rank2([tabs[t][k][cand[jj]] for k in range(n)], nb,
                                 init=([b[ii] for b in basis], rank[ii]))
            keep = np.nonzero(rk <= rstar)[0]
            if keep.size == 0:
                continue
            total += keep.size
            if total > cap:
                return None, None
            for q in range(t):
                new_sol[q].append(sol[q][ii[keep]])
            new_sol[t].append(cand[jj[keep]])
            for b in range(nb):
                new_basis[b].append(bs[b][keep])
            new_rank.append(rk[keep])
        if total == 0:
            return False, None
        sol = [np.concatenate(x) for x in new_sol]
        basis = [np.concatenate(x) for x in new_basis]
        rank = np.concatenate(new_rank)
    return True, [int(s_[0]) for s_ in sol]

def companion(f, d):
    """Companion matrix over GF(2) of the monic polynomial with bit mask f of degree d."""
    C = np.zeros((d, d), dtype=np.int64)
    for i in range(d - 1):
        C[i + 1, i] = 1
    for i in range(d):
        C[i, d - 1] = (f >> i) & 1
    return C

def clmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1; b >>= 1
    return r

def block_diag(*Ms):
    r = sum(M.shape[0] for M in Ms); c = sum(M.shape[1] for M in Ms)
    out = np.zeros((r, c), dtype=np.int64); i = j = 0
    for M in Ms:
        out[i:i+M.shape[0], j:j+M.shape[1]] = M; i += M.shape[0]; j += M.shape[1]
    return out

def rational_forms_gf2_n4():
    out = []
    for f in range(16, 32):
        out.append(companion(f, 4))
    for f1 in (2, 3):
        for q in range(4, 8):
            out.append(block_diag(companion(f1, 1), companion(clmul(f1, q), 3)))
    for f in range(4, 8):
        out.append(block_diag(companion(f, 2), companion(f, 2)))
    for f1 in (2, 3):
        for l in (2, 3):
            out.append(block_diag(companion(f1, 1), companion(f1, 1), companion(clmul(f1, l), 2)))
    for f1 in (2, 3):
        out.append(block_diag(*[companion(f1, 1)]*4))
    return out

def kron_L(eps):          # L_eps: eps x (eps+1) pencil, parts [I 0], [0 I]
    a = np.zeros((eps, eps + 1), dtype=np.int64); b = np.zeros((eps, eps + 1), dtype=np.int64)
    for i in range(eps):
        a[i, i] = 1; b[i, i + 1] = 1
    return a, b

def singular_pencils_n4(rng):
    out = []
    def reg(r, kind):
        if r == 0:
            return np.zeros((0, 0), dtype=np.int64), np.zeros((0, 0), dtype=np.int64)
        if kind == 0:                                  # finite part (I, C)
            return np.eye(r, dtype=np.int64), rng.integers(0, 2, size=(r, r))
        if kind == 1:                                  # infinite part (N, I)
            N = np.zeros((r, r), dtype=np.int64)
            for i in range(r - 1):
                N[i, i + 1] = 1
            return N, np.eye(r, dtype=np.int64)
        return np.eye(r, dtype=np.int64), np.eye(r, dtype=np.int64)
    combos = []
    for eps_list in ([], [0], [1], [2], [3], [0, 0], [0, 1], [1, 1], [0, 2]):
        for eta_list in ([], [0], [1], [2], [3], [0, 0], [0, 1], [1, 1], [0, 2]):
            if not eps_list and not eta_list:
                continue
            rows = sum(eps_list) + sum(e + 1 for e in eta_list)
            cols = sum(e + 1 for e in eps_list) + sum(eta_list)
            if rows <= 4 and cols <= 4 and 4 - rows == 4 - cols:
                combos.append((eps_list, eta_list, 4 - rows))
    for eps_list, eta_list, r in combos:
        for kind in ((0, 1, 2) if r > 0 else (0,)):
            pa, pb = [], []
            for e in eps_list:
                a, b = kron_L(e); pa.append(a); pb.append(b)
            for e in eta_list:
                a, b = kron_L(e); pa.append(a.T.copy()); pb.append(b.T.copy())
            a, b = reg(r, kind); pa.append(a); pb.append(b)
            B1 = block_diag(*pa); B2 = block_diag(*pb)
            assert B1.shape == (4, 4)
            P = rand_invertible(4, 2, rng); Q = rand_invertible(4, 2, rng)      # hide the normal form
            out.append(((P @ B1 @ Q) % 2, (P @ B2 @ Q) % 2))
    return out

def linear_table(P, S, n):
    """Table of B -> P B S on n x n GF(2) matrices coded as ints (bit k*n + l)."""
    tab = np.array([0], dtype=np.uint32)
    for bit in range(n*n):
        Bm = np.zeros((n, n), dtype=np.int64); Bm[bit // n, bit % n] = 1
        tab = np.concatenate([tab, tab ^ np.uint32(mat_to_int((P @ Bm @ S) % 2))])
    return tab

def pencil_reps_gf2(n, r):
    """Pairs (B_1 = diag(I_r, 0), B_2) such that every non-zero element of the span has rank <= r:
    one B_2 per orbit of a subgroup of the stabiliser of B_1 in GL_n x GL_n, together with B_2 -> B_2 + B_1."""
    N = 1 << (n*n)
    B1 = np.diag([1]*r + [0]*(n - r)); b1 = mat_to_int(B1)
    I = np.eye(n, dtype=np.int64)
    tabs = [np.arange(N, dtype=np.uint32) ^ np.uint32(b1)]
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            T = (I + E(n, i, j)) % 2
            if i < r and j < r:
                gens = [(T, T)]                          # T B_1 T^-1 = B_1 (T is an involution)
            elif i >= r and j >= r:
                gens = [(T, I), (I, T)]
            elif i < r <= j:
                gens = [(T, I)]
            else:
                gens = [(I, T)]
            for P, S in gens:
                assert ((P @ B1 @ S) % 2 == B1).all()
                tabs.append(linear_table(P, S, n))
    for tb in tabs:
        assert (tb[tb] == np.arange(N)).all()            # every generator acts as an involution
    lab = np.arange(N, dtype=np.int64)
    while True:
        old = lab.copy()
        for tb in tabs:
            lab = np.minimum(lab, lab[tb])
        if (lab == old).all():
            break
    codes = np.arange(N, dtype=np.uint32)
    rows = lambda c: [(c >> np.uint32(n*k)) & np.uint32((1 << n) - 1) for k in range(n)]
    rk0, _ = batch_rank2(rows(codes), n)
    rk1, _ = batch_rank2(rows(codes ^ np.uint32(b1)), n)
    ok = (rk0 <= r) & (rk1 <= r)
    reps = np.unique(lab[ok])
    return B1, [int_to_mat(int(c), n) for c in reps], int(ok.sum())

def _t5_job(args):
    name, B1, B2 = args
    res, wit = decide_low_rank_2([B1, B2], 4, 5)
    return name, B1, B2, res, wit

def T5(rng, budget=150.0):
    print("== T5  Corollary (at most two terms) at n = 4 over GF(2) (COMPLETE): exact decision 'is rank <= 5 reachable?' over all 2^32 (A_1, A_2)")
    # WLOG B_1 has maximal rank r in the span and B_1 = diag(I_r, 0).  r = 4: B_2 up to conjugacy (34 classes).
    # r < 4: B_2 up to a subgroup of the stabiliser of B_1 and up to B_2 -> B_2 + B_1.
    I4 = np.eye(4, dtype=np.int64)
    jobs = [("r=4 (I, C)", I4, C) for C in rational_forms_gf2_n4()]
    info = []
    for r in (3, 2, 1):
        B1, reps, total = pencil_reps_gf2(4, r)
        info.append(f"r={r}: {total} admissible B_2 in {len(reps)} orbits")
        jobs += [(f"r={r}", B1, B2) for B2 in reps]
    nlist = len(jobs)
    # redundant extras: Kronecker-singular normal forms hidden by random equivalences, and random pairs
    jobs += [("extra: Kronecker-singular", a_, b_) for a_, b_ in singular_pencils_n4(rng)]
    for _ in range(40):
        jobs.append(("extra: random dense", rng.integers(0, 2, size=(4, 4)), rng.integers(0, 2, size=(4, 4))))
    for _ in range(40):
        jobs.append(("extra: random sparse", (rng.random((4, 4)) < 0.3).astype(np.int64), (rng.random((4, 4)) < 0.3).astype(np.int64)))
    t0 = time.time(); cnt = {}; und = 0; done = 0; found = 0
    import multiprocessing as mp
    with mp.Pool(4) as pool:
        for name, B1, B2, res, wit in pool.imap_unordered(_t5_job, jobs, chunksize=4):
            done += 1
            if res is None:
                und += 1
            elif res:
                found += 1
                As = alpha_to_As(wit, 2, 4)
                kd = kerdim(As, [B1, B2], 2)
                claim(False, f"T5 Corollary (at most two terms) violated at n=4 GF(2): B1={B1.tolist()} B2={B2.tolist()} A={[A.tolist() for A in As]} ker={kd}")
            cnt[name] = cnt.get(name, 0) + 1
            if time.time() - t0 > budget:
                pool.terminate(); break
    tag = "COMPLETE" if (done == len(jobs) and und == 0) else "INCOMPLETE"
    print(f"   {'; '.join(info)}")
    print(f"   [{tag}] decided {done} of {len(jobs)} B-pairs ({', '.join(f'{k}: {v}' for k, v in sorted(cnt.items()))}); "
          f"undecided (cap) {und}; B-pairs where rank <= 5 is reachable: {found}; time {time.time() - t0:.1f}s")
    # Theorem FL on the same classes: exact max kernel is unknown, but 'kernel > min flag bound' must be unreachable
    cls = jobs[:nlist]; dec = 0; und2 = 0; asc_att = 0; hist = {}
    for name, B1, B2 in cls:
        beta = min_flag_bound2([B1, B2], 4)
        hist[beta] = hist.get(beta, 0) + 1
        if beta >= 10:
            continue                                      # covered by the two-term decision above
        b_, _ = block_ascent([B1, B2], 4, rng, restarts=3)
        claim(b_ <= beta, f"T5 Theorem FL violated (ascent): B1={B1.tolist()} B2={B2.tolist()} ker {b_} > flag bound {beta}")
        asc_att += (b_ == beta)
        if beta >= 8:
            res, wit = decide_low_rank_2([B1, B2], 4, 15 - beta)
            if res is None:
                und2 += 1
            else:
                dec += 1
                claim(not res, f"T5 Theorem FL violated (exact): B1={B1.tolist()} B2={B2.tolist()} ker > flag bound {beta}")
    print(f"   Theorem FL on the {len(cls)} classes: min flag bound over all 315 GF(2)-flags (B and B^T), histogram {dict(sorted(hist.items()))}; "
          f"classes with bound 8 or 9 decided exactly: {dec} (undecided {und2}); classes with bound < 10 where exhaustive block "
          f"ascent attains the bound: {asc_att} of {sum(v for k, v in hist.items() if k < 10)}")
    # positive controls for the decision procedure
    res, wit = decide_low_rank_2([I4, np.zeros((4, 4), dtype=np.int64)], 4, 6)
    assert res is True                                    # the pairing has rank exactly 6
    S_ = lambda i, j: E(4, i, j) + E(4, j, i)
    three = [S_(0, 1) + E(4, 3, 3), S_(0, 2), S_(1, 2)]   # dual pairing on a 3-block, padded
    res3, wit3 = decide_low_rank_2(three, 4, 5)
    k3 = kerdim(alpha_to_As(wit3, 3, 4), three, 2) if res3 else None
    print(f"   positive controls: threshold 6 with (I, 0): {res};  THREE terms at n = 4 (padded dual pairing), threshold 5: {res3} "
          f"(dim ker {k3} > 10: the two-term bound also fails for three terms at n = 4)")
    assert res3 is True and k3 == 11
    # n = 5, GF(2), two terms: block ascent with exhaustive block moves (1024 values per block), bound 15
    I5 = np.eye(5, dtype=np.int64); best5 = 0; inst = 0
    fam5 = [(I5, np.zeros((5, 5), dtype=np.int64))]
    for f in (0b100101, 0b111111, 0b100000, 0b100001, 0b110011):
        fam5.append((I5, companion(f, 5)))
    for _ in range(14):
        fam5.append((I5, rng.integers(0, 2, size=(5, 5))))
    for _ in range(14):
        fam5.append((rng.integers(0, 2, size=(5, 5)), rng.integers(0, 2, size=(5, 5))))
    for _ in range(10):
        fam5.append(((rng.random((5, 5)) < 0.25).astype(np.int64), (rng.random((5, 5)) < 0.25).astype(np.int64)))
    for B1, B2 in fam5:
        starts = [[1 << i for i in range(5)]] if (B1 == I5).all() else []          # A_1 = I, A_2 = 0: the pairing
        b_, _ = block_ascent([B1, B2], 5, rng, restarts=3, starts=starts, max_moves=80)
        inst += 1; best5 = max(best5, b_)
        claim(b_ <= 15, f"T5 Corollary (at most two terms) violated at n=5 GF(2): B1={B1.tolist()} B2={B2.tolist()} ker {b_}")
    print(f"   n = 5, GF(2), two terms: exhaustive block ascent on {inst} B-pairs: largest kernel {best5} (bound 15)")

# ----------------------------------------------------------------------------------------------------------
# T6  adversarial first factors for Corollary (one triangularizable side) and Theorem FL
# ----------------------------------------------------------------------------------------------------------
def block_ascent(Bs, n, rng, restarts, starts=(), max_moves=60):
    """Block-coordinate ascent over GF(2) with EXHAUSTIVE block moves (all 2^(K n) values of one alpha_i) and
    random tie-breaking.  Returns the largest kernel dimension found."""
    K = len(Bs); nb = n*n; NA = 1 << (K*n)
    Bs_rows = [mat_to_rows(B) for B in Bs]
    tabs = [block_tables(Bs_rows, n, i) for i in range(n)]
    best = 0; best_alpha = None
    for rs in range(restarts + len(starts)):
        alpha = list(starts[rs]) if rs < len(starts) else [int(rng.integers(NA)) for _ in range(n)]
        cur = nb + 1; stall = 0; moves = 0
        while stall < 2*n and moves < max_moves:
            i = int(rng.integers(n)); moves += 1
            others = [int(tabs[j][k][alpha[j]]) for j in range(n) if j != i for k in range(n)]
            xb = xor_basis(others)
            init = ([np.uint32(xb.get(b, 0)) for b in range(nb)], np.int16(len(xb)))
            rk, _ = batch_rank2(tabs[i], nb, init=init)
            m = int(rk.min())
            c = np.nonzero(rk == m)[0]
            alpha[i] = int(c[rng.integers(c.size)])
            if m < cur:
                cur = m; stall = 0
            else:
                stall += 1
        if nb - cur > best:
            best = nb - cur; best_alpha = list(alpha)
    return best, best_alpha

def decide_n3_gf2(Bs, rstar=2):
    return decide_low_rank_2(Bs, 3, rstar)

def perm_matrix(f, n):
    """Read map: (P x)[i] = x[f(i)]."""
    P = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        P[i, f(i) % n] = 1
    return P

def span_basis(mats, p):
    n = mats[0].shape[0]
    R, _ = rref_mod(np.array([M.reshape(-1) for M in mats]), p)
    return [r.reshape(n, n) for r in R]

def basis_with(first, mats, p):
    """Independent subfamily of first + mats spanning the same space, keeping the elements of `first` in front."""
    out = []
    for M in list(first) + list(mats):
        if rank_mod(np.array([x.reshape(-1) for x in out + [M]]), p) > len(out):
            out.append(M)
    return out

def group_closure(gens, n):
    """Closure of permutation matrices under multiplication (small groups)."""
    key = lambda M: M.tobytes()
    seen = {key(g): g for g in gens}
    frontier = list(gens)
    while frontier:
        new = []
        for a in frontier:
            for g in gens:
                c = (a @ g)
                if key(c) not in seen:
                    seen[key(c)] = c; new.append(c)
        frontier = new
    return list(seen.values())

def anneal_gf2(Bs, n, rng, iters, start_As):
    """Single-bit annealing over the A_a (GF(2)), python-int rank.  Weak; used only where nothing better fits."""
    K = len(Bs)
    Brow = [mat_to_rows(B) for B in Bs]
    A = [[int(sum(int(start_As[a][i][j]) << j for j in range(n))) for i in range(n)] for a in range(K)]
    def rows():
        out = []
        for i in range(n):
            for k in range(n):
                m = 1 << (k*n + i)
                for a in range(K):
                    ai = A[a][i]; br = Brow[a][k]
                    if br:
                        j = 0
                        while ai:
                            if ai & 1:
                                m ^= br << (j*n)
                            ai >>= 1; j += 1
                out.append(m)
        return out
    cur = n*n - rank_bits(rows()); best = cur; T = 1.0
    for it in range(iters):
        a = int(rng.integers(K)); i = int(rng.integers(n)); j = int(rng.integers(n))
        A[a][i] ^= 1 << j
        new = n*n - rank_bits(rows())
        if new >= cur or rng.random() < math.exp((new - cur) / max(T, 1e-9)):
            cur = new
        else:
            A[a][i] ^= 1 << j
        T *= 0.9995
        best = max(best, cur)
    return best

def _t6_job(args):
    name, Bs = args
    res, wit = decide_low_rank_2(Bs, 4, 5)
    return name, res

def T6(rng):
    print("== T6  adversarial first factors (Corollary (one triangularizable side), Theorem FL)")
    I3 = np.eye(3, dtype=np.int64); n = 3
    # --- exact decisions at n = 3 over GF(2): 3-dimensional commutative algebras (maximal at n = 3)
    R3 = perm_matrix(lambda i: i + 1, 3)
    C8 = companion(0b1011, 3)                        # x^3 + x + 1: the field GF(8); flag only over GF(8)
    Nil = E(3, 0, 1) + E(3, 1, 2)
    algs = {
        "circulants F2[Z_3]": [I3, R3, (R3 @ R3) % 2],
        "field GF(8) (no GF(2)-flag)": [I3, C8, (C8 @ C8) % 2],
        "F2[x]/(x^3)": [I3, Nil, (Nil @ Nil) % 2],
        "diagonal": [E(3, 0, 0), E(3, 1, 1), E(3, 2, 2)],
        "GF(4) x GF(2)": [I3, block_diag(companion(7, 2), np.zeros((1, 1), dtype=np.int64)), E(3, 2, 2)],
        "span{I, E02, E12}": [I3, E(3, 0, 2), E(3, 1, 2)],
        "span{I, E01, E02}": [I3, E(3, 0, 1), E(3, 0, 2)],
        "span{I, E01, E12, E02} (not commutative, triangular)": [I3, E(3, 0, 1), E(3, 1, 2), E(3, 0, 2)],
        "Sylow-2 of S_3 x trivial: span{I, (01)}": [I3, perm_matrix(lambda i: [1, 0, 2][i], 3)],
    }
    for name, Bs in algs.items():
        P = rand_invertible(3, 2, rng); Q = rand_invertible(3, 2, rng)
        for hidden, Bh in (("", Bs), (" (hidden by P . Q)", [(P @ B @ Q) % 2 for B in Bs])):
            res, wit = decide_n3_gf2(Bh, 2)
            assert decide_low_rank_p(Bh, 3, 2, 2)[0] == res, "GF(p) and GF(2) decision codes disagree"
            if res:
                kd = kerdim(alpha_to_As(wit, len(Bh), 3), Bh, 2)
                claim(False, f"T6 Corollary (one triangularizable side) or (a pair of flags) violated at n=3 GF(2): {name}{hidden}: ker {kd}")
            print(f"   n=3 GF(2) exact: {name}{hidden}: kernel >= 7 reachable? {res}")
    # positive control: three alternating matrices (dual pairing) do reach rank 1
    alt = [E(3, i, j) + E(3, j, i) for i in range(3) for j in range(i + 1, 3)]
    res, wit = decide_n3_gf2(alt, 2)
    assert decide_low_rank_p(alt, 3, 2, 2)[0] == res, "GF(p) and GF(2) decision codes disagree"
    kd = kerdim(alpha_to_As(wit, 3, 3), alt, 2) if res else None
    print(f"   positive control, B-span = alternating matrices (dual pairing): kernel >= 7 reachable? {res} (found ker {kd})")
    assert res is True
    # --- Theorem FL, exact, n = 3 over GF(2): random 3- and 4-dimensional spans with flag bound beta;
    #     'kernel >= beta + 1' must be unreachable for every choice of first factors
    cntE = {}; undE = 0; tries = 0; total = 0
    while total < 70 and tries < 600:
        tries += 1
        d = 3 if rng.random() < 0.6 else 4
        if rng.random() < 0.6:                            # inside a random staircase, hidden by an equivalence
            g = sorted(int(x) for x in rng.integers(1, 4, size=3))
            cells = [(k, i) for i in range(3) for k in range(g[i])]
            Bs = []
            for _ in range(d):
                B = np.zeros((3, 3), dtype=np.int64)
                for (k, i) in cells:
                    B[k, i] = rng.integers(0, 2)
                Bs.append(B)
            P = rand_invertible(3, 2, rng); Q = rand_invertible(3, 2, rng)
            Bs = [(P @ B @ Q) % 2 for B in Bs]
        else:
            Bs = [(rng.random((3, 3)) < 0.35).astype(np.int64) for _ in range(d)]
        if rank_mod(np.array([B.reshape(-1) for B in Bs]), 2) < d:
            continue
        beta = min_flag_bound2(Bs, 3)
        if beta >= 9 or beta < (4 if d == 3 else 6):
            continue
        res, wit = decide_low_rank_2(Bs, 3, 8 - beta)
        total += 1
        if res is None:
            undE += 1
        elif res:
            kd = kerdim(alpha_to_As(wit, d, 3), Bs, 2)
            claim(False, f"T6 Theorem FL violated at n=3 GF(2): Bs={[B.tolist() for B in Bs]} ker {kd} > flag bound {beta}")
        cntE[(d, beta)] = cntE.get((d, beta), 0) + 1
    print(f"   n=3 GF(2) exact, Theorem FL: {total} random spans (dim, flag bound): count {dict(sorted(cntE.items()))}; "
          f"'kernel > flag bound' reachable: {sum(1 for f in FAIL if 'T6 Theorem FL violated at n=3' in f)}; undecided {undE}")
    # --- exact decisions at n = 4 over GF(2) with three second factors (all 2^48 first factors)
    I4 = np.eye(4, dtype=np.int64)
    R4 = perm_matrix(lambda i: i + 1, 4); N4 = E(4, 0, 1) + E(4, 1, 2) + E(4, 2, 3); C16 = companion(0b10011, 4)
    jobs = [("circulant I, R, R^2 (parts (a) and (b))", [I4, R4, (R4 @ R4) % 2]),
            ("I, N, N^2 (nilpotent Jordan block)", [I4, N4, (N4 @ N4) % 2]),
            ("I, C, C^2 in the field GF(16) (flag only over GF(16))", [I4, C16, (C16 @ C16) % 2]),
            ("2-group: I, (01), (02)(13)", [I4, perm_matrix(lambda i: [1, 0, 2, 3][i], 4), perm_matrix(lambda i: [2, 3, 0, 1][i], 4)]),
            ("2-group AGL_1(Z/4): i+1, 3i, 3i+1", [R4, perm_matrix(lambda i: 3*i, 4), perm_matrix(lambda i: 3*i + 1, 4)]),
            ("even-stride decimation with rotations: I, i+1, 2i (not a group; binomial flag)",
             [I4, R4, perm_matrix(lambda i: 2*i, 4)]),
            ("decimations 2i, 2i+1 and I (binomial flag)", [perm_matrix(lambda i: 2*i, 4), perm_matrix(lambda i: 2*i + 1, 4), I4]),
            ("commuting: I, E02 + E13, E03", [I4, E(4, 0, 2) + E(4, 1, 3), E(4, 0, 3)]),
            ("Schur-type commutative: E02, E03, E12 (+ no identity)", [E(4, 0, 2), E(4, 0, 3), E(4, 1, 2)]),
            ("GF(4) (x) I_2: I, C (+) C, E-block", [I4, block_diag(companion(7, 2), companion(7, 2)), block_diag(np.zeros((2, 2), dtype=np.int64), np.eye(2, dtype=np.int64))])]
    import multiprocessing as mp
    with mp.Pool(4) as pool:
        out = pool.map(_t6_job, jobs)
    for name, res in out:
        claim(res is not True, f"T6 Corollary (one triangularizable side) violated at n=4 GF(2): {name}")
        print(f"   n=4 GF(2) exact (three second factors): {name}: kernel >= 11 reachable? {res}")
    # --- GF(3), n = 3: circulants F3[x]/(x-1)^3 and the field GF(27) (exact decisions; 3^9 alphas per block)
    R3 = perm_matrix(lambda i: i + 1, 3)
    C27 = np.array([[0, 0, 1], [1, 0, 1], [0, 1, 0]])            # companion of x^3 - x - 1, irreducible mod 3
    assert all((v**3 - v - 1) % 3 for v in range(3))
    assert ((C27 @ C27 @ C27 - C27 - I3) % 3 == 0).all()
    for name, Bs in (("circulants F3[Z_3]", [I3, R3, (R3 @ R3) % 3]), ("field GF(27)", [I3, C27, (C27 @ C27) % 3])):
        res, wit, sizes = decide_low_rank_p(Bs, 3, 3, 2)
        if res:
            claim(False, f"T6 Corollary (one triangularizable side) violated at n=3 GF(3): {name}")
        print(f"   n=3 GF(3) exact: {name}: kernel >= 7 reachable? {res} (candidate lists per block {sizes})")
    alt3 = [(E(3, i, j) - E(3, j, i)) % 3 for i in range(3) for j in range(i + 1, 3)]
    res, wit, sizes = decide_low_rank_p(alt3, 3, 3, 2)
    kd = kerdim(digits_to_As(wit, 3, 3), alt3, 3) if res else None
    print(f"   positive control GF(3), B-span = antisymmetric matrices: kernel >= 7 reachable? {res} (found ker {kd}; lists {sizes})")
    assert res is True
    # --- n = 4, GF(2): block ascent with exhaustive block moves
    n = 4
    circ = [I4, R4, (R4 @ R4) % 2, (R4 @ R4 @ R4) % 2]
    pairing_start = lambda Bs, idx: [1 << (idx*4 + i) for i in range(4)]                          # A_idx = I, others 0
    b, al = block_ascent(circ, 4, rng, restarts=14, starts=[pairing_start(circ, 0)])
    claim(b <= 10, f"T6 Corollary (one triangularizable side) violated: circulants n=4 GF(2), ker {b}")
    print(f"   n=4 GF(2) circulants = F2[Z_4] (parts (a) and (b)): best kernel by exhaustive block ascent {b} (bound 10)")
    # Sylow 2-subgroups of S_4: AGL_1(Z/4) (2-adic hierarchy) and the interval hierarchy
    agl = group_closure([perm_matrix(lambda i: i + 1, 4), perm_matrix(lambda i: 3*i, 4)], 4)
    intv = group_closure([perm_matrix(lambda i: [1, 0, 2, 3][i], 4), perm_matrix(lambda i: [2, 3, 0, 1][i], 4)], 4)
    for name, G in (("AGL_1(Z/4)", agl), ("interval-hierarchy Sylow", intv)):
        sb = span_basis(G, 2)
        fb = min_flag_bound2(sb, 4)
        best = 0
        for _ in range(5):                                           # 4-dimensional subspaces of the span, A = I start
            pick = [sb[t] for t in rng.permutation(len(sb))[:4]]
            if not any((B == I4).all() for B in pick):
                pick[0] = I4
            idxI = next(t for t, B in enumerate(pick) if (B == I4).all())
            b, _ = block_ascent(pick, 4, rng, restarts=2, starts=[pairing_start(pick, idxI)])
            best = max(best, b)
        sbI = basis_with([I4], sb, 2)
        best = max(best, anneal_gf2(sbI, 4, rng, 6000, [I4] + [np.zeros((4, 4), dtype=np.int64)]*(len(sbI) - 1)))
        claim(best <= 10, f"T6 Corollary (one triangularizable side), part (b), violated: {name} n=4 GF(2): ker {best}")
        print(f"   n=4 GF(2) {name}: |G| = {len(G)}, span dim {len(sb)}, min flag bound over all 315 GF(2)-flags {fb}; "
              f"best kernel found {best} (bound 10)")
    # the two Sylow subgroups TOGETHER (rotation + adjacent swap generate S_4): part (b) does not apply
    s4 = group_closure([perm_matrix(lambda i: i + 1, 4), perm_matrix(lambda i: [1, 0, 2, 3][i], 4)], 4)
    sb = span_basis(s4, 2)
    fb = min_flag_bound2(sb, 4)
    sbI = basis_with([I4], sb, 2)
    best = anneal_gf2(sbI, 4, rng, 12000, [I4] + [np.zeros((4, 4), dtype=np.int64)]*(len(sbI) - 1))
    for _ in range(4):
        pick = [I4] + [sb[t] for t in rng.permutation(len(sb))[:3]]
        b, _ = block_ascent(pick, 4, rng, restarts=2, starts=[pairing_start(pick, 0)])
        best = max(best, b)
    claim(best <= fb, f"T6 Theorem FL violated for the span of S_4: ker {best} > {fb}")
    print(f"   n=4 GF(2) rotations AND dyadic interval swaps together: group order {len(s4)}, span dim {len(sb)}, "
          f"min flag bound {fb} (> 10 means part (b) gives nothing); best kernel found {best}")
    # staircase subspaces at n = 4: random 3- and 4-dimensional subspaces of St(g), exhaustive block ascent
    viol = 0; att = 0; tot = 0
    for _ in range(10):
        g = sorted(int(x) for x in rng.integers(0, 5, size=4))
        cells = [(k, i) for i in range(4) for k in range(g[i])]
        if len(cells) < 3:
            continue
        d = int(rng.integers(3, 5))
        Bs = []
        for _ in range(d):
            B = np.zeros((4, 4), dtype=np.int64)
            for (k, i) in cells:
                B[k, i] = rng.integers(0, 2)
            Bs.append(B)
        fb = min_flag_bound2(Bs, 4)
        assert fb == min(min_flag_bound(Bs, 4, 2), min_flag_bound([B.T for B in Bs], 4, 2))      # bitset == dense
        b, _ = block_ascent(Bs, 4, rng, restarts=3)
        tot += 1
        if b > fb:
            viol += 1; claim(False, f"T6 Theorem FL violated: staircase subspace g={g}, ker {b} > flag bound {fb}")
        if b == fb:
            att += 1
    print(f"   n=4 GF(2) random 3-4 dim subspaces of staircases: {tot} instances, violations {viol}, "
          f"flag bound attained by the search in {att}")
    # n = 8: AGL_1(Z/8), annealing from the pairing
    n = 8; I8 = np.eye(8, dtype=np.int64)
    G8 = group_closure([perm_matrix(lambda i: i + 1, 8), perm_matrix(lambda i: 3*i, 8), perm_matrix(lambda i: 5*i, 8)], 8)
    pick = [I8] + [G8[t] for t in rng.permutation(len(G8))[:5]]
    best = anneal_gf2(pick, 8, rng, 4000, [I8] + [np.zeros((8, 8), dtype=np.int64)]*5)
    claim(best <= 36, f"T6 Corollary (one triangularizable side), part (b), violated at n=8: ker {best}")
    print(f"   n=8 GF(2) AGL_1(Z/8) (order {len(G8)}), 6 terms, annealing from the pairing: best kernel {best} (bound 36) [weak]")

# ----------------------------------------------------------------------------------------------------------
# T7  decimation and masks: the character flag
# ----------------------------------------------------------------------------------------------------------
def freq_orders(n, rng, extra=3):
    """Orderings of Z_n by |frequency|; ties +k / -k in every fixed way plus random choices."""
    half = [(k, -k) for k in range(1, (n - 1)//2 + 1)]
    tail = [n//2] if n % 2 == 0 else []
    outs = []
    outs.append([0] + [x for (a, b) in half for x in (a, b)] + tail)
    outs.append([0] + [x for (a, b) in half for x in (b, a)] + tail)
    for _ in range(extra):
        outs.append([0] + [x for (a, b) in half for x in ((a, b) if rng.random() < 0.5 else (b, a))] + tail)
    return outs

def T7(rng):
    print("== T7  Corollary (blocks and expansion), decimations and masks: g(i) on the character flag")
    # (a) combinatorial count, all n <= 60, s <= 8, including multipliers not coprime to n and m = 0
    worst = -10**9; bad = 0; cnt = 0
    for n in range(2, 61):
        for s in range(1, 9):
            for order in freq_orders(n, rng, extra=2):
                img = set()
                for i, k in enumerate(order, start=1):
                    for m in range(-s, s + 1):
                        img.add((m * k) % n)
                    gi = len(img)
                    cnt += 1
                    worst = max(worst, gi - (s*i + 1))
                    if gi > s*i + 1:
                        bad += 1
    claim(bad == 0, f"T7 g(i) <= s i + 1 fails combinatorially ({bad} cases)")
    bad2 = 0; cnt2 = 0
    for n in range(3, 61, 2):
        for s in range(1, 6):
            mus = [int(x) for x in rng.integers(1, n, size=s)]            # ARBITRARY multipliers, with their negatives
            for order in freq_orders(n, rng, extra=1):
                img = set()
                for i, k in enumerate(order, start=1):
                    for mu in mus:
                        img.add((mu * k) % n); img.add((-mu * k) % n)
                    cnt2 += 1
                    if len(img) > s*i + 1:
                        bad2 += 1
    claim(bad2 == 0, "T7 symmetric-multiplier count fails")
    print(f"   the same bound for ARBITRARY multiplier sets (+-mu_1, ..., +-mu_s), not only |m| <= s: {cnt2} cases, violations {bad2}")
    print(f"   combinatorial: {cnt} (n, s, order, i) cases, n <= 60, s <= 8: max of g(i) - (s i + 1) = {worst}; violations {bad}")
    # (b) actual matrices over GF(p), p = 1 mod n (covers even n, where char 2 is excluded by the hypothesis)
    def root_of_unity(n, p):
        for x in range(2, p):
            w = pow(x, (p - 1)//n, p)
            if all(pow(w, n//q, p) != 1 for q in range(2, n + 1) if n % q == 0 and all(q % r for r in range(2, q))):
                return w
        raise ValueError
    bad = 0; badT = {1: 0, 2: 0, 3: 0}; casesT = {1: 0, 2: 0, 3: 0}; cases = 0; mask_bad = 0; mask_eq = 0; mask_cases = 0
    for n, p in ((5, 11), (6, 7), (7, 29), (8, 17), (9, 19), (10, 11), (12, 13)):
        w = root_of_unity(n, p)
        for s in (1, 2, 3):
            Bs = [perm_matrix(lambda i, m=m, t=t: m*i + t, n) for m in range(-s, s + 1) for t in range(n)]
            for order in freq_orders(n, rng, extra=1):
                F = np.array([[pow(w, (k * i) % n, p) for k in order] for i in range(n)], dtype=np.int64)
                g = profile(Bs, F, p)
                comb = []
                img = set()
                for k in order:
                    for m in range(-s, s + 1):
                        img.add((m*k) % n)
                    comb.append(len(img))
                cases += 1
                if g != comb or any(g[i] > s*(i + 1) + 1 for i in range(n)):
                    bad += 1; claim(False, f"T7 decimation profile wrong: n={n} p={p} s={s} g={g} comb={comb}")
                # write maps (transposed convention), multipliers m != 0 only
                BsT = [perm_matrix(lambda i, m=m, t=t: m*i + t, n).T for m in range(-s, s + 1) if m for t in range(n)]
                gT = profile(BsT, F, p)
                casesT[s] += 1
                if any(gT[i] > s*(i + 1) + 1 for i in range(n)):
                    badT[s] += 1
        # masks: M pieces, all rotations of every piece
        for Mp in (2, 3):
            cuts = [(k * n) // Mp for k in range(Mp + 1)]
            Bs = []
            for piece in range(Mp):
                for t in range(n):
                    P = np.zeros((n, n), dtype=np.int64)
                    for i in range(cuts[piece], cuts[piece + 1]):
                        P[i, (i + t) % n] = 1
                    Bs.append(P)
            order = freq_orders(n, rng, extra=0)[0]
            F = np.array([[pow(w, (k * i) % n, p) for k in order] for i in range(n)], dtype=np.int64)
            g = profile(Bs, F, p)
            exact = [sum(min(i, cuts[q + 1] - cuts[q]) for q in range(Mp)) for i in range(1, n + 1)]
            mask_cases += 1
            if any(g[i] > Mp*(i + 1) for i in range(n)) or g != exact:
                mask_bad += 1; claim(False, f"T7 mask profile: n={n} M={Mp} g={g} expected {exact}")
            if all(g[i] == Mp*(i + 1) for i in range(n)):
                mask_eq += 1
    print(f"   GF(p), p = 1 mod n, n in 5..12, s <= 3, all t, m in [-s, s] incl. 0 and non-coprime: {cases} cases, "
          f"profile == combinatorial count and <= s i + 1: violations {bad}")
    print("   same families transposed (write maps y[m i + t] <- x[i], m != 0): character-flag profile exceeds s i + 1 in "
          + ", ".join(f"s={k}: {badT[k]}/{casesT[k]}" for k in (1, 2, 3))
          + " cases (the count only uses that the frequency sets S_i are symmetric and that there are s multipliers up to sign)")
    print(f"   masks, M = 2, 3: g(i) = sum_l min(i, |J_l|) <= M i in all {mask_cases} cases (violations {mask_bad}); "
          f"literal equality g(i) = M i for all i in {mask_eq} cases (it must fail once i exceeds a piece length)")
    # (c) the same over GF(2^k), n odd
    bad = 0; cases = 0
    for n, k in ((3, 2), (5, 4), (7, 3), (9, 6)):
        gf = GF2k(k); w = gf.exp[(gf.q - 1)//n]
        for s in (1, 2, 3):
            maps = [(m, t) for m in range(-s, s + 1) for t in range(n)]
            for order in freq_orders(n, rng, extra=1):
                chars = [[gf.pw(w, (kf * i) % n) for i in range(n)] for kf in order]       # chars[c][i]
                img_rows = []; g = []
                for c in range(n):
                    for (m, t) in maps:
                        img_rows.append([chars[c][(m*i + t) % n] for i in range(n)])   # (B chi)(i) = chi(m i + t)
                    g.append(gf.rank(img_rows))
                cases += 1
                if any(g[i] > s*(i + 1) + 1 for i in range(n)):
                    bad += 1; claim(False, f"T7 GF(2^{k}) decimation profile n={n} s={s}: {g}")
    print(f"   GF(2^k), n = 3, 5, 7, 9: {cases} cases, violations {bad}")
    # (e) n a power of char F (excluded by the hypothesis of the decimation bound): the binomial flag
    #     W_i = ker (R - 1)^i = span{ j -> C(j, d) mod p : d < i } is preserved by EVERY affine map j -> m j + t,
    #     units or not, so Corollary (a pair of flags) gives the half bound for all rotations and all decimations
    #     together: this is Corollary (all affine index maps in characteristic p)
    out = []
    for n, p in ((4, 2), (8, 2), (16, 2), (9, 3), (27, 3), (25, 5)):
        F = np.array([[math.comb(j, d) % p for d in range(n)] for j in range(n)], dtype=np.int64)
        assert rank_mod(F, p) == n
        R = perm_matrix(lambda i: i + 1, n)
        Wchk = all(rank_mod((np.linalg.matrix_power((R - np.eye(n, dtype=np.int64)) % p, 1) @ F[:, :i]) % p, p) <= i - 1
                   for i in range(1, n + 1))                          # (R - 1) W_i inside W_(i-1): dimension drops
        Bs = [perm_matrix(lambda i, m=m, t=t: m*i + t, n) for m in range(n) for t in range(n)]
        g = profile(Bs, F, p)
        okp = all(g[i] <= i + 1 for i in range(n))
        claim(okp and Wchk, f"T7(e) binomial flag not preserved by affine maps: n={n} p={p} g={g}")
        # masks on the same flag (the character flag does not exist here)
        cuts = [0, n // 2, n]
        Bm = []
        for piece in range(2):
            for t in range(n):
                P = np.zeros((n, n), dtype=np.int64)
                for i in range(cuts[piece], cuts[piece + 1]):
                    P[i, (i + t) % n] = 1
                Bm.append(P)
        gm = profile(Bm, F, p)
        okm = gm == [min(i, cuts[1]) + min(i, n - cuts[1]) for i in range(1, n + 1)]
        claim(okm, f"T7(e) mask profile on the binomial flag: n={n} p={p} g={gm}")
        out.append(f"n={n} char {p}: all {n*n} affine maps g(i) <= i: {okp}; two masks: g(i) = min(i, n/2) + min(i, n - n/2): {okm}")
    print("   n a power of char F (binomial flag ker (R-1)^i instead of characters): " + "; ".join(out))
    # (d) kernel side, GF(2): decimation families, annealing from the pairing (weak) against the decimation bound
    for n, s in ((5, 1), (5, 2), (7, 1), (7, 2)):
        In = np.eye(n, dtype=np.int64)
        Bs = [perm_matrix(lambda i, m=m, t=t: m*i + t, n) for m in range(-s, s + 1) if m for t in range(n)]
        sb = basis_with([In], Bs, 2)
        best = 0
        for st in range(2):
            best = max(best, anneal_gf2(sb, n, rng, 2500, [In] + [np.zeros((n, n), dtype=np.int64)]*(len(sb) - 1)))
        bound = sum(min(n, s*i + 1) for i in range(1, n + 1))
        claim(best <= bound, f"T7 decimation kernel bound violated n={n} s={s}: {best} > {bound}")
        print(f"   kernel side n={n} s={s} (span dim {len(sb)}): annealing from the pairing {n*(n+1)//2} reaches {best}; "
              f"flag bound {bound} [weak search]")

# ----------------------------------------------------------------------------------------------------------
# T8  rotations + one interval mask generate M_n(F)
# ----------------------------------------------------------------------------------------------------------
def algebra_dim(gens, p, n):
    basis = np.zeros((0, n*n), dtype=np.int64)
    queue = [np.eye(n, dtype=np.int64)]
    elems = []
    while queue:
        M = queue.pop()
        cand = np.concatenate([basis, (M.reshape(1, -1) % p)], axis=0)
        R, piv = rref_mod(cand, p)
        if len(piv) > basis.shape[0]:
            basis = R
            for G in gens:
                queue.append((M @ G) % p)
    return basis.shape[0]

def T8(rng):
    print("== T8  algebra generated by the rotation and one interval mask")
    bad = 0; cases = 0
    for p in (2, 3, 5):
        for n in range(2, 8):
            R = perm_matrix(lambda i: i + 1, n)
            for start in (0, 1):
                for length in range(1, n):
                    D = np.diag([1 if (i - start) % n < length else 0 for i in range(n)])
                    d = algebra_dim([R, D], p, n)
                    cases += 1
                    if d != n*n:
                        bad += 1; claim(False, f"T8 rotation + interval mask do not generate M_n: p={p} n={n} len={length} dim={d}")
    ctrl = []
    for n in (4, 6):
        R = perm_matrix(lambda i: i + 1, n)
        D = np.diag([1 if i % 2 == 0 else 0 for i in range(n)])
        ctrl.append((n, algebra_dim([R, D], 2, n)))
    print(f"   {cases} cases (p in 2,3,5; n <= 7; every proper interval): all of dimension n^2, violations {bad}; "
          f"control, periodic mask (even positions): " + ", ".join(f"n={n}: dim {d} of {n*n}" for n, d in ctrl))

# ----------------------------------------------------------------------------------------------------------
# T9  sharp instances against ALL flags
# ----------------------------------------------------------------------------------------------------------
def tensor_perm(n1, n2, f):
    """Permutation operator on (F^n1 (x) F^n2) (x) (F^n1 (x) F^n2) given on index tuples (a1,a2,b1,b2)."""
    n = n1*n2; N = n*n
    P = np.zeros((N, N), dtype=np.int64)
    for a1, a2, b1, b2 in itertools.product(range(n1), range(n2), range(n1), range(n2)):
        c1, c2, d1, d2 = f(a1, a2, b1, b2)
        P[(c1*n2 + c2)*n + (d1*n2 + d2), (a1*n2 + a2)*n + (b1*n2 + b2)] = 1
    return P

def T9(rng):
    print("== T9  sharp instances: min over ALL flags of GF(p)^n (profiles B, B^T, A, A^T) against dim ker")
    def run(name, Kop, n, p):
        ker = n*n - rank_mod((swap_matrix(n) - Kop) % p, p)
        Asup, Bsup = supports(Kop, n, p)
        # sanity: the supports reproduce K
        vals = {}
        for nm, S in (("B", Bsup), ("B^T", [B.T for B in Bsup]), ("A", Asup), ("A^T", [A.T for A in Asup])):
            vals[nm] = min_flag_bound(S, n, p)
        b = min(vals.values())
        claim(ker <= b, f"T9 Theorem FL violated on {name} n={n} p={p}: ker {ker} > min flag bound {b}")
        print(f"   {name}, n={n}, GF({p}): Kronecker rank {len(Bsup)}, dim ker {ker}, min flag bounds {vals}"
              + ("  [sharp]" if ker == b else ""))
    for p in (2, 3):
        for n in (3, 4):
            if n == 4 and p == 3:
                continue
            S = swap_matrix(n); v = np.eye(n, dtype=np.int64).reshape(-1, 1)
            run("dual pairing L'", (S - v @ v.T) % p, n, p)
        n = 4
        if p == 2:
            P13 = tensor_perm(2, 2, lambda a1, a2, b1, b2: (b1, a2, a1, b2))
            P24 = tensor_perm(2, 2, lambda a1, a2, b1, b2: (a1, b2, b1, a2))
            run("Klein four P13 + P24 - I", (P13 + P24 - np.eye(16, dtype=np.int64)) % p, 4, p)
            run("partial transpose P13 (blocks 2,2)", P13, 4, p)
            run("partial transpose P24 (blocks 2,2)", P24, 4, p)
            # I (x) I plus an exact swap on a 2-dimensional coordinate block
            Kb = np.eye(16, dtype=np.int64)
            for i in range(2):
                for j in range(2):
                    Kb[i*4 + j, :] = 0; Kb[i*4 + j, j*4 + i] = 1
            run("pairing + exact swap on a 2-block", Kb % p, 4, p)
    # block formula of Corollary (blocks and expansion) on partial transposes n = n1 n2 (blocks n2 times size n1): (n^2 + sum n_s^2)/2
    for n1, n2, p in ((2, 2, 2), (2, 3, 2), (3, 2, 3), (2, 2, 5)):
        n = n1*n2
        P13 = tensor_perm(n1, n2, lambda a1, a2, b1, b2: (b1, a2, a1, b2))
        ker = n*n - rank_mod((swap_matrix(n) - P13) % p, p)
        c5 = (n*n + n2 * n1*n1)//2
        claim(ker <= c5, f"T9 block formula violated on partial transpose n1={n1} n2={n2}")
        print(f"   block formula: partial transpose n1={n1}, n2={n2}, GF({p}): dim ker {ker}; (n^2 + sum n_s^2)/2 = {c5}"
              + ("  [sharp]" if ker == c5 else ""))
    # the block formula with unequal blocks: full block-triangular second-factor space, K = block-restricted swap
    for sizes, p in (((1, 2, 1), 2), ((3, 1), 3), ((2, 1, 2), 2)):
        n = sum(sizes); off = np.cumsum((0,) + sizes)
        blk = [next(s for s in range(len(sizes)) if off[s] <= i < off[s+1]) for i in range(n)]
        # B's: all E_{k,l} with block(k) <= block(l); extremal K = sum over those of E_{l,k} (x) E_{k,l}
        As = [E(n, l, k) for k in range(n) for l in range(n) if blk[k] <= blk[l]]
        Bs = [E(n, k, l) for k in range(n) for l in range(n) if blk[k] <= blk[l]]
        ker = kerdim(As, Bs, p); c5 = (n*n + sum(s*s for s in sizes))//2
        best = 0
        for _ in range(30):
            Ar = [rng.integers(0, p, size=(n, n)) for _ in Bs]
            best = max(best, kerdim(Ar, Bs, p))
        claim(ker <= c5 and best <= c5, f"T9 block formula violated for blocks {sizes}")
        print(f"   block formula: blocks {sizes}, GF({p}): restricted swap has dim ker {ker}; formula {c5}"
              + ("  [sharp]" if ker == c5 else "") + f"; random first factors reach {best}")

# ----------------------------------------------------------------------------------------------------------
# T10  Corollary (blocks and expansion): arithmetic
# ----------------------------------------------------------------------------------------------------------
def T10(rng):
    print("== T10 Corollary (blocks and expansion): sum_i min(n, c i + c0) against (1 - 1/(2c)) n^2 + O((1 + c0/c) n)")
    worst = -1e18
    for c in (1, 1.5, 2, 3, 5, 8):
        for c0 in (0, 1, 2, 5, 20):
            for n in (4, 9, 16, 50, 200, 1000):
                s = sum(min(n, c*i + c0) for i in range(1, n + 1))
                rem = s - (1 - 1/(2*c)) * n*n
                worst = max(worst, rem / ((1 + c0/c) * n))
                if rem > (0.5 + c0/c) * n + 1e-9:
                    claim(False, f"T10 expansion arithmetic: c={c} c0={c0} n={n}: remainder {rem} > (1/2 + c0/c) n")
    print(f"   c >= 1: remainder / ((1 + c0/c) n) is at most {worst:.3f} on the grid; "
          f"explicitly sum <= (1 - 1/(2c)) n^2 + (1/2 + c0/c) n")
    # K terms: c = K, c0 = 0
    ex = [(K, n, sum(min(n, K*i) for i in range(1, n + 1)), (1 - 1/(2*K))*n*n) for K in (1, 2, 3) for n in (6, 12)]
    print("   'K terms give rate <= 1 - 1/(2K)': exact bound vs (1 - 1/(2K)) n^2: "
          + ", ".join(f"K={K} n={n}: {s} vs {v:.0f}" for K, n, s, v in ex) + "  (the difference is the term of order n; K = 1 is the pairing value n(n+1)/2)")
    # c < 1: the formula fails.  B = diag(I_m, 0), A = I, n = 2m; flag alternating kernel / non-kernel vectors
    rows = []
    for m in (2, 4, 8, 12):
        n = 2*m
        B = np.diag([1]*m + [0]*m); A = np.eye(n, dtype=np.int64)
        order = [x for t in range(m) for x in (m + t, t)]          # e_m, e_0, e_{m+1}, e_1, ...
        F = np.eye(n, dtype=np.int64)[:, order]
        g = profile([B], F, 2)
        assert all(g[i] <= (i + 1)/2 for i in range(n)), g       # g(i) <= c i + c0 with c = 1/2, c0 = 0
        # kernel over GF(2) with python-int rank
        Brow = mat_to_rows(B)
        mrows = []
        for i in range(n):
            for k in range(n):
                mrows.append((1 << (k*n + i)) ^ (Brow[k] << (i*n)))     # A = I: only j = i
        ker = n*n - rank_bits(mrows)
        rows.append((n, ker, sum(g), None))
        claim(ker <= sum(g), "T10 Theorem FL violated on the projection example")
    print("   c = 1/2, c0 = 0 (B = projection of rank n/2, flag alternating kernel and non-kernel vectors, g(i) = floor(i/2)):")
    print("     " + "; ".join(f"n={n}: dim ker {k} = n(n+2)/8, Theorem FL bound sum g = {sg}" for n, k, sg, _ in rows))
    print("     the formula (1 - 1/(2c)) n^2 + O(n) of Corollary (blocks and expansion) would give O(n): false for c < 1 (the hypothesis c >= 1 is needed)")
    REMARKS.append("Corollary (blocks and expansion): the expansion formula fails for c < 1 (projection example: g(i) <= i/2, dim ker = n(n+2)/8); the hypothesis c >= 1 is needed.")

# ----------------------------------------------------------------------------------------------------------
# T11  coordinate flags against the direct count for row patterns
# ----------------------------------------------------------------------------------------------------------
def T11(rng):
    print("== T11 coordinate flags: sum g against the count n(n+1)/2 + beta^- for row patterns")
    n = 4
    perms = list(itertools.permutations(range(n)))
    eq = 0; strict = 0; wrong = 0; tot = 0; ex = None; idf = 0; idb = 0
    for trial in range(60):
        dens = rng.choice([0.2, 0.4, 0.7])
        Q = [[ip for ip in range(n) if rng.random() < dens] for _ in range(n)]     # Q[i] = output rows of input row i
        # the direct count: min over orders c, d of the rows of n(n+1)/2 + beta^-(c, d)
        direct = 10**9
        for c in perms:
            for d in perms:
                beta = sum(max(0, d[i] - min(c[x] for x in Q[i])) for i in range(n) if Q[i])
                direct = min(direct, n*(n+1)//2 + beta)
        # Theorem FL on coordinate flags with first factors E_{i' i}: forward profile (A) and backward profile (A^T)
        As = [E(n, ip, i) for i in range(n) for ip in Q[i]]
        res = {}
        for nm, S in (("fwd", As), ("bwd", [A.T for A in As])):
            tE = 10**9; tmax = 10**9
            for order in perms:
                F = np.eye(n, dtype=np.int64)[:, list(order)]
                g = profile(S, F, 2) if S else [0]*n
                tE = min(tE, sum(g)); tmax = min(tmax, sum(max(t + 1, g[t]) for t in range(n)))
            res[nm] = (tE, tmax)
        tE = min(res["fwd"][0], res["bwd"][0])
        tot += 1
        idf += (res["fwd"][1] == direct); idb += (res["bwd"][1] == direct)
        if tE > direct:
            wrong += 1
        if tE == direct:
            eq += 1
        else:
            strict += 1
            if ex is None and tE < direct:
                ex = (Q, tE, direct)
    print(f"   {tot} random row patterns at n = 4: min over coordinate flags of sum g == n(n+1)/2 + min beta^- in {eq}, "
          f"strictly smaller in {strict}, larger in {wrong}")
    print(f"   identity n(n+1)/2 + min_(c,d) beta^- == min over coordinate flags of sum_t max(t, g(t)): "
          f"forward profile {idf}/{tot}, backward profile {idb}/{tot}")
    if ex:
        print(f"   example: Q = {ex[0]}: coordinate-flag sum g = {ex[1]} < n(n+1)/2 + min beta^- = {ex[2]}")
    claim(wrong == 0, "T11: the count n(n+1)/2 + min beta^- is below the Theorem FL bound on coordinate flags (it should never be)")

# ----------------------------------------------------------------------------------------------------------
# T12  realignment and rank-2 perturbations
# ----------------------------------------------------------------------------------------------------------
def T12(rng):
    print("== T12 realignment duality and rank-2 perturbations of the swap")
    ok = True
    for p in (2, 3, 5):
        for n in (2, 3, 4):
            S = swap_matrix(n)
            ok &= bool((realign(S, n) == S).all())
            A = rng.integers(0, p, size=(n, n)); B = rng.integers(0, p, size=(n, n))
            ok &= bool((realign(np.kron(A, B), n) == np.outer(A.reshape(-1), B.reshape(-1))).all())
            x = rng.integers(0, p, size=n*n); y = rng.integers(0, p, size=n*n)
            ok &= bool((realign(np.outer(x, y), n) == np.kron(x.reshape(n, n), y.reshape(n, n))).all())
            L = rng.integers(0, p, size=(n*n, n*n))
            ok &= bool((realign(realign(L, n), n) == L).all())
            v = np.eye(n, dtype=np.int64).reshape(-1, 1)
            Lp = (S - v @ v.T) % p
            ok &= rank_mod(realign(Lp, n) % p, p) == n*(n-1)//2 and rank_mod((S - Lp) % p, p) == 1
    claim(ok, "T12 realignment identities")
    print(f"   R(SWAP) = SWAP, R(A (x) B) = vec A vec B^T, R(x y^T) = X (x) Y, R involution, Kronecker rank(L') = h, rank(SWAP - L') = 1: {ok}")
    worst = {}
    for p in (2, 3):
        for n in (3, 4):
            h = n*(n-1)//2; m = 10**9; S = swap_matrix(n)
            for t in range(1500 if n == 3 else 500):
                kind = t % 3
                if kind == 0:
                    xs = [rng.integers(0, p, size=n*n) for _ in range(4)]
                elif kind == 1:                       # perturbations built from symmetric / identity-like vectors
                    xs = [np.eye(n, dtype=np.int64).reshape(-1), np.eye(n, dtype=np.int64).reshape(-1),
                          rng.integers(0, p, size=n*n), rng.integers(0, p, size=n*n)]
                else:
                    P_ = rand_invertible(n, p, rng)
                    xs = [P_.reshape(-1), inv_mod(P_, p).T.reshape(-1), rng.integers(0, p, size=n*n) * (rng.random(n*n) < 0.3),
                          rng.integers(0, p, size=n*n) * (rng.random(n*n) < 0.3)]
                Ep = (np.outer(xs[0], xs[1]) + np.outer(xs[2], xs[3])) % p
                m = min(m, rank_mod(realign((S - Ep) % p, n) % p, p))
            worst[(p, n)] = (m, h)
            claim(m >= h, f"T12 rank-2 perturbation of the swap with Kronecker rank {m} < h = {h} (p={p}, n={n})")
    print("   min Kronecker rank of SWAP - (rank <= 2), sampled incl. structured: "
          + ", ".join(f"GF({p}) n={n}: {m} (h = {h})" for (p, n), (m, h) in worst.items()))

# ----------------------------------------------------------------------------------------------------------
# T13  Remark (entries of b bits)
# ----------------------------------------------------------------------------------------------------------
def T13(rng):
    print("== T13 Remark (entries of b bits): V (x) V (x) F^b with tau (x) 1; first factors act on V (x) F^b, second factors on V")
    bad = 0; tot = 0; sharp = 0
    for p in (2, 3):
        for n, b in ((3, 2), (4, 2), (3, 3)):
            for trial in range(6):
                g = sorted(int(x) for x in rng.integers(0, n + 1, size=n))
                # basis order: (first index a, lane c, second index d) -> ((a*b + c)*n + d);  K = sum A~ (x) B
                Asm, Bs, Fpl = staircase_instance(n, g, p, rng, hide=True, drop=(0.0 if trial % 2 == 0 else 0.3))
                Cs = [np.eye(b, dtype=np.int64) if trial % 2 == 0 else rng.integers(0, p, size=(b, b)) for _ in Asm]
                N = n*b*n
                Kop = np.zeros((N, N), dtype=np.int64)
                for A, B, C in zip(Asm, Bs, Cs):
                    Kop = (Kop + np.kron(np.kron(A, C) % p, B)) % p
                if trial % 3 == 2:                                     # a term whose first factor mixes lanes freely
                    Bx = Bs[int(rng.integers(len(Bs)))]
                    Kop = (Kop + np.kron(rng.integers(0, p, size=(n*b, n*b)), Bx)) % p
                # tau (x) 1: (a, c, d) -> (d, c, a)
                T = np.zeros((N, N), dtype=np.int64)
                for a in range(n):
                    for c in range(b):
                        for d in range(n):
                            T[(d*b + c)*n + a, (a*b + c)*n + d] = 1
                ker = N - rank_mod((T - Kop) % p, p)
                for F in (Fpl, np.eye(n, dtype=np.int64), rand_invertible(n, p, rng)):
                    sg = sum(profile(Bs, F, p))
                    tot += 1
                    if ker > b*sg:
                        bad += 1; claim(False, f"T13 Remark (entries of b bits) violated: p={p} n={n} b={b} ker {ker} > b sum g = {b*sg}")
                if trial % 2 == 0 and trial % 3 != 2 and ker == b*sum(g):
                    sharp += 1
    print(f"   {tot} (instance, flag) pairs: dim ker <= b * sum g violated {bad} times; planted instances attaining b * sum g: {sharp}")

# ----------------------------------------------------------------------------------------------------------
SECTIONS = {"T1": T1, "T2": T2, "T3": T3, "T4": T4, "T5": T5, "T6": T6, "T7": T7, "T8": T8, "T9": T9,
            "T10": T10, "T11": T11, "T12": T12, "T13": T13}

def main():
    want = [a for a in sys.argv[1:] if a in SECTIONS] or list(SECTIONS)
    t00 = time.time()
    for name in want:
        rng = np.random.default_rng(7919 + int(name[1:]))
        t0 = time.time()
        SECTIONS[name](rng)
        print(f"   [{name}: {time.time() - t0:.1f}s]", flush=True)
    print(f"total time {time.time() - t00:.1f}s")
    if REMARKS:
        print("REMARKS (on hypotheses; not violations):")
        for s in REMARKS:
            print("  -", s)
    if FAIL:
        print(f"VIOLATIONS OF CLAIMS: {len(FAIL)}")
        for s in FAIL[:20]:
            print("  *", s)
        return 1
    print("NO VIOLATION OF THEOREM FL OR OF ITS COROLLARIES FOUND")
    return 0

if __name__ == "__main__":
    sys.exit(main())
