"""icosian_graph.py -- the Goren-Oort dual graphs Gamma+(lambda)\\T at p = 3 and their Tanner codes.

Model. I is the icosian ring: the maximal order of the quaternion algebra over E = Q(sqrt 5) ramified only at the
two infinite places (class number 1); its norm-one units form the binary icosahedral group 2I of order 120.
The prime 3 is inert in E, O_E/3 = F9 and I/3I = M2(F9). Gamma+ = {g in I[1/3] : Nrd g = 1}/{+-1} acts on the
Bruhat-Tits tree T of PGL2(Q_9) without inversions; it is the amalgam 2I/{+-1} *_{S3} alpha (2I/{+-1}) alpha^-1
with alpha = 1 + i + j (reduced norm 3). For a prime ell = 1, 4 (mod 5) and lambda | ell,
Gamma+(lambda) = ker(Gamma+ -> PSL2(F_ell)) is torsion-free, and X = Gamma+(lambda)\\T is the 10-regular
bipartite coset graph with
    even vertices G/H0, odd vertices G/H1, edges G/He,    G = PSL2(F_ell), H0 = A5, H1 = alpha A5 alpha^-1, He = S3.

Edge labels. The edges at the base vertex Lambda0 correspond to the lines im(u alpha mod 3) in
Lambda0/3Lambda0 = F9^2 (u in 2I). At the odd base vertex Lambda1 = alpha Lambda0 (coordinates transported by
alpha) the labels are t . ker(alpha mod 3), t in 2I. The local code at every vertex is evaluation of binary
quartic forms at the 10 label vectors (a generalized Reed-Solomon [10, 5] code, self-dual with unit weights).
Two gluings:
    untw : odd labels  t . k0                (k0 spans ker(alpha mod 3))
    tw   : odd labels  Frob(t . k0)          (coordinatewise cube; the Goren-Oort gluing)
Control 'rand': a random F9^* gauge per edge on the odd side.

Computation. Unknowns are the coefficients of quartic forms at even vertices (5 per vertex); constraints are the
odd-side parity checks. dim T = 5 |V_even| - rank, exact over F9.

Usage: python3 tools/icosian_graph.py ELL [untw] [tw] [rand]      e.g.  python3 tools/icosian_graph.py 11 untw tw
"""
import itertools, sys, time
from fractions import Fraction as Fr
import numpy as np
from gf import GF

F9 = GF(3, 2)          # a + b t, t^2 = -1, encoded a + 3b
PHI9 = 2 + 3 * 1       # phi -> 2 + t  (root of x^2 - x - 1 in F9)

# ----------------------------------------------------------------------------- Z[phi], quaternions (exact)
Z0 = (Fr(0), Fr(0))


def zmul(x, y):
    a, b = x
    c, d = y
    return (a * c + b * d, a * d + b * c + b * d)


def zadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def zneg(x):
    return (-x[0], -x[1])


def qmul(p, q):
    w1, x1, y1, z1 = p
    w2, x2, y2, z2 = q
    s = lambda *t: (sum(u[0] for u in t), sum(u[1] for u in t))
    w = s(zmul(w1, w2), zneg(zmul(x1, x2)), zneg(zmul(y1, y2)), zneg(zmul(z1, z2)))
    x = s(zmul(w1, x2), zmul(x1, w2), zmul(y1, z2), zneg(zmul(z1, y2)))
    y = s(zmul(w1, y2), zneg(zmul(x1, z2)), zmul(y1, w2), zmul(z1, x2))
    z = s(zmul(w1, z2), zmul(x1, y2), zneg(zmul(y1, x2)), zmul(z1, w2))
    return (w, x, y, z)


def qconj(q):
    return (q[0], zneg(q[1]), zneg(q[2]), zneg(q[3]))


def qnorm(q):
    r = Z0
    for c in q:
        r = zadd(r, zmul(c, c))
    return r


def perm_parity(p):
    p = list(p)
    s = 0
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                s ^= 1
    return s


def icosians():
    U = set()
    for pos in range(4):
        for s in (1, -1):
            q = [Z0] * 4
            q[pos] = (Fr(s), Fr(0))
            U.add(tuple(q))
    for sg in itertools.product((1, -1), repeat=4):
        U.add(tuple((Fr(s, 2), Fr(0)) for s in sg))
    half = Fr(1, 2)
    vals0 = [Z0, (half, Fr(0)), (Fr(-1, 2), half), (Fr(0), half)]  # 0, 1/2, phi^-1/2, phi/2
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
    for a in U:
        assert qnorm(a) == (Fr(1), Fr(0))
    for a in U:
        for b in U:
            assert qmul(a, b) in Us, "icosians not closed"
    return U


# ----------------------------------------------------------------------------- reductions
def fr_mod(x, m):
    return x.numerator * pow(x.denominator, -1, m) % m


def z_to_f9(z):
    a, b = fr_mod(z[0], 3), fr_mod(z[1], 3)
    return F9.a(a, F9.m(b, PHI9))


def z_to_fl(z, ell, phil):
    return (fr_mod(z[0], ell) + fr_mod(z[1], ell) * phil) % ell


def mat9_mul(A, B):
    return tuple(tuple(F9.a(F9.m(A[i][0], B[0][j]), F9.m(A[i][1], B[1][j])) for j in range(2)) for i in range(2))


def mat9_add(A, B):
    return tuple(tuple(F9.a(A[i][j], B[i][j]) for j in range(2)) for i in range(2))


def mat9_scal(c, A):
    return tuple(tuple(F9.m(c, A[i][j]) for j in range(2)) for i in range(2))


ONE9 = ((1, 0), (0, 1))
I9 = ((1, 1), (1, 2))      # (1 1; 1 -1), square -1
J9 = ((0, 1), (2, 0))      # (0 1; -1 0)
K9 = mat9_mul(I9, J9)


def q_to_m9(q):
    w, x, y, z = (z_to_f9(c) for c in q)
    M = mat9_scal(w, ONE9)
    M = mat9_add(M, mat9_scal(x, I9))
    M = mat9_add(M, mat9_scal(y, J9))
    M = mat9_add(M, mat9_scal(z, K9))
    return M


def fl_data(ell):
    phil = next(x for x in range(ell) if (x * x - x - 1) % ell == 0)
    a, b = next((a, b) for a in range(ell) for b in range(ell) if (a * a + b * b + 1) % ell == 0)
    Il = np.array([[a, b], [b, -a % ell]], dtype=np.int64)
    Jl = np.array([[0, 1], [ell - 1, 0]], dtype=np.int64)
    Kl = Il @ Jl % ell
    return phil, Il, Jl, Kl


def q_to_ml(q, ell, phil, Il, Jl, Kl):
    w, x, y, z = (z_to_fl(c, ell, phil) for c in q)
    return (w * np.eye(2, dtype=np.int64) + x * Il + y * Jl + z * Kl) % ell


# ----------------------------------------------------------------------------- PSL2(F_ell) as int arrays (N,4)
def normalize(M, ell):
    """M: (N,4) int64 mod ell; choose sign so that the first nonzero entry is <= (ell-1)/2."""
    M = M % ell
    first = np.where(M[:, 0] != 0, M[:, 0], np.where(M[:, 1] != 0, M[:, 1], M[:, 2]))
    flip = first > (ell - 1) // 2
    M[flip] = (-M[flip]) % ell
    return M


def keys(M, ell):
    return ((M[:, 0] * ell + M[:, 1]) * ell + M[:, 2]) * ell + M[:, 3]


def mulN(A, B, ell):
    """A (N,4) times B (4,) or (N,4)."""
    B = np.broadcast_to(B, A.shape)
    C = np.stack([A[:, 0] * B[:, 0] + A[:, 1] * B[:, 2], A[:, 0] * B[:, 1] + A[:, 1] * B[:, 3],
                  A[:, 2] * B[:, 0] + A[:, 3] * B[:, 2], A[:, 2] * B[:, 1] + A[:, 3] * B[:, 3]], axis=1)
    return normalize(C % ell, ell)


def gen_group(gens, ell):
    idm = np.array([[1, 0, 0, 1]], dtype=np.int64)
    seen = {int(keys(idm, ell)[0])}
    frontier = idm
    allm = [idm]
    while len(frontier):
        new = []
        for g in gens:
            P = mulN(frontier, g, ell)
            k = keys(P, ell)
            mask = np.array([int(x) not in seen for x in k])
            if mask.any():
                P = P[mask]
                k = k[mask]
                _, idx = np.unique(k, return_index=True)
                P = P[idx]
                for x in k[idx]:
                    seen.add(int(x))
                new.append(P)
        frontier = np.concatenate(new) if new else np.zeros((0, 4), dtype=np.int64)
        if len(frontier):
            allm.append(frontier)
    G = np.concatenate(allm)
    k = keys(G, ell)
    order = np.argsort(k)
    return G[order], k[order]


# ----------------------------------------------------------------------------- main construction
def build(ell, verbose=True, rand_reps=None):
    t0 = time.time()
    U = icosians()
    alpha = ((Fr(1), Fr(0)), (Fr(1), Fr(0)), (Fr(1), Fr(0)), Z0)    # 1 + i + j
    assert qnorm(alpha) == (Fr(3), Fr(0))
    abar = qconj(alpha)
    Us = set(U)
    # Gamma_e = {u in 2I : alpha^-1 u alpha in 2I}
    third = (Fr(1, 3), Fr(0))
    conj_in = []
    for u in U:
        t = qmul(qmul(abar, u), alpha)
        t = tuple(zmul(third, c) for c in t)
        conj_in.append(t in Us)
    Ge = [u for u, c in zip(U, conj_in) if c]
    assert len(Ge) == 12, len(Ge)
    # reductions
    M9 = [q_to_m9(u) for u in U]
    A9 = q_to_m9(alpha)
    phil, Il, Jl, Kl = fl_data(ell)
    ML = [q_to_ml(u, ell, phil, Il, Jl, Kl) for u in U]
    Al = q_to_ml(alpha, ell, phil, Il, Jl, Kl)
    Albar = q_to_ml(abar, ell, phil, Il, Jl, Kl)
    inv3 = pow(3, -1, ell)
    Alinv = Albar * inv3 % ell
    assert np.array_equal(Al @ Alinv % ell, np.eye(2, dtype=np.int64))
    # ring-hom sanity on a sample of products
    idx = {u: n for n, u in enumerate(U)}
    for a in range(0, 120, 7):
        for b in range(0, 120, 11):
            c = idx[qmul(U[a], U[b])]
            assert mat9_mul(M9[a], M9[b]) == M9[c]
            assert np.array_equal(ML[a] @ ML[b] % ell, ML[c])
    # labels at base vertices
    A = A9
    # image of rank-1 matrix A: a nonzero column; kernel: (A[0][1], -A[0][0]) or from row 2
    assert F9.a(F9.m(A[0][0], A[1][1]), F9.neg[F9.m(A[0][1], A[1][0])]) == 0
    col = (A[0][0], A[1][0]) if (A[0][0] or A[1][0]) else (A[0][1], A[1][1])
    row = (A[0][0], A[0][1]) if (A[0][0] or A[0][1]) else (A[1][0], A[1][1])
    p0 = col
    k0 = (row[1], int(F9.neg[row[0]]))
    # check A k0 = 0
    for i in range(2):
        assert F9.a(F9.m(A[i][0], k0[0]), F9.m(A[i][1], k0[1])) == 0
    # PSL2 elements
    H0 = normalize(np.array([m.reshape(4) for m in ML]), ell)
    H1m = [(Al @ m @ Alinv) % ell for m in ML]
    H1 = normalize(np.array([m.reshape(4) for m in H1m]), ell)
    He = normalize(np.array([ML[idx[u]].reshape(4) for u in Ge]), ell)
    # generators: a few elements of H0 and H1
    gens = [H0[i] for i in range(0, 120, 13)] + [H1[i] for i in range(0, 120, 13)]
    G, Gk = gen_group(gens, ell)
    N = len(G)
    psl = ell * (ell * ell - 1) // 2
    if verbose:
        print(f"ell={ell}: |G| = {N} (|PSL2| = {psl}); {time.time()-t0:.1f}s", flush=True)

    def lookup(M):
        k = keys(M, ell)
        pos = np.searchsorted(Gk, k)
        assert np.all(Gk[np.minimum(pos, N - 1)] == k)
        return pos

    def cosets(H):
        best = None
        for h in np.unique(H, axis=0):
            k = keys(mulN(G, h, ell), ell)
            best = k if best is None else np.minimum(best, k)
        ids, inv = np.unique(best, return_inverse=True)
        return inv, len(ids)

    e_of, nE = cosets(He)
    v0_of, nV0 = cosets(H0)
    v1_of, nV1 = cosets(H1)
    if verbose:
        print(f"  |E| = {nE}, |V0| = {nV0}, |V1| = {nV1}; {time.time()-t0:.1f}s", flush=True)
    assert nE == 10 * nV0 == 10 * nV1
    # endpoints of each edge
    e_even = np.full(nE, -1)
    e_odd = np.full(nE, -1)
    e_even[e_of] = v0_of
    e_odd[e_of] = v1_of
    # representatives of vertices
    rep0 = np.full(nV0, -1)
    rep0[v0_of[::-1]] = np.arange(N)[::-1]
    rep1 = np.full(nV1, -1)
    rep1[v1_of[::-1]] = np.arange(N)[::-1]
    if rand_reps is not None:   # frame-independence test: random coset representatives
        rr = np.random.default_rng(rand_reps)
        perm = rr.permutation(N)
        rep0 = np.full(nV0, -1)
        rep0[v0_of[perm]] = perm
        rep1 = np.full(nV1, -1)
        rep1[v1_of[perm]] = perm
    # even side: for each even vertex and each u in 2I: edge and label vector M9[u] p0
    lab0 = np.array([[F9.a(F9.m(m[0][0], p0[0]), F9.m(m[0][1], p0[1])),
                      F9.a(F9.m(m[1][0], p0[0]), F9.m(m[1][1], p0[1]))] for m in M9])
    lab1 = np.array([[F9.a(F9.m(m[0][0], k0[0]), F9.m(m[0][1], k0[1])),
                      F9.a(F9.m(m[1][0], k0[0]), F9.m(m[1][1], k0[1]))] for m in M9])
    # choose 10 coset representatives of 2I / Gamma_e (left cosets u Gamma_e) by edge at the base vertex
    E0 = np.zeros((nV0, 120), dtype=np.int64)
    for j in range(120):
        P = mulN(G[rep0], H0[j], ell)
        E0[:, j] = e_of[lookup(P)]
    E1 = np.zeros((nV1, 120), dtype=np.int64)
    for j in range(120):
        P = mulN(G[rep1], H1[j], ell)
        E1[:, j] = e_of[lookup(P)]
    # pick, per base position, one u per distinct edge (same partition for all vertices)
    def reps_for(Erow):
        seen, out = {}, []
        for j, e in enumerate(Erow):
            if e not in seen:
                seen[e] = j
                out.append(j)
        return out
    R0 = reps_for(E0[0])
    R1 = reps_for(E1[0])
    assert len(R0) == 10 and len(R1) == 10
    # check the partition of 2I into 10 classes is the same for every vertex
    part0 = [tuple(sorted(np.nonzero(E0[0] == E0[0, j])[0])) for j in R0]
    for v in range(0, nV0, max(1, nV0 // 50)):
        assert [tuple(sorted(np.nonzero(E0[v] == E0[v, j])[0])) for j in R0] == part0
    # psi trivial: labels within a class agree up to c with c^4 = 1
    for cls in part0:
        x = lab0[cls[0]]
        for j in cls:
            y = lab0[j]
            # find c with y = c x
            c = next(c for c in range(1, 9) if F9.m(c, x[0]) == y[0] and F9.m(c, x[1]) == y[1])
            assert F9.pw(c, 4) == 1
    part1 = [tuple(sorted(np.nonzero(E1[0] == E1[0, j])[0])) for j in R1]
    for cls in part1:
        x = lab1[cls[0]]
        for j in cls:
            y = lab1[j]
            c = next(c for c in range(1, 9) if F9.m(c, x[0]) == y[0] and F9.m(c, x[1]) == y[1])
            assert F9.pw(c, 4) == 1
    # sanity: edges at a vertex are distinct, and each edge's endpoints are consistent
    assert all(len(set(E0[v, R0])) == 10 for v in range(nV0))
    assert all(len(set(E1[v, R1])) == 10 for v in range(nV1))
    for v in range(nV0):
        assert np.all(e_even[E0[v, R0]] == v)
    for v in range(nV1):
        assert np.all(e_odd[E1[v, R1]] == v)
    # labels distinct points of P^1 at each base vertex
    def proj(x):
        x = list(x)
        if x[0]:
            c = int(F9.inv[x[0]])
            return (1, F9.m(c, x[1]))
        return (0, 1)
    assert len({proj(lab0[j]) for j in R0}) == 10
    assert len({proj(lab1[j]) for j in R1}) == 10
    if verbose:
        print(f"  structure checks passed; {time.time()-t0:.1f}s", flush=True)
    return dict(ell=ell, nE=nE, nV=nV0, E0=E0[:, R0], E1=E1[:, R1], lab0=lab0[R0], lab1=lab1[R1],
                U=U, R0=R0, R1=R1, rep0=G[rep0], rep1=G[rep1], alpha_l=Al,
                e_even=e_even, e_odd=e_odd, p0=p0, k0=k0)


def monos(x, d=4):
    """values of x0^(d-a) x1^a, a = 0..d at the vector x."""
    return [F9.m(F9.pw(int(x[0]), d - a), F9.pw(int(x[1]), a)) for a in range(d + 1)]


def frob(x):
    return [int(F9.frob_tab[int(c)]) for c in x]


def girth_and_simple(S):
    nV, nE = S["nV"], S["nE"]
    # adjacency: vertices 0..nV-1 even, nV..2nV-1 odd
    adj = [[] for _ in range(2 * nV)]
    for e in range(nE):
        a, b = int(S["e_even"][e]), nV + int(S["e_odd"][e])
        adj[a].append(b)
        adj[b].append(a)
    multi = sum(len(a) - len(set(a)) for a in adj) // 2
    g = 10 ** 9
    for s in [0, nV]:  # vertex-transitive on each side
        dist = {s: 0}
        par = {s: -1}
        q = [s]
        for x in q:
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    par[y] = x
                    q.append(y)
                elif par[x] != y:
                    g = min(g, dist[x] + dist[y] + 1)
    if multi:
        g = 2
    return g, multi, adj


def tanner_dim(S, conv, seed=0):
    nV = S["nV"]
    rng = np.random.default_rng(seed)
    lab0 = S["lab0"]
    lab1 = S["lab1"]
    if conv == "tw":
        lab1 = np.array([frob(x) for x in lab1])
    m0 = np.array([monos(x) for x in lab0])   # 10 x 5 (even positions)
    m1 = np.array([monos(x) for x in lab1])   # 10 x 5 (odd positions)
    # check self-duality of the local code with unit weights
    for m in (m0, m1):
        Gm = m.T  # 5 x 10
        assert np.all(F9.matmul(Gm, Gm.T) == 0)
    # position of each edge at its even vertex
    nE = S["nE"]
    pos0 = np.zeros(nE, dtype=np.int64)
    for v in range(nV):
        pos0[S["E0"][v]] = np.arange(10)
    M = np.zeros((5 * nV, 5 * nV), dtype=np.int64)
    gauge = rng.integers(1, 9, size=nE) if conv == "rand" else np.ones(nE, dtype=np.int64)
    for v1 in range(nV):
        for j in range(10):
            e = S["E1"][v1, j]
            v0 = S["e_even"][e]
            a = m1[j]                       # odd parity row values at this position (5,)
            b = m0[pos0[e]]                 # even form monomials at the edge (5,)
            g = int(gauge[e])
            for r in range(5):
                ar = F9.m(int(a[r]), g)
                if ar == 0:
                    continue
                row = 5 * v1 + r
                cols = slice(5 * v0, 5 * v0 + 5)
                M[row, cols] = F9.add[M[row, cols], F9.mul[ar, b]]
    rk = F9.rank(M)
    return 5 * nV - rk


if __name__ == "__main__":
    ell = int(sys.argv[1])
    convs = sys.argv[2:] or ["untw", "tw", "rand"]
    t0 = time.time()
    S = build(ell)
    g, multi, adj = girth_and_simple(S)
    print(f"  girth = {g}, multi-edges = {multi}", flush=True)
    nE = S["nE"]
    for c in convs:
        t1 = time.time()
        d = tanner_dim(S, c)
        print(f"RESULT ell={ell} |V|={2*S['nV']} |E|={nE} girth={g} conv={c} dim={d} rate={d/nE:.4f} "
              f"pred(chi, compact)={nE//10} ({time.time()-t1:.1f}s)", flush=True)
