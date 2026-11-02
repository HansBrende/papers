"""lambda_level1.py -- exact check of the kernel-density hypothesis at the first nested level of the λ₀-adic chain.

Theorem H of the paper asserts positive kernel density of the operator A (the ℓ = 11 Goren–Oort Tanner operator, 'tw'
gluing) along the λ₀-adic congruence chain Γ⁺(λ₀^{k+1}).  The paper proves it from Riemann–Roch on the
Hilbert modular surface:  dim_{F9} ker = h⁰(Y_k, L|Y_k) ≥ V_k − 1, and predicts exactly V_k + c_k − 2
(V_k = vertices of one type, c_k = cusps of Γ(λ₀^{k+1})).  At k = 0 this is 11 + 12 − 2 = 21.
This script checks k = 1 (index 11³ = 1331): V₁ = 14641, c₁ = 132, prediction 14771 over F9.

Method.  X₁ = Γ⁺(λ₀²)\\T → X₀ = Γ⁺(λ₀)\\T is a regular cover with group K = ker(PSL2(Z/121) → PSL2(F11)) ≅ F11³
(abelian).  The cover is the derived graph of a voltage assignment k_e ∈ K on the edges of X₀, computed from
lifts of the coset representatives to PSL2(Z/121) (quaternion reductions of the icosians mod 121).  Over
F = F_{3^10} (which contains F9 and the 11th roots of unity) the level-1 operator splits into the 1331 twisted
operators A_ψ = Σ_e coef_e ψ(k_e) (55 × 55), so dim ker(level 1) = Σ_ψ dim ker A_ψ.
Consistency checks: ψ = 1 gives the base value 21; dims are constant on Frobenius orbits (ψ ↦ ψ⁹) and on
PSL2(F11)-conjugation orbits; the voltages generate K (connected cover).

Needs numpy. Run from the paper directory:  python3 tools/lambda_level1.py [untw] [random SEED]
     (untw: the untwisted gluing; random SEED: a control, a random
     F11^3-cover of the same base graph instead of the congruence cover; the prediction does not apply)
"""
import sys, time
from collections import Counter
import numpy as np

import icosian_graph as gt  # icosians, quaternion arithmetic, F9, labels

F9 = gt.F9
ELL = 11
MOD = ELL * ELL
t0 = time.time()


# ------------------------------------------------------------------ splitting of the icosian algebra mod 121
def lift_root(ell, mod):
    r = next(x for x in range(ell) if (x * x - x - 1) % ell == 0)     # same prime λ₀ as gt.fl_data
    x, m = r, ell
    while m < mod:
        m *= ell
        x = (x - (x * x - x - 1) * pow(2 * x - 1, -1, m)) % m
    return x


phil = lift_root(ELL, MOD)
assert (phil * phil - phil - 1) % MOD == 0
a0, b0 = next((a, b) for a in range(ELL) for b in range(ELL) if (a * a + b * b + 1) % ELL == 0)
a1, b1 = next((a, b) for a in range(a0, MOD, ELL) for b in range(b0, MOD, ELL) if (a * a + b * b + 1) % MOD == 0)
Il = np.array([[a1, b1], [b1, -a1 % MOD]], dtype=np.int64)
Jl = np.array([[0, 1], [MOD - 1, 0]], dtype=np.int64)
Kl = Il @ Jl % MOD
assert np.array_equal(Il @ Il % MOD, (MOD - 1) * np.eye(2, dtype=np.int64))
assert np.array_equal((Il @ Jl + Jl @ Il) % MOD, np.zeros((2, 2), dtype=np.int64))

U = gt.icosians()
idx = {u: n for n, u in enumerate(U)}
alpha = ((gt.Fr(1), gt.Fr(0)), (gt.Fr(1), gt.Fr(0)), (gt.Fr(1), gt.Fr(0)), gt.Z0)
abar = gt.qconj(alpha)
third = (gt.Fr(1, 3), gt.Fr(0))
Ge = [u for u in U if tuple(gt.zmul(third, c) for c in gt.qmul(gt.qmul(abar, u), alpha)) in set(U)]
assert len(Ge) == 12
ML = [gt.q_to_ml(u, MOD, phil, Il, Jl, Kl) for u in U]           # 2I in SL2(Z/121)
Al = gt.q_to_ml(alpha, MOD, phil, Il, Jl, Kl)
Alinv = gt.q_to_ml(abar, MOD, phil, Il, Jl, Kl) * pow(3, -1, MOD) % MOD
assert np.array_equal(Al @ Alinv % MOD, np.eye(2, dtype=np.int64))
H1L = [Al @ m @ Alinv % MOD for m in ML]                          # α 2I α⁻¹
for a in range(0, 120, 7):                                        # ring-hom sanity
    for b in range(0, 120, 11):
        assert np.array_equal(ML[a] @ ML[b] % MOD, ML[idx[gt.qmul(U[a], U[b])]])


def key(M, m):
    """normalised key of ±M in PSL2(Z/m): sign chosen so that the first nonzero entry is < m/2"""
    f = [int(x) % m for x in (M[0][0], M[0][1], M[1][0], M[1][1])]
    first = next(x for x in f if x)
    if first > (m - 1) // 2:
        f = [(-x) % m for x in f]
    return tuple(f)


def red(M):
    return np.array(M, dtype=np.int64) % ELL


# ------------------------------------------------------------------ base group G0 = PSL2(F11), with lifts to Z/121
gens = [ML[i] for i in range(0, 120, 13)] + [H1L[i] for i in range(0, 120, 13)]
G0 = {key(np.eye(2, dtype=np.int64), ELL): np.eye(2, dtype=np.int64)}   # key mod 11 -> lift mod 121
order = list(G0)
frontier = list(G0)
while frontier:
    new = []
    for k in frontier:
        g = G0[k]
        for s in gens:
            h = g @ s % MOD
            kh = key(h, ELL)
            if kh not in G0:
                G0[kh] = h
                order.append(kh)
                new.append(kh)
    frontier = new
assert len(G0) == ELL * (ELL * ELL - 1) // 2, len(G0)                  # 660 = |PSL2(F11)|
pos_of = {k: n for n, k in enumerate(order)}
N0 = len(order)


def mulk(k1, M):
    """key of (element with key k1, using its stored lift) times matrix M, mod 11"""
    return key(G0[k1] @ M % MOD, ELL)


H0k = [key(m, ELL) for m in ML]
H1k = [key(m, ELL) for m in H1L]
Hek = sorted({key(ML[idx[u]], ELL) for u in Ge})


def coset_ids(Hlist):
    Hm = [G0[k] for k in sorted(set(Hlist))]
    best = []
    for k in order:
        best.append(min(key(G0[k] @ h % MOD, ELL) for h in Hm))
    uniq = sorted(set(best))
    num = {b: i for i, b in enumerate(uniq)}
    return [num[b] for b in best], len(uniq)


e_of, nE = coset_ids(Hek)
v0_of, nV0 = coset_ids(H0k)
v1_of, nV1 = coset_ids(H1k)
assert (nE, nV0, nV1) == (110, 11, 11)
e_even = [-1] * nE
e_odd = [-1] * nE
for n in range(N0):
    e_even[e_of[n]] = v0_of[n]
    e_odd[e_of[n]] = v1_of[n]
rep0 = [None] * nV0
rep1 = [None] * nV1
for n in range(N0):
    if rep0[v0_of[n]] is None:
        rep0[v0_of[n]] = order[n]
    if rep1[v1_of[n]] is None:
        rep1[v1_of[n]] = order[n]


def edge_of_key(k):
    return e_of[pos_of[k]]


E0 = [[edge_of_key(mulk(rep0[v], ML[j])) for j in range(120)] for v in range(nV0)]
E1 = [[edge_of_key(mulk(rep1[v], H1L[j])) for j in range(120)] for v in range(nV1)]


def reps_for(row):
    seen, out = set(), []
    for j, e in enumerate(row):
        if e not in seen:
            seen.add(e)
            out.append(j)
    return out


R0, R1 = reps_for(E0[0]), reps_for(E1[0])
assert len(R0) == 10 and len(R1) == 10
part0 = [tuple(j for j in range(120) if E0[0][j] == E0[0][r]) for r in R0]
part1 = [tuple(j for j in range(120) if E1[0][j] == E1[0][r]) for r in R1]
for v in range(nV0):
    assert [tuple(j for j in range(120) if E0[v][j] == E0[v][r]) for r in R0] == part0
for v in range(nV1):
    assert [tuple(j for j in range(120) if E1[v][j] == E1[v][r]) for r in R1] == part1

# ------------------------------------------------------------------ 'tw' labels and coefficients (as in gen_operator.py)
M9 = [gt.q_to_m9(u) for u in U]
A9 = gt.q_to_m9(alpha)
col = (A9[0][0], A9[1][0]) if (A9[0][0] or A9[1][0]) else (A9[0][1], A9[1][1])
row = (A9[0][0], A9[0][1]) if (A9[0][0] or A9[0][1]) else (A9[1][0], A9[1][1])
p0, k0 = col, (row[1], int(F9.neg[row[0]]))


def apply9(m, x):
    return [F9.a(F9.m(m[0][0], x[0]), F9.m(m[0][1], x[1])), F9.a(F9.m(m[1][0], x[0]), F9.m(m[1][1], x[1]))]


lab0 = [apply9(M9[j], p0) for j in R0]
UNTW = "untw" in sys.argv[1:]
RANDOM_SEED = int(sys.argv[sys.argv.index("random") + 1]) if "random" in sys.argv[1:] else None
lab1 = [apply9(M9[j], k0) if UNTW else gt.frob(apply9(M9[j], k0)) for j in R1]   # 'tw': Frobenius on odd side
m0 = [gt.monos(x) for x in lab0]
m1 = [gt.monos(x) for x in lab1]
pos0, pos1, jE0, jE1 = [0] * nE, [0] * nE, [0] * nE, [0] * nE
for v in range(nV0):
    for t, j in enumerate(R0):
        pos0[E0[v][j]] = t
        jE0[E0[v][j]] = j
for v in range(nV1):
    for t, j in enumerate(R1):
        pos1[E1[v][j]] = t
        jE1[E1[v][j]] = j

# ------------------------------------------------------------------ voltages k_e in K, as vectors in sl2(F11) ≅ F11³
Ge_lifts = {key(ML[idx[u]], ELL): ML[idx[u]] for u in Ge}


def inv_sl2(M):
    return np.array([[M[1][1], -M[0][1]], [-M[1][0], M[0][0]]], dtype=np.int64) % MOD


volt = []
for e in range(nE):
    g0 = G0[rep0[e_even[e]]] @ ML[jE0[e]] % MOD                       # lift of rep0 · h0
    g1 = G0[rep1[e_odd[e]]] @ H1L[jE1[e]] % MOD                      # lift of rep1 · h1
    s = key(inv_sl2(g1) @ g0 % MOD, ELL)                             # (rep1 h1)⁻¹ rep0 h0 ∈ He (mod 11)
    assert s in Ge_lifts, "edge relation not in He"
    k = g0 @ inv_sl2(g1 @ Ge_lifts[s] % MOD) % MOD                   # ∈ K
    kr = k % ELL
    if np.array_equal(kr, (ELL - 1) * np.eye(2, dtype=np.int64) % ELL):
        k = (-k) % MOD
    assert np.array_equal(k % ELL, np.eye(2, dtype=np.int64)), "voltage not in K"
    X = ((k - np.eye(2, dtype=np.int64)) % MOD) // ELL
    assert (X[0][0] + X[1][1]) % ELL == 0
    volt.append((int(X[0][0]), int(X[0][1]), int(X[1][0])))

# connectivity of the cover: holonomies of cycles span F11³ (gauge the BFS tree to 0)
adj = [[] for _ in range(22)]
for e in range(nE):
    adj[e_even[e]].append((11 + e_odd[e], e, 1))
    adj[11 + e_odd[e]].append((e_even[e], e, -1))
pot = {0: np.zeros(3, dtype=np.int64)}
queue = [0]
for x in queue:
    for y, e, sgn in adj[x]:
        if y not in pot:
            pot[y] = (pot[x] + sgn * np.array(volt[e])) % ELL
            queue.append(y)
hol = [(pot[e_even[e]] + np.array(volt[e]) - pot[11 + e_odd[e]]) % ELL for e in range(nE)]


def rank_mod(rows, p):
    M = [list(map(int, r)) for r in rows]
    rk, ncol = 0, len(M[0])
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c] % p), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        iv = pow(M[rk][c], -1, p)
        M[rk] = [x * iv % p for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] % p:
                f = M[i][c]
                M[i] = [(x - f * y) % p for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk


if RANDOM_SEED is not None:      # control: a random F11^3-cover of the same graph (not a congruence cover)
    rr = np.random.default_rng(RANDOM_SEED)
    volt = [tuple(int(x) for x in rr.integers(0, ELL, size=3)) for _ in range(nE)]
    pot = {0: np.zeros(3, dtype=np.int64)}
    queue = [0]
    for x in queue:
        for y, e, sgn in adj[x]:
            if y not in pot:
                pot[y] = (pot[x] + sgn * np.array(volt[e])) % ELL
                queue.append(y)
    hol = [(pot[e_even[e]] + np.array(volt[e]) - pot[11 + e_odd[e]]) % ELL for e in range(nE)]
assert rank_mod(hol, ELL) == 3, "cover not connected"
print(f"base graph and voltages: |G0| = {N0}, |E| = {nE}; holonomy rank 3 (connected cover); {time.time()-t0:.1f}s",
      flush=True)

# ------------------------------------------------------------------ F_{3^10} by log tables
P, N = 3, 10
Q = P ** N
Q1 = Q - 1


def polymulmod(a, b, f):
    res = [0] * (2 * N - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                res[i + j] = (res[i + j] + x * y) % P
    for d in range(len(res) - 1, N - 1, -1):
        c = res[d]
        if c:
            for i in range(N + 1):
                res[d - N + i] = (res[d - N + i] - c * f[i]) % P
    return res[:N]


def x_order_ok(f):
    """is x a generator of F_3[x]/(f)^*  (f monic of degree N)?"""
    def powx(e):
        result = [1] + [0] * (N - 1)
        base = [0, 1] + [0] * (N - 2)
        while e:
            if e & 1:
                result = polymulmod(result, base, f)
            base = polymulmod(base, base, f)
            e >>= 1
        return result
    one = [1] + [0] * (N - 1)
    if powx(Q1) != one:
        return False
    return all(powx(Q1 // q) != one for q in (2, 11, 61))          # 3^10 − 1 = 2³ · 11² · 61


fpoly = None
for code in range(P ** N):
    f = [(code // P ** i) % P for i in range(N)] + [1]
    if f[0] and x_order_ok(f):
        fpoly = f
        break
assert fpoly is not None
EXP = np.zeros(2 * Q1, dtype=np.int64)
LOG = np.zeros(Q, dtype=np.int64)
cur = [1] + [0] * (N - 1)
POW3 = np.array([P ** i for i in range(N)], dtype=np.int64)
for e in range(Q1):
    c = int(np.dot(cur, POW3))
    EXP[e] = c
    LOG[c] = e
    cur = polymulmod(cur, [0, 1] + [0] * (N - 2), fpoly)
EXP[Q1:] = EXP[:Q1]
assert len(set(EXP[:Q1].tolist())) == Q1
DIG = np.array([[(c // P ** i) % P for i in range(N)] for c in range(Q)], dtype=np.int64)


def fadd(a, b):
    return (DIG[a] + DIG[b]) % P @ POW3


def fsub(a, b):
    return (DIG[a] - DIG[b]) % P @ POW3


def fmul(a, b):
    a, b = np.asarray(a), np.asarray(b)
    out = EXP[(LOG[a] + LOG[b]) % Q1]
    return np.where((a == 0) | (b == 0), 0, out)


def finv(a):
    return int(EXP[(-LOG[a]) % Q1])


def frank(M):
    M = np.array(M, dtype=np.int64)
    n, m = M.shape
    r = 0
    for c in range(m):
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0:
            continue
        p = r + nz[0]
        if p != r:
            M[[r, p]] = M[[p, r]]
        M[r] = fmul(M[r], finv(int(M[r, c])))
        rows = np.nonzero(M[:, c])[0]
        rows = rows[rows != r]
        if len(rows):
            M[rows] = fsub(M[rows], fmul(M[rows, c][:, None], M[r][None, :]))
        r += 1
        if r == n:
            break
    return r


# F9 = F3[t]/(t² + 1) inside F_{3^10}: t ↦ s with s² = −1
s_im = int(EXP[Q1 // 4])
assert int(fmul(s_im, s_im)) == int(np.dot([2] + [0] * (N - 1), POW3))


def f9_to_big(c):
    a, b = int(c) % 3, int(c) // 3
    return int(fadd(a, fmul(b, s_im))) if b else a


zeta = int(EXP[Q1 // ELL])                                           # primitive 11th root of unity
ZPOW = [int(EXP[(Q1 // ELL) * i % Q1]) for i in range(ELL)]

# coefficient of edge e in A[(v0, c), (v1, r)]
COEF = []
for e in range(nE):
    C = np.zeros((5, 5), dtype=np.int64)
    for c in range(5):
        for r in range(5):
            C[c, r] = f9_to_big(F9.m(int(m1[pos1[e]][r]), int(m0[pos0[e]][c])))
    COEF.append(C)


def twisted(psi):
    """A_ψ: 55 × 55 over F_{3^10}, rows (even vertex, c), cols (odd vertex, r); ψ(X) = ζ^{ψ·X}"""
    A = np.zeros((55, 55), dtype=np.int64)
    for e in range(nE):
        ph = ZPOW[(psi[0] * volt[e][0] + psi[1] * volt[e][1] + psi[2] * volt[e][2]) % ELL]
        v0, v1 = e_even[e], e_odd[e]
        blk = A[5 * v0:5 * v0 + 5, 5 * v1:5 * v1 + 5]
        A[5 * v0:5 * v0 + 5, 5 * v1:5 * v1 + 5] = fadd(blk, fmul(COEF[e], ph))
    return A


base = 55 - frank(twisted((0, 0, 0)))
print(f"gluing {'untw' if UNTW else 'tw'}; trivial character (base level): dim ker = {base}  "
      f"(expected {20 if UNTW else 21}); {time.time()-t0:.1f}s", flush=True)
assert base == (20 if UNTW else 21)

dims = {}
for a in range(ELL):
    for b in range(ELL):
        for c in range(ELL):
            psi = (a, b, c)
            dims[psi] = 55 - frank(twisted(psi))
total = sum(dims.values())
print(f"all 1331 characters done; {time.time()-t0:.1f}s", flush=True)


# Frobenius orbits ψ ↦ 9ψ and conjugation orbits.  ψ = (a, b, c) pairs with X = [[x, y], [z, −x]] by
# a x + b y + c z = tr(X Y) for Y = [[a/2, c], [b, −a/2]]; PSL2(F11) acts on Y by conjugation.
def frob_ok():
    return all(dims[p] == dims[tuple(9 * x % ELL for x in p)] for p in dims)


inv2 = pow(2, -1, ELL)


def Y_of(psi):
    a, b, c = psi
    return np.array([[a * inv2 % ELL, c], [b, (-a * inv2) % ELL]], dtype=np.int64)


def psi_of(Y):
    return (int(2 * Y[0][0] % ELL), int(Y[1][0] % ELL), int(Y[0][1] % ELL))


def conj_ok():
    g_list = [G0[k] % ELL for k in order]
    for psi in list(dims)[::37]:
        Y = Y_of(psi)
        for g in g_list[::7]:
            ginv = np.array([[g[1][1], -g[0][1]], [-g[1][0], g[0][0]]], dtype=np.int64) % ELL
            if dims[psi_of(g @ Y @ ginv % ELL)] != dims[psi]:
                return False
    return True


det_class = Counter()
for psi, d in dims.items():
    Y = Y_of(psi)
    det = int((Y[0][0] * Y[1][1] - Y[0][1] * Y[1][0]) % ELL)
    det_class[(det, d)] += 1

V1, c1 = 11 * 1331, 132
print(f"Frobenius-orbit invariance: {frob_ok()};  conjugation invariance (sampled): "
      f"{conj_ok() if RANDOM_SEED is None else 'n/a (random cover)'}")
print("dim ker A_ψ by det(Y) class:", sorted(det_class.items()))
print(f"LEVEL 1 (index 1331): dim_F9 ker = {total};  prediction V1 + c1 - 2 = {V1 + c1 - 2};  "
      f"lower bound V1 - 1 = {V1 - 1};  density over F9 = {total / 1331:.4f}, over F3 = {2 * total / 1331:.4f}")
