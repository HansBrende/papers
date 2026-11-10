"""Check the corollary on address digits and the remark on composition on small instances.

Usage (standard library only; a few seconds):

    python3 tools/digit_and_composition_checks.py

Both statements are proved in the paper; this script only tests them on small instances over GF(2) and GF(3).

Notation: the side length is d; tau is the swap on d x d matrices, X -> X^T; a term A (x) B acts by X -> A X B^T, and
the vec index of the entry (i, j) is i*d + j; [K, T] = K T - T K.

 1. Corollary (every address digit must be broken).  Index set Z_m x Z_q, d = m q, index (u, v) -> u*q + v.
    For K = sum_a A_a (x) (B'_a (x) C_a) with random A_a, random m x m B'_a and random q x q circulants C_a:
    dim ker(tau - K) <= (d^2 + d^2/q)/2.  For the partial transpose that exchanges the first digits of the two
    indices: [K, T] = 0 for T = 1 (x) (1_m (x) rotation), dim ker[tau, T] = d^2/q, and dim ker(tau - K) equals the
    bound.
 2. Remark (composition).  For M interval classes of Z_d, T = 1 (x) sigma and a hop K whose second factors are
    P_J sigma^e (P_J the diagonal mask of a class, random first factors): rank[K, T] <= M d, and for two hops
    rank[K_2 K_1, T] <= 2 M d.
 3. The same remark, the unshuffle.  d = q^k, digits a = (a_0, ..., a_{k-1}); G_j adds one to digit j; the perfect
    unshuffle U moves digit j to position j + 1 (cyclically).  Then U G_j = G_{j+1} U, rank[U, G_j] = d - d/q, and
    rank[1 (x) U, 1 (x) G_j] = d^2 - d^2/q, for every j.

All random choices come from one fixed seed.  The script prints one line per case and ends with ALL CHECKS PASSED,
or raises an AssertionError.
"""
import random
import sys


def rank_mod(M, p):
    M = [r[:] for r in M]
    rk = 0
    rows = len(M)
    cols = len(M[0]) if M else 0
    for c in range(cols):
        piv = next((i for i in range(rk, rows) if M[i][c] % p), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], p - 2, p)
        M[rk] = [(x * inv) % p for x in M[rk]]
        for i in range(rows):
            if i != rk and M[i][c] % p:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[rk])]
        rk += 1
        if rk == rows:
            break
    return rk


def mul(A, B, p):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(r, c)) % p for c in Bt] for r in A]


def add(A, B, p, s=1):
    return [[(a + s * b) % p for a, b in zip(r1, r2)] for r1, r2 in zip(A, B)]


def eye(N):
    return [[int(i == j) for j in range(N)] for i in range(N)]


def rand(N, M, p, rng):
    return [[rng.randrange(p) for _ in range(M)] for _ in range(N)]


def kron(A, B, p):
    """Kronecker product; on vec(X), row-major, kron(A, B) is X -> A X B^T."""
    return [[(a * b) % p for a in ra for b in rb] for ra in A for rb in B]


def swap(d):
    S = [[0] * (d * d) for _ in range(d * d)]
    for i in range(d):
        for j in range(d):
            S[i * d + j][j * d + i] = 1
    return S


def commutator(K, T, p):
    return add(mul(K, T, p), mul(T, K, p), p, -1)


def rotation(q):
    return [[int((i + 1) % q == j) for j in range(q)] for i in range(q)]


def check_digit(rng):
    for p in (2, 3):
        for m, q in ((2, 2), (2, 3), (3, 2)):
            d = m * q
            N = d * d
            tau = swap(d)
            Gq = rotation(q)
            bound = (N + N // q) // 2
            worst = 0
            for _ in range(10):
                K = [[0] * N for _ in range(N)]
                for _ in range(rng.randrange(1, 4)):
                    C = [[0] * q for _ in range(q)]
                    P = eye(q)
                    for _ in range(q):
                        C = add(C, P, p, rng.randrange(p))
                        P = mul(P, Gq, p)
                    K = add(K, kron(rand(d, d, p, rng), kron(rand(m, m, p, rng), C, p), p), p)
                D = N - rank_mod(add(tau, K, p, -1), p)
                assert D <= bound, (p, m, q, D, bound)
                worst = max(worst, D)
            # the partial transpose: (K X)[(u,v)][(u',v')] = X[(u',v)][(u,v')]
            K = [[0] * N for _ in range(N)]
            for u in range(m):
                for v in range(q):
                    for u2 in range(m):
                        for v2 in range(q):
                            K[(u * q + v) * d + (u2 * q + v2)][(u2 * q + v) * d + (u * q + v2)] = 1
            T = kron(eye(d), kron(eye(m), Gq, p), p)
            D = N - rank_mod(add(tau, K, p, -1), p)
            kt = N - rank_mod(commutator(tau, T, p), p)
            rc = rank_mod(commutator(K, T, p), p)
            assert rc == 0 and kt == N // q and D == bound, (p, m, q, D, kt, rc, bound)
            print(f"digit: GF({p}), index Z_{m} x Z_{q}: random digit-uniform K: largest dim {worst} <= {bound}; "
                  f"partial transpose: dim = {D} = (d^2 + d^2/q)/2, [K,T] = 0, dim ker[tau,T] = {kt} = d^2/q")


def check_composition(rng):
    for p in (2, 3):
        for d, cuts in ((6, [0, 2, 6]), (6, [0, 1, 3, 6]), (8, [0, 2, 5, 8])):
            classes = [list(range(cuts[k], cuts[k + 1])) for k in range(len(cuts) - 1)]
            M = len(classes)
            sig = rotation(d)
            T = kron(eye(d), sig, p)

            def hop():
                K = [[0] * (d * d) for _ in range(d * d)]
                for _ in range(12):
                    J = rng.choice(classes)
                    P = [[int(i == j and i in J) for j in range(d)] for i in range(d)]
                    S = eye(d)
                    for _ in range(rng.randrange(d)):
                        S = mul(S, sig, p)
                    K = add(K, kron(rand(d, d, p, rng), mul(P, S, p), p), p)
                return K
            w1 = w2 = 0
            for _ in range(4):
                K1, K2 = hop(), hop()
                w1 = max(w1, rank_mod(commutator(K1, T, p), p))
                w2 = max(w2, rank_mod(commutator(mul(K2, K1, p), T, p), p))
            assert w1 <= M * d and w2 <= 2 * M * d, (p, d, M, w1, w2)
            print(f"composition: GF({p}), d = {d}, M = {M}: largest rank[K_1,T] = {w1} <= Md = {M*d}; "
                  f"largest rank[K_2 K_1,T] = {w2} <= 2Md = {2*M*d}")


def check_unshuffle():
    for p in (2, 3, 5):
        for q, k in ((2, 2), (2, 3), (3, 2)):
            d = q ** k

            def digits(a):
                return [(a // q ** j) % q for j in range(k)]

            def index(ds):
                return sum(x * q ** j for j, x in enumerate(ds))

            def perm_matrix(f):
                """The matrix that sends the basis vector e_a to e_f(a)."""
                P = [[0] * d for _ in range(d)]
                for a in range(d):
                    P[f(a)][a] = 1
                return P

            def bump(j):
                def f(a):
                    ds = digits(a)
                    ds[j] = (ds[j] + 1) % q
                    return index(ds)
                return f

            def shift(a):
                ds = digits(a)
                return index([ds[(j - 1) % k] for j in range(k)])     # digit j moves to position j + 1

            U = perm_matrix(shift)
            G = [perm_matrix(bump(j)) for j in range(k)]
            for j in range(k):
                assert mul(U, G[j], p) == mul(G[(j + 1) % k], U, p), "U G_j = G_{j+1} U fails"
                r = rank_mod(commutator(U, G[j], p), p)
                r2 = rank_mod(commutator(kron(eye(d), U, p), kron(eye(d), G[j], p), p), p)
                assert r == d - d // q and r2 == d * d - d * d // q, (p, q, k, j, r, r2)
            print(f"unshuffle: GF({p}), d = {q}^{k}: U G_j = G_(j+1) U; rank[U,G_j] = {d - d//q} = d - d/q and "
                  f"rank[1 (x) U, 1 (x) G_j] = {d*d - d*d//q} = d^2 - d^2/q for every digit j")


def main():
    rng = random.Random(20261110)
    check_digit(rng)
    check_composition(rng)
    check_unshuffle()
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
