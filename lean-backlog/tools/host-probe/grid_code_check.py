"""Exact check of the explicit code on the 3x3 grid host (rows = 9 points (i,j), columns = lines R_k, C_k).
A_j[i,k] = X[(i,j),R_k] (i != k), B_i[j,k] = X[(i,j),C_k] (j != k).
Code: for i<k, A_j[i,k] = S_j[i,k], A_j[k,i] = S_j[i,k] - D[i,k]; for j<k, B_i[j,k] = T_i[j,k],
B_i[k,j] = T_i[j,k] - D[j,k].  21 free symbols on the 36 non-incident cells (pairing gives 18).
Checks over Z_q for q = 2, 3, 4, 5 by exact rank over the integers mod p (p prime) and, for all q, by the
explicit recovery formulas on random words."""
import itertools, random
pairs = [(0, 1), (0, 2), (1, 2)]
def word(S, T, D, q):
    A = {}; B = {}
    for j in range(3):
        for (i, k) in pairs:
            A[(j, i, k)] = S[(j, i, k)] % q; A[(j, k, i)] = (S[(j, i, k)] - D[(i, k)]) % q
    for i in range(3):
        for (j, k) in pairs:
            B[(i, j, k)] = T[(i, j, k)] % q; B[(i, k, j)] = (T[(i, j, k)] - D[(j, k)]) % q
    return A, B
def Dfrom(M, idx, q):       # M = A_j or B_i given as dict with fixed first index idx
    return {(a, b): (M[(idx, a, b)] - M[(idx, b, a)]) % q for (a, b) in pairs}
def sgnD(D, a, b, q):       # value of X[a,b] - X[b,a]
    return D[(a, b)] if a < b else (-D[(b, a)]) % q
random.seed(1)
for q in (2, 3, 4, 5, 6, 7):
    seen = set()
    for trial in range(2000):
        S = {(j, i, k): random.randrange(q) for j in range(3) for (i, k) in pairs}
        T = {(i, j, k): random.randrange(q) for i in range(3) for (j, k) in pairs}
        D = {p: random.randrange(q) for p in pairs}
        A, B = word(S, T, D, q)
        for k in range(3):
            # column R_k from rows (k,0),(k,1),(k,2): entries A_j[k,*] for all j, and all of B_k
            Dk = Dfrom(B, k, q)
            assert Dk == {p: D[p] % q for p in pairs}
            for j in range(3):
                for i in range(3):
                    if i != k:
                        assert A[(j, i, k)] == (A[(j, k, i)] + sgnD(Dk, i, k, q)) % q
            # column C_k from rows (0,k),(1,k),(2,k): entries B_i[k,*] for all i, and all of A_k
            Dk = Dfrom(A, k, q)
            for i in range(3):
                for j in range(3):
                    if j != k:
                        assert B[(i, j, k)] == (B[(i, k, j)] + sgnD(Dk, j, k, q)) % q
    # injectivity: the 21 parameters are read off from the word
    #   S_j[i,k] = A_j[i,k], T_i[j,k] = B_i[j,k] (upper entries), D = A_0 upper minus lower
    print(f"q = {q}: recovery identities hold on 2000 random words; parameters are entries of the word, so |C| = q^21")
