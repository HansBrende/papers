"""Check the examples of the remark "Two is sharp": few Kronecker terms whose swap code exceeds the pairing value.

Usage (standard library only; a few seconds):

    python3 tools/three_term_example.py

Notation: the side length is d; tau is the swap on d x d matrices, X -> X^T; a term A (x) B acts by X -> A X B^T;
E_ij is the matrix unit; vec index of the entry (i, j) is i*d + j.  Over the prime fields GF(2), GF(3), GF(5), GF(7)
the script checks:

 1. For d = 2, ..., 5: Pi = sum_{i,j} E_ij (x) E_ij is X -> trace(X) * 1 and has rank one;
    tau - Pi = sum_{i<j} (E_ij - E_ji) (x) (E_ji - E_ij), a sum of h = d(d-1)/2 terms;
    so K = tau - Pi has h terms and its swap code ker(tau - K) = ker(Pi) has dimension d^2 - 1.
    At d = 3 that is three terms and dimension 8 > 6.
 2. At d = 4, with indices 0, ..., 3: the three terms
        (E_01 - E_10) (x) (E_10 - E_01),   (E_02 - E_20) (x) (E_20 - E_02),
        (E_12 - E_21 + E_33) (x) (E_21 - E_12 + E_33)
    (the d = 3 example with E_33 added to both factors of the third term) have a swap code of dimension 11 > 10.

It prints one line per case and ends with ALL CHECKS PASSED, or raises an AssertionError.
"""
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


def unit(d, i, j):
    M = [[0] * d for _ in range(d)]
    M[i][j] = 1
    return M


def comb(d, p, terms):
    M = [[0] * d for _ in range(d)]
    for c, X in terms:
        M = [[(a + c * b) % p for a, b in zip(r1, r2)] for r1, r2 in zip(M, X)]
    return M


def kron(A, B, p):
    """Matrix of X -> A X B^T on vec(X), row-major."""
    d = len(A)
    return [[(A[i][k] * B[j][l]) % p for k in range(d) for l in range(d)] for i in range(d) for j in range(d)]


def swap(d):
    S = [[0] * (d * d) for _ in range(d * d)]
    for i in range(d):
        for j in range(d):
            S[i * d + j][j * d + i] = 1
    return S


def add(A, B, p, s=1):
    return [[(a + s * b) % p for a, b in zip(r1, r2)] for r1, r2 in zip(A, B)]


def main():
    for p in (2, 3, 5, 7):
        for d in (2, 3, 4, 5):
            N = d * d
            Pi = [[0] * N for _ in range(N)]
            for i in range(d):
                for j in range(d):
                    Pi = add(Pi, kron(unit(d, i, j), unit(d, i, j), p), p)
            # Pi is X -> trace(X) * identity
            for i in range(d):
                for j in range(d):
                    for k in range(d):
                        for l in range(d):
                            assert Pi[i * d + j][k * d + l] == (1 if (i == j and k == l) else 0)
            assert rank_mod(Pi, p) == 1
            K = [[0] * N for _ in range(N)]
            terms = 0
            for i in range(d):
                for j in range(i + 1, d):
                    A = comb(d, p, [(1, unit(d, i, j)), (-1, unit(d, j, i))])
                    B = comb(d, p, [(1, unit(d, j, i)), (-1, unit(d, i, j))])
                    K = add(K, kron(A, B, p), p)
                    terms += 1
            assert K == add(swap(d), Pi, p, -1), "tau - Pi is not the stated sum"
            dim = N - rank_mod(add(swap(d), K, p, -1), p)
            assert terms == d * (d - 1) // 2 and dim == N - 1
            print(f"GF({p}), d = {d}: tau - Pi has {terms} terms; swap code of dimension {dim} = d^2 - 1 "
                  f"(pairing value {d*(d+1)//2})")
        d = 4
        t1 = kron(comb(d, p, [(1, unit(d, 0, 1)), (-1, unit(d, 1, 0))]), comb(d, p, [(1, unit(d, 1, 0)), (-1, unit(d, 0, 1))]), p)
        t2 = kron(comb(d, p, [(1, unit(d, 0, 2)), (-1, unit(d, 2, 0))]), comb(d, p, [(1, unit(d, 2, 0)), (-1, unit(d, 0, 2))]), p)
        t3 = kron(comb(d, p, [(1, unit(d, 1, 2)), (-1, unit(d, 2, 1)), (1, unit(d, 3, 3))]),
                  comb(d, p, [(1, unit(d, 2, 1)), (-1, unit(d, 1, 2)), (1, unit(d, 3, 3))]), p)
        K = add(add(t1, t2, p), t3, p)
        dim = d * d - rank_mod(add(swap(d), K, p, -1), p)
        assert dim == 11
        print(f"GF({p}), d = 4: the three padded terms have a swap code of dimension {dim} > 10")
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
