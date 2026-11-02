"""gf.py -- finite fields GF(p^n), Q = p^n <= 1024, with table arithmetic (pure numpy).

Elements are the integers 0..Q-1, read as base-p digit vectors of polynomial coefficients modulo a fixed monic
irreducible polynomial `poly` (low -> high). For Q = 9 the polynomial is t^2 + 1, so a + b t is encoded as
a + 3 b and t is a square root of -1.

Used by icosian_graph.py; self-test: python3 tools/gf.py
"""
import numpy as np


def _polymod(a, b, p):
    a = a[:]
    while len(a) >= len(b):
        if a[-1] == 0:
            a.pop()
            continue
        coef = a[-1] * pow(b[-1], p - 2, p) % p
        sh = len(a) - len(b)
        for i in range(len(b)):
            a[sh + i] = (a[sh + i] - coef * b[i]) % p
        a.pop()
    while a and a[-1] == 0:
        a.pop()
    return a


def _irreducible(c, p, n):
    for d in range(1, n // 2 + 1):
        for code in range(p ** d):
            f = [(code // p ** i) % p for i in range(d)] + [1]
            if not _polymod(c, f, p):
                return False
    return True


class GF:
    def __init__(self, p, n, poly=None):
        self.p, self.n, self.Q = p, n, p ** n
        Q = self.Q
        assert Q <= 1024
        if poly is None:
            if n == 1:
                poly = [0, 1]
            elif p == 3 and n == 2:
                poly = [1, 0, 1]  # t^2 + 1
            else:
                for code in range(p ** n):
                    c = [(code // p ** i) % p for i in range(n)] + [1]
                    if _irreducible(c, p, n):
                        poly = c
                        break
        self.poly = poly
        dig = np.array([[(a // p ** i) % p for i in range(n)] for a in range(Q)], dtype=np.int64)
        pw = p ** np.arange(n)
        self.dig = dig
        A = (dig[:, None, :] + dig[None, :, :]) % p
        self.add = (A * pw).sum(-1).astype(np.uint16)
        # multiplication: polynomial product then reduction
        prod = np.zeros((Q, Q, 2 * n - 1), dtype=np.int64)
        for i in range(n):
            for j in range(n):
                prod[:, :, i + j] += dig[:, None, i] * dig[None, :, j]
        for k in range(2 * n - 2, n - 1, -1):
            c = prod[:, :, k] % p
            for i in range(n + 1):
                prod[:, :, k - n + i] -= c * poly[i]
        prod = prod[:, :, :n] % p
        self.mul = (prod * pw).sum(-1).astype(np.uint16)
        self.neg = (((-dig) % p) * pw).sum(-1).astype(np.uint16)
        self.sub = self.add[np.arange(Q)[:, None], self.neg[None, :]]
        inv = np.zeros(Q, dtype=np.uint16)
        for a in range(1, Q):
            inv[a] = int(np.nonzero(self.mul[a] == 1)[0][0])
        self.inv = inv
        self.add = np.ascontiguousarray(self.add)
        self.mul = np.ascontiguousarray(self.mul)
        # Frobenius x -> x^p
        fr = np.zeros(Q, dtype=np.uint16)
        for a in range(Q):
            r = 1
            for _ in range(p):
                r = int(self.mul[r, a])
            fr[a] = r
        self.frob_tab = fr

    def m(self, a, b):
        return int(self.mul[a, b])

    def a(self, a, b):
        return int(self.add[a, b])

    def pw(self, a, k):
        r, b = 1, a
        while k:
            if k & 1:
                r = int(self.mul[r, b])
            b = int(self.mul[b, b])
            k >>= 1
        return r

    def from_int(self, x):
        return int(x) % self.p  # prime-field element

    def rank(self, M):
        """Rank by Gaussian elimination (pure numpy)."""
        return len(self._rref(M)[1])

    def matmul(self, A, B):
        A = np.asarray(A, dtype=np.int64)
        B = np.asarray(B, dtype=np.int64)
        out = np.zeros((A.shape[0], B.shape[1]), dtype=np.int64)
        for t in range(A.shape[1]):
            out = self.add[out, self.mul[A[:, t][:, None], B[t][None, :]]].astype(np.int64)
        return out

    def _rref(self, M):
        R = np.array(M, dtype=np.int64).copy()
        nr, nc = R.shape
        piv = []
        r = 0
        for c in range(nc):
            if r >= nr:
                break
            nz = np.nonzero(R[r:, c])[0]
            if nz.size == 0:
                continue
            i = r + nz[0]
            if i != r:
                R[[r, i]] = R[[i, r]]
            R[r] = self.mul[self.inv[R[r, c]], R[r]]
            for j in range(nr):
                if j != r and R[j, c]:
                    R[j] = self.sub[R[j], self.mul[R[j, c], R[r]]]
            piv.append(c)
            r += 1
        return R[:r], piv

    def nullspace(self, M):
        """Rows spanning {x : M x = 0}."""
        R, piv = self._rref(M)
        nc = R.shape[1] if R.size else np.asarray(M).shape[1]
        free = [c for c in range(nc) if c not in set(piv)]
        N = np.zeros((len(free), nc), dtype=np.int64)
        for t, f in enumerate(free):
            N[t, f] = 1
            for i, c in enumerate(piv):
                N[t, c] = self.neg[R[i, f]]
        return N


if __name__ == "__main__":
    F = GF(3, 2)
    assert F.m(3, 3) == F.neg[1]  # t^2 = -1
    rng = np.random.default_rng(1)
    A = rng.integers(0, 9, size=(40, 30))
    B = rng.integers(0, 9, size=(30, 50))
    C = F.matmul(A, B)
    assert F.rank(C) <= 30
    print("rank of random 40x30 * 30x50 over GF(9):", F.rank(C))
