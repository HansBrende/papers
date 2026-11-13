"""Checks for lean-backlog/notes/pass-calculus.md.

1. Transposition as five layers (complex numbers, any d):
     X^T = N T^-1 (F^-1 (x) 1) M (F (x) 1) T^-1 X,
   T = row shear (row r shifted by r), F (x) 1 = DFT along the row index, M = entrywise multiplication by
   w^(t c), N = reversal of the column index.
2. Cut profile: Kronecker rank of an operator on the d^2 cells of a row-major tape, d = 2^k, across the split
   of the 2k address bits into the top 2k - m and the low m bits, for the swap, the shear, the prefix sum over
   rows, a perfect unshuffle of the rows and the DFT along the row index.

Usage:  python3 lean-backlog/tools/pass_layers.py
"""
import numpy as np


def op_from_map(d, f):
    """Operator on vec(X) (row-major) that moves the entry at (r, c) to f(r, c)."""
    P = np.zeros((d * d, d * d))
    for r in range(d):
        for c in range(d):
            r2, c2 = f(r, c)
            P[(r2 % d) * d + (c2 % d), r * d + c] = 1
    return P


def five_layers(d, rng):
    w = np.exp(2j * np.pi / d)
    F = np.array([[w ** (t * r) for r in range(d)] for t in range(d)])
    Fi = np.conj(F.T) / d
    Tinv = op_from_map(d, lambda r, c: (r, c - r))
    N = op_from_map(d, lambda r, c: (r, -c))
    M = np.diag([w ** (t * c) for t in range(d) for c in range(d)])
    I = np.eye(d)
    K = N @ Tinv @ np.kron(Fi, I) @ M @ np.kron(F, I) @ Tinv
    X = rng.standard_normal((d, d))
    return np.abs((K @ X.reshape(-1)).reshape(d, d) - X.T).max()


def cut_ranks(K, k):
    """Kronecker ranks across the address splits m = 1 .. 2k-1 (low m bits against the rest)."""
    n = 2 * k
    out = []
    for m in range(1, n):
        hi, lo = 2 ** (n - m), 2 ** m
        R = K.reshape(hi, lo, hi, lo).transpose(0, 2, 1, 3).reshape(hi * hi, lo * lo)
        out.append(int(np.linalg.matrix_rank(R, tol=1e-9)))
    return out


def main():
    rng = np.random.default_rng(1)
    for d in (3, 4, 5, 8, 9):
        print(f"five layers, d={d}: max error {five_layers(d, rng):.2e}")
    for k in (2, 3):
        d = 2 ** k
        I = np.eye(d)
        w = np.exp(2j * np.pi / d)
        F = np.array([[w ** (t * r) for r in range(d)] for t in range(d)]) / np.sqrt(d)
        L = np.tril(np.ones((d, d)))
        unsh = np.zeros((d, d))
        for r in range(d):
            unsh[(r >> 1) + (r & 1) * (d // 2), r] = 1
        ops = {
            "swap": op_from_map(d, lambda r, c: (c, r)),
            "row shear": op_from_map(d, lambda r, c: (r, c + r)),
            "column shear": op_from_map(d, lambda r, c: (r + c, c)),
            "prefix sum over rows": np.kron(L, I),
            "unshuffle of rows": np.kron(unsh, I),
            "DFT along rows": np.kron(F, I),
            "DFT within rows": np.kron(I, F),
        }
        print(f"d={d}: Kronecker ranks at the address splits m = 1..{2 * k - 1}")
        for name, K in ops.items():
            print(f"  {name:22s} {cut_ranks(K, k)}")


if __name__ == "__main__":
    main()
