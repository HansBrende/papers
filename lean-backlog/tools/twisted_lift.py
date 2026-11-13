"""Toy model of the wall: least rank of a block-monomial involution minus an
element of M_d (x) W, with W a w-dimensional space of n x n matrices.

Target:  (tau v)(g) = U_g v(iota g),  U_{iota g} = U_g^{-1},  iota a fixed-point-free
involution of [d].  Decoder: K = sum_s kappa_s (x) W_s with kappa_s free d x d.
Code = ker(tau - K) in F^d (x) F^n.  Pairing (K = 1) gives dn/2.

Method (numerical, real field): alternating projections between the affine
space tau - M_d (x) W and the matrices of rank <= rho.  A run "reaches rho" if
the distance falls below 1e-9; the kernel dimension is then dn - rho.
This is a search: failure to reach a rank proves nothing.

Usage: uv run python lean-backlog/tools/twisted_lift.py n w d [restarts] [iters]
"""
import sys
import numpy as np


def instance(n, w, d, rng, orth=False, toral=False, paired=True):
    assert d % 2 == 0
    iota = np.arange(d) ^ 1                       # pairs (0,1), (2,3), ...
    U = np.zeros((d, n, n))
    for g in range(0, d, 2):
        A = rng.standard_normal((n, n))
        if orth:
            A, _ = np.linalg.qr(A)
        U[g] = A
        U[g + 1] = np.linalg.inv(A) if paired else rng.standard_normal((n, n))
    if toral:      # W inside the diagonal matrices (commutative)
        Ws = [np.eye(n)] + [np.diag(rng.standard_normal(n)) for _ in range(w - 1)]
    else:
        Ws = [np.eye(n)] + [rng.standard_normal((n, n)) for _ in range(w - 1)]
    # orthonormal basis of W for the Frobenius inner product
    Q, _ = np.linalg.qr(np.stack([x.ravel() for x in Ws], axis=1))
    return iota, U, Q                              # Q: n*n x w


def blocks(Y, d, n):
    return Y.reshape(d, n, d, n).transpose(0, 2, 1, 3)   # [g,h] -> n x n


def unblocks(B, d, n):
    return B.transpose(0, 2, 1, 3).reshape(d * n, d * n)


def affine_project(Y, tau_b, Q, d, n):
    B = blocks(Y, d, n).reshape(d, d, n * n)
    T = tau_b.reshape(d, d, n * n)
    PB = (B @ Q) @ Q.T
    PT = (T @ Q) @ Q.T
    return unblocks((PB + T - PT).reshape(d, d, n, n), d, n)


def search(n, w, d, rho, rng, iters=4000, orth=False, inst=None):
    iota, U, Q = inst if inst is not None else instance(n, w, d, rng, orth)
    tau_b = np.zeros((d, d, n, n))
    for g in range(d):
        tau_b[g, iota[g]] = U[g]
    tau = unblocks(tau_b, d, n)
    # start: tau minus a random element of M_d (x) W
    Y = affine_project(tau + rng.standard_normal(tau.shape), tau_b, Q, d, n)
    dist = np.inf
    for it in range(iters):
        u, s, vt = np.linalg.svd(Y)
        dist = np.sqrt((s[rho:] ** 2).sum())
        if dist < 1e-9:
            break
        L = (u[:, :rho] * s[:rho]) @ vt[:rho]
        Y = affine_project(L, tau_b, Q, d, n)
    return dist, np.abs(Y).max()


def main():
    n, w, d = (int(x) for x in sys.argv[1:4])
    restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    iters = int(sys.argv[5]) if len(sys.argv) > 5 else 4000
    rng = np.random.default_rng(20261113)
    inst = instance(n, w, d, rng)
    N = d * n
    print(f"n={n} w={w} d={d}: dn={N}, pairing kernel {N//2}, "
          f"parameter count allows about {d*np.sqrt(w):.1f}")
    for excess in range(0, N // 2 + 1):
        rho = N // 2 - excess                      # kernel = N/2 + excess
        best = np.inf
        for _ in range(restarts):
            dist, size = search(n, w, d, rho, rng, iters, inst=inst)
            best = min(best, dist)
            if dist < 1e-9:
                break
        ok = best < 1e-9
        print(f"  kernel {N - rho:3d} (pairing {'+' if excess else ' '}{excess}): "
              f"{'reached' if ok else 'not reached'}  dist={best:.2e}", flush=True)
        if not ok:
            break


if __name__ == "__main__":
    main()
