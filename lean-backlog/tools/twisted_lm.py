"""Second search for the toy model of twisted_lift.py: solve the bilinear system
(tau - K(kappa)) E = 0 for kappa (w d^2 unknowns) and a D-dimensional subspace
(E = B0 + B1 F in a random chart) by Levenberg-Marquardt, several restarts.

A hit is confirmed by the singular values of tau - K(kappa) itself (kernel
dimension at tolerance 1e-8) and the size of kappa is printed, because codes
found only with exploding coefficients are artefacts (valleys to infinity).
Numerical over the reals; a failure to find D proves nothing.

Usage: uv run python lean-backlog/tools/twisted_lm.py n w d [restarts] [Dmin]
"""
import sys
import numpy as np
from scipy.optimize import least_squares
from twisted_lift import instance


def build(n, w, d, inst):
    iota, U, Q = inst
    N = d * n
    tau = np.zeros((N, N))
    for g in range(d):
        tau[g * n:(g + 1) * n, iota[g] * n:(iota[g] + 1) * n] = U[g]
    Wb = [Q[:, s].reshape(n, n) for s in range(w)]
    return tau, Wb


def K_of(kappa, Wb, d, n):
    return sum(np.kron(kappa[s], Wb[s]) for s in range(len(Wb)))


def attempt(n, w, d, D, tau, Wb, rng, start_pairing=True):
    N = d * n
    Pr = rng.standard_normal((D, N))
    B0 = np.linalg.pinv(Pr)                       # N x D, Pr B0 = I
    _, _, vt = np.linalg.svd(Pr)
    B1 = vt[D:].T                                 # N x (N-D), Pr B1 = 0
    nk = w * d * d

    def unpack(x):
        kappa = x[:nk].reshape(w, d, d)
        F = x[nk:].reshape(N - D, D)
        return kappa, B0 + B1 @ F

    def res(x):
        kappa, E = unpack(x)
        return ((tau - K_of(kappa, Wb, d, n)) @ E).ravel()

    x0 = rng.standard_normal(nk + (N - D) * D) * 0.5
    if start_pairing:
        # K = 1 lies in M_d (x) W: coefficient of the identity direction
        c = [np.trace(Wb[s]) for s in range(w)]   # <1, Wb_s>
        k0 = np.stack([c[s] * np.eye(d) for s in range(w)])
        x0[:nk] = k0.ravel() + 0.3 * rng.standard_normal(nk)
    sol = least_squares(res, x0, method="trf", xtol=1e-14, ftol=1e-14, gtol=1e-14,
                        max_nfev=400)
    kappa, _ = unpack(sol.x)
    s = np.linalg.svd(tau - K_of(kappa, Wb, d, n), compute_uv=False)
    ker = int((s < 1e-8).sum())
    return ker, np.abs(kappa).max(), np.sqrt(2 * sol.cost)


def main():
    n, w, d = (int(x) for x in sys.argv[1:4])
    restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    N = d * n
    Dmin = int(sys.argv[5]) if len(sys.argv) > 5 else N // 2
    rng = np.random.default_rng(20261113)
    inst = instance(n, w, d, rng)
    tau, Wb = build(n, w, d, inst)
    print(f"n={n} w={w} d={d}: dn={N}, pairing {N//2}, flag bound "
          f"{N - d*(n//(w+1))}, parameter count about {d*np.sqrt(w):.1f}", flush=True)
    for D in range(Dmin, N + 1):
        hit = None
        for r in range(restarts):
            ker, size, resid = attempt(n, w, d, D, tau, Wb, rng, start_pairing=(r % 2 == 0))
            if ker >= D:
                hit = (ker, size)
                break
        if hit:
            print(f"  D={D:3d}: found, kernel {hit[0]}, max|kappa|={hit[1]:.2f}", flush=True)
        else:
            print(f"  D={D:3d}: not found in {restarts} restarts (last residual {resid:.1e})",
                  flush=True)
            break


if __name__ == "__main__":
    main()
