"""Alternating least squares for: N x N matrix X = U V^T of rank <= r with X_xx = 1 and X_xy = 0 for
y outside H(x) (x != y).  Then ker X has dimension >= N - r and is a linear whole-row code on the
residual cells (real field).  Heuristic: a residual near zero is a lead, to be confirmed exactly."""
import sys, numpy as np
from host_probe import fano, pg2, doily, grid, build

def als(H, r, sweeps, seed, tol=1e-22):
    rng = np.random.default_rng(seed)
    N = H.shape[0]
    C = ~H                     # constrained entries (includes the diagonal)
    T = np.eye(N)
    U = rng.standard_normal((N, r)); V = rng.standard_normal((N, r))
    err = None
    for s in range(sweeps):
        for x in range(N):
            m = C[x]
            U[x] = np.linalg.lstsq(V[m], T[x, m], rcond=None)[0]
        for y in range(N):
            m = C[:, y]
            V[y] = np.linalg.lstsq(U[m], T[m, y], rcond=None)[0]
        R = (U @ V.T - T) * C
        err = float((R**2).sum())
        if err < tol: break
    X = np.where(C, T, U @ V.T)          # constraints imposed exactly
    sv = np.linalg.svd(X, compute_uv=False)
    return err, s + 1, sv[r-1], sv[r]

if __name__ == "__main__":
    name = sys.argv[1]
    n, lines = {"fano": fano, "pg3": lambda: pg2(3), "doily": doily, "grid": grid}[name]()
    cells, H = build(n, lines)
    N = len(cells)
    for K in [int(x) for x in sys.argv[2].split(",")]:
        out = [als(H, N - K, int(sys.argv[4]), seed) for seed in range(int(sys.argv[3]))]
        print(f"{name} dim {K}: " + "  ".join(f"err {e:.1e} sweeps {s} sv_r {a:.1e} sv_r+1 {b:.1e};" for e, s, a, b in out), flush=True)
