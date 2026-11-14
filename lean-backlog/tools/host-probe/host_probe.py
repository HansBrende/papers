"""Probe of incidence hosts: rows = points, columns = lines, helpers of a column = points on its line.
Residual cells = non-incident (p, l).  A linear whole-row code on residual cells is a subspace of
ker(I - M) for some M supported on the helper relation H (x=(p,l) -> cells (q,m), q on l, q not on m).
Reports: order residual (exact, subset DP), pair value, spectrum of the mutual graph, and an
alternating-projection search for M with rank(I-M) <= r (heuristic, real field)."""
import itertools, sys
import numpy as np

def fano():
    return 7, [frozenset({i, (i+1) % 7, (i+3) % 7}) for i in range(7)]

def pg2(q):
    def norm(v):
        for x in v:
            if x:
                inv = pow(x, -1, q); return tuple((inv*y) % q for y in v)
    pts = sorted(set(norm(v) for v in itertools.product(range(q), repeat=3) if any(v)))
    lines = [frozenset(i for i, p in enumerate(pts) if sum(a*b for a, b in zip(p, l)) % q == 0) for l in pts]
    return len(pts), lines

def doily():
    duads = list(itertools.combinations(range(6), 2)); idx = {d: i for i, d in enumerate(duads)}
    synth = set()
    for perm in itertools.permutations(range(6)):
        synth.add(frozenset(idx[tuple(sorted((perm[2*i], perm[2*i+1])))] for i in range(3)))
    return 15, sorted(synth, key=sorted)

def grid():
    P = lambda i, j: 3*i + j
    return 9, [frozenset(P(i, j) for j in range(3)) for i in range(3)] + [frozenset(P(i, j) for i in range(3)) for j in range(3)]

def order_sum(n, lines):
    masks = [sum(1 << p for p in l) for l in lines]
    full = (1 << n) - 1
    inside = [0]*(1 << n)
    for S in range(1 << n):
        inside[S] = sum(1 for m in masks if m & S == m)
    best = [0]*(1 << n)
    for S in range(1, 1 << n):
        b = 0; T = S
        while T:
            low = T & -T; b = max(b, best[S ^ low]); T ^= low
        best[S] = b + (inside[S] if S != full else 0)
    return best[full]

def build(n, lines):
    cells = [(p, j) for p in range(n) for j, l in enumerate(lines) if p not in l]
    idx = {c: i for i, c in enumerate(cells)}
    N = len(cells)
    H = np.zeros((N, N), bool)
    for (p, j), i in idx.items():
        for q in lines[j]:
            for m, lm in enumerate(lines):
                if q not in lm:
                    H[i, idx[(q, m)]] = True
    return cells, H

def ap(H, r, iters, seed):
    rng = np.random.default_rng(seed)
    N = H.shape[0]
    X = np.eye(N) - H * rng.standard_normal((N, N)) / np.sqrt(H.sum(1).mean())
    for it in range(iters):
        U, s, Vt = np.linalg.svd(X)
        if s[r] < 1e-9: break
        Y = (U[:, :r] * s[:r]) @ Vt[:r]
        X = np.where(H, Y, 0.0); np.fill_diagonal(X, 1.0)
    s = np.linalg.svd(X, compute_uv=False)
    return s[r] if r < N else 0.0, it

if __name__ == "__main__":
    name = sys.argv[1]
    n, lines = {"fano": fano, "pg3": lambda: pg2(3), "doily": doily, "grid": grid}[name]()
    cells, H = build(n, lines)
    N = len(cells)
    mutual = H & H.T
    osum = order_sum(n, lines)
    print(f"{name}: points {n}, lines {len(lines)}, residual cells {N}, helper degree {H.sum(1)[0]}, mutual degree {mutual.sum(1)[0]}")
    print(f"  order residual = {N} - {osum} = {N - osum}")
    A = mutual.astype(float)
    tri = np.trace(A @ A @ A) / 6
    ev = np.round(np.linalg.eigvalsh(A), 6)
    vals, mult = np.unique(ev, return_counts=True)
    print(f"  mutual triangles = {tri:.0f}; mutual-graph spectrum (value:mult): " + ", ".join(f"{v:g}:{m}" for v, m in zip(vals, mult)))
    seeds, iters = int(sys.argv[3]), int(sys.argv[4])
    if seeds < 0 or iters < 0:
        raise SystemExit("seeds and iters must be nonnegative")
    if seeds == 0 or iters == 0:
        print("  alternating-projection search skipped (zero seeds or iterations)")
        raise SystemExit(0)
    for K in [int(x) for x in sys.argv[2].split(",")]:
        res = []
        for seed in range(seeds):
            res.append(ap(H, N - K, iters, seed))
        best = min(res)
        print(f"  target dim {K} (rank {N-K}): best sigma_(r+1) = {best[0]:.2e} after {best[1]+1} its; all: " + " ".join(f"{a:.1e}" for a, _ in res), flush=True)
