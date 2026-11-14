"""Full Shannon (polymatroid) bound for storage codes on a graph: maximise h(V) over polymatroids
with h({v}) <= 1 and h(N(v) + v) = h(N(v)) for every vertex.  All 2^n subsets are variables and all
elemental inequalities are used, so the optimum is the exact Shannon bound (floating point, HiGHS).
Graphs: Petersen (n = 10) and the sampled triangle-free non-bipartite cubic graphs of minrank_cubic.py."""
import sys, numpy as np, networkx as nx, scipy.sparse as sp
from scipy.optimize import linprog
from minrank_cubic import sample

def shannon(G):
    n = G.number_of_nodes(); N = 1 << n; full = N - 1
    rows, cols, vals = [], [], []; r = 0
    def add(terms):
        nonlocal r
        for c, v in terms:
            rows.append(r); cols.append(c); vals.append(v)
        r += 1
    for i in range(n):
        for j in range(i + 1, n):
            bi, bj = 1 << i, 1 << j
            rest = full ^ bi ^ bj
            S = rest
            while True:                       # all subsets S of rest
                add([(S | bi | bj, 1.0), (S, 1.0), (S | bi, -1.0), (S | bj, -1.0)])
                if S == 0: break
                S = (S - 1) & rest
    for i in range(n):
        add([(full ^ (1 << i), 1.0), (full, -1.0)])
    for v in G:
        nb = sum(1 << u for u in G[v])
        add([(nb | (1 << v), 1.0), (nb, -1.0)])
    A = sp.csr_matrix((vals, (rows, cols)), shape=(r, N))
    c = np.zeros(N); c[full] = -1.0
    bounds = [(0, 0)] + [(0, 1) if (S & (S - 1)) == 0 else (0, None) for S in range(1, N)]
    res = linprog(c, A_ub=A, b_ub=np.zeros(r), bounds=bounds, method="highs-ipm", options={"time_limit": 240})
    return (-res.fun if res.fun is not None else float("nan")), res.status

if __name__ == "__main__":
    n, want = int(sys.argv[1]), int(sys.argv[2])
    graphs = [nx.petersen_graph()] if n == 10 else []
    graphs += sample(n, want, 20000, 1)
    if len(sys.argv) > 3: graphs = graphs[:int(sys.argv[3])]
    vals = []
    for i, G in enumerate(graphs):
        val, st = shannon(G)
        alpha = len(nx.max_weight_clique(nx.complement(G), weight=None)[0])
        vals.append(val)
        print(f"  graph {i:3d}: girth {nx.girth(G)}, n - alpha = {n - alpha}, Shannon bound = {val:.6f} (status {st})", flush=True)
    print(f"n = {n}: {len(graphs)} graphs; Shannon bound min {min(vals):.6f}, max {max(vals):.6f}; n/2 = {n/2}")
