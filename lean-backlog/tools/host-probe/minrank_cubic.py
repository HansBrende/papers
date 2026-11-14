"""Counterexample search for: a real matrix with unit diagonal whose off-diagonal support lies in
the edges of a triangle-free graph of maximum degree three has rank at least n/2.
Samples connected, triangle-free, non-bipartite cubic graphs on n vertices (random regular graphs,
deduplicated up to isomorphism) and runs the rank-constrained ALS of als.py at rank n/2 - 1, with
rank n/2 as a positive control.  Heuristic: only full convergence with bounded entries is a lead."""
import sys, numpy as np, networkx as nx
from als import als

def sample(n, want, tries, seed):
    rng = np.random.default_rng(seed); out = []
    for _ in range(tries):
        G = nx.random_regular_graph(3, n, seed=int(rng.integers(1 << 30)))
        if not nx.is_connected(G) or nx.is_bipartite(G): continue
        if sum(nx.triangles(G).values()) > 0: continue
        if any(nx.is_isomorphic(G, H) for H in out): continue
        out.append(G)
        if len(out) >= want: break
    return out

def mask(G):
    n = G.number_of_nodes(); H = np.zeros((n, n), bool)
    for u, v in G.edges(): H[u, v] = H[v, u] = True
    return H

if __name__ == "__main__":
    n, want, seeds, sweeps = map(int, sys.argv[1:5])
    graphs = [nx.petersen_graph()] if n == 10 else []
    graphs += sample(n, want, 20000, 1)
    print(f"n = {n}: {len(graphs)} non-isomorphic connected triangle-free non-bipartite cubic graphs sampled")
    worst = None
    for i, G in enumerate(graphs):
        H = mask(G); g = nx.girth(G)
        ctrl = min(als(H, n // 2, sweeps, s)[0] for s in range(2))
        res = [als(H, n // 2 - 1, sweeps, s) for s in range(seeds)]
        best = min(res)
        if worst is None or best[0] < worst[0]: worst = (best[0], i, g)
        print(f"  graph {i:3d} girth {g} alpha-bound n-alpha = {n - len(nx.max_weight_clique(nx.complement(G), weight=None)[0])}: "
              f"control rank n/2 err {ctrl:.1e}; rank n/2-1 best err {best[0]:.2e} (sv_r {best[2]:.1e}, sv_r+1 {best[3]:.1e})", flush=True)
    print(f"smallest error at rank n/2 - 1: {worst[0]:.2e} (graph {worst[1]}, girth {worst[2]})")
