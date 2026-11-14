"""Exact test over F_2: is there a matrix with unit diagonal, off-diagonal support inside the edges
of G (asymmetric zeros allowed), and rank at most n/2 - 1?  Depth-first search over the rows, a
maximum independent set first (its rows are independent), pruning when the rank exceeds the target.
Graphs: Petersen, and the sampled triangle-free non-bipartite cubic graphs of minrank_cubic.py."""
import sys, itertools, networkx as nx
from minrank_cubic import sample

def reduce(v, basis):
    for b in basis:
        v = min(v, v ^ b)
    return v

def exists(G, rmax):
    n = G.number_of_nodes()
    I = nx.max_weight_clique(nx.complement(G), weight=None)[0]
    order = list(I) + [v for v in nx.bfs_tree(G, I[0]) if v not in I]
    order += [v for v in G if v not in order]
    opts = []
    for v in order:
        nb = list(G[v]); rows = []
        for k in range(len(nb) + 1):
            for S in itertools.combinations(nb, k):
                rows.append((1 << v) | sum(1 << u for u in S))
        opts.append(rows)
    nodes = 0
    def dfs(i, basis):
        nonlocal nodes
        nodes += 1
        if i == n: return True
        for row in opts[i]:
            r = reduce(row, basis)
            if r == 0:
                if dfs(i + 1, basis): return True
            elif len(basis) < rmax:
                nb = sorted(basis + [r], reverse=True)
                if dfs(i + 1, nb): return True
        return False
    return dfs(0, []), nodes, len(I)

if __name__ == "__main__":
    n, want = int(sys.argv[1]), int(sys.argv[2])
    graphs = [nx.petersen_graph()] if n == 10 else []
    graphs += sample(n, want, 20000, 1)
    found = 0; tot = 0
    for i, G in enumerate(graphs):
        ok, nodes, a = exists(G, n // 2 - 1)
        ctrl, _, _ = exists(G, n // 2)
        found += ok; tot += nodes
        if ok or not ctrl:
            print(f"  graph {i}: rank <= n/2-1 exists: {ok}; rank <= n/2 exists: {ctrl}; alpha {a}", flush=True)
    print(f"n = {n}: {len(graphs)} graphs; with an F_2 matrix of rank <= n/2 - 1: {found}; search nodes {tot}")
