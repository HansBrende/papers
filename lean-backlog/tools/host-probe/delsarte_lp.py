"""Delsarte linear-programming bound for storage codes on a graph, in difference form.

A code over an alphabet of size q on a graph G with N vertices (vertex v is a function of its
neighbours) is a set of words in which no two distinct words differ in a FORBIDDEN way: at some
vertex v but at none of its neighbours.  The supports S of allowed differences are the sets in
which every vertex has a neighbour.  The association scheme is the N-fold product of the trivial
scheme on q points, with one relation per support, so the LP has one variable A_S per allowed S:

    maximise sum_S A_S   subject to   A_empty = 1,  A_S >= 0,
    sum_S A_S * (-1/(q-1))^{|S & T|} >= 0   for every T.

Every code has at most LP-value words.  Splitting a symbol into sub-symbols does not refine the
bound: the invertible linear maps of each symbol preserve the forbidden set and act transitively
on its nonzero values, so the finer LP symmetrises back to this one.

Usage: uv run --no-project --with numpy --with scipy --with networkx python delsarte_lp.py
"""
import math
import numpy as np
import networkx as nx
from scipy.optimize import linprog


def bound(G, q):
    n = G.number_of_nodes()
    N = 1 << n
    nb = [sum(1 << u for u in G[v]) for v in range(n)]
    allowed = [S for S in range(N) if all((nb[v] & S) for v in range(n) if S >> v & 1)]
    pc = [bin(x).count("1") for x in range(N)]
    r = -1.0 / (q - 1)
    A = np.array([[-(r ** pc[S & T]) for S in allowed] for T in range(N)])
    Aeq = np.array([[1.0 if S == 0 else 0.0 for S in allowed]])
    for method in ("highs-ds", "highs-ipm"):
        res = linprog(-np.ones(len(allowed)), A_ub=A, b_ub=np.zeros(N), A_eq=Aeq, b_eq=[1.0],
                      bounds=[(0, None)] * len(allowed), method=method)
        if res.status == 0:
            return -res.fun, len(allowed)
    return float("nan"), len(allowed)


if __name__ == "__main__":
    graphs = {"C5": nx.cycle_graph(5), "C7": nx.cycle_graph(7), "C9": nx.cycle_graph(9),
              "Petersen": nx.petersen_graph(), "K33": nx.complete_bipartite_graph(3, 3),
              "cube": nx.hypercube_graph(3)}
    graphs = {k: nx.convert_node_labels_to_integers(g) for k, g in graphs.items()}
    capacity = {"C5": 2.5, "C7": 3.5, "C9": 4.5, "Petersen": 5, "K33": 3, "cube": 4}
    order = {"C5": 3, "C7": 4, "C9": 5, "Petersen": 6, "K33": 3, "cube": 4}
    for name, G in graphs.items():
        print(f"{name}: capacity {capacity[name]}, order bound {order[name]}")
        for q in (2, 3, 4, 5, 8, 16, 64):
            v, m = bound(G, q)
            print(f"    q={q}: LP {v:.3f}, exponent {math.log(v, q):.4f}" if v == v
                  else f"    q={q}: solver failed", flush=True)
    # closed forms observed at every tested q (floating-point LP; not proved)
    for q in (2, 3, 4, 5, 8, 16, 64):
        assert abs(bound(graphs["C5"], q)[0] / (q * q * (q + 1) / 2) - 1) < 1e-6
        assert abs(bound(graphs["C7"], q)[0] / (q ** 4 * (q + 3) / (3 * q + 1)) - 1) < 1e-6
    print("C5: LP = q^2 (q+1)/2 and C7: LP = q^4 (q+3)/(3q+1) at all tested q")
