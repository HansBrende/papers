"""Orbit-reduced Shannon LP for storage codes on the Petersen graph, solved by dual simplex to get a
sparse dual certificate of h(V) <= 5.  Variables: orbits of vertex subsets under the 120 automorphisms.
Outer cycle 0..4, inner vertices 5..9, spokes i -- i+5, inner edges i+5 -- ((i+2) mod 5)+5."""
import numpy as np, networkx as nx, scipy.sparse as sp
from scipy.optimize import linprog
from networkx.algorithms.isomorphism import GraphMatcher

G = nx.petersen_graph(); n = 10; N = 1 << n; full = N - 1
auts = [[m[i] for i in range(n)] for m in GraphMatcher(G, G).isomorphisms_iter()]
def image(S, p):
    T = 0
    for i in range(n):
        if S >> i & 1: T |= 1 << p[i]
    return T
canon = [min(image(S, p) for p in auts) for S in range(N)]
reps = sorted(set(canon)); idx = {S: k for k, S in enumerate(reps)}
def var(S): return idx[canon[S]]
def cl(S):
    ch = True
    while ch:
        ch = False
        for v in G:
            if not S >> v & 1 and all(S >> u & 1 for u in G[v]): S |= 1 << v; ch = True
    return S
rowset = {}
def add(terms, label):
    d = {}
    for c, v in terms: d[c] = d.get(c, 0) + v
    key = tuple(sorted((c, v) for c, v in d.items() if v))
    if key and key not in rowset: rowset[key] = label
for i in range(n):
    for j in range(i + 1, n):
        rest = full ^ (1 << i) ^ (1 << j); S = rest
        while True:
            A, B = S | 1 << i, S | 1 << j
            add([(var(cl(A | B)), 1), (var(S), 1), (var(A), -1), (var(B), -1)], ("sub", A, B))
            if S == 0: break
            S = (S - 1) & rest
for v in G:
    nb = sum(1 << u for u in G[v])
    add([(var(nb | 1 << v), 1), (var(nb), -1)], ("rec", v))
for i in range(n):
    add([(var(full ^ 1 << i), 1), (var(full), -1)], ("mono", i))
keys = list(rowset); m = len(keys); K = len(reps)
A = sp.lil_matrix((m, K))
for r, key in enumerate(keys):
    for c, v in key: A[r, c] = v
c = np.zeros(K); c[var(full)] = -1
bounds = [(0, None)] * K; bounds[var(0)] = (0, 0); bounds[var(1)] = (0, 1)
res = linprog(c, A_ub=A.tocsr(), b_ub=np.zeros(m), bounds=bounds, method="highs-ds")
print(f"automorphisms {len(auts)}, subset orbits {K}, distinct rows {m}, value {-res.fun:.6f}")
names = lambda S: "{" + ",".join(str(i) for i in range(n) if S >> i & 1) + "}"
y = res.ineqlin.marginals
print("dual multipliers (nonzero), each row: h(cl(A u B)) + h(A n B) <= h(A) + h(B):")
for r in np.argsort(y):
    if abs(y[r]) > 1e-9:
        lab = rowset[keys[r]]
        if lab[0] == "sub":
            _, P, Q = lab
            print(f"  {-y[r]:.4f}  A={names(P)} B={names(Q)}  A n B={names(P & Q)}  cl(A u B)={names(cl(P | Q))}  |cl A|={bin(cl(P)).count('1')} |cl B|={bin(cl(Q)).count('1')}")
        else:
            print(f"  {-y[r]:.4f}  {lab}")
print("singleton cap multiplier:", -res.upper.marginals[var(1)])
