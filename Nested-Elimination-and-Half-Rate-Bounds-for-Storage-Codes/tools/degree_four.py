"""Generate the data of `lean/HalfRate/DegreeFour.lean`: a storage code of rate 7/13 on a 4-regular triangle-free graph.

The graph G13 has graph6 string `L?`@F@wlEcBoBo` (13 vertices, 4-regular, triangle-free, odd girth 5), with vertices
numbered as networkx's `from_graph6_bytes` numbers them. The code is the F_4-linear code with generator matrix
[I_7 | D(w)] over F_4 = {0, 1, w, w^2}, w^2 = w + 1, columns indexed by the vertices, where D(s) has rows
  (1,0,1,1,0,1), (1,1,0,1,0,1), (1,1,1,0,0,1), (0,1,1,1,1,0), (1,1,0,0,s,s), (1,0,1,0,s,s), (1,0,0,1,s,s).
Every column lies in the F_4-span of the columns of its four neighbours, so each symbol is an F_4-linear function of
its neighbours' symbols.

For the kernel-checked proof, a symbol a + b w of F_4 is written as the bit pair (a, b) in (ZMod 2)^2, and the code as
an F_2-linear code: message bit 2r + c is the coefficient of w^c in the r-th F_4 message symbol. Multiplication by
lambda in F_4 becomes a 2 x 2 matrix over F_2. The script computes the neighbour lists, the 14 x 13 x 2 generator and
the 13 x 4 x 2 x 2 recovery coefficients, checks every identity in exact arithmetic, and prints the Lean definitions.
Usage: python3 tools/degree_four.py > generated.lean.txt (requires networkx).
"""
import itertools
import networkx as nx

G6 = 'L?`@F@wlEcBoBo'
EXP = [1, 2, 3]                      # F_4 encoded 0, 1, 2 = w, 3 = w^2; addition is XOR
LOG = {1: 0, 2: 1, 3: 2}


def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[(LOG[a] + LOG[b]) % 3]


def bits(x):                         # x = a + b w  ->  (a, b); encodings: 1 = (1,0), w = (0,1), w^2 = (1,1)
    return {0: (0, 0), 1: (1, 0), 2: (0, 1), 3: (1, 1)}[x]


def mulmat(lam):                     # 2 x 2 matrix over F_2 of y -> lam * y in the basis (1, w)
    cols = [bits(mul(lam, 1)), bits(mul(lam, 2))]       # images of 1 and of w
    return [[cols[0][0], cols[1][0]], [cols[0][1], cols[1][1]]]


G = nx.from_graph6_bytes(G6.encode())
n = G.number_of_nodes()
assert n == 13 and all(d == 4 for _, d in G.degree())
assert sum(nx.triangles(G).values()) == 0
nb = [sorted(G[v]) for v in range(n)]
s = 2                                # s = w
D = [[1, 0, 1, 1, 0, 1], [1, 1, 0, 1, 0, 1], [1, 1, 1, 0, 0, 1], [0, 1, 1, 1, 1, 0],
     [1, 1, 0, 0, s, s], [1, 0, 1, 0, s, s], [1, 0, 0, 1, s, s]]
Gm = [[1 if i == j else 0 for j in range(7)] + D[i] for i in range(7)]
col = lambda v: [Gm[i][v] for i in range(7)]

# recovery coefficients over F_4: col v = sum_k lam[v][k] col(nb[v][k])
lam = []
for v in range(n):
    sol = None
    for xs in itertools.product(range(4), repeat=4):
        acc = [0] * 7
        for x, u in zip(xs, nb[v]):
            acc = [p ^ mul(x, q) for p, q in zip(acc, col(u))]
        if acc == col(v):
            assert sol is None, "recovery coefficients not unique"
            sol = xs
    assert sol is not None and all(sol), f"vertex {v}: no recovery with nonzero coefficients"
    lam.append(list(sol))

# binary generator: gen[i][v][j], message bit i = 2r + c is w^c in row r
gen = [[[0, 0] for _ in range(n)] for _ in range(14)]
for r in range(7):
    for c in range(2):
        beta = 1 if c == 0 else 2
        for v in range(n):
            gen[2 * r + c][v] = list(bits(mul(beta, Gm[r][v])))
rec = [[mulmat(lam[v][k]) for k in range(4)] for v in range(n)]

# exact checks of what the Lean proof uses
for i in range(14):
    for v in range(n):
        for j in range(2):
            rhs = sum(rec[v][k][j][jp] * gen[i][nb[v][k]][jp] for k in range(4) for jp in range(2)) % 2
            assert gen[i][v][j] == rhs
for v in range(7):
    for j in range(2):
        for i in range(14):
            assert gen[i][v][j] == (1 if i == 2 * v + j else 0)


def lean_vec(xs):
    return "![" + ", ".join(xs) + "]"


print("def g13nb : Fin 13 → Fin 4 → Fin 13 :=\n  " +
      lean_vec([lean_vec([str(u) for u in nb[v]]) for v in range(n)]))
print("def g13gen : Fin 14 → Fin 13 → Fin 2 → ZMod 2 :=\n  " +
      lean_vec([lean_vec([lean_vec([str(b) for b in gen[i][v]]) for v in range(n)]) for i in range(14)]))
print("def g13rec : Fin 13 → Fin 4 → Fin 2 → Fin 2 → ZMod 2 :=\n  " +
      lean_vec([lean_vec([lean_vec([lean_vec([str(b) for b in row]) for row in rec[v][k]]) for k in range(4)])
                for v in range(n)]))
