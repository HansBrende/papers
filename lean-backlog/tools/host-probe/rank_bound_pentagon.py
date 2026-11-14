"""Translation-invariant rank bound on the binary pentagon, by brute force.

P: F_2^5 -> F_2 with P(0) = 1 and P(z) = 0 on every nonzero ALLOWED difference (every vertex of
the support has a neighbour in the support); P is free on the 15 forbidden differences.  For a
code C the matrix M[x, y] = P(x + y) restricted to C is the identity, so |C| <= rank_{F_2}(M).
All 2^15 choices of P are tried.  Standard library only (networkx for the exact comparison).
"""
import collections

n = 5
nb = [(1 << ((v - 1) % n)) | (1 << ((v + 1) % n)) for v in range(n)]


def allowed(S):
    return all(nb[v] & S for v in range(n) if S >> v & 1)


def rank(rows):
    rows = list(rows)
    r = 0
    for bit in range(32):
        piv = next((i for i in range(r, len(rows)) if rows[i] >> bit & 1), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i] >> bit & 1:
                rows[i] ^= rows[r]
        r += 1
    return r


if __name__ == "__main__":
    free = [z for z in range(1, 32) if not allowed(z)]
    assert len(free) == 15
    hist = collections.Counter()
    for mask in range(1 << 15):
        supp = [0] + [free[i] for i in range(15) if mask >> i & 1]
        hist[rank([sum(1 << (x ^ z) for z in supp) for x in range(32)])] += 1
    print("rank histogram:", sorted(hist.items()))
    print("minimum rank:", min(hist), "(order bound 2^3 = 8)")
    import networkx as nx
    G = nx.Graph()
    G.add_nodes_from(range(32))
    G.add_edges_from((x, y) for x in range(32) for y in range(x + 1, 32) if not allowed(x ^ y))
    print("largest binary code:", max(len(c) for c in nx.find_cliques(nx.complement(G))))
