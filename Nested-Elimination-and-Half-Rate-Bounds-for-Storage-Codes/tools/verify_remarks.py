#!/usr/bin/env python3
"""Exact checks of the computational remarks of the paper (the section on the limits of the method).

Usage (from the paper directory, the parent of paper/ and lean/):

    python3 tools/verify_remarks.py

Plain Python 3, standard library only, deterministic; it prints one line per check, each ending in
"OK", and the running time. A relation is a list N with N[v] the in-neighbours of v (an arc u -> v
for every u in N[v]). The checks:

0. The relation Cay(Z_9, {1, -1, 3}), N(q) = {q-1, q+1, q-3}, of Proposition 7.1 and Example 7.2.
   No set H with {} != H != Z_9 has (a) at most one parent outside H at every vertex of H and (b) at
   most one child in H at every vertex outside H (Proposition 7.1, which also has a written proof;
   exhaustive over the 2^9 subsets). The piece certificate of Example 7.2 for H1 = {0,1,2,3,5,6} in
   context {} is checked step by step against conditions (C1) and (C2) of the paper's definition of
   piece certificates, with the outside parents and their co-supply as stated; so are the pieces {4}
   and {7, 8} that complete the decomposition, and the global elimination certificate printed after
   Proposition 7.1.
1. The relation X15. Loopless, in- and out-degrees at most 3, no transitive triangle, strongly
   connected, and not 2-dicolourable. Its minimum nonempty cores (sets H != {} in which every vertex
   has at most one in-neighbour outside H) are found by exhaustive search: the only one is the
   hexagon {0, ..., 5}. The hexagon has no piece certificate in context {} (Definition "Piece
   certificates" of the paper) with at most 7 records: an exhaustive search over the partitions of
   the hexagon into at most 7 records (empty records allowed), all elimination orders and all
   supplying records, with the outside parents' steps only required to be nested; co-supplied
   outside parents are a special case. Control: the 7-vertex piece {0, 1, 2, 3, 6, 12, 14} does have
   a certificate with 3 records. The 3-record global elimination certificate of X15 printed in the
   paper is checked step by step.
2. Twelve chorded digon cycles of lengths 13, 15 and 16. Loopless, with the digons v <-> v+1
   (mod L), one-way chords, at most one chord into and one chord out of every vertex, no transitive
   triangle, no valid sweep among the 2L sweeps, and a 3-record elimination certificate, given below
   as data and checked step by step.
3. The Petersen graph (outer 5-cycle 0-4, inner pentagram 5-9, spokes i - 5+i) has no global
   elimination certificate with any number of records: with unboundedly many records, a certificate
   is an elimination order in which the later neighbours of every vertex can all be given one record,
   different from the vertex's own; the search runs over all elimination orders, keeping the forced
   equalities of records in a union-find structure and pruning as soon as a forced inequality fails.
   It is exhaustive; the number of search nodes is printed. Control: the same search finds a global
   certificate of X15.
4. Folded cubes. Over GF(2), the kernel of I + A for the folded (2k+1)-cube has dimension
   N/2 + 2^(k-1) (N = 2^(2k)) for k = 2, 3; the formula is due to Barg, Schwartz and Yohananov.
"""
import itertools
import time

# Proposition 7.1 and Example 7.2: the relation of Cay(Z_9, {1, -1, 3}).
D9 = [[(q - 1) % 9, (q + 1) % 9, (q - 3) % 9] for q in range(9)]

# Example 7.2: the piece H1 in context {}, its records X, Y and the empty record Z, the list, the
# supplying record of each step (as an index into the records), and the outside parents as stated.
D9_PIECE = ({0, 1, 2, 3, 5, 6}, [{0, 2, 6}, {1, 3, 5}, set()], [2, 3, 5, 6, 0, 1], [1, 0, 0, 2, 1, 2])
D9_OUTSIDE = {2: 8, 0: 8, 3: 4, 5: 4, 6: 7, 1: 7}
# The rest of the decomposition: the pieces {4} and {7, 8} (records, list, supplying records).
D9_REST = [({4}, [{4}, set()], [4], [1]), ({7, 8}, [{7}, {8}], [7, 8], [1, 0])]
# The global elimination certificate printed after Proposition 7.1: records and list.
D9_GLOBAL = ([{0, 4}, {1, 3, 6, 8}, {2, 5, 7}], [0, 1, 2, 3, 4, 7, 5, 6, 8])

X15 = [[5, 1, 6], [0, 2, 7], [1, 3, 8], [2, 4, 6], [3, 5, 7], [4, 0, 8], [14, 0, 10], [13, 4, 9],
       [9, 14, 5], [6, 11, 7], [9, 12], [2, 13, 12], [14, 11], [1, 8, 11], [3, 13, 12]]

# The 3-record global elimination certificate of X15 printed in the paper: records and list.
X15_GLOBAL = ([0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 2],
              [0, 4, 5, 7, 1, 9, 8, 2, 11, 12, 10, 6, 3, 13, 14])

# A 7-vertex piece of X15 with a certificate (positive control for the piece search).
X15_PIECE = [0, 1, 2, 3, 6, 12, 14]

# The Petersen graph: outer 5-cycle, inner pentagram, spokes; every edge in both directions.
PETERSEN_EDGES = ([(i, (i + 1) % 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
                  + [(i, 5 + i) for i in range(5)])
PETERSEN = [sorted({b for a, b in PETERSEN_EDGES if a == v} | {a for a, b in PETERSEN_EDGES if b == v})
            for v in range(10)]

# (L, N, record of each vertex, elimination order)
CYCLES = [
    (13, [[12, 1, 4], [0, 2, 10], [1, 3, 12], [2, 4, 7], [3, 5, 8], [4, 6], [5, 7, 1], [6, 8, 11], [7, 9, 0], [8, 10, 6], [9, 11, 5], [10, 12, 3], [11, 0, 9]],
     [0, 2, 0, 1, 0, 2, 1, 2, 1, 2, 1, 2, 1], [11, 9, 7, 6, 5, 4, 10, 1, 2, 0, 8, 3, 12]),
    (13, [[12, 1, 8], [0, 2, 5], [1, 3, 7], [2, 4, 0], [3, 5, 12], [4, 6, 10], [5, 7, 3], [6, 8, 11], [7, 9, 4], [8, 10, 6], [9, 11, 1], [10, 12, 2], [11, 0]],
     [0, 1, 0, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [0, 5, 1, 2, 11, 3, 9, 7, 6, 10, 12, 4, 8]),
    (13, [[12, 1, 9], [0, 2, 4], [1, 3, 10], [2, 4, 8], [3, 5, 7], [4, 6, 0], [5, 7, 2], [6, 8, 12], [7, 9, 11], [8, 10, 5], [9, 11, 6], [10, 12, 1], [11, 0, 3]],
     [0, 1, 0, 1, 0, 2, 1, 2, 1, 2, 1, 2, 1], [11, 7, 2, 6, 5, 9, 0, 8, 3, 4, 1, 10, 12]),
    (15, [[14, 1, 6], [0, 2, 11], [1, 3, 5], [2, 4, 9], [3, 5, 14], [4, 6, 13], [5, 7], [6, 8, 3], [7, 9, 1], [8, 10, 0], [9, 11], [10, 12, 4], [11, 13, 8], [12, 14, 2], [13, 0, 7]],
     [0, 1, 0, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [0, 11, 9, 1, 2, 3, 7, 8, 10, 13, 5, 6, 12, 14, 4]),
    (15, [[14, 1], [0, 2, 6], [1, 3, 11], [2, 4], [3, 5, 9], [4, 6, 14], [5, 7, 13], [6, 8, 12], [7, 9, 2], [8, 10, 1], [9, 11], [10, 12, 5], [11, 13, 4], [12, 14], [13, 0, 8]],
     [0, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [3, 2, 7, 13, 5, 6, 11, 1, 0, 9, 4, 8, 10, 12, 14]),
    (15, [[14, 1, 10], [0, 2, 9], [1, 3, 8], [2, 4, 14], [3, 5, 12], [4, 6, 11], [5, 7], [6, 8, 0], [7, 9, 4], [8, 10, 13], [9, 11, 3], [10, 12, 2], [11, 13, 7], [12, 14, 6], [13, 0, 5]],
     [0, 1, 2, 1, 2, 1, 0, 2, 1, 2, 1, 2, 1, 2, 1], [0, 2, 11, 12, 4, 5, 6, 13, 9, 7, 1, 14, 3, 8, 10]),
    (15, [[14, 1, 9], [0, 2, 8], [1, 3], [2, 4, 12], [3, 5, 11], [4, 6, 2], [5, 7, 0], [6, 8], [7, 9, 13], [8, 10, 3], [9, 11], [10, 12, 1], [11, 13, 6], [12, 14, 5], [13, 0, 4]],
     [0, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [3, 2, 9, 5, 13, 7, 8, 1, 0, 6, 11, 4, 10, 12, 14]),
    (15, [[14, 1, 9], [0, 2, 8], [1, 3, 7], [2, 4, 12], [3, 5, 11], [4, 6, 10], [5, 7, 0], [6, 8, 14], [7, 9, 13], [8, 10, 3], [9, 11, 2], [10, 12], [11, 13, 6], [12, 14], [13, 0, 4]],
     [0, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [3, 2, 9, 5, 13, 7, 8, 1, 0, 6, 11, 4, 10, 12, 14]),
    (15, [[14, 1, 8], [0, 2, 7], [1, 3, 12], [2, 4, 6], [3, 5, 10], [4, 6, 0], [5, 7, 14], [6, 8], [7, 9, 4], [8, 10, 2], [9, 11, 1], [10, 12], [11, 13, 5], [12, 14, 9], [13, 0, 3]],
     [0, 1, 0, 2, 0, 2, 0, 2, 1, 2, 1, 2, 1, 2, 1], [3, 2, 9, 13, 11, 5, 4, 12, 0, 14, 6, 7, 1, 10, 8]),
    (16, [[15, 1, 3], [0, 2, 9], [1, 3, 7], [2, 4, 13], [3, 5], [4, 6, 1], [5, 7, 12], [6, 8, 15], [7, 9, 4], [8, 10, 14], [9, 11], [10, 12, 2], [11, 13, 8], [12, 14, 0], [13, 15, 5], [14, 0, 11]],
     [0, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [0, 4, 10, 14, 8, 9, 12, 2, 1, 11, 13, 3, 15, 6, 5, 7]),
    (16, [[15, 1, 7], [0, 2, 13], [1, 3, 11], [2, 4, 10], [3, 5], [4, 6, 15], [5, 7, 14], [6, 8, 12], [7, 9], [8, 10, 1], [9, 11, 0], [10, 12, 5], [11, 13, 4], [12, 14, 9], [13, 15, 3], [14, 0, 8]],
     [0, 2, 0, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [8, 9, 14, 4, 12, 6, 7, 13, 1, 2, 0, 10, 3, 15, 5, 11]),
    (16, [[15, 1, 7], [0, 2, 11], [1, 3, 15], [2, 4, 10], [3, 5, 9], [4, 6, 13], [5, 7, 14], [6, 8, 12], [7, 9, 2], [8, 10, 0], [9, 11, 6], [10, 12, 5], [11, 13, 3], [12, 14, 1], [13, 15, 8], [14, 0]],
     [0, 1, 2, 1, 2, 0, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [0, 2, 8, 14, 3, 12, 7, 6, 10, 9, 4, 5, 11, 1, 13, 15]),
]


def out_lists(N):
    out = [[] for _ in N]
    for v, ins in enumerate(N):
        for u in ins:
            out[u].append(v)
    return out


def has_tt(N):
    n = len(N)
    arc = [[False] * n for _ in range(n)]
    for v, ins in enumerate(N):
        for u in ins:
            arc[u][v] = True
    return any(arc[x][y] and arc[y][z] and arc[x][z]
               for x in range(n) for y in range(n) for z in range(n)
               if len({x, y, z}) == 3)


def strongly_connected(N):
    n, out = len(N), out_lists(N)
    def reach(adj):
        seen, stack = {0}, [0]
        while stack:
            v = stack.pop()
            for w in adj[v]:
                if w not in seen:
                    seen.add(w); stack.append(w)
        return len(seen) == n
    return reach(out) and reach(N)


def acyclic(N, S):
    S = set(S)
    indeg = {v: sum(1 for u in N[v] if u in S) for v in S}
    out = out_lists(N)
    queue = [v for v in S if indeg[v] == 0]
    seen = 0
    while queue:
        v = queue.pop(); seen += 1
        for w in out[v]:
            if w in S:
                indeg[w] -= 1
                if indeg[w] == 0:
                    queue.append(w)
    return seen == len(S)


def two_dicolourable(N):
    n = len(N)
    for mask in range(1 << (n - 1)):          # vertex n-1 always in the second class
        A = [v for v in range(n) if mask >> v & 1]
        B = [v for v in range(n) if not mask >> v & 1]
        if acyclic(N, A) and acyclic(N, B):
            return True
    return False


def minimum_cores(N):
    n = len(N)
    for k in range(1, n + 1):
        cores = [set(H) for H in itertools.combinations(range(n), k)
                 if all(sum(1 for u in N[v] if u not in H) <= 1 for v in H)]
        if cores:
            return cores
    return []


def record_partitions(k, m):
    """All partitions of k positions into at most m records, each listed once (records numbered
    in order of first use; the unused record numbers are empty records)."""
    def rec(prefix, top):
        if len(prefix) == k:
            yield tuple(prefix)
            return
        for c in range(min(top + 2, m)):
            yield from rec(prefix + [c], max(top, c))
    yield from rec([], -1)


def piece_certificate(N, H, m):
    """Search for a piece certificate of H in context {} with m records (empty records allowed):
    records partitioning H, an elimination order, a supplying record b(v) != own record at every
    vertex with the parents of v inside H that are not yet eliminated in record b(v), at most one
    parent outside H per vertex (its outside parent), and nested charges: if two consecutive steps
    have the same outside parent w, the earlier step's supply plus its vertex lies in the later
    step's supply. Co-supplied outside parents are a special case of nested ones. Returns a
    certificate (records, order, supplying records) or None, and the number of search nodes."""
    H = sorted(H)
    Hs = set(H)
    outside = {}
    for v in H:
        o = [u for u in N[v] if u not in Hs]
        if len(o) > 1:
            return None, 0
        outside[v] = o[0] if o else None
    inner = {v: {u for u in N[v] if u in Hs} for v in H}
    nodes = 0
    for labels in record_partitions(len(H), m):
        a = dict(zip(H, labels))
        P = [frozenset(v for v in H if a[v] == i) for i in range(m)]
        trail = []

        def dfs(S, last):
            nonlocal nodes
            nodes += 1
            if len(S) == len(H):
                return True
            for v in H:
                if v in S:
                    continue
                todo = inner[v] - S
                w = outside[v]
                for b in range(m):
                    if b == a[v] or not todo <= P[b]:
                        continue
                    Q = S | P[b]
                    if w is not None and w in last and not last[w] <= Q:
                        continue
                    nxt = dict(last)
                    if w is not None:
                        nxt[w] = Q | {v}
                    trail.append((v, b))
                    if dfs(S | {v}, nxt):
                        return True
                    trail.pop()
            return False

        if dfs(frozenset(), {}):
            return (labels, [v for v, _ in trail], [b for _, b in trail]), nodes
    return None, nodes


def check_piece(N, U, H, records, order, supplies):
    """Check a piece certificate for H in context U step by step: the records are pairwise disjoint
    with union H, the list is a listing of H without repetitions, every supplying record differs from
    the own record, (C1) every parent of v_t lies in U, in the supply Q_t (the revealed set plus the
    supplying record) or is the single outside parent of v_t, a vertex outside U and H, and (C2) if
    two consecutive steps have the same outside parent, the earlier supply plus its vertex lies in
    the later supply. Returns (outside parents, co-supplied?) or None if a condition fails."""
    U, H = set(U), set(H)
    if any(records[i] & records[j] for i in range(len(records)) for j in range(i)):
        return None
    if set().union(*records) != H or len(order) != len(H) or set(order) != H:
        return None
    own = {v: i for i, P in enumerate(records) for v in P}
    parent, last, supplies_of = {}, {}, {}
    S = set()
    for v, b in zip(order, supplies):
        if b == own[v]:
            return None
        Q = S | records[b]
        rest = set(N[v]) - U - Q
        if len(rest) > 1 or rest & H:
            return None                               # (C1)
        if rest:
            w = rest.pop()
            parent[v] = w
            if w in last and not last[w] <= Q:
                return None                           # (C2)
            last[w] = Q | {v}
            supplies_of.setdefault(w, set()).add(b)
        S.add(v)
    return parent, all(len(bs) == 1 for bs in supplies_of.values())


def private_proper_pieces(N):
    """The sets H with {} != H != V such that (a) every vertex of H has at most one parent outside H
    and (b) every vertex outside H is a parent of at most one vertex of H (exhaustive)."""
    n, out = len(N), out_lists(N)
    found = []
    for mask in range(1, (1 << n) - 1):
        H = {v for v in range(n) if mask >> v & 1}
        if all(sum(1 for u in N[v] if u not in H) <= 1 for v in H) and \
           all(sum(1 for w in out[u] if w in H) <= 1 for u in range(n) if u not in H):
            found.append(H)
    return found


def sweep_valid(L, N, z, d):
    order = [(z + d * k) % L for k in range(L)]
    pos = {v: i for i, v in enumerate(order)}
    par = list(range(L))
    def find(a):
        while par[a] != a:
            a = par[a]
        return a
    for v in order:
        later = [u for u in N[v] if pos[u] > pos[v]]
        for u in later[1:]:
            par[find(u)] = find(later[0])
    cls = [find(v) for v in range(L)]
    return all(cls[v] != cls[(v + 1) % L] for v in range(L))


def check_certificate(N, rec, order):
    pos = {v: i for i, v in enumerate(order)}
    if sorted(order) != list(range(len(N))):
        return False
    for v in order:
        later = {rec[u] for u in N[v] if pos[u] > pos[v]}
        if len(later) > 1 or rec[v] in later:
            return False
    return True


def global_certificate_search(N):
    """Is there a global elimination certificate with any number of records? Search over all
    elimination orders (depth first, every unplaced vertex tried at every node). The later parents
    of each placed vertex are forced into one record (union-find) and the vertex's own record must
    differ from theirs; a node is pruned as soon as two forced-different vertices share a record.
    With unboundedly many records these forced conditions are also sufficient. Returns the answer
    and the number of search nodes."""
    n = len(N)
    nodes = 0

    def find(p, x):
        while p[x] != x:
            x = p[x]
        return x

    def dfs(placed, p, ineq):
        nonlocal nodes
        nodes += 1
        if len(placed) == n:
            return True
        for v in range(n):
            if v in placed:
                continue
            later = [u for u in N[v] if u not in placed and u != v]
            if v in N[v]:
                continue                         # a loop can never be supplied
            p2 = list(p)
            for x in later[1:]:
                ra, rb = find(p2, later[0]), find(p2, x)
                if ra != rb:
                    p2[ra] = rb
            ineq2 = ineq + [(v, later[0])] if later else ineq
            if any(find(p2, x) == find(p2, y) for x, y in ineq2):
                continue
            if dfs(placed | {v}, p2, ineq2):
                return True
        return False

    return dfs(frozenset(), list(range(n)), []), nodes


def gf2_kernel_dim(rows, n):
    rank, rows = 0, list(rows)
    for bit in range(n):
        piv = next((i for i in range(rank, len(rows)) if rows[i] >> bit & 1), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i] >> bit & 1:
                rows[i] ^= rows[rank]
        rank += 1
    return n - rank


def folded_cube_kernel(k):
    n = 1 << (2 * k)
    gens = [1 << i for i in range(2 * k)] + [n - 1]
    rows = []
    for v in range(n):
        r = 1 << v
        for g in gens:
            r ^= 1 << (v ^ g)
        rows.append(r)
    return gf2_kernel_dim(rows, n), n // 2 + (1 << (k - 1))


def ok(message, condition):
    assert condition, message
    print(message + ": OK")


def main():
    start = time.perf_counter()
    ok("Z9: no set H with {} != H != Z9 satisfies (a) and (b) of Proposition 7.1 (exhaustive over 2^9 sets)",
       private_proper_pieces(D9) == [])
    H1, recs, order, sup = D9_PIECE
    res = check_piece(D9, set(), H1, recs, order, sup)
    ok("Z9: the piece certificate of Example 7.2 satisfies (C1) and (C2), with outside parents %s, "
       "co-supplied" % ", ".join("%d -> %d" % (w, v) for v, w in sorted(res[0].items())) if res else "Z9: Example 7.2",
       res is not None and res[0] == D9_OUTSIDE and res[1])
    U = set(H1)
    for H, recs, order, sup in D9_REST:
        assert check_piece(D9, U, H, recs, order, sup) is not None
        U |= H
    ok("Z9: the pieces {4} and {7, 8} complete the decomposition of Example 7.2", U == set(range(9)))
    recs, order = D9_GLOBAL
    rec = [next(i for i, P in enumerate(recs) if v in P) for v in range(9)]
    ok("Z9: the printed 3-record global elimination certificate is valid",
       sorted(v for P in recs for v in P) == list(range(9)) and check_certificate(D9, rec, order))
    N = X15
    out = out_lists(N)
    ok("X15: loopless", all(v not in N[v] for v in range(len(N))))
    ok("X15: max in-degree %d, max out-degree %d (at most 3)" % (max(map(len, N)), max(map(len, out))),
       max(map(len, N)) <= 3 and max(map(len, out)) <= 3)
    ok("X15: no transitive triangle, strongly connected, not 2-dicolourable",
       not has_tt(N) and strongly_connected(N) and not two_dicolourable(N))
    cores = minimum_cores(N)
    ok("X15: minimum nonempty cores %s (the hexagon only)" % [sorted(H) for H in cores], cores == [set(range(6))])
    cert, nodes = piece_certificate(N, range(6), 7)
    ok("X15: the hexagon has no piece certificate in context {} with at most 7 records, nested or "
       "co-supplied outside parents (exhaustive: %d record partitions, %d search nodes)"
       % (sum(1 for _ in record_partitions(6, 7)), nodes), cert is None)
    cert, _ = piece_certificate(N, X15_PIECE, 3)
    ok("X15 control: the piece %s has a certificate with 3 records" % X15_PIECE, cert is not None)
    ok("X15: the printed 3-record global elimination certificate is valid",
       check_certificate(N, *X15_GLOBAL))
    for L, NC, rec, order in CYCLES:
        assert all(v not in NC[v] and (v - 1) % L in NC[v] and (v + 1) % L in NC[v] for v in range(L))
        chords = [(u, v) for v in range(L) for u in NC[v] if u not in ((v - 1) % L, (v + 1) % L)]
        assert all(v not in NC[u] for u, v in chords)
        assert len({u for u, _ in chords}) == len(chords) == len({v for _, v in chords})
        assert not has_tt(NC)
        assert not any(sweep_valid(L, NC, z, d) for z in range(L) for d in (1, -1))
        assert check_certificate(NC, rec, order)
    ok("chorded cycles: %d checked (loopless digon cycles, one-way chords, at most one chord into and "
       "out of every vertex, no transitive triangle, no valid sweep among the 2L sweeps, a 3-record "
       "certificate each)" % len(CYCLES), True)
    found, nodes = global_certificate_search(PETERSEN)
    ok("Petersen: no global elimination certificate with any number of records (exhaustive search "
       "over all elimination orders, %d search nodes)" % nodes, not found)
    found, _ = global_certificate_search(X15)
    ok("Petersen control: the same search finds a global certificate of X15", found)
    for k in (2, 3):
        dim, formula = folded_cube_kernel(k)
        ok("folded cube k = %d: dim ker(I + A) = %d = N/2 + 2^(k-1)" % (k, dim), dim == formula)
    print("all checks passed in %.1f s" % (time.perf_counter() - start))


if __name__ == "__main__":
    main()
