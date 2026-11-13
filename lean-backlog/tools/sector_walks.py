"""Check of the sector-walk statement (section 13 of row-spread-of-cones.md).

Group G, helper rows rho(r) = r*T.  Cell (c, r), sector g = c^-1 r.
Mutual step: (c, r) -> (c g t, c t'^-1); sector g -> t^-1 g^-1 t'^-1.
Claims checked on small groups, by brute force on the cells:
  (1) the sector of a mutual neighbour is t^-1 g^-1 t'^-1;
  (2) a sector lies on an odd closed sector walk of length l  iff
      g x g = y for some x in T(T^-1 T)^j, y in T^-1(T T^-1)^j, l = 2j+1;
  (3) the number of such sectors is at most w^(2l) * R2, R2 = max number of
      square roots of an element.
Standard library only.
"""
import itertools, random, sys

def compose(p, q):            # (p*q)(i) = p(q(i))
    return tuple(p[i] for i in q)
def inverse(p):
    r = [0]*len(p)
    for i, x in enumerate(p): r[x] = i
    return tuple(r)
def generate(gens):
    n = len(gens[0]); e = tuple(range(n))
    seen = {e}; frontier = [e]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = compose(g, s)
                if h not in seen: seen.add(h); nxt.append(h)
        frontier = nxt
    return sorted(seen)

def groups():
    yield "S4", generate([(1,0,2,3), (1,2,3,0)])
    # Z7 : Z3, odd order 21: x -> x+1, x -> 2x on Z/7
    yield "7:3", generate([tuple((i+1) % 7 for i in range(7)), tuple((2*i) % 7 for i in range(7))])
    yield "A5", generate([(1,2,0,3,4), (0,1,3,4,2), (1,0,3,2,4)])
    # dihedral of order 16 on 8 points
    yield "D8", generate([tuple((i+1) % 8 for i in range(8)), tuple((-i) % 8 for i in range(8))])

def run(name, G, w, rng, lmax=5):
    idx = {g: i for i, g in enumerate(G)}
    mul = lambda a, b: compose(a, b)
    T = rng.sample(G, w)
    Ti = [inverse(t) for t in T]
    # (1) cell-level check
    for _ in range(200):
        c, r = rng.choice(G), rng.choice(G)
        g = mul(inverse(c), r)
        t, t2 = rng.choice(T), rng.choice(T)
        c2, r2 = mul(r, t), mul(c, inverse(t2))
        assert mul(inverse(c2), r2) == mul(mul(inverse(t), inverse(g)), inverse(t2))
        # mutual: c2 in r T, c in r2 T
        assert mul(inverse(r), c2) in T and mul(inverse(r2), c) in T
    # sector graph
    step = {g: {mul(mul(ti, inverse(g)), ti2) for ti in Ti for ti2 in Ti} for g in G}
    R2 = max(sum(1 for h in G if mul(h, h) == z) for z in G)
    out = []
    for l in range(1, lmax + 1, 2):
        # sectors with a closed sector walk of length exactly l
        walk = set()
        for g in G:
            cur = {g}
            for _ in range(l): cur = set().union(*(step[h] for h in cur))
            if g in cur: walk.add(g)
        # word description
        j = (l - 1)//2
        X = set(T); Y = set(Ti)
        for _ in range(j):
            X = {mul(mul(x, ti), t) for x in X for ti in Ti for t in T}
            Y = {mul(mul(y, t), ti) for y in Y for t in T for ti in Ti}
        word = {g for g in G if any(mul(mul(g, x), g) in Y for x in X)}
        assert walk == word, (name, l)
        assert len(walk) <= w**(2*l) * R2
        out.append((l, len(walk)))
    return T, R2, out

rng = random.Random(1)
for name, G in groups():
    for w in (2, 3):
        for trial in range(3):
            T, R2, out = run(name, G, w, rng)
            print(f"{name:4s} d={len(G):3d} w={w} R2={R2:3d} odd-walk sectors by length {out}")
print("all checks passed")
