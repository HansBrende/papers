"""a5_checks.py -- exact checks of the finite group theory of the paper's lemma on A5 acting on the projective
line (A5 in PGL2 over the algebraic closure of F3). Pure Python. Run:  python3 tools/a5_checks.py

Checks:
 (1) subgroups A5 of PGL2(F9): count, conjugacy classes under PGL2(F9) and PSL2(F9), normaliser order;
 (2) injective homomorphisms A5 -> PGL2(F9) up to PGL2(F9)-conjugation (expect 2), and Frobenius swaps them;
 (3) centraliser of A5 in PGL2(F81) (expect trivial);
 (4) orbit sizes of A5 on P^1(F_{3^m}), m = 2, 4, 6, 8 (non-free orbits must already live in P^1(F81));
 (5) stabiliser of each point of P^1(F9) is S3, S3 self-normalising, 10 distinct stabilisers;
 (6) tr^2/det of order-5 elements (two classes, values = squares of the two roots of x^2+x-1).
GF(3^m) via exp/log tables of a primitive element.
"""
import itertools


def polymulmod(a, b, f):
    m = len(f) - 1
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % 3
    for k in range(len(r) - 1, m - 1, -1):
        c = r[k]
        if c:
            for i in range(m + 1):
                r[k - m + i] = (r[k - m + i] - c * f[i]) % 3
    return (r + [0] * m)[:m]


class GF:
    def __init__(self, m):
        self.m, self.q = m, 3 ** m
        for coeffs in itertools.product(range(3), repeat=m):
            f = list(coeffs) + [1]
            if f[0] == 0:
                continue
            # try x as primitive element: order of x must be q-1
            x = [0, 1] + [0] * (m - 2) if m >= 2 else [None]
            if m == 1:
                continue
            cur = [1] + [0] * (m - 1)
            seen = set()
            exp = []
            ok = True
            for k in range(self.q - 1):
                t = self.toint(cur)
                if t in seen:
                    ok = False
                    break
                seen.add(t)
                exp.append(t)
                cur = polymulmod(cur, x, f)
            if ok and self.toint(cur) == 1 and len(seen) == self.q - 1:
                self.f = f
                self.exp = exp
                break
        self.log = [None] * self.q
        for k, t in enumerate(self.exp):
            self.log[t] = k
        self.dig = [tuple((i // 3 ** k) % 3 for k in range(m)) for i in range(self.q)]
        self.p3 = [3 ** k for k in range(m)]

    def toint(self, v):
        return sum(c * 3 ** k for k, c in enumerate(v))

    def M(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[(self.log[a] + self.log[b]) % (self.q - 1)]

    def A(self, a, b):
        da, db = self.dig[a], self.dig[b]
        return sum(((x + y) % 3) * p for x, y, p in zip(da, db, self.p3))

    def N(self, a):
        return sum(((-x) % 3) * p for x, p in zip(self.dig[a], self.p3))

    def S(self, a, b):
        return self.A(a, self.N(b))

    def inv(self, a):
        return self.exp[(-self.log[a]) % (self.q - 1)]

    def frob(self, a):
        return 0 if a == 0 else self.exp[(3 * self.log[a]) % (self.q - 1)]


def embedding(Fs, Fb):
    """field embedding Fs -> Fb sending the primitive element of Fs to a power of that of Fb."""
    k = (Fb.q - 1) // (Fs.q - 1)
    g = Fb.exp[k]  # element of order q_s - 1
    # find j with g^j satisfying the minimal polynomial f_s of Fs's generator
    for j in range(Fs.q - 1):
        r = Fb.exp[(k * j) % (Fb.q - 1)]
        acc, pw = 0, 1
        for c in Fs.f:
            for _ in range(c):
                acc = Fb.A(acc, pw)
            pw = Fb.M(pw, r)
        if acc == 0:
            emb = [0] + [Fb.exp[(k * j * e) % (Fb.q - 1)] for e in range(Fs.q - 1)]
            # emb indexed by log: element exp[e] of Fs -> r^e
            table = [0] * Fs.q
            for e in range(Fs.q - 1):
                table[Fs.exp[e]] = emb[e + 1]
            for a in range(Fs.q):
                for b in range(Fs.q):
                    assert table[Fs.M(a, b)] == Fb.M(table[a], table[b])
                    assert table[Fs.A(a, b)] == Fb.A(table[a], table[b])
            return table
    raise ValueError


F9 = GF(2)


def mm(F, X, Y):
    a, b, c, d = X
    e, f, g, h = Y
    return (F.A(F.M(a, e), F.M(b, g)), F.A(F.M(a, f), F.M(b, h)), F.A(F.M(c, e), F.M(d, g)), F.A(F.M(c, f), F.M(d, h)))


def det(F, X):
    a, b, c, d = X
    return F.S(F.M(a, d), F.M(b, c))


def normp(F, X):
    for x in X:
        if x:
            ix = F.inv(x)
            return tuple(F.M(ix, y) for y in X)
    raise ValueError


GL = [X for X in itertools.product(range(9), repeat=4) if det(F9, X) != 0]
PGL = sorted(set(normp(F9, X) for X in GL))
assert len(PGL) == 720
idx = {X: i for i, X in enumerate(PGL)}
mult = [[idx[normp(F9, mm(F9, X, Y))] for Y in PGL] for X in PGL]
ID = idx[normp(F9, (1, 0, 0, 1))]
inv = [next(j for j in range(720) if mult[i][j] == ID) for i in range(720)]


def order(i):
    k, x = 1, i
    while x != ID:
        x = mult[x][i]
        k += 1
    return k


ords = [order(i) for i in range(720)]
sq9 = set(F9.M(a, a) for a in range(1, 9))
PSL = [i for i, X in enumerate(PGL) if det(F9, X) in sq9]
assert len(PSL) == 360
PSLs = set(PSL)


def gen(gens):
    S, fr = {ID}, [ID]
    while fr:
        nf = []
        for x in fr:
            for g in gens:
                y = mult[x][g]
                if y not in S:
                    S.add(y)
                    nf.append(y)
        fr = nf
    return frozenset(S)


def conj(g, H):
    return frozenset(mult[mult[g][h]][inv[g]] for h in H)


subs, pairs = set(), []
for a in (i for i in range(720) if ords[i] == 2):
    for b in (i for i in range(720) if ords[i] == 3):
        if ords[mult[a][b]] == 5:
            H = gen([a, b])
            if len(H) == 60:
                subs.add(H)
                pairs.append((a, b))
print("(1) A5 subgroups of PGL2(F9):", len(subs), "; all inside PSL2(F9):", all(H <= PSLs for H in subs))


def classes(group, sets):
    seen, cls = set(), []
    for H in sets:
        if H in seen:
            continue
        orb = {conj(g, H) for g in group}
        seen |= orb
        cls.append(orb)
    return cls


cP, cS = classes(range(720), subs), classes(PSL, subs)
print("    classes under PGL2(F9):", [len(c) for c in cP], "; under PSL2(F9):", [len(c) for c in cS])
H0 = next(iter(subs))
print("    |N_PGL2(F9)(A5)| =", sum(1 for g in range(720) if conj(g, H0) == H0))

seen, orbs = set(), []
for pr in pairs:
    if pr in seen:
        continue
    orb = {(mult[mult[g][pr[0]]][inv[g]], mult[mult[g][pr[1]]][inv[g]]) for g in range(720)}
    seen |= orb
    orbs.append(orb)
print("(2) injective homs A5 -> PGL2(F9):", len(pairs), "; PGL2(F9)-conjugacy classes:", [len(o) for o in orbs])


def frobX(i):
    return idx[normp(F9, tuple(F9.frob(x) for x in PGL[i]))]


pr = next(iter(orbs[0]))
print("    Frobenius sends class 0 to class", [k for k, o in enumerate(orbs) if (frobX(pr[0]), frobX(pr[1])) in o])

roots = [x for x in range(9) if F9.A(F9.A(F9.M(x, x), x), 2) == 0]  # x^2 + x - 1
print("(6) roots of x^2+x-1 in F9:", roots, "; Frobenius-conjugate:", F9.frob(roots[0]) == roots[1])
for k, o in enumerate(orbs):
    a, b = next(iter(o))
    c = mult[a][b]  # order 5: the image of st
    X = PGL[c]
    t = F9.A(X[0], X[3])
    v = F9.M(F9.M(t, t), F9.inv(det(F9, X)))
    print(f"    class {k}: tr^2/det of image of st (order 5) =", v, "; squares of roots:", [F9.M(r, r) for r in roots])

P1 = [(1, x) for x in range(9)] + [(0, 1)]


def act(F, X, pt):
    a, b, c, d = X
    x, y = pt
    u, v = F.A(F.M(a, x), F.M(b, y)), F.A(F.M(c, x), F.M(d, y))
    if u:
        return (1, F.M(F.inv(u), v))
    return (0, 1)


stabs = [frozenset(h for h in H0 if act(F9, PGL[h], pt) == pt) for pt in P1]
S3 = stabs[0]
print("(5) stabiliser orders of the 10 points of P^1(F9):", sorted(len(s) for s in stabs),
      "; distinct stabilisers:", len(set(stabs)), "; element orders in a stabiliser:", sorted(ords[s] for s in S3),
      "; |N_A5(S3)| =", sum(1 for h in H0 if conj(h, S3) == S3))
# each S3 fixes exactly one point of P^1(F9)
print("    points of P^1(F9) fixed by each stabiliser S3:",
      sorted(sum(1 for pt in P1 if all(act(F9, PGL[h], pt) == pt for h in s)) for s in set(stabs)))

for m in (2, 4, 6, 8):
    Fb = GF(m)
    emb = embedding(F9, Fb)
    Hb = [tuple(emb[x] for x in PGL[h]) for h in H0]
    pts = [(1, x) for x in range(Fb.q)] + [(0, 1)]
    pid = {p: i for i, p in enumerate(pts)}
    perm = [[pid[act(Fb, X, p)] for p in pts] for X in Hb]
    done = [False] * len(pts)
    sizes = {}
    for i in range(len(pts)):
        if not done[i]:
            orb = {perm[k][i] for k in range(60)}
            for j in orb:
                done[j] = True
            sizes[len(orb)] = sizes.get(len(orb), 0) + 1
    print(f"(4) m={m}: |P^1(F_3^{m})| = {len(pts)}; A5-orbit sizes {{size: count}} = {dict(sorted(sizes.items()))}")
    if m == 4:
        a, b = next(iter(orbs[0]))
        ga, gb = tuple(emb[x] for x in PGL[a]), tuple(emb[x] for x in PGL[b])
        cnt = 0
        cand = [(1, b_, c_, d_) for b_ in range(Fb.q) for c_ in range(Fb.q) for d_ in range(Fb.q)] + \
               [(0, 1, c_, d_) for c_ in range(Fb.q) for d_ in range(Fb.q)]
        for X in cand:
            if det(Fb, X) == 0:
                continue
            if all(normp(Fb, mm(Fb, X, g)) == normp(Fb, mm(Fb, g, X)) for g in (ga, gb)):
                cnt += 1
        print("(3) centraliser of A5 in PGL2(F81): order", cnt)
