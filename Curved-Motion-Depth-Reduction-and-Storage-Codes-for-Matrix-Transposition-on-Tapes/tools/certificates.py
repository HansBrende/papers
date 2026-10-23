"""Exact Shannon certificates for rate bounds h(V) <= lam * sum_v h(v) on valid polymatroids,
printed as Lean proofs for the MotionDepthCodes library.

Usage (from the paper directory, with numpy and scipy installed):

    python3 tools/certificates.py GRAPH LAM_NUM LAM_DEN PREFIX NBHD_NAME [--trivial] [--all-pairs]

GRAPH is C5, petersen, clebsch or Kp/q (circular clique). PREFIX names the
automorphisms; NBHD_NAME is the Lean neighbourhood table they must preserve.

By default the polymatroid is symmetrized over the full automorphism group
(computed by backtracking). The proof starts with `RateBound.of_invariant` and
uses one elemental inequality per orbit row, closure equalities
(`eq_of_closure`), and invariance equalities h(sigma R) = h(R) for explicit
automorphisms sigma. With --trivial no symmetrization is used. Rows use only
non-adjacent pairs unless --all-pairs is given (needed for Clebsch at 5/8).

A sparse candidate is found by linear programming (HiGHS) and re-solved exactly
in rationals on its support; the exact identity is checked before printing. The
proof ends with `linear_combination` and exact rational coefficients, so Lean
re-checks the identity. The output has the automorphism definitions, a line
"-- PROOF", then the tactic proof. Different solver versions may print a
different certificate; any printed certificate is valid, and the Lean files are
the checked record.
"""
import sys
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix, hstack, identity

sys.setrecursionlimit(10000)


def graph(name):
    if name == "C5":
        n = 5; E = [(i, (i + 1) % 5) for i in range(5)]
    elif name == "petersen":
        n = 10
        E = [(0, 1), (0, 4), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7), (3, 4), (3, 8), (4, 9),
             (5, 7), (5, 8), (6, 8), (6, 9), (7, 9)]
    elif name == "clebsch":
        n = 16
        E = [(a, b) for a in range(16) for b in range(a + 1, 16)
             if bin(a ^ b).count("1") == 1 or a ^ b == 15]
    elif name.startswith("K") and "/" in name:
        p, q = map(int, name[1:].split("/")); n = p
        E = [(i, j) for i in range(p) for j in range(i + 1, p) if q <= (j - i) % p <= p - q]
    else:
        raise ValueError(name)
    nb = [0] * n
    for a, b in E:
        nb[a] |= 1 << b; nb[b] |= 1 << a
    return n, nb


def automorphisms(n, nb):
    adj = [[bool(nb[a] >> b & 1) for b in range(n)] for a in range(n)]
    deg = [bin(x).count("1") for x in nb]
    res, perm, used = [], [-1] * n, [False] * n

    def rec(k):
        if k == n:
            res.append(tuple(perm)); return
        for img in range(n):
            if used[img] or deg[img] != deg[k]:
                continue
            if all(adj[u][k] == adj[perm[u]][img] for u in range(k)):
                perm[k] = img; used[img] = True
                rec(k + 1)
                used[img] = False; perm[k] = -1
    rec(0)
    return res


def apply(perm, S, n):
    T = 0
    for v in range(n):
        if S >> v & 1:
            T |= 1 << perm[v]
    return T


def main():
    name, lam = sys.argv[1], Fraction(int(sys.argv[2]), int(sys.argv[3]))
    prefix, nbname = sys.argv[4], sys.argv[5]
    n, nb = graph(name)
    full = (1 << n) - 1
    auts = [tuple(range(n))] if "--trivial" in sys.argv else automorphisms(n, nb)
    print(f"-- {name}: |Aut| = {len(auts)}", file=sys.stderr)
    # closure
    clc = {}

    def nxt(S):
        T = S
        for v in range(n):
            if nb[v] & ~S == 0:
                T |= 1 << v
        return T

    def cl(S):
        if S in clc:
            return clc[S]
        T = S
        while True:
            U = nxt(T)
            if U == T:
                break
            T = U
        clc[S] = T
        return T

    # orbit representatives via numpy over all closed sets met
    lo = np.array([[sum(1 << p[v] for v in range(min(8, n)) if b >> v & 1) for b in range(256)] for p in auts],
                  dtype=np.int64)
    hi = np.array([[sum(1 << p[v + 8] for v in range(n - 8) if b >> v & 1) for b in range(256)] for p in auts],
                  dtype=np.int64) if n > 8 else None
    repc = {}

    def reps(masks):
        arr = np.array(masks, dtype=np.int64)
        best = arr.copy()
        for g in range(len(auts)):
            img = lo[g][arr & 255]
            if hi is not None:
                img = img | hi[g][(arr >> 8) & 255]
            best = np.minimum(best, img)
        for m, b in zip(masks, best.tolist()):
            repc[m] = b

    # vertex orbit representatives
    vrep = {}
    for v in range(n):
        vrep[v] = min(p[v] for p in auts)
    ireps = sorted(set(vrep.values()))
    # rows
    raw_rows = []
    closed_needed = set()
    for i in ireps:
        for j in range(n):
            if j == i or (nb[i] >> j & 1 and "--all-pairs" not in sys.argv):
                continue
            bi, bj = 1 << i, 1 << j
            rest = full & ~(bi | bj)
            sub = rest
            while True:
                sets = (sub | bi | bj, sub, sub | bi, sub | bj)
                cls = tuple(cl(S) for S in sets)
                raw_rows.append((i, j, sub, cls))
                closed_needed.update(cls)
                if sub == 0:
                    break
                sub = (sub - 1) & rest
    closed_needed.add(full)
    for v in range(n):
        closed_needed.add(cl(1 << v))
    closed_list = sorted(closed_needed)
    reps(closed_list)
    var = {}
    for c in closed_list:
        r = repc[c]
        if r != 0 and r not in var:
            var[r] = len(var)

    def vid(c):
        r = repc[c]
        return None if r == 0 else var[r]

    rows = {}
    for (i, j, sub, cls) in raw_rows:
        coef = {}
        for c, s in zip(cls, (1, 1, -1, -1)):
            x = vid(c)
            if x is not None:
                coef[x] = coef.get(x, 0) + s
        key = tuple(sorted((x, s) for x, s in coef.items() if s != 0))
        if key:
            sz = bin(sub).count("1")
            if key not in rows or sz < rows[key][3]:
                rows[key] = (i, j, sub, sz)
    nv = len(var)
    keys = list(rows)
    print(f"-- rows {len(keys)} orbit variables {nv}", file=sys.stderr)
    I, J, Vv = [], [], []
    for r, key in enumerate(keys):
        for x, s in key:
            I.append(x); J.append(r); Vv.append(s)
    AT = coo_matrix((Vv, (I, J)), shape=(nv, len(keys))).tocsr()
    target = [Fraction(0)] * nv
    target[vid(full)] += 1
    for v in range(n):
        target[vid(cl(1 << v))] -= lam
    Aeq = hstack([AT, -identity(nv)]).tocsr()
    w = np.concatenate([1.0 + np.array([rows[k][3] for k in keys], dtype=float), np.full(nv, 1.0)])
    res = linprog(w, A_eq=Aeq, b_eq=np.array([float(t) for t in target]), bounds=(0, None), method="highs-ds")
    print(f"-- LP status {res.status}", file=sys.stderr)
    if res.status != 0:
        sys.exit(1)
    y, mu = res.x[:len(keys)], res.x[len(keys):]
    cols = [("y", k) for k in range(len(keys)) if y[k] > 1e-9] + [("m", s) for s in range(nv) if mu[s] > 1e-9]
    M = [[Fraction(0)] * len(cols) for _ in range(nv)]
    for c, (t, k) in enumerate(cols):
        if t == "y":
            for x, s in keys[k]:
                M[x][c] += s
        else:
            M[k][c] -= 1
    guess = [Fraction(res.x[k] if t == "y" else res.x[len(keys) + k]).limit_denominator(1000) for t, k in cols]
    sol = exact_solve(M, target, guess)
    chk = [Fraction(0)] * nv
    for c, (t, k) in enumerate(cols):
        assert sol[c] >= 0, "negative weight"
        if t == "y":
            for x, s in keys[k]:
                chk[x] += sol[c] * s
        else:
            chk[k] -= sol[c]
    assert chk == target, "exact identity fails"
    inv_var = {x: r for r, x in var.items()}
    used = [(sol[c], rows[keys[k]]) for c, (t, k) in enumerate(cols) if t == "y" and sol[c] != 0]
    mused = [(sol[c], inv_var[k]) for c, (t, k) in enumerate(cols) if t == "m" and sol[c] != 0]
    print(f"-- exact certificate: {len(used)} orbit rows, {len(mused)} nonnegativity terms, "
          f"weights {sorted(set(str(u[0]) for u in used))}", file=sys.stderr)
    emit(prefix, nbname, n, nb, full, auts, used, mused, lam, cl, nxt, repc)


def exact_solve(M, rhs, guess):
    m = len(M); k = len(M[0])
    A = [row[:] + [rhs[r]] for r, row in enumerate(M)]
    piv, r = [], 0
    for c in range(k):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = 1 / A[r][c]
        A[r] = [a * inv for a in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c); r += 1
        if r == m:
            break
    x = [None] * k
    free = [c for c in range(k) if c not in piv]
    for c in free:
        x[c] = guess[c]
    for i, c in enumerate(piv):
        x[c] = A[i][k] - sum(A[i][f] * x[f] for f in free)
    for i in range(len(piv), m):
        assert A[i][k] - sum(A[i][f] * x[f] for f in free) == 0, "inconsistent"
    return x


def lit(S, n, full):
    if S == full:
        return "univ"
    if S == 0:
        return "∅"
    return "{" + ", ".join(str(v) for v in range(n) if S >> v & 1) + "}"


def frac(q):
    return f"({q.numerator} : ℝ)" if q.denominator == 1 else f"({q.numerator} / {q.denominator} : ℝ)"


def emit(prefix, nbname, n, nb, full, auts, used, mused, lam, cl, nxt, repc):
    L = lambda S: lit(S, n, full)
    facts = []          # (name, lean text)
    coef = {}           # residual coefficient per atom (set mask): R = T - E + sum mu h(S)
    def addc(S, c):
        coef[S] = coef.get(S, 0) + c
    # target T = h univ - lam * sum h{v}
    addc(full, Fraction(1))
    for v in range(n):
        addc(1 << v, -lam)
    elems = []
    for k, (wt, (i, j, K, _)) in enumerate(used):
        A, B, U = K | 1 << i, K | 1 << j, K | 1 << i | 1 << j
        nm = f"e{k + 1}"
        facts.append((nm, f"  have {nm} : h {L(U)} + h {L(K)} ≤ h {L(A)} + h {L(B)} := "
                          f"hh.elemental (by decide) (by decide)"))
        elems.append((nm, wt))
        for S, s in ((U, 1), (K, 1), (A, -1), (B, -1)):
            addc(S, -wt * s)
    nonnegs = []
    for k, (wt, S) in enumerate(mused):
        nm = f"n{k + 1}"
        facts.append((nm, f"  have {nm} := hh.nonneg {L(S)}"))
        nonnegs.append((nm, wt))
        addc(S, wt)
    # forest: parent of each atom, with fact orientation
    parent = {}         # X -> (P, factname, sign) ; sign = +1 if fact is "h X = h P", -1 if "h P = h X"
    aut_used = []       # list of perms (tuples)
    aut_index = {}
    def get_aut(R, T):
        """an automorphism sigma with sigma(R) = T, reusing used ones when possible"""
        for idx, p in enumerate(aut_used):
            if apply(p, R, n) == T:
                return idx
        for p in auts:
            if apply(p, R, n) == T:
                aut_used.append(p)
                return len(aut_used) - 1
        raise AssertionError("no automorphism")
    todo = list(coef)
    seen = set()
    cnt = [0, 0]
    while todo:
        X = todo.pop()
        if X in seen:
            continue
        seen.add(X)
        if X == 0:
            continue
        c = cl(X)
        if X != c:
            P = nxt(X)
            cnt[0] += 1
            nm = f"c{cnt[0]}"
            facts.append((nm, f"  have {nm} : h {L(P)} = h {L(X)} := hh.eq_of_closure hv (by decide) (by decide)"))
            parent[X] = (P, nm, -1)
            todo.append(P)
        else:
            R = repc[c] if c in repc else None
            if R is None:
                raise AssertionError("missing rep")
            if R != X:
                g = get_aut(R, X)
                cnt[1] += 1
                nm = f"s{cnt[1]}"
                facts.append((nm, f"  have {nm} : h {L(X)} = h {L(R)} := by\n"
                                  f"    have h1 := hinv {prefix}Aut{g} {prefix}Aut{g}_isAut {L(R)}\n"
                                  f"    rwa [show ({L(R)} : Finset (Fin {n})).map {prefix}Aut{g}.toEmbedding = {L(X)} by decide] at h1"))
                parent[X] = (R, nm, 1)
                todo.append(R)
    # coefficients: process nodes in order of decreasing depth
    depth = {}
    def dep(X):
        if X in depth:
            return depth[X]
        d = 0 if X not in parent else dep(parent[X][0]) + 1
        depth[X] = d
        return d
    for X in list(coef) + list(parent):
        dep(X)
    acc = dict(coef)
    fcoef = {}
    for X in sorted(parent, key=lambda X: -depth[X]):
        P, nm, s = parent[X]
        r = acc.get(X, Fraction(0))
        # contribution at X must equal r: s * c = r  ->  c = s * r  (s = +-1); parent receives -s*c = -r
        cX = s * r
        fcoef[nm] = cX
        acc[X] = Fraction(0)
        acc[P] = acc.get(P, Fraction(0)) + r
    # roots must balance (empty set handled by h0)
    c0 = acc.get(0, Fraction(0))
    for X, r in acc.items():
        if X != 0 and X not in parent and r != 0:
            raise AssertionError(f"unbalanced root {L(X)}: {r}")
    # print automorphism definitions
    defs = []
    for g, p in enumerate(aut_used):
        inv = [0] * n
        for a, b in enumerate(p):
            inv[b] = a
        defs.append(f"/-- An automorphism used by the certificate. -/\n"
                    f"def {prefix}Aut{g} : Equiv.Perm (Fin {n}) where\n"
                    f"  toFun := ![{', '.join(map(str, p))}]\n"
                    f"  invFun := ![{', '.join(map(str, inv))}]\n"
                    f"  left_inv := by intro x; revert x; decide\n"
                    f"  right_inv := by intro x; revert x; decide\n\n"
                    f"theorem {prefix}Aut{g}_isAut : IsAut {nbname} {prefix}Aut{g} := by\n  decide\n")
    print("\n".join(defs))
    print("-- PROOF")
    if len(auts) > 1:
        print("  apply RateBound.of_invariant")
        print("  intro h hh hv hinv")
    else:
        print("  intro h hh hv")
    for nm, txt in facts:
        print(txt)
    print("  have h0 := hh.empty")
    print(f"  simp only [sum_fin_{n}]")
    terms = [f"{frac(w)} * {nm}" for nm, w in elems]
    terms += [f"{frac(w)} * {nm}" for nm, w in nonnegs]
    terms += [f"{frac(c)} * {nm}" for nm, c in fcoef.items() if c != 0]
    if c0 != 0:
        terms.append(f"{frac(c0)} * h0")
    lines, cur = [], "  linear_combination"
    for t in terms:
        piece = (" " if cur.endswith("linear_combination") else " + ") + t
        if len(cur) + len(piece) > 98:
            lines.append(cur + (" +" if not cur.endswith("linear_combination") else ""))
            cur = "    " + t
        else:
            cur += piece
    lines.append(cur)
    print("\n".join(lines))
    print(f"-- facts: {len(elems)} elementals, {cnt[0]} closure steps, {cnt[1]} invariance steps, "
          f"{len(aut_used)} automorphisms", file=sys.stderr)


if __name__ == "__main__":
    main()
