"""Exact decision for class-uniform rules over GF(2): is there a rule whose code has dimension >= D?

This script reproduces the section "Small sizes" of the paper.  The side length is d in the paper and n here.

Setting (the paper's definition of class-uniform rules).  The rows of an n x n matrix X are x_c, c in Z_n.  A
class-uniform rule for a partition of Z_n is a family of functionals a[J][r] on n x n matrices with
    X[c][r] = <a[J(c)][r], sigma^c X>      for all c, r,          (sigma^c X)[i][j] = X[i][j + c],
where J(c) is the class of c.  The code of the rule is the kernel of the n^2 x n^2 matrix N whose row (c, r) is
    N[(c,r)][(i,j)] = a[J(c)][r][(i, j - c)]  XOR  [(i,j) == (c,r)].
dim code >= D  iff  rank N <= m := n^2 - D  iff  N = C G for some C (n^2 x m) and G (m x n^2).

SAT encoding (CryptoMiniSat through the Python package pycryptosat, native XOR clauses): variables for the
functionals, for C, for G and for the products C[row][k] & G[k][q]; one XOR of length m + 1 per entry of N.  Options:
  --rref     break the GL_m symmetry: G in reduced row echelon form with unknown pivot columns (loses no solutions);
  --hankel   restrict to codes that contain the space of matrices constant along anti-diagonals inside each class
             (rows of G orthogonal to it).  This is a subfamily: "unsatisfiable" with --hankel says nothing about
             the whole family.
A satisfiable answer is verified independently of the solver: the functionals are read off, N is rebuilt, its rank is
recomputed, and the kernel is checked against the criterion "for each class J, sum_{c in J} sigma^c X_c = 0 implies
sum_{c in J} row_c(X_c) = 0".  With --save the rule and a basis of its code are written to a JSON file that
tools/verify_class_uniform_code.py checks from the definition.
An unsatisfiable answer means: no class-uniform rule over GF(2) for this partition has a code of dimension >= D.  It
rests on the solver.  A time-out means nothing.

Usage (needs the Python package pycryptosat):
  python3 tools/class_uniform_sat.py N "0,1,3|2,4,5" D [--rref] [--hankel] [--time SEC] [--threads T] [--save FILE]
Controls: N = 4, "0,1|2,3", D = 12 satisfiable and D = 13 unsatisfiable; N = 4, "0|1,2,3", 12 and 13 likewise;
N = 5, "0,1|2,3|4", D = 20 satisfiable and D = 21 unsatisfiable.  The code of the paper's proposition on classes with
no almost-period: N = 6, "0,1,3|2,4,5", D = 25, --rref (about three minutes), saved in tools/data/.
"""
import argparse, json, sys, time
import pycryptosat


def rank_rows(rows):
    basis = {}
    r = 0
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v; r += 1; break
    return r


def kernel_basis(rows, width):
    """Basis of {x : <row, x> = 0 for all rows} over GF(2); rows and vectors are int bitmasks."""
    piv = {}
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v; break
    # reduce to RREF
    for h in sorted(piv):
        for h2 in piv:
            if h2 != h and piv[h2] >> h & 1:
                piv[h2] ^= piv[h]
    free = [q for q in range(width) if q not in piv]
    out = []
    for f in free:
        x = 1 << f
        for h, v in piv.items():
            if v >> f & 1:
                x |= 1 << h
        out.append(x)
    return out


def chain_bound(n, classes, smax=3):
    import itertools
    cls = {c: k for k, J in enumerate(classes) for c in J}
    best = n * n
    for s in range(1, smax + 1):
        for sh in itertools.combinations(range(1, n), s):
            shifts = (0,) + sh
            diffs = {(a - b) % n for a in shifts for b in shifts if a != b}
            parent = list(range(n))
            def find(x):
                while parent[x] != x:
                    parent[x] = parent[parent[x]]; x = parent[x]
                return x
            for c in range(n):
                for d in diffs:
                    e = (c + d) % n
                    if cls[c] == cls[e]:
                        parent[find(c)] = find(e)
            chi = len({find(c) for c in range(n)})
            best = min(best, (s * n * n + n * chi) // (s + 1))
    return best


def build(n, classes, D, rref, hankel, threads, tlimit, seed):
    N2 = n * n
    m = N2 - D
    cls = {c: k for k, J in enumerate(classes) for c in J}
    M = len(classes)
    nv = [0]
    def new():
        nv[0] += 1
        return nv[0]
    a = [[[new() for _ in range(N2)] for _ in range(n)] for _ in range(M)]          # a[J][r][(i,j)]
    C = [[new() for _ in range(m)] for _ in range(N2)]                              # C[(c,r)][k]
    G = [[new() for _ in range(N2)] for _ in range(m)]                              # G[k][q]
    kw = dict(threads=threads)
    if tlimit:
        kw["time_limit"] = tlimit
    S = pycryptosat.Solver(**kw)
    nclauses = 0
    for c in range(n):
        for r in range(n):
            row = c * n + r
            for i in range(n):
                for j in range(n):
                    q = i * n + j
                    avar = a[cls[c]][r][i * n + (j - c) % n]
                    xs = [avar]
                    for k in range(m):
                        p = new()
                        x, y = C[row][k], G[k][q]
                        S.add_clause([-p, x]); S.add_clause([-p, y]); S.add_clause([p, -x, -y])
                        xs.append(p)
                    # avar XOR [q == row] = XOR_k C & G
                    S.add_xor_clause(xs, q == row)
                    nclauses += 1
    if rref and m > 0:
        piv = [[new() for _ in range(N2)] for _ in range(m)]                        # piv[k][q]: pivot of row k is q
        for k in range(m):
            S.add_clause(piv[k])
            for q in range(N2):
                for q2 in range(q + 1, N2):
                    S.add_clause([-piv[k][q], -piv[k][q2]])
                # pivot entry is 1, earlier entries of the row are 0, other rows vanish in the pivot column
                S.add_clause([-piv[k][q], G[k][q]])
                for q0 in range(q):
                    S.add_clause([-piv[k][q], -G[k][q0]])
                for k2 in range(m):
                    if k2 != k:
                        S.add_clause([-piv[k][q], -G[k2][q]])
            if k + 1 < m:
                # pivots strictly increase: piv[k] = q implies piv[k+1] > q
                for q in range(N2):
                    S.add_clause([-piv[k][q]] + [piv[k + 1][q2] for q2 in range(q + 1, N2)])
    if hankel:
        for J in classes:
            c0 = J[0]
            for j0 in range(n):
                for k in range(m):
                    S.add_xor_clause([G[k][c * n + (j0 - (c - c0)) % n] for c in J], False)
    return S, a, C, G, nv[0]


def verify(n, classes, sol, a):
    """Rebuild N from the functionals, return (rank, kernel dimension, criterion check)."""
    N2 = n * n
    cls = {c: k for k, J in enumerate(classes) for c in J}
    rows = []
    for c in range(n):
        for r in range(n):
            v = 0
            for i in range(n):
                for j in range(n):
                    bit = bool(sol[a[cls[c]][r][i * n + (j - c) % n]]) ^ (i * n + j == c * n + r)
                    if bit:
                        v |= 1 << (i * n + j)
            rows.append(v)
    rk = rank_rows(rows)
    ker = kernel_basis(rows, N2)
    assert len(ker) == N2 - rk
    for x in ker:
        for v in rows:
            assert bin(v & x).count("1") % 2 == 0
    # independent criterion: for each class, sum_c sigma^c X_c = 0 implies sum_c row_c(X_c) = 0
    def sigma(x, c):
        y = 0
        for i in range(n):
            for j in range(n):
                if x >> (i * n + (j + c) % n) & 1:
                    y |= 1 << (i * n + j)
        return y
    ok = True
    for J in classes:
        Sv = []; SL = []
        for c in J:
            for x in ker:
                s = sigma(x, c)
                Sv.append(s); SL.append(s | (((x >> (c * n)) & ((1 << n) - 1)) << N2))
        ok &= rank_rows(Sv) == rank_rows(SL)
    return rk, len(ker), ok, ker


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("classes")
    ap.add_argument("D", type=int)
    ap.add_argument("--rref", action="store_true")
    ap.add_argument("--hankel", action="store_true")
    ap.add_argument("--time", type=float, default=0)
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--save")
    args = ap.parse_args()
    n = args.n
    classes = [[int(x) for x in part.split(",")] for part in args.classes.split("|")]
    assert sorted(c for J in classes for c in J) == list(range(n)), "classes must partition Z_n"
    M = len(classes)
    D = args.D
    if args.hankel and args.rref and D < M * n:
        sys.exit("with --hankel and --rref the target D must be at least M*n (the Hankel space has that dimension)")
    print(f"n={n} classes={classes} D={D} (rank <= {n*n - D}); pairing {n*(n+1)//2}; "
          f"copy cap {(n*n + M*n)//2}; chain bound {chain_bound(n, classes)}; "
          f"rref={args.rref} hankel={args.hankel} threads={args.threads} time={args.time}", flush=True)
    t0 = time.time()
    S, a, C, G, nvars = build(n, classes, D, args.rref, args.hankel, args.threads, args.time, args.seed)
    print(f"  built: {nvars} variables in {time.time() - t0:.1f}s", flush=True)
    t0 = time.time()
    sat, sol = S.solve()
    dt = time.time() - t0
    if sat is None:
        print(f"RESULT n={n} classes={args.classes} D={D} hankel={args.hankel}: TIMEOUT after {dt:.0f}s", flush=True)
        return 2
    if not sat:
        scope = "codes containing the Hankel space" if args.hankel else "all class-uniform rules over GF(2)"
        print(f"RESULT n={n} classes={args.classes} D={D} hankel={args.hankel}: UNSAT in {dt:.0f}s "
              f"(no code of dimension >= {D} among {scope})", flush=True)
        return 1
    rk, kd, ok, ker = verify(n, classes, sol, a)
    assert kd >= D and ok, (kd, D, ok)
    print(f"RESULT n={n} classes={args.classes} D={D} hankel={args.hankel}: SAT in {dt:.0f}s; "
          f"verified: rank {rk}, kernel dimension {kd}, criterion {ok}", flush=True)
    if args.save:
        cls = {c: k for k, J in enumerate(classes) for c in J}
        out = {"n": n, "classes": classes, "kernel_dimension": kd,
               "a": [[[int(bool(sol[v])) for v in a[J][r]] for r in range(n)] for J in range(M)],
               "kernel_basis": ker}
        with open(args.save, "w") as f:
            json.dump(out, f)
    return 0


if __name__ == "__main__":
    sys.exit(main())
