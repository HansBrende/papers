"""Check the certificates behind the memo's numerical remark exactly, over the rationals.

Usage:

    python3 tools/check_certificates.py                          check every certificate in data/ and data/numerical/
    python3 tools/check_certificates.py FILE...                   check the given certificate files
    python3 tools/check_certificates.py --translates FILE...      also compute the translate intersections
    python3 tools/check_certificates.py --structure FILE...       also check the rank statements of the memo's proof

Each certificate (format as for `gen_rational_data.py`: n, classes, a, dimension) describes a class-uniform rule over the
rationals.  The script checks that the classes partition Z/n, builds the n^2 x n^2 linear system of the rule,
    X[c][r] = sum_{i,j} a[J(c)][r][i*n + j] * X[i][(j + c) mod n]   for every row c and every r,
computes its rank by exact elimination over the rationals, and checks that the dimension of the solution space, the
code of the rule, equals the stated dimension.  It also prints the interval value (n^2 + Mn)/2 for the M classes and
the excess of the code over it, both exactly.

A decoder reads one anti-diagonal if a[J][r][i*n + j] = 0 unless i + j = r (mod n).  If every decoder does, each
equation involves only the entries X[i][s - i] of one anti-diagonal s = c + r of X, and the code is the direct sum of
its parts X_s on the n anti-diagonals; the script reports whether this holds.

With --translates it also computes, for every shift delta != 0, the dimension of the intersection of the code X with
its translate sigma^delta X, where (sigma^delta X)[i][j] = X[i][j + delta]; it prints the smallest of these and the
shifts that attain it, and checks the bound 2 dim X <= n^2 + dim(X cap sigma^delta X).  For codes whose decoders read
one anti-diagonal it uses X cap sigma^delta X = sum_s (X_s cap X_{s + delta}), in coordinates indexed by the row;
otherwise it computes a basis of the whole code, which takes a few minutes at n = 24.

With --structure, for the parity-coset classes {0, 2, ..., n - 4} and the rest of Z/n (n = 4k), it checks the rank
statements of the memo's proof that the parity-coset codes have dimension (n^2 + 2n)/2 + n/4 - 1: the decoders read one anti-diagonal; the code contains the
class indicators on every anti-diagonal (the space H*); on anti-diagonal s the block of the system on the n - 2 entries
outside the rows 0 and n - 2 has rank r_s, with dim X_s = 2 + (n - 2 - r_s); r_s = n/2 - 2 when s = 1 (mod 4) and
s != n - 7, and r_s = n/2 - 1 otherwise; for odd s != n - 7 the block splits by the parity of the row, its part on the
odd residues has the row space of T - I for T: c -> s + 1 - c, and its part on the even residues has rank k - 1; at
s = n - 7 the only equation with coefficients at residues of the other parity is that of row n - 2, and it has a
coefficient at every odd residue; for even s, in the system on anti-diagonal s (an equation for each row, an unknown for
each entry), the column of the entry in row s + 5 vanishes, and for every even i other than 0 and n - 2 the column of
the entry in row s + 3 - i is -2 times the column of the entry in row i.

It needs only the Python standard library; the rank check of the largest certificate (n = 36) takes under a minute.
Exit status 1 if any check fails.
"""
import glob
import json
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))


def rref(rows, ncol):
    """Reduced row echelon form over the rationals; returns the nonzero rows and the pivot columns."""
    rows = [r[:] for r in rows]
    pivots = []
    rk = 0
    for col in range(ncol):
        p = next((i for i in range(rk, len(rows)) if rows[i][col] != 0), None)
        if p is None:
            continue
        rows[rk], rows[p] = rows[p], rows[rk]
        inv = 1 / rows[rk][col]
        rows[rk] = [x * inv for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[rk])]
        pivots.append(col)
        rk += 1
    return rows[:rk], pivots


def rank(rows, ncol):
    """Rank over the rationals (entries are Fractions)."""
    return len(rref(rows, ncol)[1]) if rows else 0


def kernel(rows, ncol):
    """A basis of the solution space of the homogeneous system with the given rows."""
    R, pivots = rref(rows, ncol)
    basis = []
    for f in (c for c in range(ncol) if c not in pivots):
        v = [Fraction(0)] * ncol
        v[f] = Fraction(1)
        for row, p in zip(R, pivots):
            v[p] = -row[f]
        basis.append(v)
    return basis


def translates_full(n, system):
    """dim(X cap sigma^delta X) for delta = 1, ..., n - 1, from a basis of the whole code X."""
    basis = kernel(system, n * n)
    out = {}
    for delta in range(1, n):
        shifted = [[v[i * n + (j + delta) % n] for i in range(n) for j in range(n)] for v in basis]
        out[delta] = 2 * len(basis) - rank(basis + shifted, n * n)
    return out


def blocks(n, a, cls):
    """For decoders that read one anti-diagonal: the system on anti-diagonal s, in the unknowns z_i = X[i][s - i]."""
    out = []
    for s in range(n):
        rows = []
        for c in range(n):
            r = (s - c) % n
            row = [Fraction(0)] * n
            for i in range(n):
                row[i] += a[cls[c]][r][i * n + (r - i) % n]
            row[c] -= 1
            rows.append(row)
        out.append(rows)
    return out


def translates_blocks(n, parts):
    """dim(X cap sigma^delta X) for delta = 1, ..., n - 1, from the parts X_s of the code on the anti-diagonals."""
    return {delta: sum(len(parts[s]) + len(parts[(s + delta) % n]) - rank(parts[s] + parts[(s + delta) % n], n)
                       for s in range(n))
            for delta in range(1, n)}


def structure(n, data, B, parts):
    """Check the rank statements of the memo's proof for the parity-coset classes; returns True if all hold."""
    k = n // 4
    keep = [i for i in range(n) if i not in (0, n - 2)]
    hstar = all(sum(row[i] for i in J) == 0 for rows in B for row in rows for J in data["classes"])
    r = {s: rank([[row[i] for i in keep] for row in B[s]], n - 2) for s in range(n)}
    dims_ok = all(len(parts[s]) == 2 + (n - 2 - r[s]) for s in range(n))
    pattern = {s: n // 2 - 2 if (s % 4 == 1 and s != n - 7) else n // 2 - 1 for s in range(n)}
    pattern_ok = r == pattern
    split_ok = odd_ok = even_ok = True
    odd = [i for i in range(n) if i % 2 == 1]
    even = [i for i in keep if i % 2 == 0]
    for s in range(1, n, 2):
        if s == n - 7:
            continue
        if any(B[s][c][i] != 0 for c in range(n) for i in keep if c % 2 != i % 2):
            split_ok = False
        A = [[B[s][c][i] for i in odd] for c in odd]
        T = []
        for c in odd:
            row = [Fraction(0)] * len(odd)
            row[odd.index(c)] += 1
            row[odd.index((s + 1 - c) % n)] -= 1
            T.append(row)
        if not rank(A, len(odd)) == rank(T, len(odd)) == rank(A + T, len(odd)):
            odd_ok = False
        if rank([[B[s][c][i] for i in even] for c in range(0, n, 2)], len(even)) != k - 1:
            even_ok = False
    pairs_ok = True
    for s_ in range(0, n, 2):
        col = lambda i: [B[s_][c][i] for c in range(n)]
        if any(col((s_ + 5) % n)) or any(col((s_ + 3 - i) % n) != [-2 * x for x in col(i)] for i in even):
            pairs_ok = False
    crossing = sorted({c for c in range(n) for i in keep if c % 2 != i % 2 and B[n - 7][c][i] != 0})
    reached = [i for i in odd if B[n - 7][n - 2][i] != 0]
    boundary_ok = crossing == [n - 2] and reached == odd
    print(f"{'':24s} structure: H* in X {hstar}; dim X_s = 2 + (n - 2 - r_s) {dims_ok}; r_s as in the proof "
          f"{pattern_ok}; parity split at odd s != n - 7 {split_ok}; odd part ~ T - I {odd_ok}; even part rank k - 1 "
          f"{even_ok}; at s = n - 7 only row n - 2 crosses parity, at every odd residue {boundary_ok}; at even s "
          f"the column at s + 5 vanishes and the column at s + 3 - i is -2 times that at i {pairs_ok}", flush=True)
    return hstar and dims_ok and pattern_ok and split_ok and odd_ok and even_ok and boundary_ok and pairs_ok


def check(path, with_translates=False, with_structure=False):
    with open(path) as f:
        data = json.load(f)
    n = data["n"]
    members = [c for J in data["classes"] for c in J]
    if sorted(members) != list(range(n)):
        print(f"{os.path.basename(path):24s} the classes do not partition Z/{n}", flush=True)
        return False
    M = len(data["classes"])
    cls = {c: J for J, members in enumerate(data["classes"]) for c in members}
    a = [[[Fraction(s) for s in f] for f in aJ] for aJ in data["a"]]
    system = []
    for c in range(n):
        for r in range(n):
            row = [Fraction(0)] * (n * n)
            for i in range(n):
                for j in range(n):
                    x = a[cls[c]][r][i * n + j]
                    if x:
                        row[i * n + (j + c) % n] += x
            row[c * n + r] -= 1
            system.append(row)
    dim = n * n - rank(system, n * n)
    interval = Fraction(n * n + M * n, 2)
    excess = dim - interval
    ok = dim == data["dimension"]
    anti = all(a[J][r][i * n + j] == 0 or (i + j - r) % n == 0
               for J in range(M) for r in range(n) for i in range(n) for j in range(n))
    print(f"{os.path.basename(path):24s} n={n:2d} M={M} dim={dim:4d} stated={data['dimension']:4d} "
          f"interval value={str(interval):>6s} excess={'+' if excess >= 0 else ''}{excess} "
          f"one anti-diagonal: {'yes' if anti else 'no'} {'OK' if ok else 'MISMATCH'}", flush=True)
    if anti and (with_translates or with_structure):
        B = blocks(n, a, cls)
        parts = [kernel(rows, n) for rows in B]
        if sum(len(p) for p in parts) != dim:
            print(f"{'':24s} the parts on the anti-diagonals do not add up to the dimension", flush=True)
            return False
    if with_translates:
        inter = translates_blocks(n, parts) if anti else translates_full(n, system)
        t = min(inter.values())
        at = [delta for delta in inter if inter[delta] == t]
        bound_ok = all(2 * dim <= n * n + x for x in inter.values())
        print(f"{'':24s} smallest dim(X cap sigma^delta X) = {t} at delta in {at}; 2 dim X - n^2 = {2 * dim - n * n}; "
              f"bound {'holds' if bound_ok else 'FAILS'}", flush=True)
        ok = ok and bound_ok
    if with_structure:
        parity = n % 4 == 0 and n >= 8 and M == 2 and sorted(data["classes"][0]) == list(range(0, n - 2, 2))
        if not parity:
            print(f"{'':24s} structure: not the parity-coset classes, skipped", flush=True)
        elif not anti:
            print(f"{'':24s} structure: the decoders do not read one anti-diagonal", flush=True)
            ok = False
        else:
            ok = structure(n, data, B, parts) and ok
    return ok


def main(argv):
    args = argv[1:]
    with_translates = "--translates" in args
    with_structure = "--structure" in args
    files = [a for a in args if a not in ("--translates", "--structure")]
    files = files or (sorted(glob.glob(os.path.join(HERE, "data", "*.json")))
                      + sorted(glob.glob(os.path.join(HERE, "data", "numerical", "*.json"))))
    results = [check(p, with_translates, with_structure) for p in files]
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
