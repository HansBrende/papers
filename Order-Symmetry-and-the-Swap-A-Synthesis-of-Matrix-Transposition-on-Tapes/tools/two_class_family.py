"""The two-class rule of the proposition on an unbounded gain at two classes, over small prime fields GF(p).

Usage (from the paper's directory):
    python3 tools/two_class_family.py                 # all checks below
    python3 tools/two_class_family.py --write-data    # also (re)write tools/data/two_class_d{8,12,16}.json

For d = 4k >= 8 the classes are J0 = {0, 2, ..., d - 4} and J1 = the rest of Z/d.  With N = Z/d minus {0, d - 2},
e_j the indicator of j if j is in N and 0 otherwise, and a nonzero scalar lam, the rule has the vectors
    even r:  w0[r] = lam e_{r+3},                    w1[r] = e_{r+1},
    odd r:   w0[r] = e_{r+5}        (r != d - 7),    w0[d-7] = alpha = sum over even i in N of (-1)^(i/2) e_i,
             w1[r] = lam^-1 e_{r+3} (r != d - 5),    w1[d-5] = beta  = sum over odd i of e_i
                                                                       - lam^-1 sum over even i in N of e_i,
completed at 0 and d - 2 so that the indicators of the two classes satisfy every equation, and the decoders
    A_{Jm}(Y)_r = sum_i a_m[r][i] Y[i][r - i].
The memo to this paper has lam = 2 over fields in which 2 != 0; over GF(2), lam = 1 and all coefficients are 0 or 1.

The script checks, by exact elimination over GF(p):
  1. for d = 8, 12, ..., 48 and (p, lam) = (2, 1), (3, 1), (3, 2), (5, 1), (5, 2), (5, 3), (7, 2), (11, 6): on every
     anti-diagonal s, every rank that the proof states.  These are: the rank r_s (2k - 2 if s = 1 mod 4 and
     s != d - 7, and 2k - 1 otherwise); for even s, that e_{s+3} and the rows of the even residues of N are
     independent and span all rows; for odd s, the ranks of the odd and of the even rows; for odd s != d - 7, the
     dimension of the space W, that the row of d - 2 lies in W, and whether the row alpha - e_{s+7} does; for
     s = d - 7, the dimension of E, that alpha lies in E, and that beta does not lie in O + E.  Hence the dimension
     (d^2 + 2d)/2 + d/4 - 1 of the code.  Over GF(2) the dimension is checked for every d = 4k up to 100;
  2. for d = 8 and 12, that the full d^2 x d^2 system of the rule has a solution space of the same dimension, with no
     use of the splitting into anti-diagonals;
  3. that the saved codes tools/data/two_class_d8.json, _d12.json and _d16.json (over GF(2), lam = 1) have exactly the
     decoders of the rule and a kernel basis of the stated size.  That every saved matrix satisfies the rule and that
     they are independent is checked, from the definition, by tools/verify_class_uniform_code.py;
  4. the corollary for every fixed number M of classes, on small instances: the rule of the mixed blow-up, which has
     the two-class rule at floor(M/2) of the k = ceil(M/2) positions and, for odd M, the rule X[a][t] = X[t][a] of
     one class at the last one, is built on Z/(kd), its classes are counted, and its largest code is computed from
     the full system: its dimension is (n^2 + Mn)/2 + k floor(M/2) (d/4 - 1), with n = kd, for M = 3, ..., 7 over
     GF(2) and for M = 3, 4 over GF(3).
It stops with an AssertionError if a check fails.  It needs only the standard library and takes a few seconds.
The proposition is proved in the paper; no proof uses this script.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from entry_form_check import rank_mod, code_dimension  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SAVED = (8, 12, 16)


def classes(d):
    j0 = [c for c in range(0, d, 2) if c != d - 2]
    return [j0, [c for c in range(d) if c not in j0]]


def rule(d, p, lam):
    """The vectors a[m][r] in GF(p)^d of the rule, and the class of every row."""
    assert d % 4 == 0 and d >= 8 and lam % p
    inv = pow(lam, -1, p)
    cls = [0 if c in classes(d)[0] else 1 for c in range(d)]
    inside = [i for i in range(d) if i not in (0, d - 2)]

    def e(j, scale=1):
        v = [0] * d
        if j % d in inside:
            v[j % d] = scale % p
        return v

    alpha, beta = [0] * d, [0] * d
    for i in inside:
        if i % 2 == 0:
            alpha[i] = (-1) ** (i // 2) % p
            beta[i] = -inv % p
        else:
            beta[i] = 1
    w = [[None] * d, [None] * d]
    for r in range(d):
        if r % 2 == 0:
            w[0][r], w[1][r] = e(r + 3, lam), e(r + 1)
        else:
            w[0][r] = alpha if r == d - 7 else e(r + 5)
            w[1][r] = beta if r == d - 5 else e(r + 3, inv)
    a = [[None] * d, [None] * d]
    for m in range(2):
        for r in range(d):
            v = list(w[m][r])
            v[0] = (int(m == 0) - sum(w[m][r][i] for i in inside if cls[i] == 0)) % p
            v[d - 2] = (int(m == 1) - sum(w[m][r][i] for i in inside if cls[i] == 1)) % p
            a[m][r] = v
    return a, cls


def check_ranks(d, p, lam):
    """The rank statements of the proof on every anti-diagonal; returns the dimension of the code."""
    k = d // 4
    a, cls = rule(d, p, lam)
    inside = [i for i in range(d) if i not in (0, d - 2)]
    total = 0
    for s in range(d):
        # the equations of the anti-diagonal s, restricted to the unknowns in N
        rows = {}
        for c in range(d):
            v = [a[cls[c]][(s - c) % d][i] for i in inside]
            if c in inside:
                v[inside.index(c)] = (v[inside.index(c)] - 1) % p
            rows[c] = v
        r_s = rank_mod(list(rows.values()), p)
        expected = 2 * k - 2 if (s % 4 == 1 and s != d - 7) else 2 * k - 1
        assert r_s == expected, (d, p, lam, s, r_s, expected)
        j0 = classes(d)[0]
        if s % 2 == 0:
            unit = [int(i == (s + 3) % d) for i in inside]
            gens = [unit] + [rows[c] for c in inside if c % 2 == 0]
            assert rank_mod(gens, p) == len(gens) == 2 * k - 1, (d, p, lam, s)
            assert rank_mod(gens + list(rows.values()), p) == 2 * k - 1, (d, p, lam, s)
        else:
            odd_rows = [rows[c] for c in range(1, d, 2)]
            odd = rank_mod(odd_rows, p)
            even = rank_mod([rows[c] for c in range(0, d, 2)], p)
            assert odd == (k - 1 if s % 4 == 1 else k), (d, p, lam, s, odd)
            assert even == (k if s == d - 7 else k - 1), (d, p, lam, s, even)
            assert r_s == odd + even, (d, p, lam, s)
            if s != d - 7:
                w_rows = [rows[c] for c in j0 if c != (s + 7) % d]
                dim_w = rank_mod(w_rows, p)
                assert dim_w == (k - 1 if s % 4 == 1 or s == (d - 9) % d else k - 2), (d, p, lam, s, dim_w)
                assert rank_mod(w_rows + [rows[d - 2]], p) == dim_w, (d, p, lam, s)
                if s != (d - 9) % d:      # the row alpha - e_{s+7}: in W exactly when s = 1 mod 4
                    with_alpha = rank_mod(w_rows + [rows[(s + 7) % d]], p)
                    assert with_alpha == dim_w + (0 if s % 4 == 1 else 1), (d, p, lam, s)
            else:
                e_rows = [rows[c] for c in j0 if c != 0]
                assert rank_mod(e_rows, p) == k - 1, (d, p, lam, s)
                assert rank_mod(e_rows + [rows[0]], p) == k - 1, (d, p, lam, s)          # alpha lies in E
                assert rank_mod(odd_rows + e_rows, p) == 2 * k - 2, (d, p, lam, s)
                assert rank_mod(odd_rows + e_rows + [rows[d - 2]], p) == 2 * k - 1, (d, p, lam, s)   # beta does not
        # the whole anti-diagonal: d equations in d unknowns
        full = []
        for c in range(d):
            v = list(a[cls[c]][(s - c) % d])
            v[c] = (v[c] - 1) % p
            full.append(v)
        dim_s = d - rank_mod(full, p)
        assert dim_s == d - r_s, (d, p, lam, s, dim_s, r_s)
        total += dim_s
    assert total == (d * d + 2 * d) // 2 + k - 1, (d, p, lam, total)
    return total


def dimension_gf2(d):
    """Dimension of the code over GF(2) with lam = 1, anti-diagonal by anti-diagonal, with rows as bit masks."""
    a, cls = rule(d, 2, 1)
    total = 0
    for s in range(d):
        pivots = {}
        for c in range(d):
            v = sum(bit << i for i, bit in enumerate(a[cls[c]][(s - c) % d])) ^ (1 << c)
            while v:
                h = v.bit_length() - 1
                if h not in pivots:
                    pivots[h] = v
                    break
                v ^= pivots[h]
        total += d - len(pivots)
    return total


def functionals(d, p, lam):
    """The rule in the format of the other scripts: f[c][r] on d x d matrices, entry (i, j) at position i*d + j."""
    a, cls = rule(d, p, lam)
    per_class = [[None] * d, [None] * d]
    for m in range(2):
        for r in range(d):
            v = [0] * (d * d)
            for i in range(d):
                v[i * d + (r - i) % d] = a[m][r][i]
            per_class[m][r] = v
    return per_class, cls


def kernel_basis_gf2(d):
    """A basis of the code over GF(2) with lam = 1: matrices as integers with bit i*d + j equal to the entry (i, j)."""
    per_class, cls = functionals(d, 2, 1)
    pivots = {}
    for c in range(d):
        for r in range(d):
            v = 1 << (c * d + r)
            for pos, bit in enumerate(per_class[cls[c]][r]):
                if bit:
                    i, j = divmod(pos, d)
                    v ^= 1 << (i * d + (j + c) % d)
            while v:
                h = v.bit_length() - 1
                if h not in pivots:
                    pivots[h] = v
                    break
                v ^= pivots[h]
    # back-substitution: reduce every pivot row by the pivot rows below it
    for h in sorted(pivots):
        for g in sorted(pivots):
            if g < h and pivots[h] >> g & 1:
                pivots[h] ^= pivots[g]
    basis = []
    for free in range(d * d):
        if free not in pivots:
            x = 1 << free
            for h, row in pivots.items():
                if row >> free & 1:
                    x |= 1 << h
            basis.append(x)
    return basis


def mixed_blow_up_dimension(d, big_m, p, lam):
    """The number of classes and the dimension of the largest code of the mixed blow-up rule for M classes.

    The positions u < floor(M/2) carry the two-class rule on Z/d, and for odd M the last position carries the rule
    X[a][t] = X[t][a] of one class.  Row c = k a' + u of a matrix on Z/(kd) is decoded, at the column k t + v, by the
    decoder of position u applied to the block with the entries (sigma^c X)[k a + u][k t' + v - u].
    """
    k, pairs = (big_m + 1) // 2, big_m // 2
    n = k * d
    a, cls = rule(d, p, lam)
    two_class = [[{(i, (t - i) % d): a[m][t][i] for i in range(d) if a[m][t][i]} for t in range(d)] for m in range(2)]
    one_class = [[{(t, 0): 1} for t in range(d)]]
    position = [(cls, two_class)] * pairs + [([0] * d, one_class)] * (k - pairs)
    seen = set()
    equations = []
    for c in range(n):
        block, u = divmod(c, k)
        cls_u, dec_u = position[u]
        seen.add((u, cls_u[block]))
        for r in range(n):
            t, v = divmod(r, k)
            eq = {c * n + r: 1}
            for (i, j), coeff in dec_u[cls_u[block]][t].items():
                var = (k * i + u) * n + (k * j + v - u + c) % n
                eq[var] = (eq.get(var, 0) - coeff) % p
            equations.append(eq)
    if p == 2:
        pivots = {}
        for eq in equations:
            x = sum(1 << var for var, coeff in eq.items() if coeff)
            while x:
                h = x.bit_length() - 1
                if h not in pivots:
                    pivots[h] = x
                    break
                x ^= pivots[h]
        rank = len(pivots)
    else:
        rank = rank_mod([[eq.get(var, 0) for var in range(n * n)] for eq in equations], p)
    return len(seen), n * n - rank


def saved_path(d):
    return os.path.join(HERE, "data", f"two_class_d{d}.json")


def saved_record(d):
    per_class, _ = functionals(d, 2, 1)
    basis = kernel_basis_gf2(d)
    return {"n": d, "classes": classes(d), "kernel_dimension": len(basis), "a": per_class, "kernel_basis": basis}


def main(argv):
    if "--write-data" in argv:
        for d in SAVED:
            with open(saved_path(d), "w") as f:
                json.dump(saved_record(d), f, separators=(",", ":"))
                f.write("\n")
            print(f"wrote {os.path.relpath(saved_path(d), os.path.dirname(HERE))}")
    for p, lam in ((2, 1), (3, 1), (3, 2), (5, 1), (5, 2), (5, 3), (7, 2), (11, 6)):
        dims = [check_ranks(d, p, lam) for d in range(8, 49, 4)]
        print(f"GF({p}), lam = {lam}: rank statements and dimension hold for d = 8, 12, ..., 48 "
              f"(excess over (d^2 + 2d)/2: {[x - (d * d + 2 * d) // 2 for x, d in zip(dims, range(8, 49, 4))]})")
    for d in range(8, 101, 4):
        assert dimension_gf2(d) == (d * d + 2 * d) // 2 + d // 4 - 1, d
    print("GF(2), lam = 1: dimension (d^2 + 2d)/2 + d/4 - 1 for every d = 4k with 8 <= d <= 100")
    for d in (8, 12):
        for p, lam in ((2, 1), (3, 2), (5, 3)):
            per_class, cls = functionals(d, p, lam)
            f = [[per_class[cls[c]][r] for r in range(d)] for c in range(d)]
            assert code_dimension(f, d, p) == (d * d + 2 * d) // 2 + d // 4 - 1, (d, p, lam)
    print("d = 8, 12: the full system of the rule has the same solution space dimension over GF(2), GF(3), GF(5)")
    for d in SAVED:
        with open(saved_path(d)) as f:
            data = json.load(f)
        assert data == saved_record(d), d
        assert data["kernel_dimension"] == len(data["kernel_basis"]) == (d * d + 2 * d) // 2 + d // 4 - 1, d
        print(f"tools/data/two_class_d{d}.json holds the rule over GF(2) and {data['kernel_dimension']} matrices")
    for p, lam, cases in ((2, 1, ((3, 8), (3, 12), (3, 16), (4, 8), (4, 12), (5, 8), (6, 8), (7, 8))),
                          (3, 2, ((3, 8), (4, 8)))):
        for big_m, d in cases:
            k, pairs = (big_m + 1) // 2, big_m // 2
            n = k * d
            count, dim = mixed_blow_up_dimension(d, big_m, p, lam)
            assert count == big_m, (big_m, d, count)
            assert dim == (n * n + big_m * n) // 2 + k * pairs * (d // 4 - 1), (big_m, d, p, dim)
            print(f"GF({p}): M = {big_m} classes on Z/{n}: largest code of the mixed blow-up rule has dimension {dim} "
                  f"= (n^2 + Mn)/2 + {k * pairs * (d // 4 - 1)}")
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
