"""The parity-coset rules of the memo in closed form, and an exact check of their codes.

Usage:

    python3 tools/parity_coset_rule.py                     compare the certificates with the closed form, and check
                                                            the dimension of the code for d = 8, 12, ..., 100
    python3 tools/parity_coset_rule.py D...                check the dimension for the given d = 4k >= 8
    python3 tools/parity_coset_rule.py --structure D...    also check the rank statements of the memo's proof

For d = 4k >= 8 the classes are J0 = {0, 2, ..., d - 4} and J1, the rest; the representatives are 0 and d - 2, and N is
the set of the other residues.  The decoder of class J_m at the output coordinate r reads the anti-diagonal of r:
    A_m(Y)_r = sum_i a[m][r][i] * Y[i][r - i].
On N the coefficients are the weights w[m][r] below, where e_j is the indicator of j, read as 0 when j is not in N:
    r even:            w[0][r] = 2 e_{r+3},                     w[1][r] = e_{r+1};
    r odd, r != d - 7: w[0][r] = e_{r+5};          w[0][d-7] = sum of (-1)^(i/2) e_i over the even i in N;
    r odd, r != d - 5: w[1][r] = e_{r+3} / 2;      w[1][d-5] = sum of e_i over the odd i, minus half the sum of e_i
                                                               over the even i in N.
At the representatives the coefficients are chosen so that the indicator of each class solves every equation:
    a[m][r][0] = [m = 0] - sum of w[m][r][i] over i in N and J0,
    a[m][r][d - 2] = [m = 1] - sum of w[m][r][i] over i in N and J1.
The code of the rule is the direct sum of its parts on the anti-diagonals (every decoder reads one anti-diagonal), so
its dimension is the sum over s of the nullity of the d x d system on anti-diagonal s; the script computes it exactly
over the rationals and compares it with (d^2 + 2d)/2 + d/4 - 1.  Without arguments it first checks that the
parity-coset certificates in data/ and data/numerical/ have exactly these decoders.  It needs only the Python standard
library and `check_certificates.py` from the same directory; all sizes up to 100 take a few minutes.
Exit status 1 if any check fails.
"""
import glob
import json
import os
import sys
from fractions import Fraction

from check_certificates import blocks, kernel, rank, structure

HERE = os.path.dirname(os.path.abspath(__file__))


def rule(d):
    """The classes (as a list of class indices) and the coefficients a[m][r][i] of the parity-coset rule."""
    J0 = set(range(0, d - 2, 2))
    cls = [0 if c in J0 else 1 for c in range(d)]
    N = [i for i in range(d) if i not in (0, d - 2)]

    def e(j):
        v = [Fraction(0)] * d
        if j % d in N:
            v[j % d] = Fraction(1)
        return v

    w = [[None] * d for _ in range(2)]
    for r in range(d):
        if r % 2 == 0:
            w[0][r] = [2 * x for x in e(r + 3)]
            w[1][r] = e(r + 1)
        else:
            if r == d - 7:
                w[0][r] = [Fraction((-1) ** (i // 2)) if i in N and i % 2 == 0 else Fraction(0) for i in range(d)]
            else:
                w[0][r] = e(r + 5)
            if r == d - 5:
                w[1][r] = [Fraction(0) if i not in N else Fraction(1) if i % 2 == 1 else Fraction(-1, 2)
                           for i in range(d)]
            else:
                w[1][r] = [x / 2 for x in e(r + 3)]
    a = [[w[m][r][:] for r in range(d)] for m in range(2)]
    for m in range(2):
        for r in range(d):
            a[m][r][0] = Fraction(int(m == 0)) - sum(w[m][r][i] for i in N if cls[i] == 0)
            a[m][r][d - 2] = Fraction(int(m == 1)) - sum(w[m][r][i] for i in N if cls[i] == 1)
    return cls, a


def certificate(d):
    """The rule in the certificate format of check_certificates.py (without the dimension)."""
    cls, a = rule(d)
    classes = [[c for c in range(d) if cls[c] == m] for m in range(2)]
    full = [[[Fraction(0)] * (d * d) for _ in range(d)] for _ in range(2)]
    for m in range(2):
        for r in range(d):
            for i in range(d):
                full[m][r][i * d + (r - i) % d] = a[m][r][i]
    return {"n": d, "classes": classes, "a": full}


def target(d):
    return (d * d + 2 * d) // 2 + d // 4 - 1


def check_size(d, with_structure=False):
    data = certificate(d)
    cls = {c: J for J, members in enumerate(data["classes"]) for c in members}
    B = blocks(d, data["a"], cls)
    nullities = [d - rank(rows, d) for rows in B]
    dim = sum(nullities)
    ok = dim == target(d)
    print(f"d={d:3d} dim={dim:5d} (d^2 + 2d)/2 + d/4 - 1 = {target(d):5d} {'OK' if ok else 'MISMATCH'}", flush=True)
    if with_structure:
        parts = [kernel(rows, d) for rows in B]
        ok = structure(d, data, B, parts) and ok
    return ok


def compare_certificates():
    """Check that the parity-coset certificates have exactly the decoders of the closed form."""
    paths = sorted(glob.glob(os.path.join(HERE, "data", "parity_coset_d*.json"))
                   + glob.glob(os.path.join(HERE, "data", "numerical", "parity_coset_d*.json")))
    ok = True
    for path in paths:
        with open(path) as f:
            data = json.load(f)
        d = data["n"]
        ours = certificate(d)
        same = sorted(map(sorted, data["classes"])) == sorted(map(sorted, ours["classes"]))
        for J, members in enumerate(data["classes"]):
            m = ours["classes"].index(sorted(members)) if sorted(members) in ours["classes"] else None
            if m is None:
                same = False
                continue
            same = same and all(len(data["a"][J][r]) == d * d for r in range(d)) and all(
                Fraction(x) == y for r in range(d) for x, y in zip(data["a"][J][r], ours["a"][m][r]))
        print(f"{os.path.basename(path):24s} decoders equal to the closed form: {'yes' if same else 'NO'}", flush=True)
        ok = ok and same
    return ok


def main(argv):
    args = argv[1:]
    with_structure = "--structure" in args
    sizes = [int(x) for x in args if x != "--structure"]
    if any(d % 4 or d < 8 for d in sizes):
        print("sizes must be multiples of 4, at least 8")
        return 2
    ok = True
    if not sizes:
        ok = compare_certificates()
        sizes = list(range(8, 101, 4))
    for d in sizes:
        ok = check_size(d, with_structure) and ok
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
