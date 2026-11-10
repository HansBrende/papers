"""Generate the Lean data of the two rational class-uniform codes (n = 6, classes {0,1,3} and {2,4,5}, dimension 25).

Usage:

    python3 tools/gen_rational_data.py            write lean/ClassUniformMemo/RationalData.lean
    python3 tools/gen_rational_data.py --check    write nothing; exit 1 if that file is out of date

The script reads the certificates `data/rational_a.json` and `data/rational_b.json` next to itself and writes
`../lean/ClassUniformMemo/RationalData.lean`.  Both paths are relative to the script, so it can be run from any
directory.  It needs only the Python standard library, and its output is deterministic.

Certificate format (the format of the certificate of the parent paper, with rational entries):
  n          side length (6);
  classes    a partition of range(n) into lists ([[0, 1, 3], [2, 4, 5]]);
  a          a[J][r] is a list of n*n rationals, written as strings "p/q" or "p", the functional of class J for
             output coordinate r; the entry (i, j) of a matrix is at position i*n + j;
  dimension  the dimension of the code (25).
The rule is  X[c][r] = sum_{i,j} a[J(c)][r][i*n + j] * X[i][(j + c) mod n]  for every row c and every r, with
J(c) the index of the class of c.  The code is the space of all matrices that satisfy it.

What is computed and written, for each certificate.
  The code is the kernel of a 36 x 36 rational system.  The script brings the system to reduced echelon form and
  takes the standard kernel basis: one vector for each free position, equal to 1 there and to 0 at every other free
  position.  It multiplies the basis by the least common denominator P of its entries and the decoders by the least
  common denominator N of theirs, so that both are integral, and writes:
    ratGenRows*   the 25 integer generators, each as a list of 36 entries in row-major order;
    ratCoef*      for every class and every r, the nonzero entries ((i, j), N * a[J][r][i*n + j]);
    ratScale*     N;   ratPivots*  the free positions;   ratPivotScale*  P.
  Then N * G[c][r] = sum N a * G[i][(j + c) mod n] holds over the integers for every generator G, row c and r, and
  every generator equals P at its own free position and 0 at the others.  The script re-checks both facts and the
  dimension before writing, and that the two codes are different (together they span 30 dimensions).  The generated file contains definitions only; the two facts are proved by `decide`
  in `ClassUniformMemo/Fields.lean` and checked by the Lean kernel, so this script is not trusted.
"""
import json
import os
import sys
from fractions import Fraction
from math import lcm

HERE = os.path.dirname(os.path.abspath(__file__))
SOURCES = [("A", "rational_a.json"), ("B", "rational_b.json")]
TARGET = os.path.join(HERE, os.pardir, "lean", "ClassUniformMemo", "RationalData.lean")
SCRIPT_NAME = "tools/gen_rational_data.py"
TARGET_NAME = "lean/ClassUniformMemo/RationalData.lean"


def rref(rows, ncol):
    """Reduced row echelon form over the rationals; returns the nonzero rows and the pivot columns."""
    M = [r[:] for r in rows]
    pivots = []
    top = 0
    for col in range(ncol):
        p = next((i for i in range(top, len(M)) if M[i][col] != 0), None)
        if p is None:
            continue
        M[top], M[p] = M[p], M[top]
        inv = 1 / M[top][col]
        M[top] = [x * inv for x in M[top]]
        for i in range(len(M)):
            if i != top and M[i][col] != 0:
                f = M[i][col]
                M[i] = [x - f * y for x, y in zip(M[i], M[top])]
        pivots.append(col)
        top += 1
    return M[:top], pivots


def load(name):
    """Read one certificate and return its integer tables, after checking them from the definition."""
    with open(os.path.join(HERE, "data", name)) as f:
        data = json.load(f)
    n = data["n"]
    classes = data["classes"]
    assert n == 6 and classes == [[0, 1, 3], [2, 4, 5]], "the Lean development is written for this partition"
    a = [[[Fraction(s) for s in f] for f in aJ] for aJ in data["a"]]
    assert len(a) == 2 and all(len(aJ) == n and all(len(f) == n * n for f in aJ) for aJ in a)
    cls = {c: J for J, members in enumerate(classes) for c in members}
    system = []
    for c in range(n):
        for r in range(n):
            row = [Fraction(0)] * (n * n)
            for i in range(n):
                for j in range(n):
                    row[i * n + (j + c) % n] += a[cls[c]][r][i * n + j]
            row[c * n + r] -= 1
            system.append(row)
    R, pivots = rref(system, n * n)
    free = [p for p in range(n * n) if p not in pivots]
    basis = []
    for f in free:
        v = [Fraction(0)] * (n * n)
        v[f] = Fraction(1)
        for row, p in zip(R, pivots):
            v[p] = -row[f]
        basis.append(v)
    assert len(basis) == data["dimension"]
    P = lcm(*(x.denominator for v in basis for x in v))
    N = lcm(*(x.denominator for aJ in a for f in aJ for x in f))
    gens = [[int(x * P) for x in v] for v in basis]
    coef = [[[(p, int(x * N)) for p, x in enumerate(f) if x != 0] for f in aJ] for aJ in a]
    # re-check the two finite facts that Lean will check
    for G in gens:
        for c in range(n):
            for r in range(n):
                rhs = sum(w * G[(p // n) * n + (p % n + c) % n] for p, w in coef[cls[c]][r])
                assert N * G[c * n + r] == rhs
    for k, G in enumerate(gens):
        for l, f in enumerate(free):
            assert G[f] == (P if k == l else 0)
    return n, gens, coef, N, P, free


def check_codes_differ():
    """The two rational codes are different subspaces: together the 50 generators have rank 30 over the rationals."""
    gens = []
    for _, name in SOURCES:
        gens += [[Fraction(x) for x in G] for G in load(name)[1]]
    _, pivots = rref(gens, len(gens[0]))
    assert len(pivots) == 30, len(pivots)


def lean_int(x):
    return str(x) if x >= 0 else f"({x})"


def render():
    """The full text of the generated Lean file."""
    out = []
    out.append("/-")
    out.append(f"Generated by `{SCRIPT_NAME}` from `tools/data/rational_a.json` and `tools/data/rational_b.json`.")
    out.append("Do not edit this file: change the generator and run it again.")
    out.append("-/")
    out.append("import Mathlib.Data.ZMod.Defs")
    out.append("")
    out.append("/-!")
    out.append("# Data of the two rational class-uniform codes")
    out.append("")
    out.append("Each of the certificates `tools/data/rational_a.json` and `tools/data/rational_b.json` describes a")
    out.append("class-uniform rule over `ℚ` for the classes `{0, 1, 3}` and `{2, 4, 5}` of `ZMod 6`.  The generator checks")
    out.append("that the solution space of each rule has dimension 25; the proofs use only the 25 generators below.  This")
    out.append("file holds integer data for both codes and nothing else.  For the code `A` (and likewise `B`):")
    out.append("")
    out.append("* `ratGenRowsA`: the 25 generators, each as the list of its 36 entries in row-major order;")
    out.append("* `ratCoefA`: for the class `b` (`true` for `{0, 1, 3}`) and the output coordinate `r`, the nonzero")
    out.append("  coefficients `((i, j), a)` of the decoder, multiplied by `ratScaleA`;")
    out.append("* `ratScaleA`: the common denominator of the decoders;")
    out.append("* `ratPivotsA`: for every generator, a position where it equals `ratPivotScaleA` and the others vanish;")
    out.append("* `ratPivotScaleA`: the common denominator of the reduced kernel basis.")
    out.append("")
    out.append("All properties are proved in `ClassUniformMemo.Fields`.")
    out.append("-/")
    out.append("")
    out.append("namespace ClassUniformMemo")
    for tag, name in SOURCES:
        n, gens, coef, N, P, free = load(name)
        out.append("")
        out.append(f"/-- The 25 generators of the code `{tag}`, each as its 36 entries in row-major order. -/")
        out.append(f"def ratGenRows{tag} : List (List ℤ) :=")
        rows = ["[" + ", ".join(lean_int(x) for x in G) + "]" for G in gens]
        out.append("  [" + (",\n   ".join(rows)) + "]")
        out.append("")
        out.append(f"/-- The decoders of the code `{tag}`, multiplied by `ratScale{tag}`: the nonzero coefficients")
        out.append("`((i, j), a)` for the class `b` and the output coordinate `r`. -/")
        out.append(f"def ratCoef{tag} : Bool → ZMod 6 → List ((ZMod 6 × ZMod 6) × ℤ)")
        for b, J in ((True, 0), (False, 1)):
            for r in range(n):
                entries = ", ".join(f"(({p // n}, {p % n}), {lean_int(w)})" for p, w in coef[J][r])
                out.append(f"  | {'true' if b else 'false'}, {r} => [{entries}]")
        out.append("")
        out.append(f"/-- The common denominator of the decoders of the code `{tag}`. -/")
        out.append(f"def ratScale{tag} : ℤ := {N}")
        out.append("")
        out.append(f"/-- The private positions of the 25 generators of the code `{tag}`. -/")
        out.append(f"def ratPivots{tag} : List (ZMod 6 × ZMod 6) :=")
        out.append("  [" + ", ".join(f"({f // n}, {f % n})" for f in free) + "]")
        out.append("")
        out.append(f"/-- The value of every generator of the code `{tag}` at its private position. -/")
        out.append(f"def ratPivotScale{tag} : ℤ := {P}")
    out.append("")
    out.append("end ClassUniformMemo")
    return "\n".join(out) + "\n"


def main(argv):
    if argv[1:] not in ([], ["--check"]):
        print(__doc__)
        return 2
    check_codes_differ()
    text = render()
    if argv[1:] == ["--check"]:
        try:
            with open(TARGET) as f:
                current = f.read()
        except FileNotFoundError:
            current = None
        if current != text:
            print(f"{TARGET_NAME} is out of date; run {SCRIPT_NAME}")
            return 1
        print(f"{TARGET_NAME} is up to date")
        return 0
    with open(TARGET, "w") as f:
        f.write(text)
    print(f"wrote {TARGET_NAME}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
