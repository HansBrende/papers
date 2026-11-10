"""Generate the Lean data of the parity-coset codes at d = 8, 12, 16 (two classes, excess d/4 - 1).

Usage:

    python3 tools/gen_parity_coset_data.py            write lean/ClassUniformMemo/ParityCosetData.lean
    python3 tools/gen_parity_coset_data.py --check    write nothing; exit 1 if that file is out of date

The script reads the certificates `data/parity_coset_d8.json`, `data/parity_coset_d12.json` and
`data/parity_coset_d16.json` next to itself and writes `../lean/ClassUniformMemo/ParityCosetData.lean`.  Both paths are
relative to the script, so it can be run from any directory.  It needs only the Python standard library, and its output
is deterministic.

Certificate format: as for `gen_rational_data.py` (n, classes, a, dimension), with the classes
J0 = {0, 2, ..., n - 4} and J1 = the rest of Z/n, for n = 4k.

What is computed and written, for each certificate.
  The code is the kernel of an n^2 x n^2 rational system.  The script brings the system to reduced echelon form with the
  variables ordered so that the entries of the rows 0 and n - 2 (the two class representatives) come last; with this
  order every denominator of the standard kernel basis is a power of 2 (with the natural order, a factor 3 appears at
  n = 16).  It multiplies the basis by the least common denominator P of its entries and the decoders by the least
  common denominator N of theirs, and writes, sparsely:
    pcGen<n>     for every generator, its nonzero entries ((i, j), value);
    pcCoefTable<n>, pcCoef<n>   for every class and every r, the nonzero entries ((i, j), N * a[J][r][i*n + j]);
    pcScale<n>   N;   pcPivots<n>  the free positions;   pcPivotScale<n>  P.
  Then N * G[c][r] = sum N a * G[i][(j + c) mod n] holds over the integers for every generator G, row c and r, and every
  generator equals P at its own free position and 0 at the others.  The script re-checks both facts, that the dimension
  is (n^2 + 2n)/2 + n/4 - 1, and that N and P are powers of 2, before writing.  The generated file contains definitions
  only; the two facts are proved by `decide` in `ClassUniformMemo/ParityCoset.lean` and checked by the Lean kernel, so
  this script is not trusted.
"""
import json
import os
import sys
from fractions import Fraction
from math import lcm

HERE = os.path.dirname(os.path.abspath(__file__))
SIZES = [8, 12, 16]
TARGET = os.path.join(HERE, os.pardir, "lean", "ClassUniformMemo", "ParityCosetData.lean")
SCRIPT_NAME = "tools/gen_parity_coset_data.py"
TARGET_NAME = "lean/ClassUniformMemo/ParityCosetData.lean"


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


def is_power_of_two(x):
    return x >= 1 and x & (x - 1) == 0


def load(n):
    """Read one certificate and return its integer tables, after checking them from the definition."""
    with open(os.path.join(HERE, "data", f"parity_coset_d{n}.json")) as f:
        data = json.load(f)
    assert data["n"] == n and n % 4 == 0
    J0 = list(range(0, n - 2, 2))
    assert data["classes"] == [J0, [c for c in range(n) if c not in J0]]
    a = [[[Fraction(s) for s in f] for f in aJ] for aJ in data["a"]]
    cls = {c: (0 if c in J0 else 1) for c in range(n)}
    N2 = n * n
    system = []
    for c in range(n):
        for r in range(n):
            row = [Fraction(0)] * N2
            for i in range(n):
                for j in range(n):
                    row[i * n + (j + c) % n] += a[cls[c]][r][i * n + j]
            row[c * n + r] -= 1
            system.append(row)
    # the entries of the representative rows 0 and n - 2 come last
    order = sorted(range(N2), key=lambda v: (v // n in (0, n - 2), v))
    R, pivots = rref([[row[v] for v in order] for row in system], N2)
    free = [p for p in range(N2) if p not in pivots]
    basis = []
    for f in free:
        v = [Fraction(0)] * N2
        v[f] = Fraction(1)
        for row, p in zip(R, pivots):
            v[p] = -row[f]
        w = [Fraction(0)] * N2
        for p, var in enumerate(order):
            w[var] = v[p]
        basis.append((order[f], w))
    assert len(basis) == data["dimension"] == (n * n + 2 * n) // 2 + n // 4 - 1
    P = lcm(*(x.denominator for _, w in basis for x in w))
    N = lcm(*(x.denominator for aJ in a for f in aJ for x in f))
    assert is_power_of_two(P) and is_power_of_two(N), (P, N)
    gens = [[int(x * P) for x in w] for _, w in basis]
    coef = [[[(q, int(x * N)) for q, x in enumerate(f) if x != 0] for f in aJ] for aJ in a]
    for G in gens:
        for c in range(n):
            for r in range(n):
                rhs = sum(w * G[(q // n) * n + (q % n + c) % n] for q, w in coef[cls[c]][r])
                assert N * G[c * n + r] == rhs
    pivs = [v for v, _ in basis]
    for k, G in enumerate(gens):
        for l, v in enumerate(pivs):
            assert G[v] == (P if k == l else 0)
    return gens, coef, N, P, pivs


def lean_int(x):
    return str(x) if x >= 0 else f"({x})"


def render():
    """The full text of the generated Lean file."""
    out = []
    out.append("/-")
    out.append(f"Generated by `{SCRIPT_NAME}` from `tools/data/parity_coset_d8.json`, `tools/data/parity_coset_d12.json`")
    out.append("and `tools/data/parity_coset_d16.json`.  Do not edit this file: change the generator and run it again.")
    out.append("-/")
    out.append("import Mathlib.Data.ZMod.Defs")
    out.append("")
    out.append("/-!")
    out.append("# Data of the parity-coset codes at `d = 8, 12, 16`")
    out.append("")
    out.append("Each certificate describes a class-uniform rule over `ℚ` for the classes `J₀ = {0, 2, …, d - 4}` and")
    out.append("`J₁ =` the rest of `ZMod d`.  This file holds sparse integer data for the three codes and nothing else.")
    out.append("For the size `d` (and the suffix `D<d>`):")
    out.append("")
    out.append("* `pcGenD<d>`: for every generator, its nonzero entries `((i, j), value)`;")
    out.append("* `pcCoefD<d>`: for the class `b` (`true` for `J₀`) and the output coordinate `r`, the nonzero")
    out.append("  coefficients `((i, j), a)` of the decoder, multiplied by `pcScaleD<d>`;")
    out.append("* `pcScaleD<d>`: the common denominator of the decoders;")
    out.append("* `pcPivotsD<d>`: for every generator, a position where it equals `pcPivotScaleD<d>` and the others vanish;")
    out.append("* `pcPivotScaleD<d>`: the common denominator of the kernel basis.")
    out.append("")
    out.append("All properties are proved in `ClassUniformMemo.ParityCoset`.")
    out.append("-/")
    out.append("")
    out.append("namespace ClassUniformMemo")
    for n in SIZES:
        gens, coef, N, P, pivs = load(n)
        t = f"D{n}"
        out.append("")
        out.append(f"/-- The nonzero entries of the {len(gens)} generators of the parity-coset code at `d = {n}`. -/")
        out.append(f"def pcGen{t} : List (List ((ZMod {n} × ZMod {n}) × ℤ)) :=")
        rows = []
        for G in gens:
            ent = ", ".join(f"(({q // n}, {q % n}), {lean_int(x)})" for q, x in enumerate(G) if x != 0)
            rows.append("[" + ent + "]")
        out.append("  [" + ",\n   ".join(rows) + "]")
        out.append("")
        out.append(f"/-- The decoders of the parity-coset code at `d = {n}`, multiplied by `pcScale{t}`, as a table: entry `J`")
        out.append("(`0` for the class `true`, `1` for `false`) lists, for every output coordinate `r`, the nonzero")
        out.append("coefficients `((i, j), a)`. -/")
        out.append(f"def pcCoefTable{t} : List (List (List ((ZMod {n} × ZMod {n}) × ℤ))) :=")
        blocks = []
        for J in (0, 1):
            lines = []
            for r in range(n):
                entries = ", ".join(f"(({q // n}, {q % n}), {lean_int(w)})" for q, w in coef[J][r])
                lines.append("[" + entries + "]")
            blocks.append("[" + ",\n    ".join(lines) + "]")
        out.append("  [" + ",\n   ".join(blocks) + "]")
        out.append("")
        out.append(f"/-- The decoder coefficients of the class `b` and the output coordinate `r` at `d = {n}`. -/")
        out.append(f"def pcCoef{t} (b : Bool) (r : ZMod {n}) : List ((ZMod {n} × ZMod {n}) × ℤ) :=")
        out.append(f"  (pcCoefTable{t}.getD (if b then 0 else 1) []).getD r.val []")
        out.append("")
        out.append(f"/-- The common denominator of the decoders of the parity-coset code at `d = {n}`. -/")
        out.append(f"def pcScale{t} : ℤ := {N}")
        out.append("")
        out.append(f"/-- The private positions of the generators of the parity-coset code at `d = {n}`. -/")
        out.append(f"def pcPivots{t} : List (ZMod {n} × ZMod {n}) :=")
        out.append("  [" + ", ".join(f"({v // n}, {v % n})" for v in pivs) + "]")
        out.append("")
        out.append(f"/-- The value of every generator of the parity-coset code at `d = {n}` at its private position. -/")
        out.append(f"def pcPivotScale{t} : ℤ := {P}")
    out.append("")
    out.append("end ClassUniformMemo")
    return "\n".join(out) + "\n"


def main(argv):
    if argv[1:] not in ([], ["--check"]):
        print(__doc__)
        return 2
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
