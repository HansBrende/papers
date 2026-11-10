"""Reproduce the section "Small sizes" of the paper: its table, the bounds in it, and the solver runs behind it.

The side length is d in the paper and n here.  A partition of Z_n is written "0,1,3|2,4,5".

Usage (run from the paper's root directory; `table`, `partitions` and `shifts` need only the standard library,
`climb` and `controls` need the package pycryptosat):

  python3 tools/small_sizes.py table
      Print the paper's table.  For every row it recomputes the pairing value n(n+1)/2, floor((n^2 + M n)/2) and the
      best bound of Theorem TP over shift sets of at most four elements, and for every row with a saved code in
      tools/data/ it re-verifies the code from the definition (tools/verify_class_uniform_code.py) and checks that
      its dimension is the value in the table.  Rows for n <= 4 are exact values from the exhaustive enumeration
      (python3 tools/exhaustive_pigeonhole_checks.py n3 n4).  Exit status 1 if anything disagrees.

  python3 tools/small_sizes.py partitions N
      List the partitions of Z_N into 1 < M < N classes up to the affine maps c -> u*c + t (u a unit), with the same
      three numbers.  This is how the rows of the table were chosen.

  python3 tools/small_sizes.py shifts N "CLASSES"
      For every single shift delta, the number of components of the graph of Theorem TP with shift set {0, delta}.
      A partition into M classes has an almost-period when some delta gives M components.

  python3 tools/small_sizes.py climb CAP N "CLASSES" [N "CLASSES" ...] [--hankel] [--start D] [--outdir DIR]
      The search that produced the saved codes.  For each partition raise the target dimension D while
      tools/class_uniform_sat.py answers "satisfiable" within CAP seconds, saving every code found to DIR (default:
      a new directory small_sizes_out in the current directory).  It stops at the first "unsatisfiable", at the first
      time-out, or at the bound of Theorem TP.  With --hankel the search is restricted to codes that contain the
      space H* of matrices with x_c' = sigma^(c' - c) x_c for all c, c' in one class (faster; can only lower the
      result), and D starts above max(pairing value, M n), the dimension of H*.

  python3 tools/small_sizes.py controls [--long]
      Re-run the solver answers that the paper quotes, with the expected outcomes: the controls at n = 4 and n = 5,
      and the two "unsatisfiable" answers of the remark on the table.  With --long also the code of dimension 25 at
      n = 6 (about three minutes) and the code of dimension 28 for {0,1},{2,4},{3,5}.  Prints PASS or FAIL per run.

An answer "unsatisfiable" rests on the solver.  A time-out means nothing.  CryptoMiniSat's time limit counts CPU
seconds summed over its threads.
"""
import itertools
import os
import subprocess
import sys
import time
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
SOLVER = os.path.join(HERE, "class_uniform_sat.py")

# The rows of the paper's table: (n, classes, kind, value, saved code or None).
#   kind "="   exact value, equal to the bound of Theorem TP
#   kind ">="  largest code found
#   kind "*"   found, and optimal on the word of the solver
TABLE = [
    (3, "0|1,2", "=", 7, None),
    (4, "0|1,2,3", "=", 12, None),
    (4, "0,1|2,3", "=", 12, None),
    (4, "0,2|1,3", "=", 12, None),
    (4, "0|1|2,3", "=", 14, None),
    (4, "0|2|1,3", "=", 14, None),
    (5, "0|1,2,3,4", "=", 17, "d5_0_1234_dim17.json"),
    (5, "0,1|2,3,4", "=", 17, "d5_01_234_dim17.json"),
    (5, "0|1,2|3,4", "=", 20, "d5_0_12_34_dim20.json"),
    (5, "0|1|2,3,4", "*", 19, "d5_0_1_234_dim19.json"),
    (5, "0|1,4|2,3", "*", 20, "d5_0_14_23_dim20.json"),
    (5, "0|1|2|3,4", "=", 22, "d5_0_1_2_34_dim22.json"),
    (6, "0|1,2,3,4,5", "=", 24, "d6_0_12345_dim24.json"),
    (6, "0,1|2,3,4,5", "=", 24, "d6_01_2345_dim24.json"),
    (6, "0,1,2|3,4,5", "=", 24, "d6_012_345_dim24.json"),
    (6, "0,2,4|1,3,5", "=", 24, "d6_024_135_dim24.json"),
    (6, "0,2|1,3,4,5", ">=", 24, "d6_02_1345_dim24.json"),
    (6, "0,3|1,2,4,5", ">=", 23, "d6_03_1245_dim23.json"),
    (6, "0,1,3|2,4,5", ">=", 25, "aperiodic_d6_dim25.json"),
    (6, "0,1|2,4|3,5", ">=", 28, "d6_01_24_35_dim28.json"),
    (6, "0,1|2,5|3,4", ">=", 28, "d6_01_25_34_dim28.json"),
    (6, "0,2|1,4|3,5", ">=", 28, "d6_02_14_35_dim28.json"),
    (6, "0|1,2,4|3,5", ">=", 28, "d6_0_124_35_dim28.json"),
    (6, "0|1,5|2,3,4", ">=", 27, "d6_0_15_234_dim27.json"),
    (6, "0|1,2,5|3,4", ">=", 27, "d6_0_125_34_dim27.json"),
    (6, "0|1,3,4|2,5", ">=", 27, "d6_0_134_25_dim27.json"),
    (6, "0|4|1,2,3,5", ">=", 27, "d6_0_1235_4_dim27.json"),
    (6, "0|3|1,2,4,5", ">=", 26, "d6_0_1245_3_dim26.json"),
]

# The solver answers quoted in the paper: (arguments, expected answer, long?).
CONTROLS = [
    ('4 "0,1|2,3" 12 --rref', "SAT", False),
    ('4 "0,1|2,3" 13 --rref', "UNSAT", False),
    ('4 "0|1,2,3" 12 --rref', "SAT", False),
    ('4 "0|1,2,3" 13 --rref', "UNSAT", False),
    ('5 "0,1|2,3|4" 20 --rref', "SAT", False),
    ('5 "0,1|2,3|4" 21 --rref', "UNSAT", False),
    ('5 "0|1,4|2,3" 20 --rref --hankel', "SAT", False),
    ('5 "0|1,4|2,3" 21 --rref', "UNSAT", False),
    ('5 "0|1|2,3,4" 19 --rref --hankel', "SAT", False),
    ('5 "0|1|2,3,4" 20 --rref --hankel', "UNSAT", False),
    ('6 "0,1,3|2,4,5" 25 --rref', "SAT", True),
    ('6 "0,1|2,4|3,5" 28 --rref --hankel', "SAT", True),
]


def parse(cl):
    return [[int(x) for x in part.split(",")] for part in cl.split("|")]


def components(n, classes, shifts):
    """Number of components of {c ~ c' : same class, c' - c in shifts - shifts}."""
    cls = {c: k for k, J in enumerate(classes) for c in J}
    diffs = {(a - b) % n for a in shifts for b in shifts if a != b}
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for c in range(n):
        for d in diffs:
            e = (c + d) % n
            if cls[c] == cls[e]:
                parent[find(c)] = find(e)
    return len({find(c) for c in range(n)})


def tp_bound(n, classes, smax=3):
    """Best value of Theorem TP, floor((s n^2 + n chi)/(s + 1)), over shift sets {0} + s shifts, 1 <= s <= smax."""
    best, arg = n * n, None
    for s in range(1, smax + 1):
        for sh in itertools.combinations(range(1, n), s):
            chi = components(n, classes, (0,) + sh)
            b = (s * n * n + n * chi) // (s + 1)
            if b < best:
                best, arg = b, ((0,) + sh, chi)
    return best, arg


def numbers(n, classes):
    M = len(classes)
    return n * (n + 1) // 2, (n * n + M * n) // 2, tp_bound(n, classes)[0]


def cmd_table():
    sys.path.insert(0, HERE)
    from verify_class_uniform_code import verified_dimension
    ok = True
    print(f"{'n':>2} {'classes':<16} {'pairing':>7} {'floor((n^2+Mn)/2)':>18} {'bound':>5}  largest code")
    for n, cl, kind, value, cert in TABLE:
        classes = parse(cl)
        pairing, cap, bound = numbers(n, classes)
        note = ""
        if cert is None:
            note = "exhaustive (exhaustive_pigeonhole_checks.py n3 n4)"
        else:
            path = os.path.join(DATA, cert)
            res = verified_dimension(path, quiet=True) if os.path.exists(path) else None
            if res is None:
                ok = False
                note = f"MISSING OR INVALID {cert}"
            else:
                n2, classes2, dim = res
                same = n2 == n and sorted(map(sorted, classes2)) == sorted(map(sorted, classes))
                if not same or dim != value:
                    ok = False
                    note = f"MISMATCH with {cert}: n = {n2}, classes {classes2}, dimension {dim}"
                else:
                    note = f"verified from data/{cert}"
        if kind == "=" and value != bound:
            ok = False
            note += "  [value differs from the bound]"
        shown = {"=": f"= {value}", ">=": f">= {value}", "*": f"{value} *"}[kind]
        print(f"{n:>2} {cl:<16} {pairing:>7} {cap:>18} {bound:>5}  {shown:<6} {note}")
    print("* found; optimal on the word of the solver (see `controls`).")
    print("TABLE CONSISTENT" if ok else "TABLE INCONSISTENT")
    return 0 if ok else 1


def set_partitions(elems):
    if not elems:
        yield []
        return
    first, rest = elems[0], elems[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def canonical(p, n):
    best = None
    for u in range(1, n):
        if gcd(u, n) != 1:
            continue
        for t in range(n):
            q = sorted(sorted((u * c + t) % n for c in J) for J in p)
            key = (sorted(len(J) for J in q), q)
            if best is None or key < best:
                best = key
    return best[1]


def cmd_partitions(n):
    seen = {}
    for p in set_partitions(list(range(n))):
        if len(p) in (1, n):
            continue
        c = canonical(p, n)
        seen[str(c)] = c
    # a partition that is a row of the paper's table is printed with the representative used there
    rows = {str(canonical(parse(cl), n)): cl for m, cl, _, _, _ in TABLE if m == n}
    for q in sorted(seen.values(), key=lambda q: (len(q), [len(J) for J in q], q)):
        cl = rows.get(str(q), "|".join(",".join(map(str, J)) for J in q))
        pairing, cap, bound = numbers(n, q)
        print(f"{cl:<22} M = {len(q)}  pairing {pairing}  floor((n^2+Mn)/2) {cap}  bound {bound}"
              + ("   in the table" if str(q) in rows else ""))
    print(f"{len(seen)} partitions of Z_{n} into 1 < M < {n} classes up to affine maps; {len(rows)} of them in the table")
    return 0


def cmd_shifts(n, cl):
    classes = parse(cl)
    M = len(classes)
    for d in range(1, n):
        chi = components(n, classes, (0, d))
        print(f"shift {d}: {chi} components" + ("   (an almost-period)" if chi == M else ""))
    best, arg = tp_bound(n, classes)
    print(f"best bound of Theorem TP over at most four shifts: {best}, from the shift set {arg[0]} with {arg[1]} components")
    return 0


def run_solver(args, cap, extra=()):
    cmd = f'"{sys.executable}" "{SOLVER}" {args} --time {cap} ' + " ".join(extra)
    out = subprocess.run(cmd, shell=True, capture_output=True, text=True).stdout
    line = [l for l in out.splitlines() if l.startswith("RESULT")]
    res = line[-1] if line else "RESULT missing (is pycryptosat installed?)"
    if ": SAT" in res:
        return "SAT", res
    if "UNSAT" in res:
        return "UNSAT", res
    return "TIMEOUT", res


def cmd_climb(argv):
    hankel = "--hankel" in argv
    if hankel:
        argv.remove("--hankel")
    start, outdir = None, "small_sizes_out"
    if "--start" in argv:
        i = argv.index("--start")
        start = int(argv[i + 1])
        del argv[i:i + 2]
    if "--outdir" in argv:
        i = argv.index("--outdir")
        outdir = argv[i + 1]
        del argv[i:i + 2]
    cap = float(argv[0])
    inst = [(int(argv[i]), argv[i + 1]) for i in range(1, len(argv), 2)]
    os.makedirs(outdir, exist_ok=True)
    for n, cl in inst:
        classes = parse(cl)
        M = len(classes)
        pairing, cap2, bound = numbers(n, classes)
        floor = max(pairing, M * n) if hankel else pairing
        D = max(start, floor + 1) if start is not None else floor + 1
        best, status = D - 1, "nothing tried"
        t0 = time.time()
        while D <= bound:
            tag = cl.replace(",", "").replace("|", "_")
            save = os.path.join(outdir, f"d{n}_{tag}_dim{D}.json")
            args = f'{n} "{cl}" {D} --rref' + (" --hankel" if hankel else "")
            ans, _ = run_solver(args, cap, ("--save", f'"{save}"'))
            if ans == "SAT":
                best, D = D, D + 1
                status = "reached the bound of Theorem TP" if D > bound else "satisfiable"
            elif ans == "UNSAT":
                status = f"unsatisfiable at {D}" + (" among codes containing H*" if hankel else "")
                break
            else:
                status = f"time-out at {D} after {cap:.0f} s: lower bound only"
                break
        print(f"n = {n}, classes {cl}{' (codes containing H*)' if hankel else ''}: largest code found {best}; {status}; "
              f"pairing {pairing}; floor((n^2+Mn)/2) = {cap2}; bound {bound}; {time.time() - t0:.0f} s", flush=True)
    return 0


def cmd_controls(long):
    ok = True
    for args, expected, is_long in CONTROLS:
        if is_long and not long:
            continue
        t0 = time.time()
        ans, line = run_solver(args, 1800)
        good = ans == expected
        ok &= good
        print(f"{'PASS' if good else 'FAIL'}  {args:<40} expected {expected:<5} got {ans:<7} ({time.time() - t0:.0f} s)",
              flush=True)
    print("ALL CONTROLS PASSED" if ok else "SOME CONTROL FAILED")
    return 0 if ok else 1


def main():
    argv = sys.argv[1:]
    if not argv:
        print(__doc__)
        return 2
    if argv[0] == "table":
        return cmd_table()
    if argv[0] == "partitions":
        return cmd_partitions(int(argv[1]))
    if argv[0] == "shifts":
        return cmd_shifts(int(argv[1]), argv[2])
    if argv[0] == "climb":
        return cmd_climb(argv[1:])
    if argv[0] == "controls":
        return cmd_controls("--long" in argv)
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
