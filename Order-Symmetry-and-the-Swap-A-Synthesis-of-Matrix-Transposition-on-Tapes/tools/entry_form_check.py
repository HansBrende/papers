"""Small-instance checks of the proposition on changes that affect single entries.

Usage (from the paper's directory):  python3 tools/entry_form_check.py

A rule is a family of linear functionals a[c][r] on n x n matrices over GF(p), one for each row c and each output
coordinate r.  Its largest code is the space of matrices X with
    X[c][r] = a[c][r](sigma^c X)        for all c and r,        (sigma^c X)[i][j] = X[i][(j + c) mod n].
For t in Z/n let m_t be the number of c with a[c][r] != a[c+1][r], where r = t - 1 - c.  The proposition says
    2 dim(code) <= n^2 + sum_t max(1, m_t).
The script checks this
  1. for every rule at n = 2 over GF(2) (65536 rules), and counts the rules that attain the bound;
  2. for random rules at n = 3, 4, 5 over GF(2) and GF(3) whose functionals are drawn, on runs of consecutive rows,
     from a small pool, so that few decoders change (random seed fixed);
  3. for the rules "X[c][r] = X[r][c] except at a set of free entries", for every set of entries at n = 3 and for
     random sets at n = 4 and 5, over GF(2).  Here the bound is often attained, so this part can tell the grouping of
     the changes by anti-diagonals from other groupings: as a control, the script counts the rules that would violate
     the same inequality with the changes grouped by diagonals c - r, or by rows c, and expects to find some;
  4. for the class-uniform rules of the saved codes in tools/data/ (over GF(2)): the functionals are read from the
     file, m_t is computed from them, and both the saved code (checked against its rule by
     verify_class_uniform_code.py) and the largest code of the rule must obey the bound.
It stops with an AssertionError if the inequality fails or if a control finds nothing.  At n = 2 anti-diagonals and
diagonals coincide, and parts 1 and 2 rarely meet the bound for n >= 3, so only part 3 tests the grouping.  The
script needs only the standard library and takes a few seconds.  No proof in the paper uses it.
"""
import glob
import itertools
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_class_uniform_code import verified_dimension  # noqa: E402


def rank_mod(rows, p):
    """Rank over GF(p) of a list of rows (lists of integers)."""
    rows = [[x % p for x in row] for row in rows]
    rank = 0
    for col in range(len(rows[0]) if rows else 0):
        piv = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], -1, p)
        rows[rank] = [x * inv % p for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col]:
                f = rows[i][col]
                rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def code_dimension(a, n, p):
    """Dimension of the largest code of the rule a[c][r] (functionals as lists of n*n coefficients)."""
    system = []
    for c in range(n):
        for r in range(n):
            row = [0] * (n * n)
            row[c * n + r] += 1
            for i in range(n):
                for j in range(n):
                    row[i * n + (j + c) % n] -= a[c][r][i * n + j]
            system.append(row)
    return n * n - rank_mod(system, p)


def bound(a, n, grouping="anti-diagonal"):
    """n^2 + sum over the groups of max(1, number of changes in the group).

    A change is a pair (c, r) with a[c][r] != a[c+1][r].  The proposition groups the changes by the anti-diagonal
    t = c + r + 1.  The groupings "diagonal" (by c - r) and "row" (by c) are used as controls only.
    """
    counts = [0] * n
    for c in range(n):
        for r in range(n):
            if a[c][r] != a[(c + 1) % n][r]:
                group = {"anti-diagonal": c + r + 1, "diagonal": c - r, "row": c}[grouping]
                counts[group % n] += 1
    return n * n + sum(max(1, m) for m in counts)


def check_all_rules_n2():
    n, p = 2, 2
    functionals = [list(f) for f in itertools.product(range(p), repeat=n * n)]
    attained = 0
    for choice in itertools.product(functionals, repeat=n * n):
        a = [[choice[c * n + r] for r in range(n)] for c in range(n)]
        dim, b = code_dimension(a, n, p), bound(a, n)
        assert 2 * dim <= b, (a, dim, b)
        attained += 2 * dim == b
    print(f"n = 2 over GF(2): all {len(functionals) ** (n * n)} rules obey the bound; {attained} attain it")


def transpose_functional(n, r):
    """Y -> Y[r][0], so that the equation at (c, r) is X[c][r] = X[r][c]."""
    f = [0] * (n * n)
    f[r * n] = 1
    return f


def identity_functional(n, c, r):
    """Y -> Y[c][r - c], so that the equation at (c, r) is empty: the entry is free."""
    f = [0] * (n * n)
    f[c * n + (r - c) % n] = 1
    return f


def random_rule(n, p, rng):
    """A rule whose functionals are constant on a few runs of consecutive rows, for each output coordinate."""
    a = [[None] * n for _ in range(n)]
    for r in range(n):
        shared = [[rng.randrange(p) if rng.random() < 0.3 else 0 for _ in range(n * n)] for _ in range(2)]
        cuts = sorted(rng.sample(range(n), rng.randint(1, min(3, n))))
        kinds = [rng.choice(["transpose", "shared0", "shared1", "identity"]) for _ in cuts]
        for c in range(n):
            kind = kinds[max((k for k, cut in enumerate(cuts) if cut <= c), default=len(cuts) - 1)]
            if kind == "transpose":
                a[c][r] = transpose_functional(n, r)
            elif kind == "identity":
                a[c][r] = identity_functional(n, c, r)
            else:
                a[c][r] = shared[int(kind[-1])]
    return a


def check_random_rules(trials=1500, seed=20261110):
    rng = random.Random(seed)
    for n in (3, 4, 5):
        for p in (2, 3):
            attained = 0
            count = trials if n < 5 else trials // 5
            for _ in range(count):
                a = random_rule(n, p, rng)
                dim, b = code_dimension(a, n, p), bound(a, n)
                assert 2 * dim <= b, (n, p, a, dim, b)
                attained += 2 * dim == b
            print(f"n = {n} over GF({p}): {count} random rules obey the bound; {attained} attain it")


def free_entry_rule(n, free):
    """X[c][r] = X[r][c] except at the entries of `free`, which are unconstrained."""
    return [[identity_functional(n, c, r) if (c, r) in free else transpose_functional(n, r) for r in range(n)]
            for c in range(n)]


def check_free_entry_rules(seed=20261110):
    rng = random.Random(seed)
    for n in (3, 4, 5):
        entries = [(c, r) for c in range(n) for r in range(n)]
        if n == 3:
            subsets = [set(s) for k in range(len(entries) + 1) for s in itertools.combinations(entries, k)]
            what = f"all {len(subsets)} sets of free entries"
        else:
            subsets = [set(rng.sample(entries, rng.randint(0, len(entries)))) for _ in range(4000 if n == 4 else 1000)]
            what = f"{len(subsets)} random sets of free entries"
        attained, control = 0, {"diagonal": 0, "row": 0}
        for free in subsets:
            a = free_entry_rule(n, free)
            dim, b = code_dimension(a, n, 2), bound(a, n)
            assert 2 * dim <= b, (n, sorted(free), dim, b)
            attained += 2 * dim == b
            for grouping in control:
                control[grouping] += 2 * dim > bound(a, n, grouping)
        assert all(control.values()), (n, control)    # the controls must fail somewhere
        print(f"n = {n} over GF(2), {what}: all obey the bound; {attained} attain it; "
              f"control: grouping by diagonals would fail on {control['diagonal']}, by rows on {control['row']}")


def check_saved_codes():
    here = os.path.dirname(os.path.abspath(__file__))
    paths = sorted(glob.glob(os.path.join(here, "data", "*.json")))
    attained = 0
    for path in paths:
        res = verified_dimension(path, quiet=True)
        assert res is not None, path
        n, classes, saved_dim = res
        with open(path) as f:
            data = json.load(f)
        cls = {c: k for k, J in enumerate(classes) for c in J}
        a = [[data["a"][cls[c]][r] for r in range(n)] for c in range(n)]
        dim, b = code_dimension(a, n, 2), bound(a, n)
        assert saved_dim <= dim, (path, saved_dim, dim)     # the saved code is a code of the rule
        assert 2 * dim <= b, (path, dim, b)
        attained += 2 * dim == b
    print(f"{len(paths)} saved rules in tools/data obey the bound; {attained} attain it")


def main():
    check_all_rules_n2()
    check_random_rules()
    check_free_entry_rules()
    check_saved_codes()
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
