"""Verify a saved code of a class-uniform rule over GF(2), from the definition only.

Usage:  python3 tools/verify_class_uniform_code.py tools/data/FILE.json [...]

FILE.json has the keys
  n            side length
  classes      a partition of range(n) into lists
  a            a[J][r] is a list of n*n bits: the functional of class J for output coordinate r, on n x n matrices
               (entry (i, j) at position i*n + j)
  kernel_basis a list of n x n matrices over GF(2), each given as an integer with bit i*n + j equal to the entry (i, j)

The class-uniform rule of the file is
    X[c][r] = sum_{i,j} a[J(c)][r][(i, j)] * X[i][(j + c) mod n]        for every row c, with J(c) the class of c.
The script checks, with no linear algebra beyond one rank computation:
  1. every listed matrix satisfies this equation at every (c, r);
  2. the listed matrices are linearly independent over GF(2).
It then prints the dimension of their span and the values it is compared with: the pairing value n(n+1)/2 and
(n^2 + M n)/2 for M classes.  It shares no code with the search that produced the file.
"""
import json
import sys


def check(path):
    with open(path) as f:
        data = json.load(f)
    n = data["n"]
    classes = data["classes"]
    a = data["a"]
    basis = data["kernel_basis"]
    assert sorted(c for J in classes for c in J) == list(range(n))
    cls = {c: k for k, J in enumerate(classes) for c in J}
    M = len(classes)
    for X in basis:
        x = [[(X >> (i * n + j)) & 1 for j in range(n)] for i in range(n)]
        for c in range(n):
            for r in range(n):
                coeff = a[cls[c]][r]
                s = 0
                for i in range(n):
                    for j in range(n):
                        if coeff[i * n + j]:
                            s ^= x[i][(j + c) % n]
                if s != x[c][r]:
                    print(f"{path}: FAILED at basis vector {X}, row {c}, coordinate {r}")
                    return False
    # independence: Gaussian elimination on the bitmasks
    piv = {}
    rank = 0
    for v in basis:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                rank += 1
                break
    if rank != len(basis):
        print(f"{path}: FAILED, the listed matrices are dependent (rank {rank} of {len(basis)})")
        return False
    print(f"{path}: n = {n}, classes {classes}: {rank} independent matrices satisfy the rule; "
          f"pairing value {n*(n+1)//2}; (n^2 + M n)/2 = {(n*n + M*n)/2:g}")
    return True


if __name__ == "__main__":
    ok = all([check(p) for p in sys.argv[1:]])
    sys.exit(0 if ok else 1)
