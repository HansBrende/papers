"""Describe a saved code of a class-uniform rule over GF(2): how it meets its own translates.

Usage (standard library only):

    python3 tools/analyse_code.py [FILE.json]

Without an argument it analyses tools/data/aperiodic_d6_dim25.json, the code of the paper's proposition on classes
with no almost-period, and reproduces the numbers quoted after that proposition: the code has dimension 25, it
contains the 12-dimensional space H* of matrices with x_c' = sigma^(c' - c) x_c for all c, c' in one class, it meets
its translate by one column in exactly 2*25 - 36 = 14 dimensions, and its translates by two and three columns in 18
and 17 dimensions.

Notation: the side length, d in the paper, is n here; X is an n x n matrix over GF(2) with rows x_c; sigma^delta X is
X with every row rotated, (sigma^delta X)[i][j] = X[i][j + delta].  The file format is that of
tools/verify_class_uniform_code.py; only "n", "classes" and "kernel_basis" are used here, and the code is the span
of "kernel_basis".  Run the verifier to check that the span is a code of the rule in the file.
"""
import json
import os
import sys


def rank(rows):
    piv = {}
    r = 0
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                r += 1
                break
    return r


def annihilator(basis, width):
    """A basis of the vectors orthogonal to every element of `basis` (bitmasks of length `width`)."""
    piv = {}
    for v in basis:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                break
    for h in sorted(piv):
        for h2 in piv:
            if h2 != h and piv[h2] >> h & 1:
                piv[h2] ^= piv[h]
    out = []
    for f in range(width):
        if f in piv:
            continue
        x = 1 << f
        for h, v in piv.items():
            if v >> f & 1:
                x |= 1 << h
        out.append(x)
    return out


def intersection_dim(spaces, width):
    """Dimension of the intersection of the subspaces spanned by the given bases."""
    ann = []
    for basis in spaces:
        ann += annihilator(basis, width)
    return width - rank(ann)


def rotate(x, n, delta):
    """sigma^delta: entry (i, j) of the result is entry (i, j + delta) of x."""
    y = 0
    for i in range(n):
        for j in range(n):
            if x >> (i * n + (j + delta) % n) & 1:
                y |= 1 << (i * n + j)
    return y


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "data", "aperiodic_d6_dim25.json")
    with open(path) as f:
        data = json.load(f)
    n, classes, basis = data["n"], data["classes"], data["kernel_basis"]
    N = n * n
    D = rank(basis)
    M = len(classes)
    print(f"{os.path.basename(path)}: n = {n}, classes {classes}")
    print(f"dimension of the code: {D}   (pairing value {n*(n+1)//2}; (n^2 + M n)/2 = {(n*n + M*n)/2:g})")
    # translates: {X in code : sigma^delta X in code} is the intersection of the code with sigma^(-delta) code
    for delta in range(1, n):
        pre = [rotate(x, n, (n - delta) % n) for x in basis]
        print(f"  dim(code meet sigma^-{delta} code) = {intersection_dim([basis, pre], N)}"
              f"   (the pigeonhole lemma gives at least 2 D - n^2 = {2*D - N})")
    # H*: x_c' = sigma^(c' - c) x_c inside each class; a basis has one vector per class and per column
    hstar = []
    for J in classes:
        c0 = J[0]
        for j0 in range(n):
            x = 0
            for c in J:
                x |= 1 << (c * n + (j0 - (c - c0)) % n)
            hstar.append(x)
    dh = rank(hstar)
    both = intersection_dim([basis, hstar], N)
    print(f"dim H* = {dh} (= M n = {M*n}); dim(code meet H*) = {both}"
          + ("   so the code contains H*" if both == dh else "   so the code does not contain H*"))
    triple = intersection_dim([basis, [rotate(x, n, n - 1) for x in basis], [rotate(x, n, n - 2) for x in basis]], N)
    print(f"dim(code meet sigma^-1 code meet sigma^-2 code) = {triple}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
