"""Odd words in affine one-class helper maps (lean-backlog/notes/pass-calculus.md, section 5).

g(c, r) = (a r + u, c + b r + v) on (Z/p)^2 has the linear part [[0, a], [1, b]].  For a family of such maps,
enumerate all words of odd length k <= KMAX in the maps and their inverses and report the largest number of
fixed points and the number of words that are the identity.  With a character of order two that is -1 on
every generator no odd word is the identity and each has at most p fixed points (Proposition 5).

Usage:  python3 lean-backlog/tools/pass_parity.py [P] [KMAX]
"""
import itertools
import sys


def compose(g, h, p):
    """g after h; an affine map is (M, t) with M a 2x2 tuple."""
    (m, t), (n, s) = g, h
    M = tuple(tuple(sum(m[i][k] * n[k][j] for k in range(2)) % p for j in range(2)) for i in range(2))
    T = tuple((sum(m[i][k] * s[k] for k in range(2)) + t[i]) % p for i in range(2))
    return M, T


def inverse(g, p):
    (m, t) = g
    det = (m[0][0] * m[1][1] - m[0][1] * m[1][0]) % p
    di = pow(det, p - 2, p)
    Mi = ((m[1][1] * di % p, -m[0][1] * di % p), (-m[1][0] * di % p, m[0][0] * di % p))
    Ti = tuple(-sum(Mi[i][k] * t[k] for k in range(2)) % p for i in range(2))
    return Mi, Ti


def fixed_points(g, p):
    (m, t) = g
    a, b, c, d = (m[0][0] - 1) % p, m[0][1], m[1][0], (m[1][1] - 1) % p
    if (a, b, c, d) == (0, 0, 0, 0):
        return p * p if t == (0, 0) else 0
    det = (a * d - b * c) % p
    if det:
        return 1
    # rank one: solvable iff (-t) is in the column space
    rows = [(a, b, -t[0] % p), (c, d, -t[1] % p)]
    r1, r2 = rows
    piv = r1 if (r1[0] or r1[1]) else r2
    oth = r2 if piv is r1 else r1
    j = 0 if piv[0] else 1
    f = oth[j] * pow(piv[j], p - 2, p) % p
    return p if (oth[2] - f * piv[2]) % p == 0 else 0


def family(spec, p):
    return [(((0, a % p), (1, b % p)), (u % p, v % p)) for a, b, u, v in spec]


def report(name, spec, p, kmax):
    gens = family(spec, p)
    letters = gens + [inverse(g, p) for g in gens]
    ident = (((1, 0), (0, 1)), (0, 0))
    for k in range(1, kmax + 1, 2):
        worst, ids, total = 0, 0, 0
        for word in itertools.product(letters, repeat=k):
            g = ident
            for x in word:
                g = compose(x, g, p)
            f = fixed_points(g, p)
            worst = max(worst, f)
            ids += f == p * p
            total += f
        print(f"  {name:34s} k={k}: words {len(letters) ** k:6d}, identities {ids:4d}, "
              f"most fixed points {worst:6d}, closed walks {total}")


def main():
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 101
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    print(f"p = {p}, p^2 = {p * p}")
    report("parity (ii): pairing, ST^2, ST^-2", [(1, 0, 0, 0), (-1, 2, 3, 5), (-1, -2, 7, 1)], p, kmax)
    report("parity (i): PT^0, PT^1, PT^3", [(1, 0, 0, 0), (1, 1, 3, 5), (1, 3, 7, 1)], p, kmax)
    report("no parity: pairing, ST^-1, ST^2", [(1, 0, 0, 0), (-1, -1, 3, 5), (-1, 2, 7, 1)], p, kmax)
    report("no parity: ST^-1 alone", [(-1, -1, 0, 0)], p, kmax)


if __name__ == "__main__":
    main()
