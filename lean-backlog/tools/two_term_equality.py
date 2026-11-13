#!/usr/bin/env python3
"""Two terms attain d(d+1)/2 only as one term G (x) G^-1: checks for Theorem 1 of lean-backlog/notes/two-term-equality.md.

Usage (from the repository root; numpy, sympy; rustc for part 4):
    python3 lean-backlog/tools/two_term_equality.py            # parts 1-3 and 5, a few seconds
    python3 lean-backlog/tools/two_term_equality.py all 8      # also part 4 with 8 threads

Setting.  K = A_0 (x) B_0 + A_1 (x) B_1 acts on d x d matrices by X -> sum_a A_a X B_a^T; the code is
{X : X^T = K X}.  Theorem 1: if the code has dimension d(d+1)/2, then K = G (x) G^-1 for an invertible G.

Parts.
 1. Symbolic (integer polynomial identities, so valid in every characteristic): the four block equations (1)-(4)
    of the proof for row factors [[alpha_a, 0], [u_a, A_a']] (A_a' general) and X = [[xi, p^T], [q, X']], at
    d = 2, 3, 4.
 2. Symbolic, derived from (1)-(4) by substituting the normal forms I and II (m = 1, 2, 3): (2'), (4'), (ii), (3a),
    (3b), the quadratic forms w^T R w of Steps 3 and 4, R at xi = 1, and the last line A_0 B_0 = 1.
 3. d = 2, complete, over GF(2), GF(3), GF(5): every operator with a code of dimension exactly 3 is swap - a b^T;
    those with at most two Kronecker terms are exactly the G (x) G^-1.
 4. (argument "all") Exhaustive search with two_term_bf.rs: for fixed row factors (A_0, A_1), all
    pairs (B_0, B_1) over GF(3) at d = 3 (3^18 each) and over GF(2) at d = 4 (2^32 each).  The row factors run
    through pencils beyond the diagonalisable ones: Jordan blocks, irreducible factors, and singular pencils
    in Kronecker form.  Asserted: the pairs with a code of dimension at least d(d+1)/2 are exactly
    (g_0 G^-1, g_1 G^-1) with G = g_0 A_0 + g_1 A_1 invertible over the field.
    For a pencil without an invertible element over the field this asserts that there is no such pair.
    The enumerator is first compared with a Python enumeration at d = 2 over GF(3) and GF(2) and at d = 3 over
    GF(2).
 5. The dual statement (Corollary 2) on examples: K_G X = X^T - tr(G^-T X) G has d(d-1)/2 terms and a code of
    codimension one; the span of its row factors is {alternating} G^-T and that of its column factors
    {alternating} G^-1 (at d = 3 every element of both is singular); and K_1 plus one term has codimension 2.
"""
import itertools
import os
import random
import subprocess
import sys
import tempfile
import time

import numpy as np
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = 20261112
rng = random.Random(SEED)


# ---------------------------------------------------------------- exact linear algebra over GF(p)
def rank_mod(M, p):
    M = np.array(M, dtype=np.int64) % p
    rows, cols = M.shape
    rk = 0
    for col in range(cols):
        nz = np.nonzero(M[rk:, col])[0]
        if len(nz) == 0:
            continue
        piv = rk + int(nz[0])
        if piv != rk:
            M[[rk, piv]] = M[[piv, rk]]
        M[rk] = (M[rk] * pow(int(M[rk, col]), p - 2, p)) % p
        below = np.nonzero(M[rk + 1:, col])[0] + rk + 1
        if len(below):
            M[below] = (M[below] - np.outer(M[below, col], M[rk])) % p
        rk += 1
        if rk == rows:
            break
    return rk


def inv_mod(M, p):
    d = M.shape[0]
    W = np.concatenate([np.array(M, dtype=np.int64) % p, np.eye(d, dtype=np.int64)], axis=1)
    for col in range(d):
        nz = np.nonzero(W[col:, col])[0]
        if len(nz) == 0:
            return None
        piv = col + int(nz[0])
        if piv != col:
            W[[col, piv]] = W[[piv, col]]
        W[col] = (W[col] * pow(int(W[col, col]), p - 2, p)) % p
        for r in range(d):
            if r != col and W[r, col]:
                W[r] = (W[r] - W[r, col] * W[col]) % p
    return W[:, d:]


def swap_matrix(d):
    S = np.zeros((d * d, d * d), dtype=np.int64)
    for i in range(d):
        for j in range(d):
            S[i * d + j, j * d + i] = 1
    return S


def op(terms, p):
    """Matrix of X -> sum_a A_a X B_a^T on row-major vec(X)."""
    return sum(np.kron(A, B) for A, B in terms) % p


def realign(K, d):
    """K^R[(i,k),(j,l)] = K[(i,j),(k,l)]; its rank is the number of Kronecker terms."""
    return K.reshape(d, d, d, d).transpose(0, 2, 1, 3).reshape(d * d, d * d)


def E(d, *positions):
    M = np.zeros((d, d), dtype=np.int64)
    for (i, j, v) in positions:
        M[i - 1, j - 1] = v
    return M


# ---------------------------------------------------------------- part 1 and 2: the equations of the proof
def eqs(al, be, u, y, z, Ap, Bp, xi, pv, q, Xp):
    """Left side minus right side of the block equations (1)-(4) of the proof."""
    m = pv.shape[0]
    e1 = xi - sum(al[a] * (be[a] * xi + (y[a].T * pv)[0, 0]) for a in range(2))
    e2 = q - sum((al[a] * (xi * z[a] + Bp[a] * pv) for a in range(2)), sp.zeros(m, 1))
    e3 = pv - sum(((u[a] * xi + Ap[a] * q) * be[a] + (u[a] * pv.T + Ap[a] * Xp) * y[a] for a in range(2)),
                  sp.zeros(m, 1))
    e4 = Xp.T - sum(((u[a] * xi + Ap[a] * q) * z[a].T + (u[a] * pv.T + Ap[a] * Xp) * Bp[a].T for a in range(2)),
                    sp.zeros(m, m))
    return e1, e2, e3, e4


def block_symbols(m):
    al = sp.symbols("alpha0 alpha1")
    be = sp.symbols("beta0 beta1")
    u = [sp.Matrix(m, 1, sp.symbols(f"u{a}_0:{m}")) for a in range(2)]
    y = [sp.Matrix(m, 1, sp.symbols(f"y{a}_0:{m}")) for a in range(2)]
    z = [sp.Matrix(m, 1, sp.symbols(f"z{a}_0:{m}")) for a in range(2)]
    xi = sp.Symbol("xi")
    pv = sp.Matrix(m, 1, sp.symbols(f"p0:{m}"))
    q = sp.Matrix(m, 1, sp.symbols(f"q0:{m}"))
    Xp = sp.Matrix(m, m, sp.symbols(f"X0:{m * m}"))
    return al, be, u, y, z, xi, pv, q, Xp


def zero(M):
    return all(sp.expand(v) == 0 for v in M) if hasattr(M, "shape") else sp.expand(M) == 0


def part1():
    for d in (2, 3, 4):
        m = d - 1
        al, be, u, y, z, xi, pv, q, Xp = block_symbols(m)
        # A_a' general: the proof uses only that the first row of A_a is (alpha_a, 0, ..., 0)
        Ap = [sp.Matrix(m, m, sp.symbols(f"A{a}_0:{m * m}")) for a in range(2)]
        Bp = [sp.Matrix(m, m, sp.symbols(f"B{a}_0:{m * m}")) for a in range(2)]
        A = [sp.Matrix(sp.BlockMatrix([[sp.Matrix([[al[a]]]), sp.zeros(1, m)], [u[a], Ap[a]]])) for a in range(2)]
        B = [sp.Matrix(sp.BlockMatrix([[sp.Matrix([[be[a]]]), y[a].T], [z[a], Bp[a]]])) for a in range(2)]
        X = sp.Matrix(sp.BlockMatrix([[sp.Matrix([[xi]]), pv.T], [q, Xp]]))
        D = X.T - sum((A[a] * X * B[a].T for a in range(2)), sp.zeros(d, d))
        e1, e2, e3, e4 = eqs(al, be, u, y, z, Ap, Bp, xi, pv, q, Xp)
        assert zero(D[0, 0] - e1) and zero(D[0, 1:].T - e2) and zero(D[1:, 0] - e3) and zero(D[1:, 1:] - e4)
        assert all(A[a][0, j] == 0 for a in range(2) for j in range(1, d))
        print(f"part 1: d = {d}: the blocks of X^T - sum_a A_a X B_a^T are the left sides of (1)-(4): identities "
              f"of integer polynomials")


def part2():
    dot = lambda s, t: (s.T * t)[0, 0]
    for m in (1, 2, 3):
        al, be, u, y, z, xi, pv, q, Xp = block_symbols(m)
        w = sp.Matrix(m, 1, sp.symbols(f"w0:{m}"))
        tau = sp.Symbol("tau")
        one, nul = sp.eye(m), sp.zeros(m, m)
        A1 = sp.Matrix(m, m, sp.symbols(f"A0:{m * m}"))
        B1 = sp.Matrix(m, m, sp.symbols(f"B0:{m * m}"))
        zv = sp.zeros(m, 1)
        for case, A1p, B1p in (("I", A1, nul), ("II", nul, B1)):
            e1, e2, e3, e4 = eqs(al, be, u, y, z, [one, A1p], [one, B1p], xi, pv, q, Xp)
            # (2'), (4') and (ii) in the normal form
            q2 = xi * (al[0] * z[0] + al[1] * z[1]) + (al[0] * one + al[1] * B1p) * pv
            R = (u[0] * xi + q) * z[0].T + (u[1] * xi + A1p * q) * z[1].T + u[0] * pv.T + u[1] * (B1p * pv).T
            assert zero(e2 - (q - q2))
            assert zero(e4 - (Xp.T - Xp - R))
            at0 = {xi: 0, **{v: 0 for v in list(pv) + list(q)}}
            assert zero(e3.subs(at0) + Xp * y[0] + A1p * Xp * y[1])
            Rq = lambda sub: R.subs({q[i]: q2[i] for i in range(m)}).subs(sub)
            xi0 = {xi: 0}
            xi1 = {xi: 1, **{v: 0 for v in pv}}
            if case == "I":
                y0 = {v: 0 for v in list(y[0]) + list(y[1])}
                # (3) at xi = 0 with y = 0:  p = alpha_0 beta_0 p + alpha_0 beta_1 A_1' p
                e3q = e3.subs({q[i]: q2[i] for i in range(m)}).subs(y0).subs(xi0)
                assert zero(e3q - (pv - al[0] * be[0] * pv - al[0] * be[1] * A1 * pv))
                # w^T R w at xi = 0
                form = dot(w, Rq(xi0) * w)
                assert zero(form - dot(pv, dot(al[0] * z[0] + u[0], w) * w + al[0] * dot(z[1], w) * A1.T * w))
            else:
                y0 = {v: 0 for v in y[0]}
                e3q = e3.subs({q[i]: q2[i] for i in range(m)}).subs(y0)
                # (3a), (3b)
                assert zero(e3q.subs(xi0) - (pv - (al[0] * be[0] * one + al[1] * be[0] * B1 + u[1] * y[1].T) * pv))
                assert zero(e3q.subs(xi1) + be[0] * (u[0] + al[0] * z[0] + al[1] * z[1]) + be[1] * u[1])
                # sub-case alpha_1 = 0: w^T R w at xi = 0
                form = dot(w, Rq(xi0).subs({al[1]: 0}) * w)
                vec = dot(al[0] * z[0] + u[0], w) * w + dot(u[1], w) * B1.T * w
                assert zero(form - dot(pv, vec))
                scal = {B1[i, j]: (tau if i == j else 0) for i in range(m) for j in range(m)}
                assert zero(vec.subs(scal) - dot(al[0] * z[0] + u[0] + tau * u[1], w) * w)
                # after the last recombination: B_1' = 0
                B0 = {B1[i, j]: 0 for i in range(m) for j in range(m)}
                assert zero(dot(w, Rq(xi0).subs(B0) * w) - dot(pv, w) * dot(al[0] * z[0] + u[0], w))
                u0 = {u[0][i]: -al[0] * z[0][i] for i in range(m)}
                R1 = Rq(xi1).subs(B0).subs(u0)
                assert zero(R1 - (al[1] * z[1] * z[0].T + u[1] * z[1].T))
                assert zero(dot(w, (u[1] * z[1].T) * w) - dot(u[1], w) * dot(z[1], w))
        # last line: A_0 B_0 = 1
        a0 = al[0]
        A0 = sp.Matrix(sp.BlockMatrix([[sp.Matrix([[a0]]), sp.zeros(1, m)], [-a0 * z[0], sp.eye(m)]]))
        B0m = sp.Matrix(sp.BlockMatrix([[sp.Matrix([[1 / a0]]), sp.zeros(1, m)], [z[0], sp.eye(m)]]))
        assert (A0 * B0m).applyfunc(sp.simplify) == sp.eye(m + 1)
        print(f"part 2: m = {m}: (2'), (4'), (ii), (3a), (3b), the forms w^T R w of Steps 3 and 4, R at xi = 1, and "
              f"A_0 B_0 = 1, derived from (1)-(4) in the normal forms I and II: identities")


# ---------------------------------------------------------------- part 3: d = 2, complete
def part3():
    d = 2
    S = swap_matrix(d)
    for p in (2, 3, 5):
        vecs = [np.array(v, dtype=np.int64) for v in itertools.product(range(p), repeat=4) if any(v)]
        found = set()
        two_terms = 0
        for a in vecs:
            if a[np.nonzero(a)[0][0]] != 1:           # a b^T = (c a)(b/c)^T: normalise a
                continue
            for b in vecs:
                K = (S - np.outer(a, b)) % p
                r = rank_mod(realign(K, d), p)
                if r > 2:
                    continue
                two_terms += 1
                assert r == 1, (p, a, b)
                KR = realign(K, d)
                col = KR[:, np.nonzero(KR.any(axis=0))[0][0]]
                G = col.reshape(d, d)
                Gi = inv_mod(G, p)
                assert Gi is not None
                assert (np.kron(G, Gi) % p == K).all()
                found.add(K.tobytes())
        # all G (x) G^-1
        expected = set()
        for g in itertools.product(range(p), repeat=4):
            G = np.array(g, dtype=np.int64).reshape(d, d)
            Gi = inv_mod(G, p)
            if Gi is not None:
                K = np.kron(G, Gi) % p
                assert rank_mod(S - K, p) == 1
                expected.add(K.tobytes())
        assert found == expected
        print(f"part 3: d = 2 over GF({p}): {two_terms} operators with a code of dimension 3 and at most two "
              f"terms; all have one term and are the {len(expected)} operators G (x) G^-1")


# ---------------------------------------------------------------- part 4: exhaustive search (Rust)
def forms_d3():
    d = 3
    one = np.eye(d, dtype=np.int64)
    reg = [
        ("J_3", E(d, (2, 1, 1), (3, 2, 1))),
        ("J_2 + (0)", E(d, (2, 1, 1))),
        ("J_2 + (1)", E(d, (2, 1, 1), (3, 3, 1))),
        ("irreducible cubic x^3 - x - 1", E(d, (2, 1, 1), (3, 2, 1), (1, 3, 1), (2, 3, 1))),
        ("irreducible quadratic x^2 + 1, and (0)", E(d, (2, 1, 1), (1, 2, 2))),
        ("diag(0, 1, 2)", E(d, (2, 2, 1), (3, 3, 2))),
        ("diag(0, 0, 1)", E(d, (3, 3, 1))),
    ]
    out = [("regular, A_0 = 1, A_1 = " + name, one, A) for name, A in reg]
    e = lambda *pos: E(d, *[(i, j, 1) for i, j in pos])
    sing = [
        ("R_2 + zero row and column, R_2 = (1, diag(0,1))", e((1, 1), (2, 2)), e((2, 2))),
        ("R_2 + zero row and column, R_2 = (1, J_2)", e((1, 1), (2, 2)), e((2, 1))),
        ("R_2 + zero row and column, R_2 = (1, x^2 + 1)", e((1, 1), (2, 2)), E(d, (2, 1, 1), (1, 2, 2))),
        ("L_1 + L_0^T + R_1", e((1, 1), (3, 3)), e((1, 2))),
        ("L_1^T + L_0 + R_1", e((1, 1), (3, 3)), e((2, 1))),
        ("L_2 + L_0^T", e((1, 1), (2, 2)), e((1, 2), (2, 3))),
        ("L_2^T + L_0", e((1, 1), (2, 2)), e((2, 1), (3, 2))),
        ("L_1 + L_1^T", e((1, 1), (2, 3)), e((1, 2), (3, 3))),
        ("L_1 + L_0 + 2 L_0^T", e((1, 1)), e((1, 2))),
        ("L_1^T + L_0^T + 2 L_0", e((1, 1)), e((2, 1))),
    ]
    out += [("singular, " + name, A0, A1) for name, A0, A1 in sing]
    return out


def forms_d4():
    d = 4
    one = np.eye(d, dtype=np.int64)
    e = lambda *pos: E(d, *[(i, j, 1) for i, j in pos])
    reg = [
        ("J_4", e((2, 1), (3, 2), (4, 3))),
        ("J_3 + (0)", e((2, 1), (3, 2))),
        ("J_2 + J_2", e((2, 1), (4, 3))),
        ("J_2 + (0) + (0)", e((2, 1))),
        ("J_3 + (1)", e((2, 1), (3, 2), (4, 4))),
        ("J_2(0) + J_2(1)", e((2, 1), (3, 3), (4, 3), (4, 4))),
        ("J_2 + (0) + (1)", e((2, 1), (4, 4))),
        ("J_2 + (1) + (1)", e((2, 1), (3, 3), (4, 4))),
        ("irreducible quartic x^4 + x + 1", e((2, 1), (3, 2), (4, 3), (1, 4), (2, 4))),
        ("Jordan block of the irreducible x^2 + x + 1", e((1, 2), (2, 1), (2, 2), (3, 1), (3, 4), (4, 2), (4, 3),
                                                              (4, 4))),
    ]
    out = [("regular, A_0 = 1, A_1 = " + name, one, A) for name, A in reg]
    out.append(("regular without an invertible element over GF(2): diag(s, s, t, s + t)",
                e((1, 1), (2, 2), (4, 4)), e((3, 3), (4, 4))))
    sing = [
        ("L_1 + L_2^T", e((1, 1), (2, 3), (3, 4)), e((1, 2), (3, 3), (4, 4))),
        ("L_3 + L_0^T", e((1, 1), (2, 2), (3, 3)), e((1, 2), (2, 3), (3, 4))),
        ("L_1 + L_1^T + R_1", e((1, 1), (2, 3), (4, 4)), e((1, 2), (3, 3))),
        ("R_3 + zero row and column, R_3 = (1, J_3)", e((1, 1), (2, 2), (3, 3)), e((2, 1), (3, 2))),
        ("L_2 + L_1^T", e((1, 1), (2, 2), (3, 4)), e((1, 2), (2, 3), (4, 4))),
    ]
    out += [("singular, " + name, A0, A1) for name, A0, A1 in sing]
    return out


def flat(M):
    return "".join(str(int(v)) for v in np.array(M).reshape(-1))


def expected_pairs(A0, A1, p):
    d = A0.shape[0]
    exp = set()
    for g0 in range(p):
        for g1 in range(p):
            G = (g0 * A0 + g1 * A1) % p
            Gi = inv_mod(G, p)
            if Gi is not None:
                exp.add((flat((g0 * Gi) % p), flat((g1 * Gi) % p)))
    return exp


def run_bf(binary, p, d, threads, A0, A1):
    res = subprocess.run([binary, str(p), str(d), str(threads), flat(A0), flat(A1)], capture_output=True, text=True,
                         check=True)
    lines = res.stdout.split("\n")
    lines = [ln for ln in lines if ln]
    assert lines[-1].startswith("done")
    _, count, total = lines[-1].split()
    assert int(total) == p ** (2 * d * d) and int(count) == len(lines) - 1
    return {tuple(ln.split()) for ln in lines[:-1]}


def python_enum(p, d, A0, A1):
    S = swap_matrix(d)
    n = d * d
    out = set()
    for digs in itertools.product(range(p), repeat=2 * n):
        B0 = np.array(digs[:n], dtype=np.int64).reshape(d, d)
        B1 = np.array(digs[n:], dtype=np.int64).reshape(d, d)
        if rank_mod(S - op([(A0, B0), (A1, B1)], p), p) <= d * (d - 1) // 2:
            out.add((flat(B0), flat(B1)))
    return out


def part4(threads):
    tmp = tempfile.mkdtemp(prefix="two_term_bf_")
    binary = os.path.join(tmp, "two_term_bf")
    subprocess.run(["rustc", "-O", "-o", binary, os.path.join(HERE, "two_term_bf.rs")], check=True)
    # the enumerator against Python
    for p, d, trials in ((3, 2, 6), (2, 2, 6)):
        for _ in range(trials):
            A0 = np.array([[rng.randrange(p) for _ in range(d)] for _ in range(d)], dtype=np.int64)
            A1 = np.array([[rng.randrange(p) for _ in range(d)] for _ in range(d)], dtype=np.int64)
            assert run_bf(binary, p, d, 2, A0, A1) == python_enum(p, d, A0, A1)
    for _ in range(2):                          # the bit-mask path at d = 3 (2^18 pairs each)
        A0 = np.array([[rng.randrange(2) for _ in range(3)] for _ in range(3)], dtype=np.int64)
        A1 = np.array([[rng.randrange(2) for _ in range(3)] for _ in range(3)], dtype=np.int64)
        assert run_bf(binary, 2, 3, 2, A0, A1) == python_enum(2, 3, A0, A1)
    one3 = np.eye(3, dtype=np.int64)
    J3 = E(3, (2, 1, 1), (3, 2, 1))
    assert run_bf(binary, 2, 3, 2, one3, J3) == python_enum(2, 3, one3, J3) == expected_pairs(one3, J3, 2)
    print("part 4: the enumerator agrees with a Python enumeration on 12 random pairs of row factors at d = 2 "
          "over GF(3) and GF(2), and at d = 3 over GF(2) on 2 random pairs and on (1, J_3)", flush=True)
    for p, d, forms in ((3, 3, forms_d3()), (2, 4, forms_d4())):
        S = swap_matrix(d)
        for name, A0, A1 in forms:
            assert rank_mod(np.stack([A0.reshape(-1), A1.reshape(-1)]), p) == 2
            t0 = time.time()
            got = run_bf(binary, p, d, threads, A0, A1)
            for b0, b1 in got:                  # each reported pair: code of dimension exactly d(d+1)/2, one term
                B0 = np.array([int(c) for c in b0], dtype=np.int64).reshape(d, d)
                B1 = np.array([int(c) for c in b1], dtype=np.int64).reshape(d, d)
                K = op([(A0, B0), (A1, B1)], p)
                assert rank_mod(S - K, p) == d * (d - 1) // 2
                assert rank_mod(realign(K, d), p) == 1
            exp = expected_pairs(A0, A1, p)
            assert got == exp, (name, len(got), len(exp))
            what = ("exactly the g_a G^-1 with G invertible in the pencil" if got
                    else "and the pencil has no invertible element over the field")
            print(f"part 4: d = {d} over GF({p}), {name}: {p ** (2 * d * d)} pairs (B_0, B_1); "
                  f"{len(got)} with a code of dimension >= {d * (d + 1) // 2}, {what} "
                  f"({time.time() - t0:.0f} s)", flush=True)


# ---------------------------------------------------------------- part 5: the dual statement on examples
def part5():
    for d, p in ((3, 5), (4, 5), (5, 7)):
        S = swap_matrix(d)
        for _ in range(5):
            while True:
                G = np.array([[rng.randrange(p) for _ in range(d)] for _ in range(d)], dtype=np.int64)
                Gi = inv_mod(G, p)
                if Gi is not None:
                    break
            # K_G X = X^T - tr(G^-T X) G: matrix swap - vec(G) vec(G^-1)^T
            K = (S - np.outer(G.reshape(-1), Gi.reshape(-1))) % p
            assert rank_mod(S - K, p) == 1
            KR = realign(K, d)
            assert (KR == (S - np.kron(G, Gi)) % p).all()
            assert rank_mod(KR, p) == d * (d - 1) // 2
            # the span of the row factors is the column space of K^R = {alternating} G^-T
            alt = []
            for i in range(d):
                for j in range(i + 1, d):
                    L = np.zeros((d, d), dtype=np.int64)
                    L[i, j], L[j, i] = 1, -1
                    alt.append(((L @ Gi.T) % p).reshape(-1))
            alt = np.array(alt)
            both = np.concatenate([alt, KR.T])
            assert rank_mod(alt, p) == rank_mod(both, p) == d * (d - 1) // 2
            # the span of the column factors is the row space of K^R = {alternating} G^-1
            altc = []
            for i in range(d):
                for j in range(i + 1, d):
                    L = np.zeros((d, d), dtype=np.int64)
                    L[i, j], L[j, i] = 1, -1
                    altc.append(((L @ Gi) % p).reshape(-1))
            altc = np.array(altc)
            assert rank_mod(altc, p) == rank_mod(np.concatenate([altc, KR]), p) == d * (d - 1) // 2
            if d == 3:                              # every element of both spans is singular
                for co in itertools.product(range(p), repeat=3):
                    for sp_ in (alt, altc):
                        M = sum(c * v for c, v in zip(co, sp_)).reshape(d, d) % p
                        assert rank_mod(M, p) <= 2
                assert max(rank_mod(v.reshape(d, d), p) for v in alt) == 2
        print(f"part 5: d = {d} over GF({p}): K_G has {d * (d - 1) // 2} terms, codimension 1, row factors spanning "
              f"(alternating) G^-T (5 random G)")
    # G = 1 over the integers: X^T - tr(X) 1 = sum_{i<j} L_ij X L_ij
    for d in (3, 4):
        S = swap_matrix(d)
        K = np.zeros((d * d, d * d), dtype=np.int64)
        for i in range(d):
            for j in range(i + 1, d):
                L = np.zeros((d, d), dtype=np.int64)
                L[i, j], L[j, i] = 1, -1
                K += np.kron(L, L.T)            # X -> L X (L^T)^T = L X L
        one = np.eye(d, dtype=np.int64).reshape(-1)
        assert (K == S - np.outer(one, one)).all()
    print("part 5: X^T - tr(X) 1 = sum_{i<j} L_ij X L_ij with L_ij = E_ij - E_ji (d = 3, 4, over the integers)")
    # codimension 2 with d(d-1)/2 + 1 terms: K_1 + E_11 (x) E_11
    for p in (2, 3, 5):
        for d in (2, 3, 4, 5):
            S = swap_matrix(d)
            one = np.eye(d, dtype=np.int64).reshape(-1)
            E11 = np.zeros((d, d), dtype=np.int64)
            E11[0, 0] = 1
            K = (S - np.outer(one, one) + np.kron(E11, E11)) % p
            assert rank_mod(S - K, p) == 2 and rank_mod(realign(K, d), p) == d * (d - 1) // 2 + 1
    print("part 5: X -> X^T - tr(X) 1 + x_11 E_11 has d(d-1)/2 + 1 terms and a code of codimension 2 "
          "(d = 2, ..., 5 over GF(2), GF(3), GF(5))")


if __name__ == "__main__":
    part1()
    part2()
    part3()
    part5()
    if len(sys.argv) > 1 and sys.argv[1] == "all":
        part4(int(sys.argv[2]) if len(sys.argv) > 2 else 4)
    print("done")
