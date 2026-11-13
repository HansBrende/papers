"""Genericity check for the consistency lemma (lean-backlog/notes/twisted-swap.md, Theorem 4(b)):
for random U in M_n, n = 2k+1, i = 0, S = {1..k}, S' = {k+1..2k}, the kernel
vectors v, v' of U[S, S^c], U[S', S'^c] and gamma = (Uv)_i/v_i - (Uv')_i/v'_i.
For n = 3 gamma must equal delta/(U_23 U_32) with delta the cyclic defect
(indices 1-based in the note). Prints the smallest |gamma| over 1000 samples."""
import numpy as np
rng = np.random.default_rng(1)
for n in (3, 5, 7, 9):
    k = (n - 1) // 2
    S, S2 = list(range(1, k + 1)), list(range(k + 1, 2 * k + 1))
    worst, err = np.inf, 0.0
    for _ in range(1000):
        U = rng.standard_normal((n, n))
        def ker(Sx):
            Sc = [j for j in range(n) if j not in Sx]
            _, s, vt = np.linalg.svd(U[np.ix_(Sx, Sc)])
            v = np.zeros(n); v[Sc] = vt[-1]
            assert s[-1] > 1e-9 if len(s) == k else True
            return v
        v, v2 = ker(S), ker(S2)
        g = (U @ v)[0] / v[0] - (U @ v2)[0] / v2[0]
        worst = min(worst, abs(g))
        if n == 3:
            delta = U[0,1]*U[1,2]*U[2,0] - U[0,2]*U[2,1]*U[1,0]
            # S = {1}: v = (U12, 0, -U10) in 0-based; S' = {2}: v' = (U21, -U20, 0)
            err = max(err, abs(g - delta / (U[1,2]*U[2,1])))
    print(f"n={n}: min |gamma| over 1000 random U = {worst:.3e}" + (f", max |gamma - delta/(U23 U32)| = {err:.1e}" if n == 3 else ""))
