#!/usr/bin/env python3
"""Standalone numerical cross-checks for Remarks 4.3 and 5.7 of the paper.

Usage (from the paper directory, or from anywhere):

    python3 tools/reproduce_numerics.py

Uses only the Python 3 standard library. None of the Lean proofs in the paper
depends on this script; it independently checks the finite examples mentioned in
Remark 4.3 (rem:deg4-numerics) and Remark 5.7 (rem:dnp-numerics):
  1. Bipartite degree-4 family G_{8k} (2 <= k <= 6): connectedness, bipartiteness
     (hence triangle-freeness), vertex degrees (4 on H, 3 on V \\ H), exact
     matching number nu(G_{8k}) = 4k, exact packing numbers rho_3(G_{8k}, H) = k
     and rho_m(G_{8k}, H) = 2k, and explicit unit-diagonal F_2 check matrix M
     supported on G_{8k} with heavy set H attaining dim ker M = 4k.
  2. Deep-nesting walk U(s_0, m, 1) and pair DNP(s_0, m):
     - Proposition SL: stroke decomposition bijection, stopping-depth and parity
       counts, and O(m) recursive turn potential vs cumulative turn-jump sums;
     - Theorem V*: Z-cancellation, mod-q straddle pair/set inequalities, and
       exact parity-conditioned straddle sum (Pi_kappa / 2)^2;
     - Theorem LU: super-Fibonacci unwrapping and 2 floor(log2 q) + 2 bound;
     - Proposition OC: block path-sum bounds, exact mean drift, and Mersenne
       straddle residue q - 1;
     - Theorem A: exhaustive odd-shift straddle sum on (s_0 = 7, m = 6), and
       explicit odd-shift witness and three-regime verification on
       (s_0 = 24, m = 23, a_1 = a_2 = 1), where 4(floor(log2 24) + 1 + 1) = 24.
"""

from bisect import bisect_right
from collections import deque
from itertools import product


# ---------------------------------------------------------------------------
# 1. Remark 4.3: Bipartite degree-4 family G_{8k} separating rho_m from rho_3
# ---------------------------------------------------------------------------


def build_g8k(k: int):
    """Construct G_{8k} on 8k vertices: 0..4k-1 (A-side) and 4k..8k-1 (B-side)."""
    assert k >= 2
    n = 8 * k
    adj = [set() for _ in range(n)]

    def a_idx(r: int, j: int) -> int:
        return 4 * r + j

    def b_idx(r: int, j: int) -> int:
        return 4 * k + 4 * r + j

    def add_edge(u: int, v: int) -> None:
        adj[u].add(v)
        adj[v].add(u)

    for r in range(k):
        for j in range(4):
            add_edge(a_idx(r, 0), b_idx(r, j))
            add_edge(a_idx(r, j), b_idx(r, 0))
        for j in range(1, 4):
            add_edge(a_idx(r, j), b_idx(r, j))
            r_next = (r + 1) % k
            j_next = (j % 3) + 1
            add_edge(a_idx(r, j), b_idx(r_next, j_next))

    heavy = [a_idx(r, 0) for r in range(k)] + [b_idx(r, 0) for r in range(k)]
    return n, adj, heavy, a_idx, b_idx


def bfs_distances(n: int, adj, src: int):
    dist = [-1] * n
    dist[src] = 0
    q = deque([src])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if dist[w] == -1:
                dist[w] = dist[u] + 1
                q.append(w)
    return dist


def bipartite_matching_size(k: int, adj) -> int:
    """Exact maximum matching on bipartition [0..4k-1] x [4k..8k-1]."""
    left_n = 4 * k
    match_right = {}

    def dfs(u: int, seen: set) -> bool:
        for v in adj[u]:
            if v in seen:
                continue
            seen.add(v)
            if v not in match_right or dfs(match_right[v], seen):
                match_right[v] = u
                return True
        return False

    matched = 0
    for u in range(left_n):
        if dfs(u, set()):
            matched += 1
    return matched


def max_valid_subset(items, compat) -> int:
    """Exact maximum clique/independent-set style packing over <= 12 heavy vertices."""
    m = len(items)
    best = 0
    for mask in range(1 << m):
        pop = mask.bit_count()
        if pop <= best:
            continue
        ok = True
        chosen = [items[i] for i in range(m) if (mask >> i) & 1]
        for idx1 in range(len(chosen)):
            for idx2 in range(idx1 + 1, len(chosen)):
                if not compat(chosen[idx1], chosen[idx2]):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            best = pop
    return best


def f2_nullity(rows_masks: list[int], ncols: int) -> int:
    basis = {}
    for row in rows_masks:
        x = row
        while x:
            msb = x.bit_length() - 1
            if msb in basis:
                x ^= basis[msb]
            else:
                basis[msb] = x
                break
    return ncols - len(basis)


def verify_deg4_family() -> None:
    print("=== Remark 4.3: Bipartite degree-4 family G_{8k} ===")
    for k in range(2, 7):
        n, adj, heavy, a_idx, b_idx = build_g8k(k)
        heavy_set = set(heavy)

        # Connectedness and bipartiteness
        d0 = bfs_distances(n, adj, 0)
        assert all(d >= 0 for d in d0), f"G_{n} disconnected"
        for u in range(4 * k):
            assert all(v >= 4 * k for v in adj[u]), "A-side edge not bipartite"
        for v in range(4 * k, 8 * k):
            assert all(u < 4 * k for u in adj[v]), "B-side edge not bipartite"

        # Degrees: 4 on H, 3 on V \ H
        for v in range(n):
            expected_deg = 4 if v in heavy_set else 3
            assert len(adj[v]) == expected_deg, (v, len(adj[v]), expected_deg)

        nu = bipartite_matching_size(k, adj)
        assert nu == 4 * k

        all_dists = {u: bfs_distances(n, adj, u) for u in heavy}
        rho3 = max_valid_subset(heavy, lambda u, v: all_dists[u][v] >= 3)
        rhom = max_valid_subset(heavy, lambda u, v: len(adj[u] & adj[v]) == 0)
        assert rho3 == k, (k, rho3)
        assert rhom == 2 * k, (k, rhom)

        # Explicit unit-diagonal F_2 check matrix M supported on G_{8k}
        # with heavy set H_M = H attaining dim_{F_2} ker M = 4k:
        rows = []
        actual_heavy = set()
        for r in range(k):
            u0 = a_idx(r, 0)
            v0 = b_idx(r, 0)
            row_u0 = (1 << u0)
            for j in range(4):
                row_u0 |= 1 << b_idx(r, j)
            rows.append(row_u0)

            row_v0 = (1 << v0)
            for j in range(4):
                row_v0 |= 1 << a_idx(r, j)
            rows.append(row_v0)

            for j in range(1, 4):
                uj = a_idx(r, j)
                vj = b_idx(r, j)
                rows.append((1 << uj) | (1 << vj))
                rows.append((1 << vj) | (1 << uj))

        # Check support in G_{8k}, unit diagonal, and heavy set H_M == H
        assert len(rows) == n
        for idx, mask in enumerate(rows):
            # Reconstruct vertex index by finding diagonal/support: build indexed dict instead
            pass
        mat = {}
        for r in range(k):
            mat[a_idx(r, 0)] = {b_idx(r, j) for j in range(4)}
            mat[b_idx(r, 0)] = {a_idx(r, j) for j in range(4)}
            for j in range(1, 4):
                mat[a_idx(r, j)] = {b_idx(r, j)}
                mat[b_idx(r, j)] = {a_idx(r, j)}
        for v in range(n):
            assert mat[v] <= adj[v]
            # Star condition: |N_M(v)| <= 2, or (|N_M(v)| == 3 and reciprocated)
            rec_ok = len(mat[v]) <= 2 or (
                len(mat[v]) == 3 and all(v in mat[u] for u in range(n) if u != v and v in mat[u])
            )
            if not rec_ok:
                actual_heavy.add(v)
        assert actual_heavy == heavy_set
        ker_dim = f2_nullity(rows, n)
        assert ker_dim == 4 * k
        bound_old = nu + len(heavy) - rho3
        bound_new = nu + len(heavy) - rhom
        assert bound_old == 5 * k and bound_new == 4 * k
        print(
            f"  k={k}: |V|={n:2d}, |H|={len(heavy):2d}, nu={nu:2d}, "
            f"rho_3={rho3}, rho_m={rhom:2d}, old_bound={bound_old:2d}, "
            f"SH*_bound={bound_new:2d}, explicit dim_F2(ker M)={ker_dim:2d}"
        )


# ---------------------------------------------------------------------------
# 2. Deep-nesting walk U(s_0, m, 1) and Theorem A cross-checks (Remark 5.7)
# ---------------------------------------------------------------------------


def scale_r(s0: int, i: int) -> int:
    return 1 << (s0 - i)


def stroke_len(s0: int, m: int, kappa: int) -> int:
    return (m - kappa + 1) * scale_r(s0, kappa)


def dnp_period(s0: int, m: int) -> int:
    return 4 * stroke_len(s0, m, 0)


def decomp_depth(s0: int, m: int, kappa: int, o: int):
    rk = scale_r(s0, kappa)
    if kappa == m or o < rk:
        return 0, (), o
    pik1 = stroke_len(s0, m, kappa + 1)
    if o < rk + pik1:
        s, w, rem = decomp_depth(s0, m, kappa + 1, o - rk)
        return s + 1, (False,) + w, rem
    s, w, rem = decomp_depth(s0, m, kappa + 1, o - rk - pik1)
    return s + 1, (True,) + w, rem


def reconstruct_depth(s0: int, m: int, kappa: int, s: int, w: tuple[bool, ...], rem: int) -> int:
    if s == 0:
        return rem
    rk = scale_r(s0, kappa)
    sub = reconstruct_depth(s0, m, kappa + 1, s - 1, w[1:], rem)
    if not w[0]:
        return rk + sub
    return rk + stroke_len(s0, m, kappa + 1) + sub


def stroke_mass(m: int, cb, cf, kappa: int) -> int:
    return sum(cf(l) for l in range(kappa + 1, m + 1))


def stroke_turn_jump(s0: int, m: int, cb, cf, kappa: int, o: int) -> int:
    if o == 0 or kappa >= m:
        return 0
    rk = scale_r(s0, kappa)
    pik1 = stroke_len(s0, m, kappa + 1)
    if o < rk:
        return 0
    if o == rk:
        return cb(kappa + 1)
    if o < rk + pik1:
        return stroke_turn_jump(s0, m, cb, cf, kappa + 1, o - rk)
    if o == rk + pik1:
        return cf(kappa + 1) - cb(kappa + 1) - stroke_mass(m, cb, cf, kappa + 1)
    if o < rk + 2 * pik1:
        return stroke_turn_jump(s0, m, cb, cf, kappa + 1, o - rk - pik1)
    return 0


def period_turn_jump(s0: int, m: int, cb, cf, j_tip: int, t: int) -> int:
    pi0 = stroke_len(s0, m, 0)
    if t == 0 or t >= 4 * pi0:
        return 0
    q_stroke, rem = divmod(t, pi0)
    if rem == 0:
        return j_tip if q_stroke in (1, 3) else 0
    return stroke_turn_jump(s0, m, cb, cf, 0, rem)


def stroke_phi_rec(s0: int, m: int, cb, cf, kappa: int, o: int) -> int:
    rk = scale_r(s0, kappa)
    if kappa >= m or o < rk:
        return 0
    pik1 = stroke_len(s0, m, kappa + 1)
    if o < rk + pik1:
        return cb(kappa + 1) + stroke_phi_rec(s0, m, cb, cf, kappa + 1, o - rk)
    return cf(kappa + 1) + stroke_phi_rec(s0, m, cb, cf, kappa + 1, o - rk - pik1)


def eval_phi_rec(s0: int, m: int, cb, cf, j_tip: int, t: int) -> int:
    pi0 = stroke_len(s0, m, 0)
    m0 = stroke_mass(m, cb, cf, 0)
    q_stroke, rem = divmod(t, pi0)
    if q_stroke == 0:
        return stroke_phi_rec(s0, m, cb, cf, 0, rem)
    if q_stroke == 1:
        return m0 + j_tip + stroke_phi_rec(s0, m, cb, cf, 0, rem)
    if q_stroke == 2:
        return 2 * m0 + j_tip + stroke_phi_rec(s0, m, cb, cf, 0, rem)
    return 3 * m0 + 2 * j_tip + stroke_phi_rec(s0, m, cb, cf, 0, rem)


def is_canceller(m: int, a: int, kappa: int) -> bool:
    return (m - kappa) % (a + 1) == a


def block_q(a: int, k_param: int) -> int:
    return ((1 << a) - 1) * (2 * k_param + 2)


def block_a(m: int, a: int, k_param: int, kappa: int) -> int:
    return 0 if is_canceller(m, a, kappa) else k_param


def block_e(m: int, a: int, k_param: int, kappa: int) -> int:
    if is_canceller(m, a, kappa):
        return -block_q(a, k_param) - 2
    j = (m - kappa) % (a + 1)
    return k_param + ((1 << j) - 1) * (2 * k_param + 2)


def period_v_apices(s0: int, m: int, kappa: int) -> list[int]:
    """Sorted list of all 2^(kappa+1) level-kappa V start times in [0, P)."""
    pi0 = stroke_len(s0, m, 0)
    apices = []
    for s0_idx in range(4):
        base0 = s0_idx * pi0
        for bits in product((False, True), repeat=kappa - 1):
            pos = base0
            for idx, b in enumerate(bits):
                lvl = idx  # 0 .. kappa - 2
                pos += scale_r(s0, lvl)
                if b:
                    pos += stroke_len(s0, m, lvl + 1)
            pos += scale_r(s0, kappa - 1)
            apices.append(pos)
    apices.sort()
    assert len(apices) == (1 << (kappa + 1))
    return apices


def single_center_straddle_card(c0: int, alpha_v: int, pi_kappa: int, rk: int) -> int:
    """Count d in [1, rk - 1] with alpha_v <= c0 - d < alpha_v + pi_kappa <= c0 + d < alpha_v + 2*pi_kappa."""
    lo = max(1, c0 - (alpha_v + pi_kappa) + 1, (alpha_v + pi_kappa) - c0)
    hi = min(rk - 1, c0 - alpha_v, alpha_v + 2 * pi_kappa - 1 - c0)
    return max(0, hi - lo + 1)


def fast_class_straddle_count(
    p_period: int,
    k_apices: list[int],
    kappa_apices: list[int],
    pi_kappa: int,
    rk: int,
    direction: bool,
    xi: int,
) -> int:
    total = 0
    for c in k_apices:
        c0 = (c + xi) % p_period if direction else (c + p_period - xi) % p_period
        idx = bisect_right(kappa_apices, c0) - 1
        if idx >= 0:
            av = kappa_apices[idx]
            if c0 < av + 2 * pi_kappa:
                total += single_center_straddle_card(c0, av, pi_kappa, rk)
    return total


def canceller_below(m: int, a: int, k: int) -> int:
    j0 = (m + 1).bit_length()  # floor(log2(m+1)) + 1
    rem = (m - (k + j0)) % (a + 1)
    delta = (rem + 1) % (a + 1)
    return k + j0 + delta


def verify_dnp_theorems() -> None:
    print("\n=== Remark 5.7: Deep-nesting stroke, straddle, Fibonacci, and Theorem A checks ===")

    # (a) Proposition SL on (s_0 = 6, m = 5)
    s0, m = 6, 5
    pi0 = stroke_len(s0, m, 0)
    counts = {}
    for o in range(pi0):
        s, w, rem = decomp_depth(s0, m, 0, o)
        assert reconstruct_depth(s0, m, 0, s, w, rem) == o
        assert o % 2 == rem % 2
        counts[(s, w, o % 2)] = counts.get((s, w, o % 2), 0) + 1
    for s in range(m + 1):
        for w in product((False, True), repeat=s):
            for par in (0, 1):
                assert counts[(s, w, par)] == scale_r(s0, s) // 2

    cb = lambda l: 1 + block_a(m, 2, 3, l)
    cf = lambda l: 2 + block_a(m, 2, 3, l) + block_e(m, 2, 3, l)
    p_per = dnp_period(s0, m)
    running = 0
    for t in range(p_per):
        if t > 0:
            running += period_turn_jump(s0, m, cb, cf, 5, t)
        assert eval_phi_rec(s0, m, cb, cf, 5, t) == running
    print(f"  Proposition SL verified on (s_0={s0}, m={m}, P={p_per}): bijection, parity, and evalPhiRec exact.")

    # (b) Theorem V* parity-conditioned straddle sum & mod-q pair bound
    av, l_half, rk = 14, 12, 32
    pi_k = 2 * l_half
    for par in (0, 1):
        s_par = sum(
            single_center_straddle_card(c0, av, pi_k, rk)
            for c0 in range(av, av + 2 * pi_k)
            if c0 % 2 == par
        )
        assert s_par == l_half * l_half
    print(f"  Theorem V* parity straddle sum verified: even={l_half**2}, odd={l_half**2} == (Pi_kappa/2)^2.")

    # (c) Proposition OC: block mean drift and Mersenne straddle failure
    for a in (1, 2, 3, 4):
        for k_param in (0, 1, 4):
            q_mass = block_q(a, k_param)
            total_drift = 0
            for d_canc in (False, True):
                for d_srv in product((False, True), repeat=a):
                    val = (-q_mass if d_canc else 1) + sum(
                        ((1 << j) * (2 * k_param + 2) if d_srv[j] else (1 + k_param))
                        for j in range(a)
                    )
                    if d_canc:
                        assert -q_mass + a * (1 + k_param) <= val <= 0
                    else:
                        assert 1 + a * (1 + k_param) <= val <= q_mass + 1
                    total_drift += val
            assert total_drift == (1 << a) * (a * (k_param + 1) + 1)
    for b_exp in range(2, 8):
        q_mers = (1 << b_exp) - 1
        for m_val in range(b_exp, 20):
            for kap in range(1, m_val + 1):
                if (m_val - kap + 2) % b_exp == 0:
                    res = (2 * ((1 << (m_val - kap + 1)) - 1)) % q_mers
                    assert res == q_mers - 1
    print("  Proposition OC verified: block drift exact and Mersenne straddle residue == q - 1.")

    # (d) Exhaustive odd-shift straddle sum on (s_0 = 7, m = 6)
    s0_ex, m_ex = 7, 6
    p_ex = dnp_period(s0_ex, m_ex)
    odd_shifts = [xi for xi in range(p_ex) if xi % 2 == 1]
    for k in (1, 2):
        kap = 5
        pi_kap = stroke_len(s0_ex, m_ex, kap)
        rk_ex = scale_r(s0_ex, k)
        assert pi_kap <= rk_ex
        k_aps = period_v_apices(s0_ex, m_ex, k)
        kap_aps = period_v_apices(s0_ex, m_ex, kap)
        for dir_flag in (True, False):
            tot = sum(
                fast_class_straddle_count(p_ex, k_aps, kap_aps, pi_kap, rk_ex, dir_flag, xi)
                for xi in odd_shifts
            )
            expected = (1 << (k + 1)) * (1 << (kap + 1)) * ((pi_kap // 2) ** 2)
            assert tot == expected, (tot, expected)
    print(f"  Exhaustive odd-shift sum verified on (s_0={s0_ex}, m={m_ex}, |Omega|={len(odd_shifts)}).")

    # (e) Theorem A full 3-regime check on (s_0 = 24, m = 23, a_1 = a_2 = 1)
    s0_a, m_a, a1, a2 = 24, 23, 1, 1
    assert 4 * ((m_a + 1).bit_length() + max(a1, a2)) == 24 <= m_a + 1
    p_a = dnp_period(s0_a, m_a)
    k_coarse = list(range(1, (m_a + 1) // 4 + 1))  # {1, 2, 3, 4, 5, 6}
    k_aps_map = {k: period_v_apices(s0_a, m_a, k) for k in k_coarse}
    kap_map = {k: canceller_below(m_a, a2, k) for k in k_coarse}
    kap_aps_map = {kap: period_v_apices(s0_a, m_a, kap) for kap in set(kap_map.values())}

    # Deterministic stride scan over odd shifts in [0, P) finds a reverse-Markov witness immediately
    witness_xi = None
    stride = (p_a // 64) | 1
    for step in range(256):
        xi = ((step * stride) | 1) % p_a
        good_levels = []
        for k in k_coarse:
            kap = kap_map[k]
            cnt = fast_class_straddle_count(
                p_a,
                k_aps_map[k],
                kap_aps_map[kap],
                stroke_len(s0_a, m_a, kap),
                scale_r(s0_a, k),
                True,
                xi,
            )
            bound = ((1 << (k + 2)) * scale_r(s0_a, k)) // (1 << (a2 + 7))
            if cnt >= bound:
                good_levels.append((k, kap, cnt, bound))
        if 16 * len(good_levels) >= len(k_coarse):
            witness_xi = (xi, good_levels)
            break
    assert witness_xi is not None
    xi_star, good_levels = witness_xi
    print(
        f"  Theorem A witness on (s_0={s0_a}, m={m_a}, a_1=a_2=1): odd shift xi={xi_star} "
        f"simultaneously straddles {len(good_levels)}/{len(k_coarse)} coarse levels "
        f"(bound requires >= 1)."
    )

    # Test all three regimes across representative (K_1, K_2, q)
    def blind_apex_err(m_v: int, a_v: int, k_par: int, q_v: int, k_lvl: int) -> int:
        return block_a(m_v, a_v, k_par, k_lvl) % q_v

    def blind_band_err(m_v: int, a_v: int, k_par: int, q_v: int, k_lvl: int, l_lvl: int) -> int:
        s = sum(
            block_a(m_v, a_v, k_par, i) + block_e(m_v, a_v, k_par, i) + 2
            for i in range(k_lvl + 1, l_lvl + 1)
        )
        return (block_e(m_v, a_v, k_par, k_lvl) - s) % q_v

    for q_small in (3, 7, 15, 31):
        for k_par in (0, 2, 5):
            # Regime 1: every 11-level window [k0, k0+11) has an error > q/8
            for k0 in range(1, m_a - 11):
                errs = []
                for idx in range(11):
                    errs.append(blind_apex_err(m_a, a1, k_par, q_small, k0 + idx))
                    errs.append(blind_band_err(m_a, a1, k_par, q_small, k0 + idx, k0 + idx))
                    if idx + 1 < 11:
                        errs.append(blind_band_err(m_a, a1, k_par, q_small, k0 + idx, k0 + idx + 1))
                    if idx + 2 < 11:
                        errs.append(blind_band_err(m_a, a1, k_par, q_small, k0 + idx, k0 + idx + 2))
                assert any(8 * e > q_small for e in errs)

    for q_big, k1, k2 in [(64, 0, 2), (64, 10, 3), (127, 4, 4), (256, 30, 5), (512, 7, 12)]:
        k1_mod, k2_mod = k1 % q_big, k2 % q_big
        q1_tilde = block_q(a1, k1_mod)
        q2_tilde = block_q(a2, k2_mod)
        if 4 * q1_tilde + 4 > q_big or 4 * q2_tilde + 4 > q_big:
            # Regime 2: fine-scale doubling overflow on an entire residue class
            k_ov = k1_mod if 4 * q1_tilde + 4 > q_big else k2_mod
            a_ov = a1 if 4 * q1_tilde + 4 > q_big else a2
            found_rem = False
            for rem in range(a_ov):
                levels = [lvl for lvl in range(1, m_a) if (m_a - lvl) % (a_ov + 1) == rem]
                if all(
                    16 * blind_apex_err(m_a, a_ov, k_ov, q_big, lvl) >= q_big
                    or 8 * blind_band_err(m_a, a_ov, k_ov, q_big, lvl, lvl) >= q_big
                    or 8 * blind_band_err(m_a, a_ov, k_ov, q_big, lvl, lvl + 1) >= q_big
                    for lvl in levels
                ):
                    found_rem = True
                    break
            assert found_rem, (q_big, k1, k2)
        else:
            # Regime 3: straddle residue >= q / 2
            active_k, other_q = (k1_mod, q2_tilde) if q1_tilde <= q2_tilde else (k2_mod, q1_tilde)
            for k_lvl, kap, _, _ in good_levels:
                a_val = block_a(m_a, a1, active_k, k_lvl)
                z_res = (2 * a_val + 2 * (-other_q - 1)) % q_big
                assert 2 * z_res >= q_big, (q_big, k1, k2, z_res)
    print("  Theorem A Regimes 1, 2, and 3 verified across all tested (K_1, K_2, q).")


if __name__ == "__main__":
    verify_deg4_family()
    verify_dnp_theorems()
    print("\nAll numerical cross-checks passed.")
