#!/usr/bin/env python3
"""Exact rational and prime-crossover verification for Section 5 (Theorems 5.4 and 5.5).

Usage:
    python3 tools/verify_linear_capacity_crossovers.py

This script uses exact rational arithmetic (fractions.Fraction) and elementary analytic
tail bounds to verify every finite threshold and leading-coefficient comparison cited in
Section 5 (linear_capacity.tex) and README.md against Theorems 3.4 and 3.5 of
Capacity and Composition of Shared Transposition Decoders:

  1. Leading-coefficient comparison against Theorem 3.5 (difference_cover_real_bound):
     For M >= 2, let
         c_M = 1 - 5/(4M) + 1/M^2 - 1/(4M^3)
     and let
         gamma*_M = min_{u, v >= 1} (1 - max(0, 1 - M / (u * v + 1)) / (u + v))
     be the optimized asymptotic leading coefficient of Paper 19's Theorem 3.5.
     Checks:
       - Theorem 3.5 beats the flag bound 1 - 1/(2M) iff M >= 7 (at M = 7, u = 4, v = 5
         gives 25/27 < 13/14), and its square-root form 1 - 1/(4 ceil(sqrt(2M))) beats
         1 - 1/(2M) iff M >= 11.
       - c_M < gamma*_M holds if and only if 2 <= M <= 40 (verified by exact rational
         minimization for 2 <= M <= 500 and an algebraic inequality at u = v = ceil(sqrt(3M))
         for all M > 500; at M = 41, u = v = 11 gives 2603/2684 < c_41).

  2. Two-class general-d bound (Theorem 5.4(b)):
     B_54(d) / b = (19/32) d^2 + (3/2) d^{3/2}.
     Checks for all integers d >= 1:
       - B_54(d) / b < (41/64) d^2 + (5/3) d^{3/2} (Paper 19 Theorem 3.4) for all d >= 1;
       - B_54(d) / b < d^2 (non-vacuous) iff d >= 14;
       - B_54(d) / b < (3/4) d^2 iff d >= 93;
       - B_54(d) / b is strictly below Paper 19 Theorem 3.5 at M = 2 for all d >= 35
         (checked directly for 1 <= d <= 60, with an exact rational tail bound for d > 60).

  3. Multi-class prime-d bound (Theorem 5.5(b)):
     B_55(M, d) / b = c_M d^2 + (5/4 - 1/(4M)) d.
     Checks across primes d:
       - At M = 2 ((19/32) d^2 + (9/8) d): < d^2 for all primes d >= 3, strictly below
         Paper 19 Theorem 3.5 for all primes d >= 7 (failing only at d in {2, 3, 5}), and
         < (3/4) d^2 for all primes d >= 11.
       - Across 2 <= M <= 40: strictly below Paper 19 Theorem 3.5 for all primes d past
         an exact finite prime crossover (from d >= 7 at M = 2 up to d >= 39,163 at M = 40,
         where the last prime failure is 39,161), proved for ALL primes d via exact integer
         evaluation through the pair-by-pair rational tail threshold D_tail(M) <= 39,322
         (attained at M = 40).

No formal Lean proof depends on this script; it documents the Section 5 prose comparisons.
"""
from __future__ import annotations

from fractions import Fraction
import math
import time


def c_m_fraction(m: int) -> Fraction:
    """Return c_M = 1 - 5/(4M) + 1/M^2 - 1/(4M^3) as an exact Fraction."""
    return Fraction(1, 1) - Fraction(5, 4 * m) + Fraction(1, m * m) - Fraction(1, 4 * m**3)


def thm35_leading_coeff(m: int) -> tuple[Fraction, tuple[int, int]]:
    """Return (gamma*_M, (u, v)) minimizing 1 - max(0, 1 - M/(uv+1))/(u+v) over u, v >= 1.

    Once u + v >= B, 1 - max(0, 1 - M/(uv+1))/(u+v) >= 1 - 1/(u+v) >= 1 - 1/B, so a single
    feasible pair (u0, v0) with value gamma0 < 1 bounds the search box by u + v <= 1/(1 - gamma0).
    """
    t0 = math.isqrt(3 * m) + 1
    best_val = Fraction(1, 1) - Fraction(max(0, t0 * t0 + 1 - m), (t0 * t0 + 1) * (2 * t0))
    best_uv = (t0, t0)
    # Since best_val < 1, any improving pair must have 1/(u + v) > 1 - best_val.
    max_sum = int(Fraction(1, 1) / (Fraction(1, 1) - best_val))
    for u in range(1, max_sum):
        for v in range(u, max_sum - u + 1):
            uv1 = u * v + 1
            if uv1 <= m:
                continue
            val = Fraction(1, 1) - Fraction(uv1 - m, uv1 * (u + v))
            if val < best_val:
                best_val = val
                best_uv = (u, v)
    return best_val, best_uv


def thm35_exact_bound(m: int, d: int, max_sum: int | None = None) -> Fraction:
    """Return min_{u, v >= 1} (d^2 - d(d - U)/(u + v)) as an exact Fraction.

    Here R = min(u*v, d - 1) and U = min(d, M * floor(d / (R + 1))).
    When max_sum is given, restricts to u + v < max_sum (used when pairs with u + v >= max_sum
    have already been proved strictly larger than the target bound via (1 - 1/(u+v)) d^2).
    """
    if d == 1:
        return Fraction(1, 1)

    # Maximize (d - U) / (u + v) using exact integer cross-multiplication best_num / best_den:
    best_num = 0
    best_den = 1

    # Case 1: pairs with u * v >= d - 1 (R = d - 1, U = min(d, M)).
    u_sat = min(d, m)
    if u_sat < d:
        min_sum_sat = d
        for u in range(1, math.isqrt(d - 1) + 2):
            v = (d - 1 + u - 1) // u
            if u + v < min_sum_sat:
                min_sum_sat = u + v
        if max_sum is None or min_sum_sat < max_sum:
            best_num = d - u_sat
            best_den = min_sum_sat

    # Case 2: pairs with u * v <= d - 2 (so d >= 3 and R = u * v).
    if d >= 3:
        max_u = math.isqrt(d - 2)
        if max_sum is not None:
            max_u = min(max_u, max_sum // 2)
        for u in range(1, max_u + 1):
            max_v = (d - 2) // u
            if max_sum is not None:
                max_v = min(max_v, max_sum - 1 - u)
            for v in range(u, max_v + 1):
                u_cap = m * (d // (u * v + 1))
                if u_cap < d:
                    num = d - u_cap
                    den = u + v
                    if num * best_den > best_num * den:
                        best_num = num
                        best_den = den
    return Fraction(d * d, 1) - Fraction(d * best_num, best_den)


def sieve_primes(limit: int) -> list[int]:
    """Return all primes <= limit."""
    if limit < 2:
        return []
    is_prime = bytearray(b"\x01") * (limit + 1)
    is_prime[0] = 0
    is_prime[1] = 0
    for p in range(2, math.isqrt(limit) + 1):
        if is_prime[p]:
            is_prime[p * p : limit + 1 : p] = bytearray(len(range(p * p, limit + 1, p)))
    return [i for i, flag in enumerate(is_prime) if flag]


def verify_leading_coefficients() -> dict[int, Fraction]:
    """Verify all leading-coefficient comparisons against flag and Theorem 3.5."""
    # Flag comparison for Theorem 3.5 (gamma*_M < 1 - 1/(2M) iff M >= 7) and
    # square_cover_bound (1 - 1/(4 ceil(sqrt(2M))) < 1 - 1/(2M) iff M >= 11):
    #   - Checked directly below for 2 <= M <= 40.
    #   - For ALL M >= 41, gamma*_M < c_M < 1 - 1/(2M) since gamma*_M < c_M (proved below for
    #     all M >= 41) and (1 - 1/(2M)) - c_M = (M - 1)(3M - 1)/(4M^3) > 0 for all M >= 2.
    #   - For ALL M >= 12, 2 ceil(sqrt(2M)) < 2(sqrt(2M) + 1) < M since M - 2 > 2 sqrt(2M)
    #     <=> (M - 2)^2 > 8M <=> M^2 - 12M + 4 > 0 (whose larger root is 6 + 4 sqrt(2) < 12).
    for m in range(2, 41):
        gamma_m, uv = thm35_leading_coeff(m)
        flag_m = Fraction(1, 1) - Fraction(1, 2 * m)
        if m <= 6:
            assert gamma_m >= flag_m, f"Expected gamma_{m} >= flag at M={m}"
        else:
            assert gamma_m < flag_m, f"Expected gamma_{m} < flag at M={m}"
        if m == 7:
            assert uv == (4, 5) and gamma_m == Fraction(25, 27) < Fraction(13, 14)
        t_sqrt = math.ceil(math.sqrt(2 * m))
        sq_coeff = Fraction(1, 1) - Fraction(1, 4 * t_sqrt)
        if m <= 10:
            assert sq_coeff >= flag_m, f"Expected sq_coeff >= flag at M={m}"
        else:
            assert sq_coeff < flag_m, f"Expected sq_coeff < flag at M={m}"

    # c_M vs gamma*_M (and c_M < 1 - 1/(2M)) for 2 <= M <= 500:
    gamma_map: dict[int, Fraction] = {}
    for m in range(2, 501):
        cm = c_m_fraction(m)
        flag_m = Fraction(1, 1) - Fraction(1, 2 * m)
        assert flag_m - cm == Fraction((m - 1) * (3 * m - 1), 4 * m**3) > 0
        gm, _ = thm35_leading_coeff(m)
        if m <= 40:
            assert cm < gm, f"Expected c_{m} < gamma*_{m}"
            gamma_map[m] = gm
        else:
            assert gm < cm, f"Expected gamma*_{m} < c_{m} at M={m}"

    # Spot check M = 41, u = v = 11:
    val_41_11 = Fraction(1, 1) - Fraction(122 - 41, 122 * 22)
    assert val_41_11 == Fraction(2603, 2684)
    assert val_41_11 < c_m_fraction(41)

    # Analytic proof that gamma*_M < c_M for ALL M > 500:
    # Choose u = v = t := ceil(sqrt(3M)), so 3M <= t^2 < (sqrt(3M) + 1)^2.
    # For M > 500, sqrt(3M) > 38.7, so t <= sqrt(3M) + 1 < 1.03 * sqrt(3M), and
    # (1 - M/(t^2 + 1)) / (2t) >= (2/3) / (2 * (sqrt(3M) + 1)) = 1 / (3*(sqrt(3M) + 1))
    # > 5 / (4M) >= 1 - c_M because 4M > 15*(sqrt(3M) + 1) holds for all M >= 50.
    assert 16 * 501 * 501 > 225 * 3 * 501 * 2  # Loose check; exact check below:
    # For M >= 501: 4M - 15 > 15*sqrt(3M) <=> (4M - 15)^2 > 675 M <=> 16 M^2 - 795 M + 225 > 0,
    # which holds for all M >= 50 since 16*50^2 - 795*50 + 225 = 475 > 0.
    assert 16 * 50 * 50 - 795 * 50 + 225 > 0
    return gamma_map


def verify_theorem_54_thresholds(gamma2: Fraction) -> None:
    """Verify Theorem 5.4(b) thresholds for (19/32) d^2 + (3/2) d^{3/2}."""
    # Exact square-free / rational equivalences:
    #   (19/32) d^2 + (3/2) d^{3/2} < d^2        <=> (3/2) < (13/32) sqrt(d) <=> 2304 < 169 d <=> d >= 14
    #   (19/32) d^2 + (3/2) d^{3/2} < (3/4) d^2  <=> (3/2) < (5/32) sqrt(d)  <=> 2304 < 25 d  <=> d >= 93
    assert 2304 // 169 == 13 and 169 * 13 < 2304 < 169 * 14
    assert 2304 // 25 == 92 and 25 * 92 < 2304 < 25 * 93

    # Against Theorem 3.4: (19/32) < (41/64) and (3/2) < (5/3), so strict for ALL d >= 1.
    assert Fraction(19, 32) < Fraction(41, 64) and Fraction(3, 2) < Fraction(5, 3)

    # Against Theorem 3.5 at M = 2:
    # For every u, v >= 1 and d >= 1, U >= min(d, 2*(d - uv)/(uv + 1)), so
    # thm35_exact_bound(2, d) >= gamma2 * d^2 - (2 / 2) * d = (17/20) d^2 - d.
    assert gamma2 == Fraction(17, 20)
    # Check analytic tail for d >= 61:
    # Need ((17/20 - 19/32) d^2 - d) > (3/2) d^{3/2}, i.e., ((41/160) d - 1)^2 > (9/4) d
    # with (41/160) d > 1 (holds for d >= 4).
    # ((41/160) d - 1)^2 - (9/4) d = (1681 d^2 - 70720 d + 25600) / 25600 > 0 for all d >= 42!
    for d in (42, 61):
        diff = (Fraction(41 * d, 160) - 1) ** 2 - Fraction(9 * d, 4)
        assert diff == Fraction(1681 * d * d - 70720 * d + 25600, 25600)
        assert diff > 0

    # Exact integer/rational check on 1 <= d <= 60:
    # B_54(d)/b < thm35(2, d)  <=>  (3/2) d^{3/2} < thm35(2, d) - (19/32) d^2.
    win_flags: list[int] = []
    loss_flags: list[int] = []
    for d in range(1, 61):
        rhs = thm35_exact_bound(2, d) - Fraction(19, 32) * (d * d)
        # Compare (3/2) * d * sqrt(d) < rhs (strict inequality):
        # If rhs <= 0, definitely false; otherwise square both sides: (9/4) * d^3 < rhs^2.
        strictly_beats = rhs > 0 and Fraction(9 * d**3, 4) < rhs * rhs
        if strictly_beats:
            win_flags.append(d)
        else:
            loss_flags.append(d)

    assert max(loss_flags) == 34, f"Expected last failure d=34, got {max(loss_flags)}"
    assert min(d for d in win_flags if d > max(loss_flags)) == 35


def compute_pair_tail_cap(m: int, cm: Fraction, lin_coeff: Fraction) -> int:
    """Return an integer D_tail(M) above which B_55(M, d) < thm35_exact_bound(M, d) for ALL d.

    Proof for d > D_tail(M) and every pair of integers u, v >= 1:
      Let s = u + v. Since U >= 0, d^2 - d(d - U)/s >= (1 - 1/s) d^2.
      1. Whenever s > 1 / (1 - c_M), gap_inf := (1 - 1/s) - c_M > 0, and for all s >= s_min
         (where s_min = floor(1 / (1 - c_M)) + 1), (1 - 1/s - c_M) d > lin_coeff holds for all
         d > lin_coeff / (1 - 1/s_min - c_M).
      2. For each of the finitely many pairs (u, v) with u, v >= 1 and u + v < s_min:
         since R + 1 = min(uv + 1, d) <= uv + 1 and floor(d / K) >= (d - (K - 1)) / K,
         U = min(d, M * floor(d / (R + 1))) >= min(d, M * (d - uv) / (uv + 1)), so
             d - U <= max(0, 1 - M / (uv + 1)) * d + M * uv / (uv + 1),
         hence
             d^2 - d(d - U)/(u + v) >= gamma_M(u, v) d^2 - (M * uv / ((uv + 1)(u + v))) d.
         Since gamma_M(u, v) >= gamma*_M > c_M (for 2 <= M <= 40), this strictly exceeds
         c_M d^2 + lin_coeff * d for all
             d > (lin_coeff + M * uv / ((uv + 1)(u + v))) / (gamma_M(u, v) - c_M).
    """
    s_min = int(Fraction(1, 1) / (Fraction(1, 1) - cm)) + 1
    outer_gap = Fraction(1, 1) - Fraction(1, s_min) - cm
    assert outer_gap > 0
    cap = int(lin_coeff / outer_gap) + 1

    for u in range(1, s_min):
        for v in range(u, s_min - u):
            uv = u * v
            uv1 = uv + 1
            gamma_uv = Fraction(1, 1) - Fraction(max(0, uv1 - m), uv1 * (u + v))
            gap_uv = gamma_uv - cm
            assert gap_uv > 0
            sub_uv = lin_coeff + Fraction(m * uv, uv1 * (u + v))
            cap = max(cap, int(sub_uv / gap_uv) + 1)
    return cap


def verify_theorem_55_prime_crossovers(gamma_map: dict[int, Fraction]) -> tuple[int, int]:
    """Verify Theorem 5.5(b) prime crossovers across 2 <= M <= 40."""
    tail_caps: dict[int, int] = {}
    for m in range(2, 41):
        cm = c_m_fraction(m)
        lin_coeff = Fraction(5, 4) - Fraction(1, 4 * m)
        assert gamma_map[m] > cm
        tail_caps[m] = compute_pair_tail_cap(m, cm, lin_coeff)

    max_tail = max(tail_caps.values())
    assert max_tail == 39322 and tail_caps[40] == 39322, f"Unexpected max tail cap: {max_tail}"
    primes = sieve_primes(max_tail)

    # At M = 2: (19/32) d^2 + (9/8) d
    # < d^2     <=> (9/8) d < (13/32) d^2 <=> 36 < 13 d <=> d >= 3 (all primes >= 3)
    # < (3/4)d^2 <=> (9/8) d < (5/32) d^2  <=> 36 < 5 d  <=> d >= 8 (all primes >= 11)
    for p in primes[:20]:
        b55_2 = Fraction(19, 32) * p * p + Fraction(9, 8) * p
        assert (b55_2 < p * p) == (p >= 3)
        assert (b55_2 < Fraction(3, 4) * p * p) == (p >= 11)

    first_always_winning_prime: dict[int, int] = {}
    last_failing_prime: dict[int, int] = {}
    for m in range(2, 41):
        cm = c_m_fraction(m)
        lin_coeff = Fraction(5, 4) - Fraction(1, 4 * m)
        s_min = int(Fraction(1, 1) / (Fraction(1, 1) - cm)) + 1
        outer_cap = int(lin_coeff / (Fraction(1, 1) - Fraction(1, s_min) - cm)) + 1
        cap = tail_caps[m]
        last_fail = 0
        for p in primes:
            if p > cap:
                break
            b55 = cm * (p * p) + lin_coeff * p
            # For p > outer_cap, every pair with u + v >= s_min already satisfies
            # d^2 - d(d - U)/(u + v) >= (1 - 1/s_min) p^2 > b55.
            b35 = thm35_exact_bound(m, p, max_sum=s_min if p > outer_cap else None)
            if not (b55 < b35):
                last_fail = p
        last_failing_prime[m] = last_fail
        # First prime strictly above last_fail:
        next_primes = [p for p in primes if p > last_fail]
        first_always_winning_prime[m] = next_primes[0]

    assert last_failing_prime[2] == 5 and first_always_winning_prime[2] == 7
    assert last_failing_prime[40] == 39161 and first_always_winning_prime[40] == 39163
    return first_always_winning_prime[2], first_always_winning_prime[40]


def main() -> None:
    t0 = time.perf_counter()
    print("1. Verifying leading-coefficient comparisons (flag bound and Theorem 3.5)...")
    gamma_map = verify_leading_coefficients()
    print(
        f"   c_M < gamma*_M iff 2 <= M <= 40 verified "
        f"(M=40: c_40={float(c_m_fraction(40)):.6f} < gamma*_40={float(gamma_map[40]):.6f}; "
        f"M=41: 2603/2684={2603/2684:.6f} < c_41={float(c_m_fraction(41)):.6f})."
    )

    print("2. Verifying Theorem 5.4(b) general-d thresholds at M = 2...")
    verify_theorem_54_thresholds(gamma_map[2])
    print(
        "   Verified: < Thm 3.4 for d >= 1; < bd^2 for d >= 14; "
        "< Thm 3.5 for d >= 35 (last failure d = 34); < (3/4)bd^2 for d >= 93."
    )

    print("3. Verifying Theorem 5.5(b) prime-d crossovers across 2 <= M <= 40...")
    p2, p40 = verify_theorem_55_prime_crossovers(gamma_map)
    elapsed = time.perf_counter() - t0
    print(
        f"   Verified across all primes d (via exact rational check + analytic tail bound): "
        f"M = 2 wins for primes d >= {p2}; M = 40 wins for primes d >= {p40} (last failure 39,161)."
    )
    print(f"All Section 5 crossover assertions passed in {elapsed:.2f}s.")


if __name__ == "__main__":
    main()
