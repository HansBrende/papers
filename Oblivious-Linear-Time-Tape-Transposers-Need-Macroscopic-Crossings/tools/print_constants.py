#!/usr/bin/env python3
"""Print the explicit constants of Sections 4, 5.1 and 6.3 in exact rational and scientific form.

Usage:

    python3 tools/print_constants.py

Uses only the Python standard library (`fractions`, `math`). Reproduces:
  * the phase-exit chain counts m_0(k) and cell-guard counts g(k) for k = 1, 2, 3, together with
    the exponential upper bound 3^{2k+1} (Section 5.1, `sharpCounts_small_values`,
    `sharpChainCount_le_pow_three`);
  * the bridge density rho_0(k, 1, 1) and threshold d_br(k, 1, 1) for k = 1, 2, 3 (Section 5.1);
  * the Theorem X constants c_E, theta_mac, d_0 and the Theorem S skeleton length cap M_max at
    k = 2, C = alpha = 1, w_val = 8 (Sections 5.1 and 6.3);
  * the first-form uniform-block-cut bridge density rho_{0,first}(2, 1, 1) and genie-depth tower
    scale (Section 5.1 and paragraph after Theorem 5.3);
  * the Theorem H slab-autonomy constants N, eps_*, eps_sm and d_H at c = 1, beta = 8, k = 2
    (Section 4).
"""
from fractions import Fraction
import math


def ceil_frac(x: Fraction) -> int:
    return -(-x.numerator // x.denominator)


def floor_frac(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_sqrt_frac(x: Fraction) -> int:
    """Smallest integer n >= 0 with n^2 >= x, for a rational x >= 0 (exact)."""
    p, q = x.numerator, x.denominator
    n = math.isqrt(p // q)
    while n * n * q < p:
        n += 1
    while n > 0 and (n - 1) * (n - 1) * q >= p:
        n -= 1
    return n


def chi_nu_tables(k: int, n_max: int) -> tuple[list[int], list[int]]:
    chi = [1]
    nu = [1]
    for n in range(n_max):
        c_next = 1 + sum(min(k, n + 1 - j) * chi[j] for j in range(n + 1))
        n_next = 1 + sum(min(k, n + 1 - j) * (nu[j] + chi[j]) for j in range(n + 1))
        chi.append(c_next)
        nu.append(n_next)
    return chi, nu


def m0_and_g(k: int) -> tuple[int, int]:
    chi, nu = chi_nu_tables(k, 2 * k)
    m0 = 1 + sum(chi[n] - 1 for n in range(2 * k + 1))
    g = 2 * k + 2 * sum(nu[n] for n in range(2 * k + 1))
    return m0, g


def b_time(m: int, C: Fraction, alpha: Fraction) -> int:
    return ceil_frac(Fraction(2 * m) * C / alpha)


def rho_pb(m: int, C: Fraction, alpha: Fraction) -> Fraction:
    bt = b_time(m, C, alpha)
    return Fraction(1, 3 * (m * (bt + 1) + 1))


def d_pb(m: int, C: Fraction, alpha: Fraction) -> int:
    bt = b_time(m, C, alpha)
    return ceil_frac(Fraction(12 * m * (2 * bt + 2)) / alpha + 6)


def rho0(k: int, C: Fraction, alpha: Fraction) -> Fraction:
    m0, _ = m0_and_g(k)
    bt = b_time(m0, C, alpha)
    return Fraction(2, 5 * (m0 * (bt + 1) + 2 * k))


def d_br(k: int, C: Fraction, alpha: Fraction) -> int:
    m0, _ = m0_and_g(k)
    bt = b_time(m0, C, alpha)
    return ceil_frac(Fraction(10 * m0 * (2 * bt + 2)) / alpha + 5)


def theorem_x_constants(
    k: int, w_val: int, C: Fraction, alpha: Fraction
) -> tuple[Fraction, Fraction, int, int]:
    _, g = m0_and_g(k)
    alpha_eff = Fraction(19, 20) * alpha
    r0 = rho0(k, C, alpha_eff)
    c_e = r0 / (2 * w_val)
    theta_mac = (Fraction(9, 20) * alpha * r0) / (w_val * (5 * k + 1) * g)
    # d0Macro_tight: max(1, d_br(k, C, 19/20 alpha), ceil(theta^(-1/2))); the clause W <= H* needs ceil(1/theta) in addition.
    d0 = max(1, d_br(k, C, alpha_eff), ceil_sqrt_frac(1 / theta_mac))
    m_max = floor_frac(Fraction(16) * C / theta_mac)
    return c_e, theta_mac, d0, m_max


def theorem_h_constants(
    k: int, beta: Fraction, c: Fraction
) -> tuple[int, Fraction, Fraction, int]:
    n_cap = floor_frac(Fraction(160) * beta * c * c)
    eps_star = Fraction(1, 8 * (n_cap + 1))
    eps_sm = eps_star / (4 * beta * (n_cap + 2) * max(1, 2 * k))
    # slabDimThreshold c beta = 20 (N + 2) / eps_* = 160 (N + 1) (N + 2); it does not depend on k.
    d_h = 160 * (n_cap + 1) * (n_cap + 2)
    return n_cap, eps_star, eps_sm, d_h


def main() -> None:
    print("=== Section 5.1: Phase-exit chain counts m_0(k) and guard counts g(k) ===")
    for k in (1, 2, 3):
        m0, g = m0_and_g(k)
        cap = 3 ** (2 * k + 1)
        r0 = rho0(k, Fraction(1), Fraction(1))
        dbr = d_br(k, Fraction(1), Fraction(1))
        print(
            f"  k = {k}: m_0 = {m0} (<= 3^{2*k+1} = {cap}), g = {g}, "
            f"rho_0({k},1,1) = {r0} (~ {float(r0):.3e}), d_br({k},1,1) = {dbr}"
        )

    print("\n=== Sections 5.1 & 6.3: Theorem X and Theorem S at k = 2, C = alpha = 1, w_val = 8 ===")
    c_e, theta_mac, d0, m_max = theorem_x_constants(2, 8, Fraction(1), Fraction(1))
    dbr_19_20 = d_br(2, Fraction(1), Fraction(19, 20))
    print(f"  d_br(2, 1, 19/20) = {dbr_19_20}")
    print(f"  c_E       = {c_e} (~ {float(c_e):.3e})")
    print(f"  theta_mac = {theta_mac} (~ {float(theta_mac):.3e})")
    print(f"  d_0       = {d0} (~ {d0:.3e}); ceil(theta^(-1/2)) = {ceil_sqrt_frac(1 / theta_mac)}")
    print(f"  ceil(1/theta) = {ceil_frac(1 / theta_mac)} (~ {float(ceil_frac(1 / theta_mac)):.3e}), needed only for W <= H*")
    print(f"  Theorem S threshold max(d_0, ceil((8/theta)^(1/2))) = {max(d0, ceil_sqrt_frac(8 / theta_mac))}")
    print(f"  M_max     = {m_max} (~ {m_max:.3e})")

    print("\n=== Section 5.1: First-form constants at k = 2, C = alpha = 1 ===")
    m_first = (2 * 2 + 1) * (2 + 1) ** (2 * 2)
    b_first = 2 * math.ceil(24 * 1 / 1)
    denom_first = 3 * math.comb(m_first + b_first, m_first)
    log10_rho_first = -math.log10(denom_first)
    print(f"  m_first(2) = {m_first}, 2*ceil(24C/alpha) = {b_first}")
    print(f"  rho_{{0,first}}(2,1,1) = 1 / {denom_first} (~ 10^{{{log10_rho_first:.2f}}} = {10**log10_rho_first:.3e})")
    # Exact genie-depth parameters from BoundedStackDepth.Main / Machines at k = 2, beta >= 2,
    # C = 1, eps_E = (19/20) * alpha * rho_{0,first}(2, 1, 19/20) / 2, eps_tcp = eps_E / (4*beta*C):
    b_first_eff = 2 * ceil_frac(Fraction(24) / Fraction(19, 20))
    denom_eff = 3 * math.comb(m_first + b_first_eff, m_first)
    eps_e = Fraction(19, 20) / (2 * denom_eff)
    eps_tcp = eps_e / (4 * 2 * 1)  # beta = w_val >= 2, C = 1
    n_heads = 2 * 2
    par_h = ceil_frac(Fraction(14 * n_heads + 80 * n_heads * n_heads) / (eps_tcp / 4)) + 1
    par_q = ceil_frac(Fraction(2 * n_heads * n_heads) / (eps_tcp / 4)) + 1
    # parJ >= Q^{n^2} since ln(max(1, 8*n^2/eps_tcp)) > 1:
    par_j_lb = int(math.log(float(Fraction(8 * n_heads * n_heads) / eps_tcp))) * (par_q ** (n_heads * n_heads))
    par_p_lb = 1 + 2 * n_heads * (par_j_lb * n_heads + 1)
    # log_4(theta_first^{-1}) > D_E >= K^P - 1 > 2^{h_0 * P}, so log10(log_4(theta_first^{-1})) > log10(h_0 * P / 2):
    log10_d_e_lb = math.log10(par_h) + math.log10(par_p_lb) + math.log10(math.log(2) / math.log(4))
    print(
        f"  genie depth (BoundedStackDepth.genieDepth, beta >= 2): "
        f"log10(h_0) = {math.log10(par_h):.2f}, log10(P) >= {math.log10(par_p_lb):.2f}, "
        f"so D_E > 4^{{10^{{{log10_d_e_lb:.1f}}}}} >> 10^{{107}} and theta_first < 4^{{-10^{{107}}}}"
    )

    print("\n=== Section 4: Theorem H constants at c = 1, beta = 8, k = 2 ===")
    n_cap, eps_star, eps_sm, d_h = theorem_h_constants(2, Fraction(8), Fraction(1))
    print(f"  N      = {n_cap}")
    print(f"  eps_*  = {eps_star} (~ {float(eps_star):.3e})")
    print(f"  eps_sm = {eps_sm} (~ {float(eps_sm):.3e})")
    print(f"  d_H    = {d_h} (~ {d_h:.3e})")


if __name__ == "__main__":
    main()
