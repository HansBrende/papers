#!/usr/bin/env python3
"""Reproducible rank-minimization check for Remark 7.6 (two-sided interval partitions).

Usage:
    python3 tools/verify_two_sided_svd.py

Note on methodology: a generic random operator K in U(I) (x) U(J) satisfies
ker(sw - K) = {0}. To search for maximum swap-code dimensions dim ker(sw - K) over
K in U(I) (x) U(J) at d in {5, 6, 7, 8}, this script runs Nesterov-accelerated
alternating projections (with O'Donoghue-Candes adaptive momentum restart) between the
linear operator subspace U(I) (x) U(J) (spanned by interval-mask rotations
P_I sigma^e (x) P_J sigma^f) and the bounded-rank manifold {K : rank(sw - K) <= d^2 - D}
via truncated SVD across deterministic random restarts.

Across the 9 benchmark interval partitions at d in {5, 6, 7, 8}, this script verifies:
  1. Generic random elements K_rand in U(I) (x) U(J) have nullity dim ker(sw - K_rand) = 0.
  2. Never-exceeded upper bound: at D = D_diamond(I, J) + 1, where
         D_diamond(I, J) := floor((d^2 + sum_{I, J} min(|I|, |J|)) / 2),
     the tail singular-value norm ||sigma_{> d^2 - D}(sw - K)||_2 stays bounded well
     away from zero (> 0.1) across every tested partition.
  3. Attainment at s >= floor(d / 2): on the contiguous fine-singleton + coarse-complement
     partitions with s >= floor(d / 2) (including the half-density benchmark s = d / 2,
     where D_diamond = (5/8) d^2 + O(d)) and the d = 6 two-run partition, bounded-norm
     operators K converge to ||sigma_{> d^2 - D_diamond}(sw - K)||_2 < 1e-11 with a clear
     nonzero singular-value gap sigma_{d^2 - D_diamond}(sw - K) > 0.5.
  4. Strict inequality on some partitions with s < d - s or unequal coarse blocks:
     on d = 7, s = 3 (D_diamond = 34), d = 7 asymmetric (1+1+5 vs 2+2+3, D_diamond = 31),
     and d = 8, s = 3 (D_diamond = 42), the tail singular-value norm at D = D_diamond stays
     bounded well away from zero (> 0.15, even without a Frobenius norm cap), while bounded-norm
     operators attain D = 32 (< 34), D = 27 (< 31), and D = 40 (< 42) to < 1e-11.

No formal proof in the manuscript depends on this numerical script.
"""
from __future__ import annotations

import time
import numpy as np


def interval_rot_basis(d: int, intervals: list[list[int]]) -> np.ndarray:
    """Return an orthonormal row basis of span{P_I sigma^e : I in intervals, e in Z_d}."""
    mats = []
    for interval in intervals:
        for shift in range(d):
            mat = np.zeros((d, d), dtype=np.float64)
            for r in interval:
                mat[r, (r + shift) % d] = 1.0
            mats.append(mat.reshape(-1))
    stacked = np.asarray(mats, dtype=np.float64)
    _, sing, vt = np.linalg.svd(stacked, full_matrices=False)
    rank = int(np.sum(sing > 1e-10))
    return vt[:rank]


def swap_operator_matrix(d: int) -> np.ndarray:
    """Return the d^2 x d^2 matrix of X |-> X^T in row-major vec coordinates."""
    sw = np.zeros((d, d, d, d), dtype=np.float64)
    for r in range(d):
        for c in range(d):
            sw[r, c, c, r] = 1.0
    return sw.reshape(d * d, d * d)


def search_min_tail_singular_norm(
    d: int,
    proj_a: np.ndarray,
    proj_b: np.ndarray,
    sw_mat: np.ndarray,
    target_nullity: int,
    restarts: int,
    steps: int,
    rng: np.random.Generator,
    norm_cap: float | None = None,
    stop_tol: float = 1e-12,
) -> tuple[float, float, float]:
    """Return (best_tail, gap_singular_value, op_frobenius_norm) at target_nullity."""
    target_rank = d * d - target_nullity

    def project_subspace(op_mat: np.ndarray) -> np.ndarray:
        tensor = op_mat.reshape(d, d, d, d).transpose(0, 2, 1, 3).reshape(d * d, d * d)
        proj = proj_a @ tensor @ proj_b
        out = proj.reshape(d, d, d, d).transpose(0, 2, 1, 3).reshape(d * d, d * d)
        if norm_cap is not None:
            frob = float(np.linalg.norm(out))
            if frob > norm_cap:
                out = out * (norm_cap / frob)
        return out

    if target_rank <= 0:
        k_proj = project_subspace(sw_mat)
        return float(np.linalg.norm(sw_mat - k_proj)), 0.0, float(np.linalg.norm(k_proj))

    best_tail = float("inf")
    best_gap = 0.0
    best_norm = 0.0

    for _ in range(restarts):
        k_cur = project_subspace(rng.normal(0.0, 0.5, size=(d * d, d * d)))
        k_prev = k_cur.copy()
        t_nesterov = 1.0
        prev_obj = float("inf")

        for step in range(steps):
            t_next = 0.5 * (1.0 + np.sqrt(1.0 + 4.0 * t_nesterov * t_nesterov))
            momentum = (t_nesterov - 1.0) / t_next if step > 0 else 0.0
            k_extrap = k_cur + momentum * (k_cur - k_prev)

            diff = sw_mat - k_extrap
            u, sing, vt = np.linalg.svd(diff, full_matrices=False)
            cur_obj = float(np.linalg.norm(sing[target_rank:]))
            if cur_obj > prev_obj:
                # O'Donoghue-Candes adaptive momentum restart
                k_extrap = k_cur
                diff = sw_mat - k_extrap
                u, sing, vt = np.linalg.svd(diff, full_matrices=False)
                cur_obj = float(np.linalg.norm(sing[target_rank:]))
                t_next = 1.0

            low_rank = (u[:, :target_rank] * sing[:target_rank]) @ vt[:target_rank, :]
            k_next = project_subspace(sw_mat - low_rank)
            k_prev = k_cur
            k_cur = k_next
            t_nesterov = t_next
            prev_obj = cur_obj

            if (step + 1) % 40 == 0 or step == steps - 1:
                sing_chk = np.linalg.svd(sw_mat - k_cur, compute_uv=False)
                tail_chk = float(np.linalg.norm(sing_chk[target_rank:]))
                if tail_chk < best_tail:
                    best_tail = tail_chk
                    best_gap = float(sing_chk[target_rank - 1])
                    best_norm = float(np.linalg.norm(k_cur))
                if best_tail < stop_tol:
                    return best_tail, best_gap, best_norm

    return best_tail, best_gap, best_norm


ATTAINING_CASES: list[tuple[str, int, list[list[int]], list[list[int]]]] = [
    (
        "d=5, s=2 contiguous singletons + 3-block",
        5,
        [[0], [1], [2, 3, 4]],
        [[0], [1], [2, 3, 4]],
    ),
    (
        "d=6, s=3 half-density singletons + 3-block",
        6,
        [[0], [1], [2], [3, 4, 5]],
        [[0], [1], [2], [3, 4, 5]],
    ),
    (
        "d=6, two-run singletons {0},{3} + two 2-blocks",
        6,
        [[0], [1, 2], [3], [4, 5]],
        [[0], [1, 2], [3], [4, 5]],
    ),
    (
        "d=6, asymmetric s_A=3 vs s_B=4 contiguous singletons",
        6,
        [[0], [1], [2], [3, 4, 5]],
        [[0], [1], [2], [3], [4, 5]],
    ),
    (
        "d=7, s=4 contiguous singletons + 3-block",
        7,
        [[0], [1], [2], [3], [4, 5, 6]],
        [[0], [1], [2], [3], [4, 5, 6]],
    ),
    (
        "d=8, s=4 half-density singletons + 4-block",
        8,
        [[0], [1], [2], [3], [4, 5, 6, 7]],
        [[0], [1], [2], [3], [4, 5, 6, 7]],
    ),
]

# Tuple: (label, d, part_a, part_b, realized_d, witness_seed, witness_restarts, witness_steps)
UPPER_BOUND_ONLY_CASES: list[
    tuple[str, int, list[list[int]], list[list[int]], int, int, int, int]
] = [
    (
        "d=7, s=3 contiguous singletons + 4-block (s < d - s)",
        7,
        [[0], [1], [2], [3, 4, 5, 6]],
        [[0], [1], [2], [3, 4, 5, 6]],
        32,
        1018,
        1,
        2800,
    ),
    (
        "d=7, asymmetric (1+1+5) vs (2+2+3)",
        7,
        [[0], [1], [2, 3, 4, 5, 6]],
        [[0, 1], [2, 3], [4, 5, 6]],
        27,
        1000,
        4,
        2400,
    ),
    (
        "d=8, s=3 contiguous singletons + 5-block (s < d - s)",
        8,
        [[0], [1], [2], [3, 4, 5, 6, 7]],
        [[0], [1], [2], [3, 4, 5, 6, 7]],
        40,
        1002,
        1,
        3600,
    ),
]


def check_generic_nullity_zero(
    d: int, proj_a: np.ndarray, proj_b: np.ndarray, sw_mat: np.ndarray, rng: np.random.Generator
) -> None:
    t_rand = rng.normal(0.0, 0.5, size=(d * d, d * d))
    k_rand = (
        (proj_a @ t_rand @ proj_b)
        .reshape(d, d, d, d)
        .transpose(0, 2, 1, 3)
        .reshape(d * d, d * d)
    )
    generic_nullity = int(np.sum(np.linalg.svd(sw_mat - k_rand, compute_uv=False) < 1e-8))
    assert generic_nullity == 0, f"Expected generic nullity 0, got {generic_nullity}"


def main() -> None:
    t0 = time.perf_counter()
    rng = np.random.default_rng(20261113)
    print("1. Verifying D_diamond attainment on s >= floor(d/2) and two-run partitions...")
    for label, d, part_a, part_b in ATTAINING_CASES:
        assert sorted(x for iv in part_a for x in iv) == list(range(d)), label
        assert sorted(x for iv in part_b for x in iv) == list(range(d)), label
        basis_a = interval_rot_basis(d, part_a)
        basis_b = interval_rot_basis(d, part_b)
        proj_a = basis_a.T @ basis_a
        proj_b = basis_b.T @ basis_b
        sw_mat = swap_operator_matrix(d)
        check_generic_nullity_zero(d, proj_a, proj_b, sw_mat, rng)

        d_diamond = (d * d + sum(min(len(ia), len(jb)) for ia in part_a for jb in part_b)) // 2
        tp_one_side = (d * d + min(len(part_a), len(part_b)) * d) // 2

        tail_hit, gap_hit, norm_hit = search_min_tail_singular_norm(
            d, proj_a, proj_b, sw_mat, d_diamond, restarts=8, steps=1800, rng=rng, norm_cap=None
        )
        tail_above, _, _ = search_min_tail_singular_norm(
            d, proj_a, proj_b, sw_mat, d_diamond + 1, restarts=5, steps=300, rng=rng, norm_cap=None
        )
        print(
            f"  [{label}] TP={tp_one_side:2d}, D_diamond={d_diamond:2d}: "
            f"tail(D_diamond)={tail_hit:.2e} (gap={gap_hit:.2f}, ||K||_F={norm_hit:.1f}), "
            f"tail(D_diamond+1)={tail_above:.2e}"
        )
        assert tail_hit < 1e-11 and gap_hit > 0.5 and norm_hit < 60.0, (
            f"Failed clean attainment of D_diamond={d_diamond} for {label}: "
            f"tail={tail_hit:.3e}, gap={gap_hit:.3e}"
        )
        assert tail_above > 0.1, (
            f"Unexpected witness at D_diamond+1={d_diamond + 1} for {label}: tail={tail_above:.3e}"
        )

    print("2. Verifying strict gap (< D_diamond) on s < d - s / general interval partitions...")
    for (
        label,
        d,
        part_a,
        part_b,
        realized_d,
        w_seed,
        w_restarts,
        w_steps,
    ) in UPPER_BOUND_ONLY_CASES:
        assert sorted(x for iv in part_a for x in iv) == list(range(d)), label
        assert sorted(x for iv in part_b for x in iv) == list(range(d)), label
        basis_a = interval_rot_basis(d, part_a)
        basis_b = interval_rot_basis(d, part_b)
        proj_a = basis_a.T @ basis_a
        proj_b = basis_b.T @ basis_b
        sw_mat = swap_operator_matrix(d)
        check_generic_nullity_zero(d, proj_a, proj_b, sw_mat, rng)

        d_diamond = (d * d + sum(min(len(ia), len(jb)) for ia in part_a for jb in part_b)) // 2
        tail_real, gap_real, norm_real = search_min_tail_singular_norm(
            d,
            proj_a,
            proj_b,
            sw_mat,
            realized_d,
            restarts=w_restarts,
            steps=w_steps,
            rng=np.random.default_rng(w_seed),
            norm_cap=None,
        )
        tail_dd, _, _ = search_min_tail_singular_norm(
            d, proj_a, proj_b, sw_mat, d_diamond, restarts=6, steps=500, rng=rng, norm_cap=None
        )
        tail_above, _, _ = search_min_tail_singular_norm(
            d, proj_a, proj_b, sw_mat, d_diamond + 1, restarts=5, steps=300, rng=rng, norm_cap=None
        )
        print(
            f"  [{label}] D_diamond={d_diamond:2d}, realized={realized_d:2d}: "
            f"tail({realized_d})={tail_real:.2e} (gap={gap_real:.2f}, ||K||_F={norm_real:.1f}), "
            f"tail(D_diamond)={tail_dd:.2e}, tail(D_diamond+1)={tail_above:.2e}"
        )
        assert tail_real < 1e-11 and gap_real > 0.5 and norm_real < 60.0, (
            f"Failed to realize D={realized_d} on {label}: tail={tail_real:.3e}"
        )
        assert tail_dd > 0.15, (
            f"Expected strict gap below D_diamond={d_diamond} on {label}: {tail_dd:.3e}"
        )
        assert tail_above > 0.1, (
            f"Unexpected witness above D_diamond={d_diamond} on {label}: {tail_above:.3e}"
        )

    elapsed = time.perf_counter() - t0
    total = len(ATTAINING_CASES) + len(UPPER_BOUND_ONLY_CASES)
    print(f"ALL CHECKS PASSED ({total} cases across d in {{5,6,7,8}} in {elapsed:.2f}s).")


if __name__ == "__main__":
    main()
