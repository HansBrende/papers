#!/usr/bin/env python3
"""Exact pairing-comparison certificates for Paper 17's three-term seed.

Standard library only. Reuses Paper 17's matrix construction and rank routine.
Run: python3 lean-backlog/tools/pairing_comparison.py --repo . --output receipt.json
Replay: python3 lean-backlog/tools/pairing_comparison.py --repo . --verify receipt.json
Search stops at the proven lower bound or after a fixed proposal budget.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import random


def inverse(a, p):
    d = len(a)
    rows = [[x % p for x in row] + [int(i == j) for j in range(d)]
            for i, row in enumerate(a)]
    for j in range(d):
        pivot = next((i for i in range(j, d) if rows[i][j]), None)
        if pivot is None:
            return None
        rows[j], rows[pivot] = rows[pivot], rows[j]
        scale = pow(rows[j][j], -1, p)
        rows[j] = [x * scale % p for x in rows[j]]
        for i in range(d):
            if i != j:
                c = rows[i][j]
                rows[i] = [(x - c * y) % p for x, y in zip(rows[i], rows[j])]
    return [row[d:] for row in rows]


def jordan_twist(s, n):
    d = s * n
    return [[int(i == j or (j == i + 1 and i // n == j // n))
             for j in range(d)] for i in range(d)]


def three_term(n, p, ops):
    d = 3 * n
    k = [[0] * (d * d) for _ in range(d * d)]
    for a, b in ((0, 1), (0, 2), (1, 2)):
        u = [[0] * d for _ in range(d)]
        for i in range(n):
            u[a * n + i][b * n + i] = 1
            u[b * n + i][a * n + i] = -1 % p
        v = [[-x % p for x in row] for row in u]
        k = ops.add(k, ops.kron(u, v, p), p)
    return k


def comparison_nullity(k, g, p, ops):
    g_inv = inverse(g, p)
    if g_inv is None:
        return None
    return len(k) - ops.rank_mod(ops.add(k, ops.kron(g, g_inv, p), p), p)


def run_case(n, p, trials, ops):
    d = 3 * n
    k = three_term(n, p, ops)
    dimension = d * d - ops.rank_mod(ops.add(ops.swap(d), k, p, -1), p)
    assert dimension == 4 * n * (n + 1)
    lower = max(0, dimension - d * (d - 1 if p == 2 else d + 1) // 2)
    best_g = jordan_twist(3, n)
    jordan_kernel = comparison_nullity(k, best_g, p, ops)
    assert jordan_kernel == (8*n - 3*(n % 2) if p == 2 else 3*n)
    best = jordan_kernel
    rng = random.Random(20261112 + 10000 * p + n)
    invertible_trials = 0
    raw_draws = 0
    for _ in range(trials):
        if best == lower:
            break
        raw_draws += 1
        g = [[rng.randrange(p) for _ in range(d)] for _ in range(d)]
        value = comparison_nullity(k, g, p, ops)
        if value is None:
            continue
        invertible_trials += 1
        assert value >= lower, (p, n, dimension, lower, value)
        if value < best:
            best, best_g = value, g
    result = dict(p=p, n=n, d=d, code_dimension=dimension,
                  lower_bound=lower, jordan_twist_kernel=jordan_kernel,
                  best_kernel=best, optimum_certified=(best == lower),
                  raw_draws=raw_draws, invertible_trials=invertible_trials, G=best_g)
    print(f'GF({p}), d={d}: code={dimension}, lower={lower}, '
          f'Jordan={jordan_kernel}, best={best}, certified={best == lower}', flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--verify', type=Path)
    parser.add_argument('--trials', type=int, default=64)
    args = parser.parse_args()
    if args.trials < 0 or bool(args.output) == bool(args.verify):
        parser.error('choose exactly one of --output and --verify; trials must be nonnegative')
    source = args.repo / 'Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/tools/three_term_example.py'
    spec = importlib.util.spec_from_file_location('published_three_term', source)
    ops = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ops)
    if args.verify:
        receipt = json.loads(args.verify.read_text())
        for case in receipt['cases']:
            p, n, d = case['p'], case['n'], case['d']
            assert p in (2, 3, 101)
            assert d == 3 * n
            k = three_term(n, p, ops)
            dimension = d*d - ops.rank_mod(ops.add(ops.swap(d), k, p, -1), p)
            lower = max(0, dimension - d * (d - 1 if p == 2 else d + 1) // 2)
            value = comparison_nullity(k, case['G'], p, ops)
            assert dimension == case['code_dimension'] == 4*n*(n+1)
            assert lower == case['lower_bound'] <= value == case['best_kernel']
            assert case['optimum_certified'] == (value == lower)
            jordan = comparison_nullity(k, jordan_twist(3, n), p, ops)
            assert jordan == case['jordan_twist_kernel'] == (8*n - 3*(n % 2) if p == 2 else 3*n)
        print(f"Verified {len(receipt['cases'])} explicit comparison certificates.")
        return
    cases = [run_case(n, p, args.trials, ops) for p in (2, 3, 101) for n in (1, 2, 3)]
    receipt = dict(scope='Exact finite certificates; no claim resolving arbitrary fixed-term decoders.',
                   seed_rule='20261112 + 10000*p + n', proposal_budget=args.trials, cases=cases)
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()
