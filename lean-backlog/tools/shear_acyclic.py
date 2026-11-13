#!/usr/bin/env python3
"""Bounded matched affine-shear experiments and independent DAG certificates.

Search needs OR-Tools; certificate replay uses only the standard library.
  python shear_acyclic.py search --repo PATH_TO_PAPERS --output receipt.json
  python shear_acyclic.py verify receipt.json
The search reuses and cross-checks Paper 17's relation convention. A saved
DAG and the pairing/loop cycle packing can certify the exact feedback-vertex
minimum. Solver timeouts prove nothing further. This continuation stops on a
strict gap beyond the pairing-plus-double-loop baseline.
"""
import argparse
from collections import deque
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import time

SEED = 20261113
P = ((1, 0), (-1, 2), (-1, -2), (-1, 4), (-1, -4))
N = ((1, 0), (-1, 2), (-1, -1), (-1, 1), (-1, 3))


def relation(d, maps):
    return [sorted({m['i'][r]*d + (c+m['j'][r]) % d for m in maps})
            for c in range(d) for r in range(d)]


def topological_order(graph, vertices):
    alive = set(vertices)
    indegree = {v: 0 for v in alive}
    for v in alive:
        for u in graph[v]:
            if u in alive:
                indegree[u] += 1
    queue = deque(sorted(v for v in alive if indegree[v] == 0))
    out = []
    while queue:
        v = queue.popleft()
        out.append(v)
        for u in graph[v]:
            if u in alive:
                indegree[u] -= 1
                if indegree[u] == 0:
                    queue.append(u)
    return out if len(out) == len(alive) else None


def pairing_loop_cycles(d, graph):
    """Vertex-disjoint cycles: replace each doubly looped pair by two loops."""
    cycles = [[c*d+c] for c in range(d)]
    double_pairs = []
    for c in range(d):
        for r in range(c+1, d):
            v, u = c*d+r, r*d+c
            if v in graph[v] and u in graph[u]:
                double_pairs.append([v, u])
                cycles.extend([[v], [u]])
            else:
                cycles.append([v, u])
    used = set()
    for cyc in cycles:
        assert not used.intersection(cyc)
        used.update(cyc)
        for i, v in enumerate(cyc):
            assert cyc[(i+1) % len(cyc)] in graph[v]
    assert len(used) == d*d
    return cycles, double_pairs


def specifications(d):
    rng = random.Random(SEED + 1000*d)
    translations = [(0, 0)] + [(rng.randrange(d), rng.randrange(d)) for _ in range(4)]
    families = {}
    for name, pattern in [('P', P), ('N', N)]:
        spec = [[a, b, u, v] for (a, b), (u, v) in zip(pattern, translations)]
        maps = [dict(i=[(a*r+u) % d for r in range(d)],
                     j=[(b*r+v) % d for r in range(d)]) for a, b, u, v in spec]
        families[name] = (spec, maps)
    ident, zero = list(range(d)), [0]*d
    controls = [dict(i=ident[:], j=zero[:])]
    for _ in range(4):
        row = ident[:]
        rng.shuffle(row)
        controls.append(dict(i=row, j=[rng.randrange(d) for _ in range(d)]))
    families['control'] = (None, controls)
    families['zero-offset'] = (None, [dict(i=m['i'][:], j=zero[:]) for m in controls])
    return families


def verify_case(case):
    d, w, family = case['d'], case['w'], case['family']
    assert d in (7, 11, 13) and 1 <= w <= 5
    expected_spec, expected_maps = specifications(d)[family]
    assert case['maps'] == expected_maps[:w]
    assert case['affine_spec'] == (expected_spec[:w] if expected_spec else None)
    graph = relation(d, case['maps'])
    # Verify every diagonal loop and every transposed pair, proving that any
    # acyclic set omits d diagonal positions and one from each unordered pair.
    for c in range(d):
        for r in range(d):
            assert r*d+c in graph[c*d+r]
    alive = case['acyclic_vertices']
    order = case['topological_order']
    assert len(set(alive)) == len(alive)
    assert all(0 <= v < d*d for v in alive)
    assert len(order) == len(alive) and set(order) == set(alive)
    index = {v: i for i, v in enumerate(order)}
    for v in alive:
        for u in graph[v]:
            if u in index:
                assert index[v] < index[u], (family, d, w, v, u)
    upper = d*d-len(alive)
    cycles, double_pairs = pairing_loop_cycles(d, graph)
    lower = len(cycles)
    assert case['double_loop_pairs'] == double_pairs
    assert case['certified_fvs_lower'] == lower
    assert case['certified_fvs_upper'] == upper
    assert lower <= upper
    assert case['pairing_optimum_certified'] == (d*(d+1)//2 == upper)
    assert case['loop_baseline_optimum_certified'] == (lower == upper)
    return lower == upper


def solve_case(d, w, name, limit, cp_model, published):
    spec, full_maps = specifications(d)[name]
    maps = full_maps[:w]
    graph = relation(d, maps)
    assert graph == published.relation(d, [(m['i'], m['j']) for m in maps])
    target = d*d - len(pairing_loop_cycles(d, graph)[0])
    if name == 'zero-offset':
        alive = [c*d+r for c in range(d) for r in range(d) if c > r]
        status, elapsed = 'explicit-calibration', 0.0
        solver_best = None
    else:
        model = cp_model.CpModel()
        keep = [model.NewBoolVar(f'k{v}') for v in range(d*d)]
        pos = [model.NewIntVar(0, d*d-1, f'p{v}') for v in range(d*d)]
        for v in range(d*d):
            for u in graph[v]:
                if u == v:
                    model.Add(keep[v] == 0)
                else:
                    model.Add(pos[v] + 1 <= pos[u]).OnlyEnforceIf([keep[v], keep[u]])
        # Make the universal pairing upper bound explicit, then maximize.
        model.Add(sum(keep) <= target)
        model.Maximize(sum(keep))
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = limit
        solver.parameters.num_workers = 1
        solver.parameters.random_seed = SEED
        start = time.monotonic()
        code = solver.Solve(model)
        elapsed = time.monotonic()-start
        status = solver.StatusName(code)
        solver_best = solver.BestObjectiveBound()
        alive = ([v for v in range(d*d) if solver.Value(keep[v])]
                 if code in (cp_model.OPTIMAL, cp_model.FEASIBLE) else [])
    order = topological_order(graph, alive)
    assert order is not None
    cycles, double_pairs = pairing_loop_cycles(d, graph)
    case = dict(d=d, w=w, family=name,
                affine_spec=spec[:w] if spec else None, maps=maps,
                solver_status=status, solver_best_acyclic_upper=solver_best,
                elapsed_seconds=round(elapsed, 3), acyclic_vertices=alive,
                topological_order=order, certified_fvs_lower=len(cycles),
                certified_fvs_upper=d*d-len(alive),
                double_loop_pairs=double_pairs,
                pairing_optimum_certified=len(alive) == d*(d-1)//2,
                loop_baseline_optimum_certified=d*d-len(alive) == len(cycles))
    verify_case(case)
    print(f'd={d} w={w} {name}: FVS in [{case["certified_fvs_lower"]},'
          f'{case["certified_fvs_upper"]}], status={status}, '
          f'solver DAG upper={solver_best}, time={elapsed:.2f}s', flush=True)
    return case


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    search = sub.add_parser('search')
    search.add_argument('--repo', type=Path, required=True)
    search.add_argument('--output', type=Path, required=True)
    search.add_argument('--seconds', type=float, default=10)
    search.add_argument('--dimensions', type=int, nargs='+', default=[7, 11, 13])
    search.add_argument('--windows', type=int, nargs='+', default=[3, 4, 5])
    replay = sub.add_parser('verify')
    replay.add_argument('receipt', type=Path)
    args = parser.parse_args()
    if args.command == 'verify':
        receipt = json.loads(args.receipt.read_text())
        exact = sum(verify_case(c) for c in receipt['cases'])
        print(f'Checked {len(receipt["cases"])} DAG/cycle-packing certificates; {exact} exact loop-adjusted optima.')
        return
    import ortools
    from ortools.sat.python import cp_model
    source = args.repo/'Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/tools/acyclic_set_search.py'
    spec = importlib.util.spec_from_file_location('paper17_acyclic', source)
    published = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(published)
    receipt = dict(seed=SEED, ortools_version=ortools.__version__,
                   published_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                   solver_seconds_per_instance=args.seconds, cases=[])
    for d in args.dimensions:
        cases = [('zero-offset', 5)] + [(name, w) for w in args.windows for name in ('P','N','control')]
        for name, w in cases:
            case = solve_case(d,w,name,args.seconds,cp_model,published)
            receipt['cases'].append(case)
            args.output.write_text(json.dumps(receipt, indent=2)+'\n')
            # A strict solver bound is only a trigger to seek a replayable
            # obstruction, NOT a mathematical certificate on its own.
            bound = case['solver_best_acyclic_upper']
            if bound is not None and bound < d*d-case['certified_fvs_lower'] - 0.5:
                print('Stopping: solver indicates a gap beyond the loop baseline; seek independent proof.', flush=True)
                return


if __name__ == '__main__':
    main()
