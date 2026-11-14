"""Exact fixed arbitrary-coefficient controls; no optimizer or host search.

From the repository root:
  python3 lean-backlog/tools/diagonal-calibration/linear_core_controls.py
Standard library. Reuses the public modular rank, host distance, matching,
and difference-code graph helpers. It writes no files and is not Lean.
"""
from collections import Counter
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
tool_dir = Path(__file__).resolve().parent
sys.path.insert(0, str(tool_dir.parent))
from cyclic_difference_code import graph
from token_blocks import distance, matching
from twisted_quotient_controls import rank as modular_rank


def unit(i, p):
    return 1 + i % (p-1)


def sources(matrix, cells):
    return set().union(*(set(matrix[v]) for v in cells)) if cells else set()


def rank(matrix, cells, p):
    cells = sorted(cells)
    columns = sorted(sources(matrix, cells))
    if not cells or not columns:
        return 0
    return modular_rank([[matrix[v].get(t, 0) for t in columns] for v in cells], p)


def failures(matrix, cells, rho, p):
    result = []
    for c, helper_rows in rho.items():
        helper = {v for v in cells if v[0] in helper_rows}
        helper_rank = rank(matrix, helper, p)
        for v in sorted(cells):
            if v[1] == c and rank(matrix, helper | {v}, p) != helper_rank:
                result.append(v)
    return result


def grid(d, lanes, given):
    matrix = {(r, c, lane): {} for r in range(d) for c in range(d)
              for lane in range(lanes)}
    matrix.update({v if len(v) == 3 else (*v, 0): dict(row)
                   for v, row in given.items()})
    return matrix, set(matrix)


def rescale(matrix, p):
    """Fixed nonzero row/source scalings; no choice is fitted to a result."""
    columns = {t: unit(j+1, p) for j, t in enumerate(sorted(sources(matrix, set(matrix))))}
    return {v: {t: value*unit(i, p)*columns[t] % p for t, value in row.items()}
            for i, (v, row) in enumerate(sorted(matrix.items()))}


def incidence(matrix, cells):
    return sum(len(matrix[v]) for v in cells)


def assert_clean(matrix, cells, rho):
    assert all(not matrix[v] or distance(v[0], v[1], rho) not in (1, 3)
               for v in cells)


def finite_bound(matrix, cells, rho, p):
    K, N, I = rank(matrix, cells, p), len(cells), incidence(matrix, cells)
    assert K == len(sources(matrix, cells))
    assert not failures(matrix, cells, rho, p)
    a = max(2, max(map(len, matrix.values()), default=0))
    L = sum(v[0] in rho[v[1]] for v in cells)
    N3 = sum(distance(v[0], v[1], rho) == 3 for v in cells)
    assert 6*K <= 2*I + N + (2*a+2)*L + (a-1)*N3
    if a == 2:
        assert 6*K <= 5*N + 6*L + N3
    return dict(K=K, N=N, I=I, a=a, L=L, N3=N3)


def clean_bound(matrix, cells, rho, p):
    assert_clean(matrix, cells, rho)
    assert not failures(matrix, cells, rho, p)
    K, N, I = rank(matrix, cells, p), len(cells), incidence(matrix, cells)
    assert K == len(sources(matrix, cells))
    assert 4*K <= N+I
    return dict(K=K, N=N, I=I, clean_fourK_slack=N+I-4*K)


def pay_near_sources(matrix, cells, rho, p):
    old_K, old_I = rank(matrix, cells, p), incidence(matrix, cells)
    exceptional = {v for v in cells if distance(v[0], v[1], rho) in (1, 3)}
    deleted = sources(matrix, exceptional)
    paid = {v: {t: a for t, a in row.items() if t not in deleted}
            for v, row in matrix.items()}
    t, J = len(deleted), old_I-incidence(paid, cells)
    assert rank(paid, cells, p) == old_K-t
    assert J >= t
    clean = clean_bound(paid, cells, rho, p)
    assert 4*old_K <= len(cells)+old_I+4*t-J <= len(cells)+old_I+3*t
    return dict(source_cost=t, deleted_incidences=J, **clean)


def difference_control(p):
    d = 5
    vertices, edges = graph(d)
    fixed = 0
    given = {}
    for cell, (u, v) in edges.items():
        row = {}
        if u != fixed:
            row[u] = 1
        if v != fixed:
            row[v] = -1 % p
        given[cell] = row
    matrix, cells = grid(d, 1, given)
    matrix = rescale(matrix, p)
    rho = {c: {c, (c+1) % d} for c in range(d)}
    finite = finite_bound(matrix, cells, rho, p)
    assert finite['K'] == len(vertices)-1 == 19
    cycle = {(2, 0, 0), (1, 2, 0), (3, 0, 0), (0, 2, 0)}
    assert rank(matrix, cycle, p) == 3
    assert len(matching({v: set(row) for v, row in matrix.items()}, cycle)) == 4
    return dict(name='nongeneric cyclic-five difference code', field=p,
                **finite, cycle_actual_rank=3, cycle_support_matching_rank=4,
                paid=pay_near_sources(matrix, cells, rho, p))


def near_helper_failure(p):
    rho = {0: {1, 2}, 1: {0, 2}, 2: {0, 1}, 3: {0, 1}}
    matrix, cells = grid(4, 1, {(0, 0): {'h': 1, 'l': 1},
                               (1, 1): {'l': 1},
                               (2, 2): {'h': 1}, (3, 3): {'h': 1}})
    matrix = rescale(matrix, p)
    finite = finite_bound(matrix, cells, rho, p)
    degree = Counter(t for v in cells for t in matrix[v])
    assert degree == {'h': 3, 'l': 2}
    retained = {v for v in cells if 'l' not in matrix[v]}
    assert rank(matrix, retained, p) == 1
    bad = failures(matrix, retained, rho, p)
    assert (3, 3, 0) in bad and distance(3, 3, rho) is None
    assert all(v[0] not in rho[v[1]] for v in cells if matrix[v])
    local = {(0, 0, 0), (1, 1, 0)}
    assert rank(matrix, local, p) == 2
    assert not local & retained
    paid = pay_near_sources(matrix, cells, rho, p)
    assert paid['source_cost'] == 2 and paid['K'] == 0
    return dict(name='far target loses its near helper core', field=p,
                **finite, raw_core_rank=1, raw_core_failures=bad, paid=paid)


def two_stage_peeling(p):
    rho = {c: {c} for c in range(4)}
    given = {(0, 3, 0): {'h': unit(0, p)},
             (3, 0, 0): {'h': unit(1, p)},
             (0, 3, 1): {'h': unit(0, p), 'p': unit(1, p)},
             (3, 0, 1): {'h': unit(1, p), 'p': unit(2, p)}}
    for i, cell in enumerate(((0, 1), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2))):
        given[cell[0], cell[1], 0] = {'q': unit(i, p)}
    matrix, cells = grid(4, 2, given)
    matrix = rescale(matrix, p)
    original_N = len(cells)
    original_K = rank(matrix, cells, p)
    constants = {v for v in cells if not matrix[v]}
    assert original_K == 3 and len(constants) == 22
    stages = []
    for expected_low in ({'p'}, {'h'}):
        before = clean_bound(matrix, cells, rho, p)
        degree = Counter(t for v in cells for t in matrix[v])
        low = {t for t, value in degree.items() if value <= 2}
        high = set(degree)-low
        assert low == expected_low and all(degree[t] == 2 for t in low)
        retained = {v for v in cells if not set(matrix[v]) & low}
        removed = cells-retained
        assert len(removed) == 2*len(low)
        after = clean_bound(matrix, retained, rho, p)
        assert after['K'] == len(high)
        assert 2*before['K'] == len(removed)+2*after['K']
        assert constants <= retained
        stages.append(dict(degrees=dict(degree), low=sorted(low), before=before,
                           removed_cells=len(removed), after=after))
        cells = retained
    degree = Counter(t for v in cells for t in matrix[v])
    assert degree == {'q': 6}
    assert rank(matrix, cells, p) == 1
    assert 2*original_K == original_N-len(cells)+2*rank(matrix, cells, p)
    assert constants <= cells and len(cells) == 28
    return dict(name='all-far actual-coefficient two-stage peeling', field=p,
                original_N=original_N, original_K=original_K, stages=stages,
                final_degree=dict(degree), final_mask_size=len(cells),
                retained_constant_cells=len(constants))


if __name__ == '__main__':
    controls = [control(p) for p in (2, 3, 5)
                for control in (difference_control, near_helper_failure, two_stage_peeling)]
    print(json.dumps(dict(status='EXACT PASS', fields=[2, 3, 5],
                          control_count=len(controls), controls=controls), indent=2))
