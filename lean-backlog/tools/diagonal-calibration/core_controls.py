"""Exact fixed controls for row-spread Section 23; no host/design search.

From the repository root:
  python3 lean-backlog/tools/diagonal-calibration/core_controls.py

Standard library only; reuses matching and distance from token_blocks.
No files are written. These checks supplement the written proofs, not Lean.
"""
from collections import Counter
import json

from token_blocks import distance, matching


def rank(tau, cells):
    return len(matching(tau, cells))


def closure_failures(tau, cells, rho):
    failures = []
    for c in rho:
        helper = {v for v in cells if v[0] in rho[c]}
        base = rank(tau, helper)
        for v in sorted(cells):
            if v[1] == c and rank(tau, helper | {v}) != base:
                failures.append(v)
    return failures


def core(tau, cells):
    degree = Counter(t for v in cells for t in tau[v])
    high = {t for t, count in degree.items() if count >= 3}
    retained = {v for v in cells if tau[v] <= high}
    return retained, high, dict(degree)


def check_rank_defect(tau, cells):
    retained, high, degree = core(tau, cells)
    assert rank(tau, cells) == len(degree)  # All tokens already pruned.
    low = set(degree) - high
    removed = cells - retained
    deficiency = len(high) - rank(tau, retained)
    n1 = sum(value == 1 for value in degree.values())
    extra = sum(len(tau[v] & low) - 1 for v in removed)
    assert deficiency >= 0 and extra >= 0
    assert 2*rank(tau, cells) == (2*rank(tau, retained) + len(removed)
                                + 2*deficiency + n1 + extra)
    return dict(high_matching_defect=deficiency, degree_one=n1,
                excess_low_incidences=extra)


def make_grid(d, b, given):
    tau = {(r, c, lane): set() for r in range(d)
           for c in range(d) for lane in range(b)}
    for v, ts in given.items():
        tau[v if len(v) == 3 else (*v, 0)] = set(ts)
    return tau, set(tau)


def failed_core_control(name, d, given, rho, target, expect_far):
    tau, cells = make_grid(d, 1, given)
    assert not closure_failures(tau, cells, rho)
    check_rank_defect(tau, cells)
    retained, high, degree = core(tau, cells)
    assert high == {'h'} and degree['l'] == 2
    failures = closure_failures(tau, retained, rho)
    target = (*target, 0)
    assert target in failures
    active = {v for v in cells if tau[v]}
    active_loops = {v for v in active if v[0] in rho[v[1]]}
    assert not active_loops
    target_distance = distance(target[0], target[1], rho)
    assert (target_distance is None) if expect_far else target_distance == 3
    # The helper square a,b resolves both h and l. Removing its low-touching
    # cells destroys all helper coordinates, including the mate of high h.
    a, b = (0, 0, 0), (1, 1, 0)
    local = {'l': a, 'h': b}
    assert all(v[0] in rho[target[1]] and t in tau[v] for t, v in local.items())
    assert rank(tau, {a, b}) == 2
    assert {v for v in {a, b} if tau[v] <= high} == set()
    exceptional = {v for v in cells if distance(v[0], v[1], rho) in (1, 3)}
    deleted = set().union(*(tau[v] for v in exceptional))
    paid_tau = {v: ts - deleted for v, ts in tau.items()}
    assert deleted == {'h', 'l'}
    assert all(not ts for ts in paid_tau.values())
    assert rank(paid_tau, cells) == 0
    assert not closure_failures(paid_tau, cells, rho)
    return dict(name=name, rank_before=rank(tau, cells),
                rank_core=rank(tau, retained), degree=degree,
                active_loop_count=0, target_distance=target_distance,
                core_recovery_failures=failures,
                tokens_deleted_for_exceptional_cells=sorted(deleted),
                rank_after_paid_cleaning=0)


def all_far_peeling_control():
    # Two coupled lanes make a two-step peeling chain p -> h; q remains.
    d, b = 4, 2
    rho = {c: {c} for c in range(d)}
    given = {(0, 3, 0): {'h'}, (3, 0, 0): {'h'},
             (0, 3, 1): {'p', 'h'}, (3, 0, 1): {'p', 'h'}}
    for r, c in ((0, 1), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2)):
        given[r, c, 0] = {'q'}
    tau, cells = make_grid(d, b, given)
    assert all(distance(v[0], v[1], rho) is None for v in cells if tau[v])
    assert not closure_failures(tau, cells, rho)
    stages = []
    for expected_low in ({'p'}, {'h'}):
        assert not any(check_rank_defect(tau, cells).values())
        retained, high, degree = core(tau, cells)
        low = set(degree) - high
        assert low == expected_low
        assert all(degree[t] == 2 for t in low)
        removed = cells - retained
        assert len(removed) == 2 * len(low)
        assert not closure_failures(tau, retained, rho)
        K, Kcore = rank(tau, cells), rank(tau, retained)
        assert 2*K == len(removed) + 2*Kcore
        assert Kcore == len(high)
        stages.append(dict(degree=degree, low=sorted(low),
                           removed_cells=len(removed), rank_before=K,
                           rank_core=Kcore))
        cells = retained
    retained, high, degree = core(tau, cells)
    assert retained == cells and degree == {'q': 6}
    assert rank(tau, cells) == 1
    return dict(name='all-far two-step mixed peeling with nonempty core',
                d=d, lanes=b, stages=stages, final_degree=degree,
                final_active_coordinates=sum(bool(tau[v]) for v in cells))


def pairing_control():
    d = 4
    rho = {c: {c} for c in range(d)}
    given = {(r, c): {f'p{min(r,c)}-{max(r,c)}'}
             for r in range(d) for c in range(d) if r != c}
    tau, cells = make_grid(d, 1, given)
    assert all(distance(v[0], v[1], rho) is None for v in cells if tau[v])
    assert not closure_failures(tau, cells, rho)
    assert not any(check_rank_defect(tau, cells).values())
    retained, high, degree = core(tau, cells)
    assert len(degree) == 6 and set(degree.values()) == {2}
    assert not high and all(not tau[v] for v in retained)
    assert len(retained) == d  # Keep the initially constant diagonal mask.
    K, Kcore = rank(tau, cells), rank(tau, retained)
    assert K == 6 and Kcore == 0
    assert 2*K == len(cells - retained) + 2*Kcore
    assert not closure_failures(tau, retained, rho)
    return dict(name='all-far window-one pairing to empty-token core',
                rank_before=K, rank_core=Kcore,
                removed_cells=len(cells - retained),
                retained_constant_cells=len(retained))


def global_inequality_countercontrol():
    rho = {c: {c, (c + 1) % 4} for c in range(4)}
    active = [(2, 0), (3, 0), (0, 1), (3, 1),
              (0, 2), (1, 2), (1, 3), (2, 3)]
    given = {}
    for i, pair in enumerate(((0, 5), (1, 4), (2, 6), (3, 7))):
        for j in pair:
            given[active[j]] = {'z', f'y{i}'}
    tau, cells = make_grid(4, 1, given)
    assert not closure_failures(tau, cells, rho)
    retained, high, degree = core(tau, cells)
    defect = check_rank_defect(tau, cells)
    assert high == {'z'} and len(cells - retained) == 8
    assert rank(tau, cells) == 5 and rank(tau, retained) == 0
    assert defect == dict(high_matching_defect=1, degree_one=0,
                          excess_low_incidences=0)
    return dict(name='four-pair residual refutes uncharged rank inequality',
                rank_before=5, rank_core=0, noncore_coordinates=8, **defect)


def main():
    near = failed_core_control('near-only active countercontrol', 3,
                               {(0, 0): {'h', 'l'}, (1, 1): {'h', 'l'},
                                (2, 2): {'h'}},
                               {0: {1, 2}, 1: {0, 2}, 2: {0, 1}},
                               (2, 2), False)
    far = failed_core_control('far target damaged by near helper coordinates', 4,
                              {(0, 0): {'h', 'l'}, (1, 1): {'h', 'l'},
                               (2, 2): {'h'}, (3, 3): {'h'}},
                              {0: {1, 2}, 1: {0, 2},
                               2: {0, 1}, 3: {0, 1}},
                              (3, 3), True)
    print(json.dumps({'status': 'PASS',
                      'controls': [near, far, all_far_peeling_control(),
                                   pairing_control(), global_inequality_countercontrol()]}, indent=2))


if __name__ == '__main__':
    main()
