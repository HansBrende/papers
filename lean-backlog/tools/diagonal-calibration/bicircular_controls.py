"""Exact controls for row-spread Section 22, using Python's standard library.

From the repository root:
  python3 lean-backlog/tools/diagonal-calibration/bicircular_controls.py

Checks explicit examples only: matching versus bicircular rank, whole-row
recovery, the finite support-incidence charge and high-reverse-row deletion.
No optimizer, host/design search or file writes; not Lean verification.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json


from token_blocks import distance, matching


def matching_rank(tau, cells):
    return len(matching(tau, cells))


def graph_rank(tau, cells):
    tokens = set().union(*(tau[cell] for cell in cells))
    parent = {t: t for t in tokens}

    def find(t):
        while parent[t] != t:
            t = parent[t]
        return t

    for cell in cells:
        if len(tau[cell]) == 2:
            a, b = sorted(tau[cell])
            parent[find(a)] = find(b)
    vertices, edges = Counter(), Counter()
    for token in tokens:
        vertices[find(token)] += 1
    for cell in cells:
        if tau[cell]:
            edges[find(next(iter(tau[cell])))] += 1
    return sum(min(number, edges[root]) for root, number in vertices.items())


def audit(name, d, supports, rho, a=2):
    tau = {(r, c): set(supports.get((r, c), ()))
           for r in range(d) for c in range(d)}
    cells = sorted(tau)
    active = [v for v in cells if tau[v]]
    tokens = set().union(*tau.values())
    assert a >= 2 and all(len(support) <= a for support in tau.values())
    assert matching_rank(tau, cells) == len(tokens)
    bicircular = all(len(support) <= 2 for support in tau.values())
    checked = 0
    if bicircular and len(active) <= 8:
        for size in range(len(active) + 1):
            for subset in combinations(active, size):
                assert matching_rank(tau, subset) == graph_rank(tau, subset)
                checked += 1
    for c in range(d):
        helper = [v for v in cells if v[0] in rho[c]]
        helper_rank = matching_rank(tau, helper)
        if bicircular:
            assert graph_rank(tau, helper) == helper_rank
        for v in cells:
            if v[1] == c:
                joined = helper if v in helper else helper + [v]
                assert matching_rank(tau, joined) == helper_rank
                if bicircular:
                    assert graph_rank(tau, joined) == helper_rank
    occurrences = {t: [v for v in cells if t in tau[v]] for t in tokens}
    degree = {t: len(vs) for t, vs in occurrences.items()}
    loops = {v for v in cells if v[0] in rho[v[1]]}
    near = {v for v in cells if distance(*v, rho) == 3}
    degree_one = {t for t in tokens if degree[t] == 1}
    assert all(occurrences[t][0] in loops for t in degree_one)
    assert len(degree_one) <= len(loops)
    low_tokens = {t for t in tokens if degree[t] == 2}
    k = {v: len(tau[v] & low_tokens) for v in cells}
    extras = {v: max(0, k[v] - 1) for v in cells}
    far_multiple = {v for v in set(cells) - loops - near if k[v] >= 2}
    charged = []
    for e in far_multiple:
        others = []
        for t in tau[e] & low_tokens:
            other = next(v for v in occurrences[t] if v != e)
            assert other in loops
            others.append(other)
            charged.append((other, t))
        assert len(set(others)) == len(others)
    assert len(set(charged)) == len(charged)
    assert len(charged) <= sum(len(tau[v]) for v in loops) <= a * len(loops)
    far_extra = sum(extras[v] for v in far_multiple)
    assert far_extra <= Fraction(a - 1, a) * len(charged)
    assert sum(extras.values()) <= (a - 1) * (len(near) + 2 * len(loops))
    n1 = len(degree_one)
    n2 = len(low_tokens)
    K, N, L, N3 = len(tokens), len(cells), len(loops), len(near)
    I = sum(map(len, tau.values()))
    assert 3*K <= I + 2*n1 + n2
    assert 2*n2 <= N + sum(extras.values())
    assert 6*K <= 2*I + N + (2*a+2)*L + (a-1)*N3
    if a == 2:
        assert 6*K <= 5*N + 6*L + N3
    return dict(name=name, a=a, N=N, K=K, I=I, L=L, N3=N3,
                degree_one=n1, degree_two=n2, total_extras=sum(extras.values()),
                far_multiple_cells=len(far_multiple), far_extras=far_extra,
                far_loop_token_charges=len(charged), subset_ranks_checked=checked)


def weak_alignment_controls():
    """Two valid designs refuting the proposed edge inference, not the cap."""
    records = []
    for d in (3, 9):
        cells = {(r, c) for r in range(d) for c in range(d)}
        tau = {v: set() for v in cells}
        if d == 3:
            y, xa, xb, bad_column = (0, 0), (0, 1), (0, 2), 1
            rho = {c: {0} for c in range(d)}
        else:
            xa, xb, y, bad_column = (0, 0), (0, 1), (0, 2), 8
            rho = {c: {1 if c < 3 else 0} for c in range(d)}
            tau[(1, 3)], tau[(1, 4)] = {'a'}, {'b'}
        tau[xa], tau[xb], tau[y] = {'a'}, {'b'}, {'a', 'b'}
        basis = {'a': xa, 'b': xb}
        local, blocks = {}, {}
        for c in range(d):
            if d == 9 and c < 3:
                local[c] = {'a': (1, 3), 'b': (1, 4)}
            elif c == bad_column:
                local[c] = {'a': y, 'b': xb}
            else:
                local[c] = {'a': xa, 'b': y}
            block = blocks[c] = set(local[c].values())
            assert len(block) == 2
            assert all(v[0] in rho[c] and t in tau[v]
                       for t, v in local[c].items())
            assert set().union(*(tau[v] for v in block)) == {'a', 'b'}
            assert all(local[c][t] == v for t, v in basis.items() if v in block)
            outside = {t for t, v in basis.items() if v not in block}
            assert {local[c][t] for t in outside} == block - set(basis.values())
        checked = audit(f'weak alignment, d={d}', d, tau, rho)
        memberships = {v: {c for c in range(d) if v in blocks[c]} for v in cells}
        m_y = len(memberships[y])
        e_a = len(set(range(d)) - memberships[xa] - {xa[1]})
        assert max((sum(i in rs and j in rs for rs in rho.values())
                    for i in range(d) for j in range(i)), default=0) == 0
        assert local[bad_column]['a'] == y and xa not in blocks[bad_column]
        assert xa[0] == y[0] and e_a < m_y - 2
        if d == 9:
            assert all(v[0] not in rho[v[1]] for v in cells if tau[v])
            assert distance(*xa, rho) is None
        records.append(dict(d=d, K=checked['K'], m_y=m_y, e_a=e_a,
                            invalid_lower_bound_at_lambda_one=m_y-2))
    return records


def main():
    controls = []
    # A degree-two token need not give mutual recovery when one cell loops.
    controls.append(audit('one-way degree-two token and a degree-one token', 2,
                          {(0, 0): {'a'}, (1, 1): {'a'}, (0, 1): {'b'}},
                          {0: {0}, 1: {0}}))

    # A far E22 edge can be supported by two host-loop singleton coordinates.
    controls.append(audit('far degree-two edge paid by host loops', 3,
                          {(0, 0): {'u'}, (1, 1): {'v'}, (2, 2): {'u', 'v'}},
                          {0: {0}, 1: {1}, 2: {0, 1}}))
    assert controls[-1]['far_multiple_cells'] == 1

    # A triangle with a token loop at w; the u-v edge is E22 and near.
    controls.append(audit('near degree-two edge', 4,
                          {(0, 0): {'u', 'w'}, (1, 1): {'v', 'w'},
                           (2, 2): {'u', 'v'}, (3, 3): {'w'}},
                          {0: {1, 2, 3}, 1: {0, 2, 3},
                           2: {0, 1, 3}, 3: {3}}))
    assert controls[-1]['total_extras'] == 1 and controls[-1]['far_multiple_cells'] == 0

    # The four-pair cyclic-four control: a doubled star, not leaf loops.
    rho = {c: {c, (c + 1) % 4} for c in range(4)}
    supports = {(r, c): {f'L{r}-{c}'} for c in range(4) for r in rho[c]}
    active = [(2, 0), (3, 0), (0, 1), (3, 1),
              (0, 2), (1, 2), (1, 3), (2, 3)]
    for i, pair in enumerate(((0, 5), (1, 4), (2, 6), (3, 7))):
        for j in pair:
            supports[active[j]] = {'z', f'y{i}'}
    controls.append(audit('cyclic-four doubled-star presentation', 4, supports, rho))
    assert controls[-1]['K'] == 13
    assert all(len(supports[v]) == 2 for v in active)
    for size in range(9):
        for subset in combinations(active, size):
            assert matching_rank(supports, subset) == graph_rank(supports, subset)
    controls[-1]['residual_subset_ranks_checked'] = 256

    # A fixed high-reverse row and three surviving diagonal sources. This
    # is a replay of the trimming argument, not a random host search.
    d, R = 4, 1
    rho = {c: {0, c} for c in range(d)}
    supports = {(0, c): {f'q{c}'} for c in range(d)}
    supports.update({(r, 0): {'q0'} for r in range(1, d)})
    supports.update({(r, r): {f'b{r}'} for r in range(1, d)})
    before = audit('high-reverse host before trimming', d, supports, rho)
    high = {r for r in range(d) if sum(r in rs for rs in rho.values()) > R}
    deleted = set().union(*(ts for (r, _), ts in supports.items() if r in high))
    reduced_supports = {v: ts - deleted for v, ts in supports.items()}
    reduced_rho = {c: rs - high for c, rs in rho.items()}
    after = audit('high-reverse host after trimming', d,
                  reduced_supports, reduced_rho)
    assert high == {0} and len(deleted) == 4
    assert after['K'] == before['K'] - len(deleted)
    assert max(sum(r in rs for rs in reduced_rho.values()) for r in range(d)) <= R
    assert all(not ts for (r, _), ts in reduced_supports.items() if r in high)
    controls.extend((before, after))

    # The same Hall charge beyond graph presentations: no graph-rank call.
    far = audit('three degree-two endpoints with loop witnesses', 4,
                {(0, 0): {'u'}, (1, 1): {'v'}, (2, 2): {'w'},
                 (3, 3): {'u', 'v', 'w'}},
                {0: {0}, 1: {1}, 2: {2}, 3: {0, 1, 2}}, a=3)
    assert far['far_extras'] == 2 and far['far_loop_token_charges'] == 3
    near = audit('three-token near cell with two degree-two endpoints', 4,
                 {(0, 0): {'u', 'w'}, (1, 1): {'v', 'w'},
                  (2, 2): {'u', 'v', 'w'}, (3, 3): {'w'}},
                 {0: {1, 2, 3}, 1: {0, 2, 3}, 2: {0, 1, 3}, 3: {3}}, a=3)
    assert near['total_extras'] == 1 and near['far_multiple_cells'] == 0
    controls.extend((far, near))
    print(json.dumps({'status': 'PASS', 'controls': controls,
                      'weak_alignment_controls': weak_alignment_controls()}, indent=2))


if __name__ == '__main__':
    main()
