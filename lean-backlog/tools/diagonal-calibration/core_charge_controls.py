"""Exact fixed boundary-charge controls for row-spread Section 24.

From the repository root:
  python3 lean-backlog/tools/diagonal-calibration/core_charge_controls.py

Standard library only; reuses the existing matching-rank checker.
No host/design search or file writes. These supplement written proofs,
not a Lean formalization. The examples have asymptotic rate one half.
"""
from collections import Counter
from fractions import Fraction
import json


from core_controls import rank


def audit(blocks, width, variant):
    assert blocks >= 2 and width >= 2 and variant in ('double_cycle', 'cycle_singletons')
    # Every nonempty proper subset of one cycle has a strict token surplus.
    # Hence disjoint helper-cycle components cannot cancel to form a square.
    k = width**2
    for mask in range(1, (1 << k)-1):
        edges = {i for i in range(k) if mask & (1 << i)}
        touched = edges | {(i+1) % k for i in edges}
        assert len(touched) > len(edges)
    d = blocks*width
    groups = [set(range(i*width, (i+1)*width)) for i in range(blocks)]
    rho = {c: groups[c//width] for c in range(d)}
    tau = {(r, c): set() for r in range(d) for c in range(d)}
    component = {}
    for i in range(blocks):
        for j in range(i+1, blocks):
            tokens = [(i, j, k) for k in range(width**2)]
            upper = [(r, c) for r in sorted(groups[i]) for c in sorted(groups[j])]
            lower = [(r, c) for r in sorted(groups[j]) for c in sorted(groups[i])]
            for k, (u, v) in enumerate(zip(upper, lower)):
                edge = {tokens[k], tokens[(k+1) % len(tokens)]}
                tau[u] = edge
                tau[v] = edge if variant == 'double_cycle' else {tokens[k]}
            component[i, j] = (set(tokens), upper, lower)
    tokens = set().union(*tau.values())
    active = {x for x in tau if tau[x]}
    N, K, L = d*d, len(tokens), d*width
    assert rank(tau, tau) == K == (N-L)//2
    assert len(active) == N-L
    assert all(x[0]//width != x[1]//width for x in active)
    # The incidence graph is a disjoint union of complete bipartite blocks;
    # every active coordinate therefore has disconnected row/column labels.
    degree = Counter(t for ts in tau.values() for t in ts)
    assert set(degree.values()) == ({4} if variant == 'double_cycle' else {3})
    sigma = {x: 3-len(ts) for x, ts in tau.items()}
    delta = {t: degree[t]-3 for t in tokens}
    local, omega = {}, {}
    for c in range(d):
        helper = {x for x in tau if x[0] in rho[c]}
        local[c] = set()
        for (i, j), (ts, upper, lower) in component.items():
            if c//width not in (i, j):
                continue
            targets = [x for x in upper+lower if x[1] == c]
            wanted = set().union(*(tau[x] for x in targets))
            counterpart = upper if c//width == i else lower
            if variant == 'cycle_singletons' and c//width == j:
                chosen = {x for x in counterpart if tau[x] & wanted}
            else:
                chosen = set(counterpart)
            assert chosen <= helper
            local[c] |= chosen
        omega[c] = set().union(*(tau[x] for x in local[c]))
        assert len(local[c]) == len(omega[c]) == rank(tau, local[c])
        assert all(tau[x] <= omega[c] for x in tau if x[1] == c and x not in helper)
        helper_rank = rank(tau, helper)
        assert all(rank(tau, helper | {x}) == helper_rank for x in tau if x[1] == c)
        boundary = sum(len(tau[x] & omega[c]) for x in tau if x not in local[c])
        assert boundary == sum(delta[t] for t in omega[c])+sum(sigma[x] for x in local[c])
    kappa = Counter(t for ts in omega.values() for t in ts)
    multiplicity = Counter(x for xs in local.values() for x in xs)
    weighted_token = sum(kappa[t]*delta[t] for t in tokens)
    weighted_support = sum((multiplicity[x]+1)*sigma[x] for x in tau)
    assert sum(delta.values())+sum(sigma.values()) == 3*(N-K)
    assert weighted_token+weighted_support >= 3*N  # Clean core: loop supports empty.
    if variant == 'double_cycle':
        assert set(kappa.values()) == {2*width}
        assert {multiplicity[x] for x in active} == {width}
        assert weighted_token == 2*width*K
        assert weighted_token+weighted_support == (2*width+1)*(N-L)+3*L
    else:
        assert set(kappa.values()) == {width+2}
        assert weighted_token == 0
        assert weighted_support == (width+7)*K+3*L
    return dict(blocks=blocks, width=width, variant=variant, d=d, N=N, K=K, L=L,
                token_degrees=sorted(set(degree.values())), all_active_far=True,
                token_defect=sum(delta.values()), support_defect=sum(sigma.values()),
                kappa=sorted(set(kappa.values())), weighted_token=weighted_token,
                weighted_support=weighted_support,
                token_charge_over_rank_deficit=str(Fraction(weighted_token, N-K)),
                support_charge_over_support_defect=str(Fraction(weighted_support, sum(sigma.values()))))


if __name__ == '__main__':
    controls = [audit(m, w, variant) for m, w in ((3, 2), (2, 3))
                for variant in ('double_cycle', 'cycle_singletons')]
    print(json.dumps(dict(status='PASS', controls=controls), indent=2))
