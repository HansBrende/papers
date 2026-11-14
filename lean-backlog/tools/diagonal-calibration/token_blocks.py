"""Exact checks of the explicit fundamental-token controls in row-spread §21.

From the repository root:
  python3 lean-backlog/tools/diagonal-calibration/token_blocks.py

Standard library only; no optimizer, host/design search, or file writes.
The finite checks supplement the written proof, not a Lean formalization.
"""
from collections import deque
from fractions import Fraction
import json


def matching(tau, cells):
    mate = {}

    def extend(cell, seen):
        for token in sorted(tau[cell]):
            if token in seen:
                continue
            seen.add(token)
            if token not in mate or extend(mate[token], seen):
                mate[token] = cell
                return True
        return False

    for cell in sorted(cells):
        extend(cell, set())
    return mate


def canonical_block(tau, helper, tokens, basis):
    mate = matching(tau, helper)
    inverse = {cell: token for token, cell in mate.items()}
    reachable = set(tokens) - set(mate)
    pending = list(reachable)
    while pending:
        token = pending.pop()
        for cell in helper:
            if token not in tau[cell] or inverse.get(cell) == token:
                continue
            assert cell in inverse
            next_token = inverse[cell]
            if next_token not in reachable:
                reachable.add(next_token)
                pending.append(next_token)
    omega = set(tokens) - reachable
    chosen = {token: mate[token] for token in omega}
    for token, cell in basis.items():
        if cell in helper:
            assert token in omega
            chosen[token] = cell
    assert len(set(chosen.values())) == len(chosen)
    assert set().union(*(tau[cell] for cell in chosen.values())) == omega
    assert all(token in tau[cell] for token, cell in chosen.items())
    return omega, chosen


def distance(row, column, rho):
    start, target = ('R', row), ('C', column)
    pending = deque([(start, 0)])
    visited = {start}
    while pending:
        (side, value), steps = pending.popleft()
        if (side, value) == target:
            return steps
        neighbors = ([('R', v) for v in rho[value]] if side == 'C'
                     else [('C', c) for c in rho if value in rho[c]])
        for node in neighbors:
            if node not in visited:
                visited.add(node)
                pending.append((node, steps + 1))
    return None


def audit(name, tau, rho, row=lambda v: v[0], column=lambda v: v[1], basis=None):
    cells = set(tau)
    tokens = set().union(*tau.values())
    if basis is None:
        basis = {token: next(v for v in sorted(cells) if tau[v] == {token})
                 for token in tokens}
    assert set(basis) == tokens
    assert all(tau[cell] == {token} for token, cell in basis.items())
    assert len(set(basis.values())) == len(tokens)
    assert len(matching(tau, cells)) == len(tokens)
    slack = cells - set(basis.values())
    rows = {row(v) for v in cells}
    codegree = max((sum(i in s and j in s for s in rho.values())
                   for i in rows for j in rows if i != j), default=0)
    m = {v: 0 for v in cells}
    kappa = {t: 0 for t in tokens}
    edges = []
    for c, helper_rows in rho.items():
        helper = {v for v in cells if row(v) in helper_rows}
        omega, chosen = canonical_block(tau, helper, tokens, basis)
        for v in cells:
            if column(v) == c and v not in helper:
                assert tau[v] <= omega
        for token, v in chosen.items():
            m[v] += 1
            kappa[token] += 1
            if v in slack:
                assert basis[token] not in helper
                edges.append((v, token, c))
    chi = {t: int(row(v) not in rho[column(v)]) for t, v in basis.items()}
    ell = len(tokens) - sum(chi.values())
    e = {t: kappa[t] - m[basis[t]] - chi[t] for t in tokens}
    assert all(value >= 0 for value in e.values())
    assert sum(m[v] for v in slack) == len(tokens) - ell + sum(e.values())
    for token in tokens:
        assert sum(t == token for _, t, _ in edges) == e[token] + chi[token]
    for v, t, _ in edges:
        assert row(v) != row(basis[t])
        assert e[t] >= m[v] - codegree - 1
    weight = sum((Fraction(e[t], e[t] + 1) for _, t, _ in edges), Fraction(0))
    assert weight <= sum(e.values())
    for v in slack:
        paid = sum((Fraction(e[t], e[t] + 1) for y, t, _ in edges if y == v),
                   Fraction(0))
        assert paid >= max(0, m[v] - codegree - 1)
    refined = sum((Fraction(m[v], max(1, m[v] - codegree)) for v in slack),
                  Fraction(0))
    assert len(tokens) <= ell + refined
    assert (codegree + 2) * len(tokens) <= (codegree + 1) * len(cells) + ell
    near = far = None
    if codegree <= 1:
        near_tokens = {t for t, v in basis.items() if distance(row(v), column(v), rho) == 3}
        far_tokens = {t for t, v in basis.items() if chi[t] and t not in near_tokens}
        for v, t, _ in edges:
            if t in far_tokens:
                assert e[t] >= m[v] - 1
        for v in slack:
            assert sum((Fraction(1, e[t] + 1) for y, t, _ in edges
                        if y == v and t in far_tokens), Fraction(0)) <= 1
        near, far = len(near_tokens), len(far_tokens)
        assert far <= len(slack)
        assert 2 * len(tokens) <= len(cells) + ell + near
    return dict(name=name, N=len(cells), rank=len(tokens), lambda_row_pair=codegree,
                basis_loops=ell, slack=len(slack), near_basis=near, far_basis=far,
                scaled_edge_weight=str(weight), E=sum(e.values()),
                refined_slack_sum=str(refined))


def main():
    controls = []
    # Window-one pairing, with independent diagonal coordinates.
    tau = {(i, c, 0): {f'P{min(i,c)}-{max(i,c)}'} for i in range(4) for c in range(4)}
    controls.append(audit('window-one pairing', tau, {c: {c} for c in range(4)}))

    # The triangle circuit plus six free host loops, attaining 3K=2N+ell.
    tau = {(i, c, 0): {f'L{i}-{c}'} for i in range(3) for c in range(3) if i != c}
    tau.update({(0, 0, 0): {'a'}, (1, 1, 0): {'b'}, (2, 2, 0): {'a', 'b'}})
    controls.append(audit('triangle and free loops', tau, {c: set(range(3)) - {c} for c in range(3)}))
    assert 3 * controls[-1]['rank'] == 2 * controls[-1]['N'] + controls[-1]['basis_loops']

    # The existing cyclic-four control after paying the shared source z.
    rho = {c: {c, (c + 1) % 4} for c in range(4)}
    tau = {(i, c, 0): {f'L{i}-{c}'} for c in range(4) for i in rho[c]}
    active = [(2, 0), (3, 0), (0, 1), (3, 1), (0, 2), (1, 2), (1, 3), (2, 3)]
    for number, pair in enumerate(((0, 5), (1, 4), (2, 6), (3, 7))):
        for j in pair:
            tau[(*active[j], 0)] = {f'y{number}'}
    controls.append(audit('cyclic-four after deleting z', tau, rho))

    # Quotient twin groups: four coordinates at each group intersection.
    tau = {}
    for i in range(4):
        for c in range(4):
            tau[i, c, 0] = ({f'L{i}-{c}'} if i // 2 == c // 2
                            else {f'P{min(i,c)}-{max(i,c)}'})
    controls.append(audit('two row/column groups with scalar mass four', tau,
                          {0: {0}, 1: {1}}, row=lambda v: v[0] // 2,
                          column=lambda v: v[1] // 2))

    # One global symbol, with its chosen basis outside the helper row. This
    # exercises nonzero scaled-edge weights (3/4) rather than only e=0.
    tau = {(i, c, 0): {'z'} for i in range(4) for c in range(4)}
    controls.append(audit('nonzero scaled-edge calibration', tau,
                          {c: {0} for c in range(4)}, basis={'z': (1, 0, 0)}))
    assert controls[-1]['scaled_edge_weight'] == '3'
    assert controls[-1]['E'] == 3
    print(json.dumps(dict(status='PASS', controls=controls), indent=2))


if __name__ == '__main__':
    main()
