#!/usr/bin/env python3
"""Check one hand-designed directed-cycle control for ordered entropy bounds.

Run from the repository root:
    python3 lean-backlog/tools/host-probe/ordered_correction_control.py

One uniform alphabet symbol is copied to three cells; every other cell is
constant. In base-alphabet entropy a set has rank one exactly when it meets
those three cells. Thus all computations below are exact over every finite
alphabet of size at least two. No optimization or host search is performed.
"""

import json


def audit(rho, active):
    d = len(rho)
    rho = tuple(frozenset(rows) for rows in rho)
    active = frozenset(active)
    cells = frozenset((r, c) for r in range(d) for c in range(d))
    assert active and active <= cells
    assert all(len(rows) == 3 and rows <= set(range(d)) for rows in rho)
    reverse = [sum(r in rows for rows in rho) for r in range(d)]
    assert reverse == [3] * d

    def rows(indices):
        return frozenset((r, c) for r in indices for c in range(d))

    def helpers(v):
        return rows(rho[v[1]])

    def h(s):
        return int(bool(active.intersection(s)))

    def conditional(s, given):
        return h(set(s).union(given)) - h(given)

    assert all(conditional({v}, helpers(v)) == 0 for v in cells)
    assert all(v not in helpers(v) for v in active)
    assert all(not (u in helpers(v) and v in helpers(u))
               for u in active for v in active if u != v)
    dependencies = {}
    for v in sorted(active):
        observed = sorted(active.intersection(helpers(v)))
        assert len(observed) == 1
        dependencies[str(v)] = observed[0]

    triples = [sorted(rs) for rs in rho]
    last = [p[2] for p in triples]
    s2 = sum(p[1] + 1 for p in triples)  # positions are 1,...,d
    s3 = sum(p[2] + 1 for p in triples)
    middle = []
    for c, (p1, p2, p3) in enumerate(triples):
        mid = {(r, c) for r in range(p2 + 1, p3)}
        middle.append(conditional(mid, rows({p1, p2})))

    correction = []
    row_terms = []
    details = []
    f_total = 0
    for q in range(d):
        columns = [c for c in range(d) if last[c] == q]
        early = {(r, c) for c in columns for r in range(q) if r not in rho[c]}
        partial = set().union(*(rho[c] - {q} for c in columns))
        done = {(q, c) for c in range(d) if last[c] < q}
        fresh = rows({q}) - done
        given = rows(partial) | done
        value = conditional(early, given)
        correction.append(value)
        row_terms.append(conditional(fresh, given))
        f_total += len(fresh)
        if columns:
            details.append({
                "row": q, "columns": columns,
                "partial_helper_rows": sorted(partial),
                "early_entropy": h(early),
                "partial_helper_entropy": h(rows(partial)),
                "done_entropy": h(done), "correction": value,
            })
    assert f_total == s3
    total = h(cells)
    u = sum(middle)
    a = sum(correction)
    endpoint_entropy = h({(last[c], c) for c in range(d)})
    assert total <= s2 + u + endpoint_entropy <= s2 + u + d
    assert total <= sum(row_terms) - a <= s3 - a
    return {
        "dimension": d, "cells": d * d,
        "rho": [sorted(rs) for rs in rho], "active_cells": sorted(active),
        "forward_degrees": [len(rs) for rs in rho],
        "reverse_degrees": reverse,
        "active_dependencies_target_to_helper": dependencies,
        "active_host_loops": 0, "active_mutual_host_pairs": 0,
        "H": total, "S2": s2, "S3": s3,
        "middle_entropies": middle, "U": u,
        "row_corrections": correction, "A": a,
        "last_helper_cell_entropy": endpoint_entropy,
        "conditional_fresh_row_terms": row_terms,
        "nonempty_last_helper_groups": details,
    }


if __name__ == "__main__":
    result = audit(
        [{0, 1, 6}, {0, 1, 4}, {0, 1, 5}, {2, 3, 6},
         {2, 3, 6}, {2, 4, 5}, {3, 4, 5}],
        {(4, 0), (5, 1), (6, 2)},
    )
    assert (result["H"], result["S2"], result["S3"],
            result["U"], result["A"]) == (1, 24, 44, 1, 0)
    groups = {entry["row"]: entry for entry in result["nonempty_last_helper_groups"]}
    assert groups[6]["early_entropy"] == 1
    assert groups[6]["partial_helper_entropy"] == 0
    assert groups[6]["done_entropy"] == 1
    print(json.dumps(result, indent=2))
