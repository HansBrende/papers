#!/usr/bin/env python3
"""Exact incidence controls for the grid-labelling audit.

Run from the repository root:
    python3 lean-backlog/tools/grid_labelling_controls.py

Checks shared-helper spread and two coset/window counterexamples. These
are finite incidence checks, not a capacity search or a tape simulation.
No generated files or third-party packages are needed.
"""
from collections import Counter
import json


def profile(d,b,neighbors):
    vertices=[(i,j,z) for i in range(d) for j in range(d) for z in range(b)]
    rows=[set() for _ in range(d)]
    cols=[set() for _ in range(d)]
    helpers=[set() for _ in range(d)]
    indeg=Counter()
    for p in vertices:
        for q in neighbors(p):
            rows[p[1]].add(q[0])
            cols[q[0]].add(p[1])
            helpers[p[1]].add(q)
            indeg[q]+=1
    return dict(window=max(map(len,rows)), reverse_window=max(map(len,cols)),
                helper_union_sizes=[len(x) for x in helpers],
                helper_columns=[len({q[1] for q in x}) for x in helpers],
                indegree_values=sorted(set(indeg.values())))


def main():
    d,b,degree=5,2,2
    regular=profile(d,b,lambda p:[(p[1],(p[0]+t)%d,p[2]) for t in range(1,degree+1)])
    assert regular['window']==regular['reverse_window']==1
    assert regular['indegree_values']==[degree]
    assert regular['helper_columns']==[d]*d
    assert regular['helper_union_sizes']==[d*b]*d
    partial=[]
    for m in (2,3,4):
        d,b=1<<m,m
        top=1<<(m-1); low=top-1
        def theta_plus_s(p):
            a,c,z=p
            return [((c&low)|((a&top)^top), (a&low)|(c&top),z)]
        result=profile(d,b,theta_plus_s)
        assert result['window']==result['reverse_window']==2
        result.update(m=m,dimension=d,canonical_b=b)
        partial.append(result)
    # C4 x (C2)^2, identified as pairs (a,c) with c encoded by two bits.
    # The bijection chi:C4->(C2)^2 is the identity on these integer labels,
    # but is not a group homomorphism. This map has no fixed vertices.
    nonlinear=profile(4,1,lambda p:[(p[1],(p[0]+1)%4,p[2])])
    assert nonlinear['window']==nonlinear['reverse_window']==1
    assert nonlinear['indegree_values']==[1]
    result=dict(regular_outdegree_counterexample=regular,
                partial_swap_coset_controls=partial,
                nonisomorphic_subgroup_block_bijection=nonlinear,
                scope='Exact incidence checks; no above-half code, tape compiler, or capacity claim.')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
