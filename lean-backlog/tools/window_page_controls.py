#!/usr/bin/env python3
"""Exact controls for contracted last-visit pages; no asymptotic inference.

Run from the repository root: python3 lean-backlog/tools/window_page_controls.py
No third-party packages. Use --output PATH to save the receipt.
"""
import argparse
from itertools import product
import json
from pathlib import Path


def crossing(a, b):
    u, v = a
    s, t = b
    return u < s < v < t or s < u < t < v


def edges(path, width):
    last = {}
    data = []
    for start in range(0, len(path), width):
        end = min(start + width, len(path))
        first = {}
        for q in range(start, end):
            first.setdefault(path[q], q)
        for cell, q in first.items():
            if cell not in last:
                continue
            p = last[cell]
            assert p < start <= q
            assert path[p] == path[q]
            assert all(path[t] != cell for t in range(p+1,q))
            if q == p+1:
                sign = 0
                assert p//width+1 == q//width
            else:
                sign = 1 if path[p+1] > cell else -1
                assert all((path[t]-cell)*sign > 0 for t in range(p+1,q))
            relative = (cell > path[start])-(cell < path[start])
            if relative < 0:
                assert sign == 1
            if relative > 0:
                assert sign == -1
            data.append(dict(edge=(p//width,q//width), p=p, q=q,
                             cell=cell, relative=relative, sign=sign))
        for q in range(start, end):
            last[path[q]] = q
    return data


def verify(path, width):
    data = edges(path, width)
    for selector in (lambda e:e['relative'] == -1,
                     lambda e:e['relative'] == 1,
                     lambda e:e['sign'] == 1,
                     lambda e:e['sign'] == -1):
        page = {e['edge'] for e in data if selector(e)}
        assert not any(crossing(a,b) for a in page for b in page)
    # Every actual coarse edge is assigned; consecutive-window pause edges
    # are already state-spine edges, and cannot cross any edge.
    for e in data:
        assert e['sign'] or e['edge'][1] == e['edge'][0]+1
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    cases = 0
    both_signs_example = None
    for length in range(1,11):
        for moves in product((-1,0,1), repeat=length-1):
            path = [0]
            for move in moves:
                path.append(path[-1]+move)
            for width in range(1,min(length,4)+1):
                data = verify(path,width)
                if both_signs_example is None:
                    upper = {e['edge'] for e in data if e['sign']==1}
                    lower = {e['edge'] for e in data if e['sign']==-1}
                    if upper & lower:
                        both_signs_example = dict(path=path,width=width,
                                                  edges=sorted(upper&lower))
                cases += 1
    h = 4
    tie_path = [0]*h+[1]*h+[0]*h+[1]*h
    ties = verify(tie_path,h)
    long_ties = [e for e in ties if e['edge'][1]-e['edge'][0]>1]
    assert [e['edge'] for e in long_ties] == [(0,2),(1,3)]
    assert crossing(long_ties[0]['edge'],long_ties[1]['edge'])
    assert all(e['relative']==0 for e in long_ties)
    assert {e['sign'] for e in long_ties} == {-1,1}
    both_path = [0,1,2,1]+[1]*4+[1,0,1,2]
    both = [e for e in verify(both_path,4) if e['edge']==(0,2)]
    assert {e['sign'] for e in both} == {-1,1}
    fan_width = 8
    fan_path = list(range(fan_width))
    for x in range(fan_width-2,-1,-1):
        fan_path += [x]*fan_width
    fan_edges = {e['edge'] for e in verify(fan_path,fan_width) if e['sign']==1}
    assert {(0,j) for j in range(1,fan_width)} <= fan_edges
    raw = list(range(2*h))+list(range(2*h-2,-1,-1))+[0]
    assert len(raw)==4*h
    attachments = [sorted({p//h for p in raw[i*h:(i+1)*h]}) for i in range(4)]
    start_rows = [raw[i*h]//h for i in range(4)]
    assert start_rows == [0,1,1,0]
    result = dict(exhaustive_read_lengths=list(range(1,11)),
                  move_alphabet=[-1,0,1], max_window_width=4,
                  cases=cases, failures=0,
                  both_signs_same_coarse_edge=both_signs_example,
                  nonadjacent_both_signs=dict(path=both_path,width=4,edges=both),
                  endpoint_uniqueness_failure=dict(width=fan_width,
                     same_page_edges=sorted(fan_edges)),
                  tie_control=dict(width=h,path=tie_path,edges=long_ties),
                  input_control=dict(width=h,path=raw,
                                     attachments=attachments,start_rows=start_rows),
                  scope='Finite diagnostics. Repaired theorem proved by excursion sign and chronological contraction.')
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
