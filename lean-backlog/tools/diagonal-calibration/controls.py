#!/usr/bin/env python3
"""Exact GF(2) diagonal codes and all-alphabet row-order upper certificates.

Run this file with standard Python; no solver or numerical tolerance is used.
The Clebsch diagonal upper10 is cited from Paper4 H4, not re-proved here.
"""
from pathlib import Path
import json


def binary_rank(rows):
    basis={}
    for x in rows:
        while x:
            k=x.bit_length()-1
            if k in basis:x^=basis[k]
            else:basis[k]=x;break
    return len(basis)


def folded_cube_control(j):
    assert j >= 1 and j % 2 == 1
    n = 1 << (j - 1)
    generators = [1 << i for i in range(j - 1)] + [n - 1]
    rows = []
    for i in range(n):
        row = 1 << i
        for g in generators:
            row ^= 1 << (i ^ g)
        rows.append(row)
    rank = binary_rank(rows)
    assert rank == (n - (1 << ((j - 1) // 2))) // 2
    return dict(j=j, vertices=n, rank=rank, dimension=n-rank)


def subgroup(a,b):
    return [0,a,b,a^b]


def cosets(d,H):
    left=set(range(d));out=[]
    while left:
        x=min(left);part=sorted(x^h for h in H)
        assert set(part)<=left
        left.difference_update(part);out.append(part)
    return out


def row_order(d,T):
    masks=[sum(1<<(c^t) for t in T) for c in range(d)]
    count=[sum((m&s)==m for m in masks) for s in range(1<<d)]
    dp=[0]*(1<<d);last=[-1]*(1<<d)
    for s in range(1,1<<d):
        options=[];r=s
        while r:
            v=r&-r;prev=s^v
            options.append((dp[prev]+count[prev],v.bit_length()-1))
            r^=v
        dp[s],last[s]=max(options)
    s=(1<<d)-1;order=[]
    while s:
        v=last[s];order.append(v);s^=1<<v
    order.reverse();pos={v:i for i,v in enumerate(order)}
    A=[(i,c) for i in range(d) for c in range(d)
       if all(pos[j]<pos[i] for j in (c^t for t in T))]
    assert len(A)==dp[-1]
    assert all(pos[j]<pos[i] for i,c in A for j,l in A if j in [c^t for t in T])
    return order,A,dp[-1]


def control(d,T):
    whole_rows=[0]*(d*d);diagonals=[]
    for g in range(d):
        S=sorted(g^t for t in T)
        if 0 in S:
            desc={'g':g,'kind':'loops','dimension':d,'rank':0,'parts':[]}
        elif g==0 and T==[1,2,4,8,15]:
            check=[(1<<i)|sum(1<<(i^s) for s in S) for i in range(d)]
            assert binary_rank(check)==6
            desc={'g':g,'kind':'Clebsch','dimension':10,'rank':6,'binary_check_rows':check}
            for i,row in enumerate(check):
                whole_rows[i*d+(i^g)]=sum(1<<(j*d+(j^g)) for j in range(d) if row>>j&1)
        else:
            planes=[subgroup(a,b) for a in S for b in S if a<b and a^b in S]
            if planes:
                parts=cosets(d,planes[0]);kind='K4 partition'
                assert all(x!=y and (x^y) in S for part in parts for x in part for y in part if x!=y)
            else:
                parts=cosets(d,[0,S[0]]);kind='matching'
            check=[sum(1<<j for j in part) for part in parts]
            assert binary_rank(check)==len(parts)
            for part in parts:
                row=sum(1<<(j*d+(j^g)) for j in part)
                for i in part:whole_rows[i*d+(i^g)]=row
            desc={'g':g,'kind':kind,'dimension':d-len(parts),'rank':len(parts),'parts':parts}
            # Brute independent-set upper matching the construction.
            indep=next((m for m in range(1<<d) if m.bit_count()==len(parts)
                       and all(not(m>>(i^s)&1) for i in range(d) if m>>i&1 for s in S)),None)
            assert indep is not None
            desc['independent_set']=[i for i in range(d) if indep>>i&1]
        diagonals.append(desc)
    dimension=sum(x['dimension'] for x in diagonals)
    assert binary_rank(whole_rows)==d*d-dimension
    for p,row in enumerate(whole_rows):
        i,c=divmod(p,d)
        if i in [c^t for t in T]:
            assert row==0
        else:
            assert row>>p&1
            assert all(j in [c^t for t in T] for q in range(d*d) if q!=p and row>>q&1 for j in [q//d])
    order,A,deficit=row_order(d,T)
    assert dimension<=d*d-deficit
    return dict(d=d,T=T,diagonals=diagonals,diagonal_dimension=dimension,
                whole_binary_check_rows=whole_rows,whole_binary_rank=d*d-dimension,
                row_order=order,acyclic_cells=A,all_alphabet_upper=d*d-deficit,
                row_order_optimum_deficit=deficit)


def main():
    results=[control(4,[1,2]),control(8,[1,2,4]),control(16,[1,2,4,8]),control(16,[1,2,4,8,15])]
    Path(__file__).with_name('receipt.json').write_text(json.dumps(results,indent=2)+'\n')
    for r in results:
        print({k:r[k] for k in ['d','T','diagonal_dimension','whole_binary_rank','all_alphabet_upper']})
    print('Folded cubes:', [folded_cube_control(j) for j in [1,3,5,7,9]])

if __name__=='__main__':main()
