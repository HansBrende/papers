#!/usr/bin/env python3
"""Exact GF3 Fano fitting-matrix CNF using two Boolean indicators per scalar.

The arithmetic tables are exhaustively checked. A known rank10 fitting
matrix supplies a full CNF assignment check, including every Tseitin gate.
"""
import argparse,json
from pathlib import Path
from functools import reduce
from gf2_cnf import CNF,write_cnf,build as gf2_build,check_packing_control
from plane_controls import plane


def OR(c,*xs):return c.neg(reduce(c.both,[c.neg(x) for x in xs]))
def add(c,a,b):
    a1,a2=a;b1,b2=b;a0=c.neg(OR(c,a1,a2));b0=c.neg(OR(c,b1,b2))
    return (OR(c,c.both(a1,b0),c.both(a0,b1),c.both(a2,b2)),
            OR(c,c.both(a2,b0),c.both(a0,b2),c.both(a1,b1)))
def mul(c,a,b):
    a1,a2=a;b1,b2=b
    return OR(c,c.both(a1,b1),c.both(a2,b2)),OR(c,c.both(a1,b2),c.both(a2,b1))
def const(x):return bool(x==1),bool(x==2)


def check_tables():
    c=CNF()
    for x in range(3):
        for y in range(3):
            assert add(c,const(x),const(y))==const((x+y)%3)
            assert mul(c,const(x),const(y))==const((x*y)%3)
    assert not c.clauses and not c.variables


def build(control,r):
    # Reuse the independently checked point-order DAG test.
    gf2_build(control,r)
    data=plane(2);A=control['acyclic_vertices'];ai={x:i for i,x in enumerate(A)};n=len(data['cells']);a=len(A)
    c=CNF()
    def var():
        x,y=c.var(),c.var();c.clause(-x,-y);return x,y
    U=[[const(int(ai[i]==t)) if i in ai else var() for t in range(r)] for i in range(n)]
    V=[[const(0) if t>=a and j in ai else var() for j in range(n)] for t in range(r)]
    for i in range(n):
        for j in range(n):
            if i!=j and data['allowed'][i][j]:continue
            out=reduce(lambda a,b:add(c,a,b),[mul(c,U[i][t],V[t][j]) for t in range(r)])
            c.clause(out[0] if i==j else c.neg(out[0]));c.clause(c.neg(out[1]))
    return c,U,V


def check_control(control):
    c,U,V=build(control,10);A=control['acyclic_vertices'];blocks=control['packing']
    ordered=[next(b for b in blocks if a in b) for a in A]
    ordered += [b for b in blocks if b not in ordered]
    C=[[int(i in b) for b in ordered] for i in range(28)]
    G=[[int(j in b) for j in range(28)] for b in ordered]
    values={}
    def setval(x,v):
        if isinstance(x,bool):assert x==bool(v)
        elif x in values:assert values[x]==bool(v)
        else:values[x]=bool(v)
    for arr,num in [(U,C),(V,G)]:
        for row,nrow in zip(arr,num):
            for pair,v in zip(row,nrow):
                setval(pair[0],v==1);setval(pair[1],v==2)
    def val(x):
        if isinstance(x,bool):return x
        return values[abs(x)] if x>0 else not values[abs(x)]
    for kind,z,x,y in c.gates:
        values[z]=val(x) and val(y) if kind=='and' else val(x)!=val(y)
    assert len(values)==c.variables
    assert all(any(val(x) for x in clause) for clause in c.clauses)
    return len(c.clauses)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--rank',type=int,default=9);ap.add_argument('--control',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();control=json.loads(a.control.read_text());check_tables();control_n=check_control(control)
    c,U,V=build(control,a.rank);digest=write_cnf(a.output,c)
    print(json.dumps(dict(variables=c.variables,clauses=len(c.clauses),sha256=digest,verified_rank10_control_clauses=control_n)))
if __name__=='__main__':main()
