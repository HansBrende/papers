#!/usr/bin/env python3
"""Reproduce the bounded Fano Shannon discovery relaxation.

Default: build and audit the finite family, without solving. --solve runs one
SciPy/HiGHS LP (1800-second limit), then verifies exact primal and dual data.
--verify search-receipt.json replays the full recorded relaxation using only
Python's standard library. For the much smaller mathematical proof use
verify_certificate.py, which does not build this LP or import this file.

Run from any working directory; see README.md. Never use Python -O.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
from itertools import product
import importlib.util
import json
from pathlib import Path
import time


def load_host(repo):
    path = repo / 'lean-backlog/tools/simplex-calibration/plane_controls.py'
    spec = importlib.util.spec_from_file_location('plane_controls', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    host = module.plane(2)
    points, cells = host['points'], host['cells']
    row = [sum(1 << j for j, (p, _) in enumerate(cells) if p == i) for i in range(7)]
    col = [sum(1 << j for j, (_, l) in enumerate(cells) if l == i) for i in range(7)]
    rho = [sum(1 << p for p in range(7)
               if sum(a*b for a,b in zip(points[p],points[l])) % 2 == 0) for l in range(7)]
    helper = [sum(row[p] for p in range(7) if rho[l] >> p & 1) for l in range(7)]
    assert all(H.bit_count() == 12 for H in helper)
    full = (1 << 28)-1
    completed = []
    for A in range(128):
        completed.append(sum(col[l] for l in range(7) if rho[l] & A == rho[l]))

    def closure(S):
        while True:
            A = sum(1 << p for p in range(7) if S & row[p] == row[p])
            new = S | completed[A]
            if new == S:
                return S
            S = new

    seeds = [closure(sum(row[p] for p in range(7) if A >> p & 1)) for A in range(128)]
    cost = [0]*128
    for A in sorted(range(1,128),key=int.bit_count):
        cost[A] = min(cost[A ^ (1 << p)] + 4 -
                      sum(r & (A ^ (1 << p)) == r for r in rho)
                      for p in range(7) if A >> p & 1)
    assert cost[-1] == 20
    tri = {sum(1 << j for j in t) for t in host['triangles']}
    assert len(tri) == 28
    ci = {cell:i for i,cell in enumerate(cells)}
    maps = []
    for images in product(points, repeat=3):
        def act(v):
            return tuple(sum(v[j]*images[j][i] for j in range(3)) % 2 for i in range(3))
        img = [act(v) for v in points]
        if len(set(img)) != 7 or (0,0,0) in img:
            continue
        pm = [points.index(v) for v in img]
        lm = []
        for l in range(7):
            moved = {pm[p] for p in range(7) if rho[l] >> p & 1}
            lm.append(next(i for i in range(7)
                           if moved == {p for p in range(7) if rho[i] >> p & 1}))
        perm = [ci[pm[p],lm[l]] for p,l in cells]
        assert all(helper[l] >> j & 1 == (helper[lm[l]] >> perm[j] & 1)
                   for l in range(7) for j in range(28))
        # Seven 4-bit tables per group element.
        maps.append([[sum(1 << perm[4*k+i] for i in range(4) if bits >> i & 1)
                      for bits in range(16)] for k in range(7)])
    assert len(maps) == 168
    return dict(row=row,col=col,rho=rho,helper=helper,full=full,
                closure=closure,seeds=seeds,cost=cost,triangles=tri,maps=maps,cells=cells)


def move(S, table):
    return sum(table[k][(S >> (4*k)) & 15] for k in range(7))


def orbits(family, maps):
    mapping = {}
    reps = []
    sizes = []
    for S in sorted(family,key=lambda x:(x.bit_count(),x)):
        if S in mapping:
            continue
        orbit = {move(S,t) for t in maps}
        assert orbit <= family
        i = len(reps)
        assert min(orbit) == S
        reps.append(S)
        sizes.append(len(orbit))
        for T in orbit:
            mapping[T] = i
    return reps,mapping,sizes


def build(args):
    start=time.monotonic()
    H=load_host(args.repo)
    seeds=set(H['seeds'])
    F=seeds | {S & T for S in seeds for T in seeds} | H['triangles']
    print('BASE_PAIRS_AND_TRIANGLES',len(F),'TRIANGLES',len(F & H['triangles']),flush=True)
    assert H['triangles'] <= F
    reps,orb,sizes=orbits(F,H['maps'])
    print('MEET_ORBITS',len(reps),flush=True)
    joins=set(F)
    # Orbit representatives suffice for one argument because F is invariant.
    for i,S in enumerate(reps):
        for T in F:
            joins.add(H['closure'](S|T))
            joins.add(S&T)
        if len(joins)>args.raw_cap:
            raise RuntimeError('raw join-family cap reached')
    print('RAW_AUXILIARY_REPRESENTATIVES',len(joins),flush=True)
    # Complete orbits symbolically, without materializing their union.
    # All representative-first-argument pair configurations are retained.
    canonical={}
    orbit_sizes={}
    for S in joins:
        images={move(S,table) for table in H['maps']}
        rep=min(images)
        canonical[S]=rep
        orbit_sizes[rep]=len(images)
    R=sorted(set(canonical.values()),key=lambda x:(x.bit_count(),x))
    index={S:i for i,S in enumerate(R)}
    O={S:index[rep] for S,rep in canonical.items()}
    Z=[orbit_sizes[S] for S in R]
    assert len(R)<=args.var_cap
    print('ONE_MEET_JOIN_STORED',len(joins),'IMPLICIT',sum(Z),'ORBITS',len(R),'SECONDS',round(time.monotonic()-start,3),flush=True)
    return H,F,reps,joins,R,O,Z


def inequalities(H,F,base_reps,R,O,cap):
    rows={}
    index={S:i for i,S in enumerate(R)}

    def put(terms,rhs,kind,sets):
        c=Counter()
        for i,a in terms:
            c[i]+=a
        key=tuple(sorted((i,a) for i,a in c.items() if a))
        if not key:
            assert rhs>=0
            return
        if key not in rows or rhs<rows[key][0]:
            rows[key]=(rhs,{'kind':kind,'sets':list(sets)})
            if len(rows)>cap:
                raise RuntimeError('inequality cap reached before solve')

    for i,S in enumerate(R):
        put([(i,-1)],0,'nonnegative',[S])
        # h(S) <= h(F_A)+|S\F_A|; every row cost is independently valid.
        A=min(range(128),key=lambda A:(H['cost'][A]+(S & ~H['seeds'][A]).bit_count(),A))
        rhs=H['cost'][A]+(S & ~H['seeds'][A]).bit_count()
        put([(i,1)],rhs,'row-budget-extension',[S,A])

    for S in base_reps:
        si=O[S]
        for T in sorted(F):
            ti=O[T]
            M=S&T
            J=H['closure'](S|T)
            mi,ji=O[M],O[J]
            put([(mi,1),(ji,1),(si,-1),(ti,-1)],0,'submodular',[S,T])
            # Exact set differences, not unit weights on abstract lattice covers.
            for P,pi,Q,qi in ((S,si,T,ti),(T,ti,S,si),
                              (S,si,M,mi),(M,mi,S,si),
                              (T,ti,M,mi),(M,mi,T,ti),
                              (S,si,J,ji),(T,ti,J,ji)):
                put([(pi,1),(qi,-1)],(P & ~Q).bit_count(),'increment',[P,Q])
            # Union closure has the entropy of the raw union.
            put([(ji,1),(si,-1)],(T & ~S).bit_count(),'closed-join-increment',[S,T])
            put([(ji,1),(ti,-1)],(S & ~T).bit_count(),'closed-join-increment',[T,S])

    result=[(key,*rows[key]) for key in sorted(rows)]
    # Known normalized 3-lane triangle code: 3h(S)=sum min(2,|S intersect T|).
    triangle3=[sum(min(2,(S&T).bit_count()) for T in H['triangles']) for S in R]
    assert triangle3[index[H['full']]]==56
    for row,rhs,name in result:
        assert sum(a*triangle3[i] for i,a in row)<=3*rhs, name
    digest=hashlib.sha256(json.dumps([(row,rhs) for row,rhs,_ in result],
                                    separators=(',',':')).encode()).hexdigest()
    print('INEQUALITIES',len(result),'LOWER_WITNESS_PASS','DIGEST',digest,flush=True)
    return result,digest


def verify_receipt(receipt,R,rows,digest,H):
    assert receipt['orbit_representatives']==R
    assert receipt['constraint_digest']==digest
    primal=[Fraction(v) for v in receipt['primal']]
    assert len(primal)==len(R)
    for row,rhs,name in rows:
        assert sum(a*primal[i] for i,a in row)<=rhs, ('primal',name)
    combined=[Fraction(0)]*len(R)
    value=Fraction(0)
    for item in receipt['dual']:
        j=item['index']
        y=Fraction(item['multiplier'])
        assert y>=0
        row,rhs,name=rows[j]
        assert item['witness']==name
        for i,a in row:
            combined[i]+=y*a
        value+=y*rhs
    top=R.index(H['full'])
    assert combined==[Fraction(i==top) for i in range(len(R))]
    assert value==primal[top]==Fraction(receipt['exact_residual_relaxation'])
    assert value+21==Fraction(receipt['exact_full_relaxation'])
    print('EXACT_PRIMAL_AND_DUAL_PASS',str(value+21),flush=True)


def solve(args,H,F,base_reps,J,R,O,Z,rows,digest):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix
    ii,jj,vv=[],[],[]
    for k,(row,_,_) in enumerate(rows):
        for j,v in row:
            ii.append(k);jj.append(j);vv.append(v)
    matrix=csr_matrix((vv,(ii,jj)),shape=(len(rows),len(R)),dtype=float)
    objective=np.zeros(len(R)); objective[R.index(H['full'])]=-1
    started=time.monotonic()
    lp=linprog(objective,A_ub=matrix,b_ub=[rhs for _,rhs,_ in rows],
               bounds=[(None,None)]*len(R),method='highs-ds',
               options={'time_limit':1800,'primal_feasibility_tolerance':1e-9,
                        'dual_feasibility_tolerance':1e-9})
    print('SOLVER',lp.status,lp.message,'SECONDS',time.monotonic()-started,
          'OBJECTIVE',None if lp.fun is None else 21-lp.fun,flush=True)
    if not lp.success:
        args.output.write_text(json.dumps(dict(status=int(lp.status),message=lp.message,
                                               scope='no exact result'),indent=2)+'\n')
        return
    rat=lambda x: Fraction(float(x)).limit_denominator(1000000)
    primal=[rat(v) for v in lp.x]
    dual=[rat(-v) for v in lp.ineqlin.marginals]
    receipt=dict(host='Fano residual28, independent loop contraction',
                 scope='Finite discovery relaxation; matching global certificate and explicit code establish the full Shannon value',
                 base_sets=len(F),base_orbits=len(base_reps),stored_auxiliary_masks=len(J),
                 implicit_closed_sets=sum(Z),variables=len(R),inequalities=len(rows),
                 constraint_digest=digest,orbit_representatives=R,
                 exact_residual_relaxation=str(primal[R.index(H['full'])]),
                 exact_full_relaxation=str(21+primal[R.index(H['full'])]),
                 primal=[str(x) for x in primal],
                 dual=[dict(index=i,multiplier=str(v),witness=rows[i][2])
                       for i,v in enumerate(dual) if v],
                 solver_seconds=time.monotonic()-started,
                 verification='Exact rational primal inequalities, dual signs and coefficient identity')
    verify_receipt(receipt,R,rows,digest,H)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print('DUAL_NONZERO',len(receipt['dual']),flush=True)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument('--raw-cap',type=int,default=100000)
    ap.add_argument('--var-cap',type=int,default=20000)
    ap.add_argument('--constraint-cap',type=int,default=250000)
    ap.add_argument('--solve',action='store_true')
    ap.add_argument('--verify',type=Path)
    ap.add_argument('--output',type=Path,default=Path('fano-reproduction.json'))
    args=ap.parse_args()
    H,F,reps,J,R,O,Z=build(args)
    rows,digest=inequalities(H,F,reps,R,O,args.constraint_cap)
    if args.verify:
        verify_receipt(json.loads(args.verify.read_text()),R,rows,digest,H)
        return
    if args.solve:
        solve(args,H,F,reps,J,R,O,Z,rows,digest)
        return
    result=dict(host='Fano residual28',loop_cells=21,seeds=len(set(H['seeds'])),
                base_sets=len(F),base_orbits=len(reps),auxiliary_family_sets=len(J),
                auxiliary_family_orbits=len(R),implicit_family_sets=sum(Z),
                triangles_in_base=len(F & H['triangles']),
                orbit_size_counts=dict(Counter(Z)),inequalities=len(rows),constraint_digest=digest,
                scope='family and constraints census only; no LP or bound')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)


if __name__=='__main__':
    main()
