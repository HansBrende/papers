#!/usr/bin/env python3
"""One bounded grid adaptation of the prior Fano Shannon relaxation.

Default: build and audit the finite family, without solving. --solve runs one
SciPy/HiGHS LP (300-second limit), then verifies exact primal and dual data.
--verify search-receipt.json replays the full recorded relaxation using only
Python's standard library. For the much smaller mathematical proof use
verify_certificate.py, which does not build this LP or import this file.

Run from any working directory; see README.md. Never use Python -O.
Adapted from the adjacent Fano discovery tool. The fixed grid family and
known-code witness differ; the mathematical certificate has its own checker.
Builds use a POSIX 300-second alarm in addition to the finite size caps.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path
import time


def load_host(repo):
    from itertools import permutations
    points=list(product(range(3),repeat=2))
    lines=[{3*i+j for j in range(3)} for i in range(3)] + [
           {3*i+j for i in range(3)} for j in range(3)]
    cells=[(p,l) for p in range(9) for l in range(6) if p not in lines[l]]
    ci={cell:i for i,cell in enumerate(cells)}
    row=[sum(1<<k for k,(p,l) in enumerate(cells) if p==i) for i in range(9)]
    col=[sum(1<<k for k,(p,l) in enumerate(cells) if l==j) for j in range(6)]
    rho=[sum(1<<p for p in L) for L in lines]
    helper=[sum(row[p] for p in L) for L in lines]
    full=(1<<36)-1
    assert all(x.bit_count()==4 for x in row)
    assert all(x.bit_count()==6 for x in col)
    assert all(x.bit_count()==12 for x in helper)
    completed=[sum(col[l] for l in range(6) if rho[l]&A==rho[l]) for A in range(512)]
    def closure(S):
        while True:
            A=sum(1<<p for p in range(9) if S&row[p]==row[p])
            new=S|completed[A]
            if new==S:return S
            S=new
    seeds=[closure(sum(row[p] for p in range(9) if A>>p&1)) for A in range(512)]
    cost=[0]*512
    for A in sorted(range(1,512),key=int.bit_count):
        cost[A]=min(cost[A^(1<<p)]+4-sum(r&(A^(1<<p))==r for r in rho)
                    for p in range(9) if A>>p&1)
    assert cost[-1]==23
    # Exact directed-host automorphisms: independent axis permutations and swap.
    perms=set()
    for f in permutations(range(3)):
        for g in permutations(range(3)):
            for swap in (False,True):
                pm=[3*(g[j] if swap else f[i])+(f[i] if swap else g[j]) for i,j in points]
                lm=[lines.index({pm[p] for p in L}) for L in lines]
                cp=tuple(ci[pm[p],lm[l]] for p,l in cells)
                assert all(bool(helper[l]>>k&1)==bool(helper[lm[l]]>>cp[k]&1)
                           for l in range(6) for k in range(36))
                perms.add(cp)
    assert len(perms)==72
    maps=[[[sum(1<<perm[4*k+i] for i in range(4) if bits>>i&1)
             for bits in range(16)] for k in range(9)] for perm in sorted(perms)]
    # Six independent private symbols plus one shared difference per sector.
    sectors=[]
    for a,b in ((0,1),(0,2),(1,2)):
        pairs=[(ci[3*a+j,b],ci[3*b+j,a]) for j in range(3)]
        pairs += [(ci[3*i+a,3+b],ci[3*i+b,3+a]) for i in range(3)]
        sectors.append(pairs)
    structures=set()
    for perm in perms:
        structs=tuple(sorted(tuple(sorted((1<<perm[u])|(1<<perm[v]) for u,v in pairs))
                             for pairs in sectors))
        structures.add(structs)
    structures=sorted(structures)
    # Every translate has equal multiplicity, checked rather than assumed.
    counts=Counter(tuple(sorted(tuple(sorted((1<<perm[u])|(1<<perm[v]) for u,v in pairs))
                                for pairs in sectors)) for perm in perms)
    assert len(set(counts.values()))==1
    def witness_scaled(S):
        return sum(sum(sum(bool(S&P) for P in pairs)+int(any(S&P==P for P in pairs))
                       for pairs in structure) for structure in structures)
    assert witness_scaled(full)==21*len(structures)
    def rank(S, structure):
        return sum(sum(bool(S&P) for P in pairs)+int(any(S&P==P for P in pairs))
                   for pairs in structure)
    for structure in structures:
        allpairs=[P for pairs in structure for P in pairs]
        assert len(allpairs)==18 and sum(allpairs)==full
        assert all(P.bit_count()==2 for P in allpairs)
        assert rank(full,structure)==21
        assert all(rank(1<<i,structure)==1 for i in range(36))
        assert all(rank(H|C,structure)==rank(H,structure) for H,C in zip(helper,col))
    return dict(row=row,col=col,rho=rho,helper=helper,full=full,
                closure=closure,seeds=seeds,cost=cost,triangles=set(),maps=maps,cells=cells,
                witness_scaled=witness_scaled,witness_scale=len(structures))


def move(S, table):
    return sum(table[k][(S >> (4*k)) & 15] for k in range(len(table)))


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
    import signal
    signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(TimeoutError('build budget300 seconds')))
    signal.alarm(300)
    H=load_host(args.repo)
    if args.family=='all-rows':
        seeds=set(H['seeds'])
    else:
        subsets={0,511}|{1<<p for p in range(9)}
        for choice in range(64):
            A=0
            for j,r in enumerate(H['rho']):
                if choice>>j&1:A|=r
            subsets.add(A)
        seeds={H['seeds'][A] for A in subsets}
    F=seeds | {S & T for S in seeds for T in seeds} | H['triangles']
    if len(F)>args.raw_cap:raise RuntimeError('base-family cap reached')
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
        A=min(range(len(H['seeds'])),key=lambda A:(H['cost'][A]+(S & ~H['seeds'][A]).bit_count(),A))
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
    # Exact average of the21-source grid code over its distinct translates.
    scale=H['witness_scale']
    triangle3=[H['witness_scaled'](S) for S in R]
    assert triangle3[index[H['full']]]==21*scale
    for row,rhs,name in result:
        assert sum(a*triangle3[i] for i,a in row)<=scale*rhs, name
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
    assert value+18==Fraction(receipt['exact_full_relaxation'])
    print('EXACT_PRIMAL_AND_DUAL_PASS',str(value+18),flush=True)


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
               options={'time_limit':300,'primal_feasibility_tolerance':1e-9,
                        'dual_feasibility_tolerance':1e-9})
    print('SOLVER',lp.status,lp.message,'SECONDS',time.monotonic()-started,
          'OBJECTIVE',None if lp.fun is None else 18-lp.fun,flush=True)
    if not lp.success:
        args.output.write_text(json.dumps(dict(status=int(lp.status),message=lp.message,
                                               scope='no exact result'),indent=2)+'\n')
        return
    rat=lambda x: Fraction(float(x)).limit_denominator(1000000)
    primal=[rat(v) for v in lp.x]
    dual=[rat(-v) for v in lp.ineqlin.marginals]
    receipt=dict(host='3x3 grid residual36, 9 point rows and 6 line columns, 18 loops',
                 scope='Truncated relaxation; an upper below order23 is global only after exact semantic dual replay; full equality needs a matching code',
                 selected_family=args.family,base_sets=len(F),base_orbits=len(base_reps),stored_auxiliary_masks=len(J),
                 implicit_closed_sets=sum(Z),variables=len(R),inequalities=len(rows),
                 constraint_digest=digest,orbit_representatives=R,
                 exact_residual_relaxation=str(primal[R.index(H['full'])]),
                 exact_full_relaxation=str(18+primal[R.index(H['full'])]),
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
    ap.add_argument('--family',choices=('all-rows','line-unions'),default='line-unions')
    ap.add_argument('--solve',action='store_true')
    ap.add_argument('--verify',type=Path)
    ap.add_argument('--output',type=Path,default=Path('grid-reproduction.json'))
    args=ap.parse_args()
    if not __debug__:raise RuntimeError('Assertions must be enabled; do not use -O')
    H,F,reps,J,R,O,Z=build(args)
    rows,digest=inequalities(H,F,reps,R,O,args.constraint_cap)
    import signal
    signal.alarm(0)
    if args.verify:
        verify_receipt(json.loads(args.verify.read_text()),R,rows,digest,H)
        return
    if args.solve:
        solve(args,H,F,reps,J,R,O,Z,rows,digest)
        return
    result=dict(host='grid residual36',loop_cells=18,seeds=len(set(H['seeds'])),
                base_sets=len(F),base_orbits=len(reps),auxiliary_family_sets=len(J),
                auxiliary_family_orbits=len(R),implicit_family_sets=sum(Z),
                triangles_in_base=len(F & H['triangles']),
                orbit_size_counts=dict(Counter(Z)),inequalities=len(rows),constraint_digest=digest,
                scope='family and constraints census only; no LP or bound')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)


if __name__=='__main__':
    main()
