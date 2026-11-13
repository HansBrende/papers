#!/usr/bin/env python3
"""Exact projective-plane relation and code-certificate controls.

Construction/certificate replay uses the standard library. The optional
packing search uses SciPy MILP only to find a candidate, verified exactly.
No solver silence or floating objective bound is treated as a theorem.
"""
from itertools import combinations, product
from pathlib import Path
import argparse, json


def norm(v, p):
    a = next(x for x in v if x % p)
    inv = pow(a, -1, p)
    return tuple(x*inv % p for x in v)


def cross(a,b,p):
    return norm(((a[1]*b[2]-a[2]*b[1])%p,
                 (a[2]*b[0]-a[0]*b[2])%p,
                 (a[0]*b[1]-a[1]*b[0])%p),p)


def plane(p):
    pts = sorted({norm(v,p) for v in product(range(p), repeat=3) if any(v)})
    ix = {v:i for i,v in enumerate(pts)}
    d = len(pts)
    incidence = [[sum(a*b for a,b in zip(x,l))%p == 0 for l in pts] for x in pts]
    loops = [(a,l) for a in range(d) for l in range(d) if incidence[a][l]]
    cells = [(a,l) for a in range(d) for l in range(d) if not incidence[a][l]]
    ci = {v:i for i,v in enumerate(cells)}
    allowed = [[incidence[b][l] for b,m in cells] for a,l in cells]
    pairs = [(i,j) for i,j in combinations(range(len(cells)),2) if allowed[i][j] and allowed[j][i]]
    triangles=[]
    for a,b,c in combinations(range(d),3):
        la,lb,lc=ix[cross(pts[b],pts[c],p)],ix[cross(pts[a],pts[c],p)],ix[cross(pts[a],pts[b],p)]
        if incidence[a][la]: continue
        tri=tuple(sorted((ci[a,la],ci[b,lb],ci[c,lc])))
        assert all(allowed[i][j] for i in tri for j in tri if i!=j)
        triangles.append(tri)
    assert len(set(triangles))==len(triangles)
    return dict(order=p,d=d,points=pts,cells=cells,loops=loops,allowed=allowed,pairs=pairs,triangles=triangles)


def rank_mod(rows, p):
    a=[row[:] for row in rows]
    r=0
    for j in range(len(a[0]) if a else 0):
        i=next((i for i in range(r,len(a)) if a[i][j]%p),None)
        if i is None:continue
        a[r],a[i]=a[i],a[r]
        inv=pow(a[r][j]%p,-1,p)
        a[r]=[x*inv%p for x in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][j]%p:
                c=a[i][j]%p
                a[i]=[(x-c*y)%p for x,y in zip(a[i],a[r])]
        r+=1
    return r


def verify_fitting(data, matrix, field):
    n=len(data['cells'])
    assert len(matrix)==n and all(len(row)==n for row in matrix)
    assert all(matrix[i][i]%field==1 for i in range(n))
    assert all(matrix[i][j]%field==0 for i in range(n) for j in range(n)
               if i!=j and not data['allowed'][i][j])
    return rank_mod(matrix,field)


def packing_matrix(n, packing):
    matrix=[[int(i==j) for j in range(n)] for i in range(n)]
    seen=set()
    for block in packing:
        assert not seen.intersection(block)
        seen.update(block)
        for i in block:
            matrix[i]=[int(j in block) for j in range(n)]
    return matrix


def verify_packing(data, packing):
    n=len(data['cells'])
    for b in packing:
        assert len(b) in (2,3)
        assert all(data['allowed'][i][j] for i in b for j in b if i!=j)
    matrix=packing_matrix(n,packing)
    ranks=[verify_fitting(data,matrix,p) for p in (2,3)]
    assert ranks[0]==ranks[1]==n-sum(len(b)-1 for b in packing)
    return matrix,ranks[0]


def packing_search(data, seconds):
    import numpy as np
    from scipy.optimize import milp, Bounds, LinearConstraint
    from scipy.sparse import lil_matrix
    blocks=data['triangles']+data['pairs']
    n=len(data['cells'])
    a=lil_matrix((n,len(blocks)),dtype=float)
    for j,b in enumerate(blocks):
        for i in b:a[i,j]=1
    result=milp(-np.array([len(b)-1 for b in blocks],float),integrality=np.ones(len(blocks)),
                bounds=Bounds(0,1),constraints=LinearConstraint(a.tocsr(),0,1),
                options={'time_limit':seconds})
    if result.x is None:return [],dict(status=int(result.status),message=result.message)
    packing=[list(blocks[j]) for j,x in enumerate(result.x) if x>.5]
    return packing,dict(status=int(result.status),message=result.message)


def best_order_dag(data):
    """Exact enumeration of point orders (Fano only), retaining nonloops
    whose point precedes every point in their hyperplane. Such cells induce
    an acyclic graph: every helper's point is strictly later.
    """
    from itertools import permutations
    p,d=data['order'],data['d'];pts=data['points'];cells=data['cells']
    lines=[[a for a in range(d) if sum(x*y for x,y in zip(pts[a],l))%p==0] for l in pts]
    best=[];best_order=None
    for order in permutations(range(d)):
        pos={x:i for i,x in enumerate(order)}
        alive=[i for i,(a,l) in enumerate(cells) if all(pos[a]<pos[b] for b in lines[l])]
        if len(alive)>len(best):best,best_order=alive,order
    idx={v:i for i,v in enumerate(sorted(best,key=lambda v:best_order.index(cells[v][0])))}
    assert all(idx[v]<idx[u] for v in best for u in best if data['allowed'][v][u])
    return best,list(best_order)


def verify_receipt(receipt):
    data=plane(receipt['order'])
    for key in ['points','cells','loops']:
        assert receipt[key]==[list(x) for x in data[key]]
    matrix,rank=verify_packing(data,receipt['packing'])
    assert matrix==receipt['residual_fitting_matrix']
    assert rank==receipt['exact_residual_rank_GF2']==receipt['exact_residual_rank_GF3']
    assert receipt['total_code_dimension']==data['d']**2-rank
    if 'acyclic_vertices' in receipt:
        A=receipt['acyclic_vertices'];order=receipt['point_order']
        assert len(A)==len(set(A)) and all(0<=i<len(data['cells']) for i in A)
        assert sorted(order)==list(range(data['d']))
        pos={v:i for i,v in enumerate(order)}
        assert all(pos[data['cells'][i][0]]<pos[data['cells'][j][0]]
                   for i in A for j in A if data['allowed'][i][j])
        assert receipt['code_dimension_upper']==data['d']**2-len(A)
    return dict(order=data['order'],dimension=data['d'],exact_rank_GF2_GF3=rank,
                code_dimension=receipt['total_code_dimension'],
                order_upper=receipt.get('code_dimension_upper'))


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--order',type=int,choices=[2,3]);ap.add_argument('--verify',type=Path)
    ap.add_argument('--seconds',type=float,default=10);ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    if args.verify:
        print(json.dumps(verify_receipt(json.loads(args.verify.read_text())),indent=2));return
    if args.order is None or args.output is None:ap.error('--order and --output are required for search')
    data=plane(args.order)
    packing,status=packing_search(data,args.seconds)
    matrix,r=verify_packing(data,packing)
    n=len(data['cells']);out=dict(order=args.order,dimension=data['d'],points=data['points'],cells=data['cells'],
        loops=data['loops'],packing=packing,packing_solver=status,residual_fitting_matrix=matrix,
        exact_residual_rank_GF2=r,exact_residual_rank_GF3=r,total_code_dimension=data['d']**2-r,
        triangle_count=len(data['triangles']),pair_count=len(data['pairs']))
    if args.order==2:
        dag,order=best_order_dag(data);out.update(acyclic_vertices=dag,point_order=order,code_dimension_upper=data['d']**2-len(dag))
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['points','cells','loops','packing','residual_fitting_matrix']},indent=2))

if __name__=='__main__':main()
