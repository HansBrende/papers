"""Exact SL2(F_p) exceptional-set and ordinary-degree audit; no optimization.

From the repository root:
  python3 lean-backlog/tools/sl2-symmetry/counts.py --until-quarter

The default primes are 5, 7, 11, 13. Without --until-quarter, only m=1,2
are checked. With it, stop at the first failed quarter gate, with m<=9.
The default output is receipt.json beside this script; --output overrides it.

E_m is counted twice: scanning all g,x, and by independent square-root
enumeration over unordered x,z. Receipts contain every positive witness.
Character degrees are the ordinary SL2 character-table formula, checked
against primary sources in the accompanying note; they are not modular
irreducible degrees in bad characteristic.
"""
from collections import Counter, defaultdict, deque
from fractions import Fraction
from itertools import combinations_with_replacement
from pathlib import Path
import argparse
import json


def ratio(a,b):
    r=Fraction(a,b)
    return {'fraction':str(r), 'decimal':float(r)}


def compute(p, until_quarter=False):
    I=(1,0,0,1)
    def mul(x,y):
        a,b,c,d=x; e,f,g,h=y
        return ((a*e+b*g)%p,(a*f+b*h)%p,(c*e+d*g)%p,(c*f+d*h)%p)
    def inv(x):
        a,b,c,d=x
        return (d,(-b)%p,(-c)%p,a)
    # Solve for the bottom-right entry rather than scan p^4 matrices.
    group=[]
    for a in range(p):
        for b in range(p):
            for c in range(p):
                if a:
                    group.append((a,b,c,((1+b*c)*pow(a,-1,p))%p))
                elif (-b*c)%p==1:
                    group.extend((a,b,c,d) for d in range(p))
    group.sort()
    d=len(group)
    assert d==p*(p*p-1) and len(set(group))==d
    assert all((a*e-b*c)%p==1 for a,b,c,e in group)
    assert all(mul(g,inv(g))==I==mul(inv(g),g) for g in group)
    T={(1,0,0,1),(1,2%p,0,1),(1,0,2%p,1)}
    gens=sorted((T|{inv(t) for t in T})-{I})
    reached={I}; queue=deque([I])
    while queue:
        g=queue.popleft()
        for t in gens:
            h=mul(g,t)
            if h not in reached:reached.add(h);queue.append(h)
    assert reached==set(group)
    unseen=set(group);class_sizes=[]
    while unseen:
        seed=min(unseen);cls={seed};queue=deque([seed]);unseen.remove(seed)
        while queue:
            g=queue.popleft()
            for t in gens:
                h=mul(mul(t,g),inv(t))
                if h not in cls:
                    cls.add(h);queue.append(h);unseen.remove(h)
        class_sizes.append(len(cls))
    assert len(class_sizes)==p+4
    D={mul(inv(x),y) for x in T for y in T}
    roots=defaultdict(list)
    for g in group:roots[mul(g,g)].append(g)
    sets=[]; X=set(T); previous_E=set()
    for m in range(1,10):
        if m>1:X={mul(x,u) for x in X for u in D}
        xs=sorted(X); ix={x:i for i,x in enumerate(xs)}
        invX={inv(x) for x in xs}
        direct={}
        for g in group:
            for x in xs:
                zinv=mul(mul(g,x),g)
                if zinv in invX:
                    z=inv(zinv)
                    assert mul(mul(mul(g,x),g),z)==I
                    direct[g]=(ix[x],ix[z])
                    break
        square={}
        for x,z in combinations_with_replacement(xs,2):
            target=mul(inv(z),x)
            for h in roots[target]:
                g=mul(h,inv(x))
                assert mul(mul(mul(g,x),g),z)==I
                square[g]=(ix[x],ix[z])
        assert set(direct)==set(square)
        assert previous_E<=set(direct)
        previous_E=set(direct)
        sets.append({'m':m,'X':xs,'X_size':len(xs),'E_size':len(direct),
                     'E_fraction':ratio(len(direct),d),
                     'E_less_than_quarter':4*len(direct)<d,
                     'rate_ceiling':ratio(d+len(direct),2*d),
                     'witnesses':[{'g':g,'x_index':pair[0],'z_index':pair[1]}
                                  for g,pair in sorted(direct.items())]})
        if m>=2 and (not until_quarter or 4*len(direct)>=d):
            break
    else:
        raise RuntimeError('Quarter gate not reached before the explicit audit cap')
    # Ordinary degrees from the complete odd-q character table.
    deg=[1,p]+[p+1]*((p-3)//2)+[p-1]*((p-1)//2)+[(p+1)//2]*2+[(p-1)//2]*2
    assert len(deg)==p+4
    assert sum(n*n for n in deg)==d
    moments={k:sum(n**k for n in deg) for k in(2,3,4)}
    assert 2*moments[3]==2*p**4-p**3-9*p
    assert 4*moments[4]==4*p**5-3*p**4+8*p**3-42*p**2-12*p-3
    # Borel: p-1 linear degrees, four of degree(p-1)/2.
    bdeg=[1]*(p-1)+[(p-1)//2]*4
    bd=p*(p-1)
    assert sum(n*n for n in bdeg)==bd
    return {'p':p,'d':d,'T':sorted(T),'difference_set_size':len(D),
            'conjugacy_class_sizes':sorted(class_sizes),
            'helper_generators_generate_full_group':True,
            'E_sets':sets,'R2':max(map(len,roots.values())),
            'largest_passing_m':max((x['m'] for x in sets if x['E_less_than_quarter']),default=0),
            'largest_passing_m_certified':not sets[-1]['E_less_than_quarter'],
            'ordinary_degrees':dict(sorted(Counter(deg).items())),
            'ordinary_moments':moments,
            'moment_ratios':{k:ratio(v,d*d) for k,v in moments.items()},
            'symmetry_rate_ceilings':{k:ratio(d*d+moments[k],2*d*d) for k in(3,4)},
            'pairing_rate':ratio(d+1,2*d),
            'borel_order':bd,'borel_degrees':dict(sorted(Counter(bdeg).items())),
            'borel_moment_ratios':{k:ratio(sum(n**k for n in bdeg),bd*bd) for k in(3,4)}}


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('primes',nargs='*',type=int,default=[5,7,11,13])
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('receipt.json'))
    ap.add_argument('--until-quarter',action='store_true')
    args=ap.parse_args()
    if any(p < 5 or any(p % t == 0 for t in range(2, int(p**0.5)+1))
           for p in args.primes):
        ap.error('each input must be a prime at least 5')
    out=[]
    for p in args.primes:
        r=compute(p,args.until_quarter);out.append(r)
        print({'p':p,'d':r['d'],'E1':r['E_sets'][0]['E_size'],
               'E2':r['E_sets'][1]['E_size'],'X2':r['E_sets'][1]['X_size'],
               'quarter_gates':[x['E_less_than_quarter'] for x in r['E_sets']],
               'all_E_counts':[x['E_size'] for x in r['E_sets']],
               'largest_passing_m':r['largest_passing_m'] if r['largest_passing_m_certified'] else None,
               'sum_n4_over_d2':r['moment_ratios'][4]['decimal'],
               'sum_n3_over_d2':r['moment_ratios'][3]['decimal']},flush=True)
    args.output.write_text('[\n' + ',\n'.join(
        json.dumps(row, separators=(',', ':')) for row in out) + '\n]\n')
