#!/usr/bin/env python3
"""Independent Tseitin CNF for GF2 Fano minrank, plus a strict LRAT/RUP checker.

No Z3 dependency. LRAT replay accepts only positive-hint RUP additions;
any RAT step is rejected rather than trusted.
"""
import argparse,json,hashlib,gzip,io,zipfile
from contextlib import contextmanager
from pathlib import Path
from functools import reduce
from plane_controls import plane,verify_receipt

class CNF:
    def __init__(self):self.variables=0;self.clauses=[];self.gates=[]
    def var(self):self.variables+=1;return self.variables
    def clause(self,*xs):
        if any(x is True for x in xs):return
        xs=[x for x in xs if x is not False]
        if any(-x in xs for x in xs):return
        self.clauses.append(list(dict.fromkeys(xs)))
    def neg(self,x):return not x if isinstance(x,bool) else -x
    def both(self,x,y):
        if x is False or y is False:return False
        if x is True:return y
        if y is True:return x
        if x==y:return x
        if x==-y:return False
        z=self.var();self.clause(-z,x);self.clause(-z,y);self.clause(z,-x,-y)
        self.gates.append(('and',z,x,y));return z
    def xor(self,x,y):
        if x is False:return y
        if y is False:return x
        if x is True:return self.neg(y)
        if y is True:return self.neg(x)
        if x==y:return False
        if x==-y:return True
        z=self.var()
        self.clause(-x,-y,-z);self.clause(x,y,-z);self.clause(x,-y,z);self.clause(-x,y,z)
        self.gates.append(('xor',z,x,y));return z


def build(control,r):
    data=plane(2);A=control['acyclic_vertices'];ai={x:i for i,x in enumerate(A)};n=len(data['cells']);a=len(A)
    assert len(A)==len(set(A))==8
    order=control['point_order'];assert sorted(order)==list(range(data['d']))
    pos={v:i for i,v in enumerate(order)}
    assert all(pos[data['cells'][i][0]]<pos[data['cells'][j][0]]
               for i in A for j in A if data['allowed'][i][j])
    c=CNF()
    U=[[bool(ai[i]==t) if i in ai else c.var() for t in range(r)] for i in range(n)]
    V=[[False if t>=a and j in ai else c.var() for j in range(n)] for t in range(r)]
    for i in range(n):
        for j in range(n):
            if i!=j and data['allowed'][i][j]:continue
            out=reduce(c.xor,[c.both(U[i][t],V[t][j]) for t in range(r)])
            c.clause(out if i==j else c.neg(out))
    return c,U,V


def check_assignment(c,U,V,C,G):
    values={}
    def setval(x,v):
        if isinstance(x,bool):assert x==bool(v)
        elif x in values:assert values[x]==bool(v)
        else:values[x]=bool(v)
    for arr,num in [(U,C),(V,G)]:
        for row,nrow in zip(arr,num):
            for x,v in zip(row,nrow):setval(x,v)
    def val(x):
        if isinstance(x,bool):return x
        return values[abs(x)] if x>0 else not values[abs(x)]
    for kind,z,x,y in c.gates:
        values[z]=val(x) and val(y) if kind=='and' else val(x)!=val(y)
    assert len(values)==c.variables
    assert all(any(val(x) for x in clause) for clause in c.clauses)
    return len(c.clauses)


def check_packing_control(control):
    c,U,V=build(control,10);A=control['acyclic_vertices'];blocks=control['packing']
    ordered=[next(b for b in blocks if a in b) for a in A]
    assert len({tuple(b) for b in ordered})==8
    ordered += [b for b in blocks if b not in ordered]
    assert len(ordered)==10
    C=[[int(i in b) for b in ordered] for i in range(28)]
    G=[[int(j in b) for j in range(28)] for b in ordered]
    return check_assignment(c,U,V,C,G)


def cnf_text(c):
    return f'p cnf {c.variables} {len(c.clauses)}\n'+''.join(' '.join(map(str,v))+' 0\n' for v in c.clauses)

def write_cnf(path,c):
    text=cnf_text(c);path.write_text(text);return hashlib.sha256(text.encode()).hexdigest()

def digest_file(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1<<20),b''):h.update(chunk)
    return h.hexdigest()

@contextmanager
def open_text(path):
    if path.suffix == '.zip':
        with zipfile.ZipFile(path) as archive:
            assert archive.namelist() == ['fano-r9.lrat']
            with archive.open('fano-r9.lrat') as raw:
                with io.TextIOWrapper(raw) as stream:
                    yield stream
    else:
        with (gzip.open(path,'rt') if path.suffix=='.gz' else path.open()) as stream:
            yield stream


def read_cnf(path):
    clauses={};header=None
    for line in path.read_text().splitlines():
        if not line or line[0]=='c':continue
        if line[0]=='p':header=line.split();continue
        vals=list(map(int,line.split()));assert vals[-1]==0
        clauses[len(clauses)+1]=vals[:-1]
    assert header is not None and int(header[3])==len(clauses)
    return clauses


def check_lrat(cnf,proof):
    clauses=read_cnf(cnf);added=deleted=0;empty=False
    with open_text(proof) as stream:
      for line_number,line in enumerate(stream,1):
        tok=line.split()
        if not tok:continue
        cid=int(tok[0])
        if tok[1]=='d':
            assert tok[-1]=='0'
            for q in map(int,tok[2:-1]):clauses.pop(q,None);deleted+=1
            continue
        vals=list(map(int,tok[1:]));z=vals.index(0);clause=vals[:z];hints=vals[z+1:]
        assert hints and hints[-1]==0;hints=hints[:-1]
        assert all(h>0 for h in hints),f'RAT step rejected at line{line_number}'
        true=set(-x for x in clause)
        contradiction=any(-x in true for x in true)
        for h in hints:
            assert h in clauses,f'missing clause{h}'
            remaining=None
            for x in clauses[h]:
                assert x not in true,f'satisfied hint at line{line_number}'
                if -x not in true:
                    assert remaining is None,f'nonunit hint at line{line_number}'
                    remaining=x
            if remaining is None:contradiction=True;break
            true.add(remaining)
        assert contradiction,f'RUP failed at line{line_number}'
        assert cid not in clauses
        clauses[cid]=clause;added+=1
        if not clause:empty=True
        if added%100000==0:print(f'Checked {added} RUP additions',flush=True)
    assert empty,'no empty clause derived'
    return dict(added=added,deleted=deleted,empty_clause_derived=empty,
                cnf_sha256=digest_file(cnf),proof_sha256=digest_file(proof))


def main():
    ap=argparse.ArgumentParser();sub=ap.add_subparsers(dest='cmd',required=True)
    p=sub.add_parser('build');p.add_argument('--rank',type=int,required=True);p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p=sub.add_parser('check');p.add_argument('cnf',type=Path);p.add_argument('proof',type=Path)
    p=sub.add_parser('replay');p.add_argument('control',type=Path);p.add_argument('cnf',type=Path);p.add_argument('proof',type=Path)
    a=ap.parse_args()
    if a.cmd=='build':
        control=json.loads(a.control.read_text());control_clauses=check_packing_control(control);c,U,V=build(control,a.rank);digest=write_cnf(a.output,c)
        print(json.dumps(dict(variables=c.variables,clauses=len(c.clauses),sha256=digest,verified_rank10_control_clauses=control_clauses)))
    else:
        if a.cmd=='replay':
            control=json.loads(a.control.read_text());verify_receipt(control);check_packing_control(control)
            c,_,_=build(control,9);assert a.cnf.read_text()==cnf_text(c), 'CNF does not match the stated graph and rank model'
        print(json.dumps(check_lrat(a.cnf,a.proof),indent=2))
if __name__=='__main__':main()
