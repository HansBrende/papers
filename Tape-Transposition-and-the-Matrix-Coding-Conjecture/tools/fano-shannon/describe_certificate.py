#!/usr/bin/env python3
"""Regenerate the geometric dictionary of the existing Fano certificate.

Run from any directory with Python 3, without -O. Standard library only.
Imports and replays the independent certificate checker, then verifies every
geometric recipe. Writes orbit-dictionary.json and orbit-dictionary.md beside
this script. No solver or new inequality search is used.
"""
from contextlib import redirect_stdout
from fractions import Fraction
from itertools import combinations
import importlib.util
import io,json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('fano_verify',ROOT/'verify_certificate.py')
M=importlib.util.module_from_spec(spec)
with redirect_stdout(io.StringIO()):spec.loader.exec_module(M)
used=sorted({S for r in M.semantic_rows for S,_ in r['canonical_coefficients']},key=lambda S:(S.bit_count(),S))
assert len(used)==34
recipes={}
raw={}
def point_kind(A):
    pts={i for i in range(7) if A>>i&1}
    if not pts:return 'empty'
    if len(pts)==1:return 'point'
    if len(pts)==2:return 'point pair'
    if len(pts)==3:return 'line' if pts in M.lines else 'noncollinear triple'
    if len(pts)==4:return 'quadrangle' if set(range(7))-pts in M.lines else 'line plus point'
    if len(pts)==5:return 'five points'
    if len(pts)==6:return 'six points'
    return 'all points'

def complexity(A):
    # Prefer named geometric primitives, then few points in explicit witnesses.
    return (0 if point_kind(A) in ('empty','point','line','all points') else 1,A.bit_count(),A)

def put(mask,expr,score):
    if mask not in raw or score<raw[mask][0]:raw[mask]=(score,expr)

for A,S in M.seed.items():
    put(S,dict(op='F',A=A,kind=point_kind(A)),(1,)+complexity(A))
for A in range(128):
    for B in range(A+1,128):
        put(M.seed[A]&M.seed[B],dict(op='meet',A=A,B=B,types=[point_kind(A),point_kind(B)]),
            (2,complexity(A)[0]+complexity(B)[0],A.bit_count()+B.bit_count(),A,B))
for T in M.triangles:
    ps=sorted({M.cells[i][0] for i in range(28) if T>>i&1})
    put(T,dict(op='triangle',points=ps),(1,0,3,sum(1<<p for p in ps)))

for S,(score,expr) in raw.items():
    rep=M.canonical(S)
    if rep in used and (rep not in recipes or score<recipes[rep][0]):
        recipes[rep]=(score,dict(expr=expr,witness_mask=S))

base_recipe_count=len(recipes)
for rep in used:
    if rep in recipes:continue
    # Remaining variables can be auxiliary intersections or closed joins.
    for term in M.certificate['terms']:
        if term['kind'] not in ('submodular','closed-join-increment'):continue
        S,T=term['sets']
        srep,trep=M.canonical(S),M.canonical(T)
        for op,target in [('join',M.closure(S|T)),('meet_aux',S&T)]:
            if M.canonical(target)!=rep:continue
            score=(3,(S|T).bit_count(),S,T)
            expr=dict(op=op,left_mask=S,right_mask=T,left_rep=srep,right_rep=trep,
                      left_expr=raw.get(S,([],None))[1],right_expr=raw.get(T,([],None))[1])
            if rep not in recipes or score<recipes[rep][0]:recipes[rep]=(score,dict(expr=expr,witness_mask=target))
    assert rep in recipes,rep

result=[]
def evaluate(expr):
    """Check a recipe against the actual labelled incidence geometry."""
    if expr['op']=='F':return M.seed[expr['A']]
    if expr['op']=='meet':return M.seed[expr['A']] & M.seed[expr['B']]
    if expr['op']=='triangle':
        P=set(expr['points'])
        return sum(1<<M.cell_index[p,next(j for j,L in enumerate(M.lines) if P-{p}<=L)]
                   for p in P)
    S,T=evaluate(expr['left_expr']),evaluate(expr['right_expr'])
    assert S==expr['left_mask'] and T==expr['right_mask']
    return M.closure(S|T) if expr['op']=='join' else S&T

for label,S in enumerate(used):
    pts=[(i,[j for p,j in M.cells if p==i and S>>M.cell_index[p,j]&1]) for i in range(7)]
    pts=[(i,js) for i,js in pts if js]
    complete_rows=[i for i,R in enumerate(M.rows) if R&S==R]
    complete_columns=[j for j,C in enumerate(M.cols) if C&S==C]
    record=dict(label=f'O{label}',mask=S,size=S.bit_count(),
                triangle_rank=str(Fraction(M.triangle_rank3(S),3)),
                whole_rows=complete_rows,whole_columns=complete_columns,
                row_cells=pts,recipe=recipes[S][1])
    witness=evaluate(record['recipe']['expr'])
    assert witness==record['recipe']['witness_mask'] and M.canonical(witness)==S
    result.append(record)

def letters(A):
    return ''.join('abcdefg'[p] for p in range(7) if A>>p&1) or r'\varnothing'

def formula(expr):
    op=expr['op']
    if op=='F':return 'F_{'+letters(expr['A'])+'}'
    if op=='meet':return 'F_{'+letters(expr['A'])+r'}\cap F_{'+letters(expr['B'])+'}'
    if op=='triangle':return 'T_{'+''.join('abcdefg'[p] for p in expr['points'])+'}'
    S,T=formula(expr['left_expr']),formula(expr['right_expr'])
    if op=='join':return r'\operatorname{cl}[('+S+r')\cup('+T+')]'
    return '('+S+r')\cap('+T+')'

def description(expr):
    if expr['op']=='F':return 'closure of '+expr['kind']+' rows'
    if expr['op']=='meet':return 'intersection: '+'; '.join(expr['types'])
    if expr['op']=='triangle':return 'mutual triangle'
    return 'closed union of two intersections' if expr['op']=='join' else 'intersection of two intersections'

doc=[
    '# The 34 set orbits in the Fano certificate',
    '',
    'Generated by `describe_certificate.py`; every formula is checked against',
    'the labelled plane and the existing exact certificate. No optimization.',
    '',
    'Label the points a=001, b=010, c=011, d=100, e=101, f=110, g=111.',
    'The lines are bdf, ade, cdg, abc, beg, afg, cef. Work on the 28',
    'nonincident cells, after conditioning on the 21 incident cells.',
    'For a set A of points, $F_A$ means the recovery closure of its complete',
    'residual rows. Subscripts such as ab mean the point set {a,b}.',
    '',
    '**The formula is a representative of the orbit**, possibly a different',
    'labelled set from its canonical mask. One common collineation transports',
    'the entire formula; independently moving its operands would change it.',
    'The JSON gives both the witness mask and the canonical mask.',
    r'The value $h_\triangle$ is the attained entropy in the triangle lane code,',
    '**not** an unconditional lower bound for other codes.',
    '',
    r'| Orbit | Canonical mask | Cells | Geometric type | Representative | $h_\triangle$ |',
    '|---|---:|---:|---|---|---:|',
]
for r in result:
    e=r['recipe']['expr']
    doc.append(f"| {r['label']} | {r['mask']} | {r['size']} | {description(e)} | ${formula(e)}$ | {r['triangle_rank']} |")
doc += [
    '',
    'The table gives 31 orbits directly as row closures or intersections of',
    'two row closures. O7 and O21 use one further intersection; O22 uses',
    'one closed union. O10 is the two-line intersection described in the',
    'proof discussion: four cells in the intersection-point row and four',
    'cross cells. O26 is a line closure, O27 is a line closure plus one',
    'cell, and O32 is the closure of the union of two lines.',
    '**No three-cell triangle orbit occurs in the positive dual.** Triangles',
    'supply the matching lower code and its values on these larger sets.',
    '',
    '## The exact weighted inequalities',
    '',
    'Write $h_i$ for the automorphism-average rank on orbit Oi. Coefficients',
    'below are integers; the weighted sum is $264h_{33}\\le4928$. The first',
    'row is normalization ($h_0=0$); all other rows are tight in the triangle',
    'code. S = submodularity with recovery closure; I = coordinate increment;',
    'J = closed-join increment; B = row purchase; N = nonnegativity.',
    'The actual operands, including their relative incidence, are in',
    '`certificate.json`; orbit names alone do not establish a row\'s validity.',
    '',
    '| Term | Weight | Kind | Inequality |',
    '|---|---:|---|---|',
]
labels={S:i for i,S in enumerate(used)}
kinds={'submodular':'S','increment':'I','closed-join-increment':'J',
       'row-closure-cap':'B','nonnegative':'N'}
def hterm(i,c):return ('' if c==1 else str(c))+f'h_{{{i}}}'
for i,row in enumerate(M.semantic_rows,1):
    left=[]; right=[]
    for S,c in row['canonical_coefficients']:
        (left if c>0 else right).append(hterm(labels[S],abs(c)))
    if row['rhs']:right.append(str(row['rhs']))
    lhs=' + '.join(left) or '0'
    rhs=' + '.join(right) or '0'
    doc.append(f"| {i} | {row['weight264']} | {kinds[row['kind']]} | ${lhs}\\le {rhs}$ |")
doc += ['', 'Proof status: written, with exact Python checks; not Lean-verified.', '']
assert base_recipe_count==31 and len(result)==34
assert not any(r['size']==3 for r in result)
(ROOT/'orbit-dictionary.json').write_text(json.dumps(result,indent=2)+'\n')
(ROOT/'orbit-dictionary.md').write_text('\n'.join(doc))
print('PASS: 34 checked orbit descriptions, 31 base recipes, 33 inequalities.')
