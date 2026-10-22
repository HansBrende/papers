#!/usr/bin/env python3
"""Read-only consolidation audit; never launches Lean/Lake or writes repository files.
Run --check-current only after a selected consolidation batch is applied.
The source contract is exact concatenation of the member texts after deleting
import lines, separated only by whitespace. Public names still require Lean's
ordinary build and the existing exact-name axiom audit.
"""
from pathlib import Path
import argparse, hashlib, json, re
P=Path('.')
A=Path('external/research-workspace/research/10-linear-decision/archive/r1912-build-speed')
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--project-root',type=Path,default=P,help='Scratch project for dry-run checking, or active project read-only')
p.add_argument('--plan',type=Path,default=Path('external/temporary/r1912-group-plan.json'))
p.add_argument('--max-phase',type=int,default=0)
p.add_argument('--groups',nargs='*',help='Select exact group names instead of phases')
p.add_argument('--check-current',action='store_true')
p.add_argument('--axioms-log',type=Path)
p.add_argument('--output',type=Path,default=Path('external/temporary/r1912-preservation-check.json'))
a=p.parse_args(); P=a.project_root; baseline=json.loads((A/'baseline-sources.json').read_text()); receipt=json.loads((A/'before-receipt.json').read_text()); plan=json.loads(a.plan.read_text())
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
for rel,text in baseline.items(): assert sha(text)==receipt['source_sha256'][rel],('baseline hash',rel)
assert len(baseline)==1158
IM=re.compile(r'^import ([^\n]+)\n',re.M)
def imports(s):
 result=[]
 for raw in IM.findall(s):
  # Existing sources use one plain module name per import. Refuse silently
  # approximating public/private/meta import syntax or inline comments.
  assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',raw.strip()),('nonplain import',raw)
  result.append(raw.strip())
 return result
def body(s):return IM.sub('',s)
def rel(m):return 'lean/'+m.replace('.','/')+'.lean'
def module(r):return r.removeprefix('lean/').removesuffix('.lean').replace('/','.')
def clean(s):
 # Hide nested comments and strings but preserve columns/newlines for reports.
 out=list(s);i=0;depth=0;string=False;line=False
 while i<len(s):
  if line:
   if s[i]=='\n':line=False
   else:out[i]=' '
   i+=1;continue
  if depth:
   if s.startswith('/-',i):out[i:i+2]=[' ',' '];depth+=1;i+=2;continue
   if s.startswith('-/',i):out[i:i+2]=[' ',' '];depth-=1;i+=2;continue
   if s[i]!='\n':out[i]=' '
   i+=1;continue
  if string:
   if s[i]=='\\' and i+1<len(s):out[i:i+2]=[' ',' '];i+=2;continue
   if s[i]=='"':string=False
   if s[i]!='\n':out[i]=' '
   i+=1;continue
  if s.startswith('--',i):out[i:i+2]=[' ',' '];line=True;i+=2;continue
  if s.startswith('/-',i):out[i:i+2]=[' ',' '];depth=1;i+=2;continue
  if s[i]=='"':out[i]=' ';string=True
  i+=1
 assert depth==0 and not string
 return ''.join(out)
def hazards(s):
 cs=clean(s);stack=[];issues=[]
 for n,line in enumerate(cs.splitlines(),1):
  stripped=line.strip()
  m=re.fullmatch(r'(namespace|section)(?:\s+(\S+))?',stripped)
  if m:stack.append((m.group(1),m.group(2),n));continue
  m=re.fullmatch(r'end(?:\s+(\S+))?',stripped)
  if m:
   if not stack:issues.append([n,'unmatched end',stripped]);continue
   kind,name,start=stack.pop()
   if m.group(1) and m.group(1)!=name:issues.append([n,'scope-name mismatch',[name,m.group(1)]] )
   continue
  if re.match(r'(?:private|protected|local|scoped|attribute|initialize|builtin_initialize|elab|macro|syntax|notation|infix|prefix|postfix|declare_syntax_cat)\b',stripped):issues.append([n,'review scope/declaration command',stripped])
  if re.match(r'(?:noncomputable\s+)?instance(?:\s*[:({\[])',stripped):issues.append([n,'anonymous instance naming',stripped])
  if re.match(r'(?:open|variable|universe)\b',stripped) and not stack:issues.append([n,'file-level scoped state',stripped])
  if re.match(r'set_option\b',stripped) and stripped!='set_option autoImplicit false':issues.append([n,'option must be reviewed',stripped])
 if stack:issues.append([None,'unclosed scopes',stack])
 return issues
selected=[g for g in plan['groups'] if g['name'] in a.groups] if a.groups is not None else [g for g in plan['groups'] if g['phase']<=a.max_phase]
if a.groups is not None:assert {g['name'] for g in selected}==set(a.groups)
assert selected
members=[m for g in selected for m in g['members']]; assert len(members)==len(set(members))
mapping={m:g['destination'] for g in selected for m in g['members']}
oldmodules={module(r):s for r,s in baseline.items() if r!='lean/SupportAxioms.lean'}
graph={m:imports(s) for m,s in oldmodules.items()}
reviews=[]
for g in selected:
 ms=g['members']; dest=g['destination']; assert dest in ms
 external=list(dict.fromkeys(mapping.get(i,i) for m in ms for i in graph[m] if i not in ms))
 flags={m:hazards(oldmodules[m]) for m in ms}; flags={m:h for m,h in flags.items() if h}
 linear=[{'member':m,'imports':graph[m],'expected':[ms[i-1]]} for i,m in enumerate(ms) if i and graph[m]!=[ms[i-1]]]
 # Other consumers of an interior member would import additional later
 # declarations after migration; flag for review even though DAG may be sound.
 consumers={m:[n for n,deps in graph.items() if m in deps and n not in ms] for m in ms[:-1]}
 consumers={m:v for m,v in consumers.items() if v}
 review={'name':g['name'],'destination':dest,'members':ms,'external_imports':external,'hazards':flags,'nonlinear_import_steps':linear,'outside_interior_consumers':consumers,'body_hashes':{m:sha(body(oldmodules[m])) for m in ms}}
 reviews.append(review)
 if a.check_current:
  for m in ms:
   if m!=dest:assert not (P/rel(m)).exists(),('old source not removed',m)
  now=(P/rel(dest)).read_text(); assert imports(now)==external,('target import ordering',dest,imports(now),external)
  # Every byte in every original non-import body survives. Only separator
  # whitespace may be added between the complete bodies.
  rest=body(now)
  for m in ms:
   b=body(oldmodules[m]); pos=rest.find(b)
   assert pos>=0 and not rest[:pos].strip(),('changed/reordered source body',m)
   rest=rest[pos+len(b):]
  assert not rest.strip(),('new code after bodies',dest)
  review['exact_bodies_verified']=True
current={str(f.relative_to(P)):f.read_text() for root in [P/'lean/TransposeFollowup',P/'lean/FixedTapeCompiler'] for f in root.rglob('*.lean')}
current['lean/SupportAxioms.lean']=(P/'lean/SupportAxioms.lean').read_text()
audit_re=re.compile(r'^#print axioms (\S+)\s*$',re.M)
beforeaudit=audit_re.findall(baseline['lean/SupportAxioms.lean']);nowaudit=audit_re.findall(current['lean/SupportAxioms.lean'])
assert len(beforeaudit)==len(set(beforeaudit))==6297
assert set(beforeaudit)==set(receipt['verified_declarations'])
assert nowaudit==beforeaudit,('audit names or order changed',len(nowaudit))
if a.check_current:
 targets={rel(g['destination']) for g in selected}; removed={rel(m) for m in members}-targets
 assert set(current)==set(baseline)-removed,('unexpected source additions/removals',set(current)^ (set(baseline)-removed))
 for r,s in baseline.items():
  if r in targets or r in removed:continue
  assert body(current[r])==body(s),('non-import source changed',r)
  expected=list(dict.fromkeys(mapping.get(i,i) for i in imports(s)))
  assert imports(current[r])==expected,('consumer imports mismatch',r,imports(current[r]),expected)
 nowgraph={module(r):imports(s) for r,s in current.items() if r!='lean/SupportAxioms.lean'}
 deletedmods={module(r) for r in removed}
 for r,s in current.items():
  assert not (set(imports(s))&deletedmods),('dangling deleted import',r)
 colors={};order=[]
 def visit(m,path):
  if colors.get(m)==1:raise AssertionError(('import cycle',path+[m]))
  if colors.get(m)==2:return
  colors[m]=1
  for i in nowgraph[m]:
   if i in nowgraph:visit(i,path+[m])
   elif i.startswith(('TransposeFollowup.','FixedTapeCompiler.')):raise AssertionError(('missing local import',m,i))
  colors[m]=2;order.append(m)
 for m in nowgraph:visit(m,[])
else:nowgraph=graph
if a.axioms_log:
 text=a.axioms_log.read_text(); assert not re.search(r'^.*\berror:',text,re.M)
 # Lean output: 'Name' depends on axioms: [propext, ...], possibly multiline.
 matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)
 noaxioms=re.findall(r"'([^']+)' does not depend on any axioms",text)
 parsed={n:{x.strip() for x in ax.split(',') if x.strip()} for n,ax in matches}
 for n in noaxioms:assert n not in parsed;parsed[n]=set()
 assert len(matches)+len(noaxioms)==len(parsed)==6297,('axiom declarations',len(parsed))
 assert set(parsed)==set(beforeaudit),('axiom names differ',set(parsed)^set(beforeaudit))
 allowed=set(receipt['allowed_axioms'])
 for n,ax in parsed.items():assert ax<=allowed,('new axiom',n,ax-allowed)
result={'mode':'current consolidation checked' if a.check_current else 'read-only candidate review','groups':reviews,'audit_names_unchanged':len(nowaudit),'baseline_hashes_verified':len(baseline),'current_math_modules':len(nowgraph),'axiom_log_checked':str(a.axioms_log) if a.axioms_log else None,'note':'Exact source bodies plus ordinary final Lean build and complete axiom audit preserve the existing six endpoint contracts. Lexical hazard report is conservative, not a Lean parser; review all reported flags before adoption.'}
a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'output':str(a.output),'groups':len(reviews),'hazard_groups':[r['name'] for r in reviews if r['hazards']],'nonlinear_groups':[r['name'] for r in reviews if r['nonlinear_import_steps']],'audit_names':len(nowaudit),'baseline_hashes':len(baseline)}))
