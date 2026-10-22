from pathlib import Path
import json,re,sys,hashlib,shutil
P=Path('.');L=P/'lean';V=P/'verification'
state=json.loads((V/'r1912-in-progress.json').read_text());assert not state['live_handles']
A=Path(state['archive']);tag=sys.argv[1];plan=json.loads(Path(sys.argv[2]).read_text());wanted=sys.argv[3:]
groups=[g for g in plan['groups'] if not wanted or g['name'] in wanted]
assert groups and (not wanted or set(wanted)=={g['name'] for g in groups})
paths=[*L.joinpath('TransposeFollowup').glob('*.lean'),*L.joinpath('FixedTapeCompiler').rglob('*.lean'),L/'SupportAxioms.lean']
before={str(p.relative_to(P)):p.read_text() for p in paths}
assert not (A/f'{tag}-sources-before.json').exists()
(A/f'{tag}-sources-before.json').write_text(json.dumps(before,indent=2)+'\n')
def rel(m):return 'lean/'+m.replace('.','/')+'.lean'
imp=re.compile(r'^import ([A-Za-z_][A-Za-z0-9_.]*)\n',re.M)
def imports(s):return imp.findall(s)
def body(s):return imp.sub('',s)
mapto={m:g['destination'] for g in groups for m in g['members']}
assert len(mapto)==sum(len(g['members']) for g in groups)
removed={rel(m) for m,d in mapto.items() if m!=d}
after={}
for r,s in before.items():
 if r in removed:continue
 ordered=list(dict.fromkeys(mapto.get(m,m) for m in imports(s)))
 after[r]=''.join('import '+m+'\n' for m in ordered)+body(s)
checks=[]
for g in groups:
 ms=g['members'];d=g['destination'];assert d in ms
 external=list(dict.fromkeys(mapto.get(i,i) for m in ms for i in imports(before[rel(m)]) if i not in ms))
 merged=''.join('import '+i+'\n' for i in external)+'\n'.join(body(before[rel(m)]) for m in ms)
 after[rel(d)]=merged
 checks.append({'group':g['name'],'destination':d,'members':ms,'body_sha256':{m:hashlib.sha256(body(before[rel(m)]).encode()).hexdigest() for m in ms},'external_imports':external})
# Check local imports and exact union order before writing anything.
graph={r[5:-5].replace('/','.'):imports(s) for r,s in after.items() if r!='lean/SupportAxioms.lean'}
seen=set();active=set()
def visit(m):
 assert m not in active,('cycle',m)
 if m in seen:return
 active.add(m)
 for i in graph[m]:
  if i in graph:visit(i)
  else:assert not i.startswith(('TransposeFollowup.','FixedTapeCompiler.')),('missing',m,i)
 active.remove(m);seen.add(m)
for m in graph:visit(m)
assert re.findall(r'^#print axioms .+$',after['lean/SupportAxioms.lean'],re.M)==re.findall(r'^#print axioms .+$',before['lean/SupportAxioms.lean'],re.M)
for r,s in before.items():
 if r in removed or after.get(r)!=s:
  f=A/tag/r;f.parent.mkdir(parents=True,exist_ok=True);f.write_text(s)
for r,s in after.items():
 if s!=before.get(r): (P/r).write_text(s)
for r in removed:(P/r).unlink()
# Verify exact non-import bodies and ungrouped contents after mutation.
for g in groups:
 actual=(P/rel(g['destination'])).read_text()
 assert actual==after[rel(g['destination'])]
 assert body(actual)=='\n'.join(body(before[rel(m)]) for m in g['members'])
targets={rel(g['destination']) for g in groups}
for r,s in after.items():
 assert (P/r).read_text()==s
 if r not in targets:assert body(s)==body(before[r])
record={'tag':tag,'groups':checks,'removed':sorted(removed),'changed':sorted(r for r,s in after.items() if s!=before.get(r)), 'before_math_modules':len(before)-1,'after_math_modules':len(after)-1,'exact_bodies_preserved':True,'audit_commands_preserved':True,'acyclic':True}
(V/f'r1912-{tag}-application.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['groups','removed','changed']}))
