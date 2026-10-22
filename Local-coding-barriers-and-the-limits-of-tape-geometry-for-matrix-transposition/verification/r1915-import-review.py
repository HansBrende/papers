from pathlib import Path
import re,json,collections,functools
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition');L=P/'lean'
prior=json.loads(Path('/private/tmp/r1912-import-graph.json').read_text());G=prior['graph'];files=prior['files']
for m in list(G):
 if m.startswith(('TransposeFollowup.','FixedTapeCompiler.')):del G[m];files.pop(m,None)
for sub in ['TransposeFollowup','FixedTapeCompiler']:
 for f in (L/sub).rglob('*.lean'):
  m='.'.join(f.relative_to(L).with_suffix('').parts);s=f.read_text();G[m]=re.findall(r'^(?:(?:public|meta|private) )*import(?: all)?\s+([A-Za-z0-9_.]+)',s,re.M);files[m]=str(f)
local={m for m in G if m.startswith(('TransposeFollowup.','FixedTapeCompiler.'))}
@functools.cache
def closure(m):
 seen=set();todo=[m]
 while todo:
  x=todo.pop()
  if x in seen:continue
  seen.add(x);todo.extend(G.get(x,[]))
 return seen
roots={m for m,ds in G.items()if 'Mathlib' in ds}
def shortest(a,b):
 q=collections.deque([(a,[a])]);seen={a}
 while q:
  x,path=q.popleft()
  if x==b:return path
  for y in G.get(x,[]):
   if y not in seen:seen.add(y);q.append((y,path+[y]))
R={m:[]for m in local}
for m in local:
 for d in G[m]:
  if d in R:R[d].append(m)
@functools.cache
def descendants(m):return {m}|set().union(*(descendants(x)for x in R[m]))
names=['ConditionalSpectralExpansion','RationalMobiusAction','SpectralGapInterface','RationalRestrictedGap','RationalContinuousExpander','UnconditionalPaidPadding'];names=['TransposeFollowup.'+n for n in names];rows={}
for n in names:
 c=closure(n);r={x:shortest(n,x)+['Mathlib']for x in sorted(c&roots)}
 rows[n]={'lines':len(Path(files[n]).read_text().splitlines()),'imports':G[n],'local_closure':len(c&local),'full_Mathlib_roots':r,'direct_consumers':R[n],'transitive_consumers':len(descendants(n)),'Mathlib_vertices':sum(x=='Mathlib'or x.startswith('Mathlib.')for x in c)}
external_imports=list(dict.fromkeys(d for n in names for d in G[n]if d not in names))
cycles=[]
for d in external_imports:
 for n in names:
  if n in closure(d):cycles.append({'external_import':d,'member':n,'path':shortest(d,n)})
output={'method':'Current local source import graph, unchanged pinned Mathlib/upstream graph from R1912. Static only, no Lean execution.','modules':rows,'merge':{'members':names,'external_imports':external_imports,'external_consumer_map':{n:[x for x in R[n]if x not in names]for n in names},'cycles':cycles,'all_members_source_lines':sum(v['lines']for v in rows.values()),'full_roots_in_union':sorted(set().union(*(closure(n)&roots for n in names)))}}
Path('/private/tmp/r1915-import-review.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
