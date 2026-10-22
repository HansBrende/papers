from pathlib import Path
from functools import cache
import ast,json,re,hashlib,statistics,datetime
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition');L=P/'lean';V=P/'verification'
A=Path('/Users/hansbrende/Documents/Codex/2026-10-09/a/research/10-linear-decision/archive/r1912-build-speed')
src=Path('/private/tmp/r1912-read-import-graph.py').read_text();tree=ast.parse(src)
fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='strip')
exec(compile(ast.Module(body=[fn],type_ignores=[]),'strip-imports','exec'))
def imports(s):return re.findall(r'^(?:(?:public|meta|private) )*import(?: all)?\s+([A-Za-z0-9_.]+)',strip(s),re.M)
def modname(p):return '.'.join(Path(p).relative_to('lean').with_suffix('').parts)
oldtext={modname(k):v for k,v in json.loads((A/'baseline-sources.json').read_text()).items() if k.startswith(('lean/TransposeFollowup/','lean/FixedTapeCompiler/'))}
newtext={'.'.join(f.relative_to(L).with_suffix('').parts):f.read_text() for root in [L/'TransposeFollowup',L/'FixedTapeCompiler'] for f in root.rglob('*.lean')}
saved=json.loads(Path('/private/tmp/r1912-import-graph.json').read_text());external={k:v for k,v in saved['graph'].items() if not k.startswith(('TransposeFollowup.','FixedTapeCompiler.'))}
graphs={'baseline':external|{m:imports(s) for m,s in oldtext.items()},'current':external|{m:imports(s) for m,s in newtext.items()}}
@cache
def closure(label,m):
 g=graphs[label];seen=set();todo=list(g.get(m,[]))
 while todo:
  q=todo.pop()
  if q not in seen:seen.add(q);todo.extend(g.get(q,[]))
 return frozenset(seen)
def local(m):return m.startswith(('TransposeFollowup.','FixedTapeCompiler.'))
def closure_stats(label,m):
 c=closure(label,m)
 groups={'mathlib':sum(q=='Mathlib' or q.startswith('Mathlib.') for q in c),'local':sum(local(q) for q in c),'original_paper':sum(q.startswith('Transpose.') or q=='Transpose' for q in c),'other_external_or_leaf':sum(not local(q) and not(q=='Mathlib' or q.startswith('Mathlib.') or q.startswith('Transpose.') or q=='Transpose') for q in c)}
 return {'module':m,'direct_imports':graphs[label].get(m,[]),'dependency_vertices':len(c),'categories':groups,'full_mathlib':'Mathlib' in c,'full_mathlib_roots':sorted(q for q in c if 'Mathlib' in graphs[label].get(q,[]))}
def longest(label,texts):
 g=graphs[label]
 @cache
 def chain(m):
  cs=[chain(q) for q in g.get(m,[]) if q in texts]
  return (max(cs,key=len) if cs else [])+[m]
 return max((chain(m) for m in texts),key=len)
baseheavy={m for m in oldtext if 'Mathlib' in closure('baseline',m)};newheavy={m for m in newtext if 'Mathlib' in closure('current',m)}
# Compose baseline-module-to-consolidated-destination mapping; the core split is
# deliberately left as original compatibility modules, not a one-to-one proof map.
mapping={m:m for m in oldtext}
for p in [V/'r1912-pilot-application.json',V/'r1912-broad19-application.json']:
 for group in json.loads(p.read_text())['groups']:
  members=set(group['members']);dest=group['destination']
  for old,current in list(mapping.items()):
   if current in members:mapping[old]=dest
represented_lost=[m for m in baseheavy if mapping[m] in newtext and 'Mathlib' not in closure('current',mapping[m])]
existing_lost=sorted((baseheavy&set(newtext))-newheavy)
source='TransposeFollowup.SourceEndpointsMeaning'
c0=closure('baseline',source);c1=closure('current',source)
source_details={'baseline':closure_stats('baseline',source),'current':closure_stats('current',source),'baseline_source_modules_merged_here':sorted(m for m,d in mapping.items() if d==source),'baseline_source_lines':len(oldtext[source].splitlines()),'current_source_lines':len(newtext[source].splitlines()),'removed_dependency_vertices':len(c0-c1),'added_dependency_vertices':len(c1-c0),'current_mathlib_import_roots':sorted(q for q in c1 if local(q) and 'Mathlib.Tactic' in graphs['current'].get(q,[]))}
log=V/'r1912-consolidated-full-build.log';logs=log.read_text().splitlines() if log.exists() else []
pat=re.compile(r'[✔⚠] \[(\d+)/(\d+)\] Built (\S+) \(([\d.]+)(ms|s)\)')
measured=[]
for line in logs:
 match=pat.search(line)
 if match:
  job,total,m,d,unit=match.groups()
  if m in newtext:measured.append({'module':m,'seconds':float(d)/(1000 if unit=='ms' else 1),'full_mathlib':m in newheavy,'job':int(job),'total_jobs':int(total)})
timing={}
for heavy in [False,True]:
 vals=[r['seconds'] for r in measured if r['full_mathlib']==heavy]
 if vals:timing['full_mathlib' if heavy else 'no_full_mathlib']={'built_samples':len(vals),'median_seconds':statistics.median(vals),'minimum_seconds':min(vals),'maximum_seconds':max(vals)}
oldpath=longest('baseline',oldtext);newpath=longest('current',newtext)
report={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Read-only final-source dependency analysis; full build still running at analysis time; no Lean/Lake invocation or repository edits by reviewer.','graph_method':'Comments/strings stripped; compound public/meta imports included. Local, original-paper and pinned Mathlib source graph expanded. Other library/core imports are leaf vertices. Counts are parsed dependencies, not loaded artifact counts or Lake jobs.','baseline':{'modules':len(oldtext),'full_mathlib':len(baseheavy),'no_full_mathlib':len(oldtext)-len(baseheavy),'longest_local_dependency_path_modules':len(oldpath),'longest_local_dependency_path':oldpath},'current':{'modules':len(newtext),'full_mathlib':len(newheavy),'no_full_mathlib':len(newtext)-len(newheavy),'longest_local_dependency_path_modules':len(newpath),'longest_local_dependency_path':newpath,'dangling_local_imports':sorted({q for m in newtext for q in graphs['current'][m] if local(q) and q not in newtext})},'same_named_survivors_losing_full_mathlib':existing_lost,'baseline_units_whose_consolidated_destination_loses_full_mathlib':sorted(represented_lost),'counting_caution':'Consolidation means baseline vs final file counts do not measure the same proof-unit population. Represented baseline units use composed grouping destination, while split native source paths count as retained compatibility wrappers.','source_endpoints':source_details,'other_targets':{m:{label:closure_stats(label,'TransposeFollowup.'+m) for label,texts in [('baseline',oldtext),('current',newtext)] if 'TransposeFollowup.'+m in texts} for m in ['NativeMicrocode','NativeMicrocodeCore','NativeIOFusionCalls','NativeZipper','ScheduledNativeIO','RationalMobius','ClosedNativePadding']},'build_snapshot':{'path':str(log),'sha256_at_snapshot':hashlib.sha256('\n'.join(logs).encode()).hexdigest(),'complete_seen':any('Build completed successfully' in s for s in logs),'error_lines':[s for s in logs if s.startswith('error:') or '✖' in s],'last_lines':logs[-8:],'timing_groups':timing,'samples':measured,'warning':'Concurrent mixed-size build samples are descriptive only; medians are not controlled A/B comparisons, sums are not wall time, and the complete build timing remains outstanding.'}}
Path('/private/tmp/r1912-final-import-review.json').write_text(json.dumps(report,indent=2))
print(json.dumps({k:report[k] for k in ['baseline','current']},indent=2))
print(json.dumps(source_details,indent=2));print('Same names lost',len(existing_lost),'represented baseline units lost',len(represented_lost));print('early timing',timing)
