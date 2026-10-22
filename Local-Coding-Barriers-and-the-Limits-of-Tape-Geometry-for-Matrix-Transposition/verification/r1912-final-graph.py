from pathlib import Path
import re,json,functools,hashlib,datetime
P=Path('.');L=P/'lean'
A=Path('external/research-workspace/research/10-linear-decision/archive/r1912-build-speed')
baseline=json.loads((A/'baseline-sources.json').read_text())
def module(k):return '.'.join(Path(k).relative_to('lean').with_suffix('').parts)
old={module(k):v for k,v in baseline.items()if k.startswith(('lean/TransposeFollowup/','lean/FixedTapeCompiler/')) and k.endswith('.lean')}
files={'.'.join(p.relative_to(L).with_suffix('').parts):p for root in ['TransposeFollowup','FixedTapeCompiler']for p in (L/root).rglob('*.lean')};cur={m:p.read_text()for m,p in files.items()}

def analyze(S):
 allimports={m:set(re.findall(r'^import\s+([A-Za-z0-9_.]+)',s,re.M))for m,s in S.items()}
 D={m:ds&S.keys()for m,ds in allimports.items()};R={m:set()for m in S}
 for m,ds in D.items():
  for d in ds:R[d].add(m)
 active=[];cycles=[]
 @functools.cache
 def path(m):
  if m in active:
   cycles.append(active[active.index(m):]+[m]);return []
  active.append(m);p=max((path(x)for x in sorted(D[m])),key=len,default=[]);active.pop();return p+[m]
 @functools.cache
 def desc(m):return {m}|set().union(*(desc(x)for x in R[m]))
 @functools.cache
 def anc(m):return {m}|set().union(*(anc(x)for x in D[m]))
 ps={m:path(m)for m in S}
 out=dict(modules=len(S),mathematical_lines=sum(len(s.splitlines())for s in S.values()),local_import_edges=sum(map(len,D.values())),cycle_free=not cycles,cycles=cycles,missing_local_imports={m:sorted(x for x in ds if x.startswith(('TransposeFollowup.','FixedTapeCompiler.')) and x not in S)for m,ds in allimports.items()if any(x.startswith(('TransposeFollowup.','FixedTapeCompiler.')) and x not in S for x in ds)})
 out['longest_path']=max(ps.values(),key=len);out['longest_path_length']=len(out['longest_path'])
 out['largest_endpoint_paths']=[dict(endpoint=m,length=len(ps[m]),path=ps[m])for m in sorted((m for m in S if not R[m]),key=lambda m:(-len(ps[m]),m))[:10]]
 out['largest_dependency_closures']=[dict(module=m,closure=len(anc(m)),direct_imports=len(D[m]),descendants=len(desc(m)))for m in sorted(S,key=lambda m:(-len(anc(m)),m))[:10]]
 scenarios={}
 for name in ['NativeMicrocode','NativeMicrocodeCore','NativeMicrocodeRun','NativeMicrocodeRunCore','NativeIO','NativeIOCore','NativeIOFusion','NativeIOFusionCore','NativeIOFusionRun','NativeIOFusionRunCore','NativeReadFusion','NativeReadFusionCore','FiniteProgramEncoding','FiniteProgramEncodingCore','SourceEndpointsMachine','SourceEndpointsMeaning']:
  seed='TransposeFollowup.'+name
  if seed not in S:continue
  aff=desc(seed)
  @functools.cache
  def ap(m):return max((ap(x)for x in sorted(D[m]&aff)),key=len,default=[])+[m]
  bp=max((ap(m)for m in sorted(aff)),key=len)
  scenarios[name]=dict(affected_modules_including_seed=len(aff),serial_dependency_path_length=len(bp),serial_dependency_path=bp,affected_source_lines=sum(len(S[m].splitlines())for m in aff),direct_consumers=sorted(R[seed]))
 out['rebuild_scenarios']=scenarios
 # Maximal chains whose interior has exactly one direct consumer and successor has no other local imports.
 prev={m:next(iter(ds))for m,ds in D.items()if len(ds)==1 and len(R[next(iter(ds))])==1}
 nxt={a:b for b,a in prev.items()}; chains=[]
 for m in S:
  if m not in prev:
   ch=[m]
   while ch[-1]in nxt:ch.append(nxt[ch[-1]])
   if len(ch)>1:chains.append(ch)
 out['remaining_strict_serial_blocks']=[dict(length=len(ch),source_lines=sum(len(S[m].splitlines())for m in ch),modules=ch)for ch in sorted(chains,key=lambda c:(-len(c),c))[:15]]
 out['source_sha256']={m:hashlib.sha256(s.encode()).hexdigest()for m,s in sorted(S.items())}
 out['direct_local_imports']={m:sorted(ds)for m,ds in sorted(D.items())}
 return out
before=analyze(old);after=analyze(cur)
assert before['cycle_free'] and after['cycle_free']
assert not before['missing_local_imports'] and not after['missing_local_imports']
comparisons=[]
for name in ['NativeMicrocode','NativeMicrocodeRun','NativeIO','NativeIOFusion','NativeIOFusionRun','NativeReadFusion','FiniteProgramEncoding']:
 a=before['rebuild_scenarios'][name];b=after['rebuild_scenarios'][name+'Core'];c=after['rebuild_scenarios'][name]
 comparisons.append(dict(old_module=name,new_implementation_module=name+'Core',old_affected=a['affected_modules_including_seed'],new_affected=b['affected_modules_including_seed'],old_serial_path=a['serial_dependency_path_length'],new_serial_path=b['serial_dependency_path_length'],new_bridge_affected=c['affected_modules_including_seed'],new_bridge_serial_path=c['serial_dependency_path_length']))
# Use completed timing receipts only, not live full-build durations.
measurements={}
for name in ['baseline-incremental','baseline-pilot-rebuild','merged-pilot-rebuild']:
 p=P/'verification'/f'r1912-{name}-timing.json'
 if p.exists():measurements[name]=json.loads(p.read_text())
output=dict(created_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='Read-only static analysis of current source while full build is live. This does not confirm build success.',baseline_archive=str(A/'baseline-sources.json'),before=before,after=after,implementation_comparisons=comparisons,completed_timing_receipts=measurements,new_modules=sorted(cur.keys()-old.keys()),removed_modules=sorted(old.keys()-cur.keys()),method='Dependency graph over local mathematical modules only; all ordinary imports parsed from source, edges importer->prerequisite. A rebuild scenario uses the seed plus its transitive local consumers, and longest dependency path within that induced subgraph. Standard/external prerequisites are treated as cached and omitted from path counts. Neither job sums nor graph lengths are wall time.')
Path('external/temporary/r1912-final-graph.json').write_text(json.dumps(output,indent=2)+'\n')
print('COUNTS',len(old),len(cur),'LINES',before['mathematical_lines'],after['mathematical_lines'],'PATH',before['longest_path_length'],after['longest_path_length'])
for c in comparisons:print(c)
print('ENDPOINTS',[(x['endpoint'],x['length'])for x in after['largest_endpoint_paths']])
print('SERIAL',[(x['length'],x['source_lines'],x['modules'][0],x['modules'][-1])for x in after['remaining_strict_serial_blocks'][:5]])
