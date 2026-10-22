#!/usr/bin/env python3
"""Deferred six-module terminal merge pilot. Prepare by default; root alone runs Lean.
Run only AFTER all prior edits and a successful ordinary Lake build
of +TransposeFollowup.UnconditionalPaidPadding (or a full build). No cache mutation.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,platform,re,shlex,signal,statistics,subprocess,tempfile,time
P=Path('.');L=P/'lean';LAKE='lake'
NAMES=['ConditionalSpectralExpansion','RationalMobiusAction','SpectralGapInterface','RationalRestrictedGap','RationalContinuousExpander','UnconditionalPaidPadding'];GROUP={'TransposeFollowup.'+n for n in NAMES}
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--run',action='store_true');ap.add_argument('--confirm-idle',action='store_true')
ap.add_argument('--validation-timing',type=Path,help='Root-provided successful CURRENT ordinary Lake build timing JSON covering +TransposeFollowup.UnconditionalPaidPadding or full build.')
ap.add_argument('--validation-log',type=Path,help='Corresponding CURRENT successful ordinary Lake build log.')
ap.add_argument('--pairs',type=int,choices=[1,2,3],default=3)
ap.add_argument('--profile',action='store_true',help='Extra profiled ImportOnly and Merged checks after timing pairs, excluded from medians.')
a=ap.parse_args()
if a.run and not(a.confirm_idle and a.validation_timing and a.validation_log):ap.error('--run requires --confirm-idle --validation-timing FILE --validation-log FILE; prerequisites must have been freshly validated after exact source restoration and prerequisite validation.')
sha=lambda b:hashlib.sha256(b).hexdigest()
def record(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
# Read sources and caches at invocation time, never use saved R1912 artifacts.
source={n:(L/'TransposeFollowup'/f'{n}.lean').read_bytes()for n in NAMES}
external=[];bodies=[];declaration_names=[]
for n in NAMES:
 s=source[n].decode();imps=re.findall(r'^import\s+([^\n]+)\n',s,re.M)
 assert imps and not re.search(r'^\s*(private\b|local\s+(?:attribute|instance)|attribute\s+\[local)',s,re.M),('Scope review needed',n)
 assert len(re.findall(r'^namespace ',s,re.M))==len(re.findall(r'^end(?: |$)',s,re.M))>0,('Namespace boundary review needed',n)
 for imp in imps:
  if imp not in GROUP and imp not in external:external.append(imp)
 body=re.sub(rb'^import [^\n]+\n',b'',source[n],flags=re.M);bodies.append(body)
 declaration_names+=re.findall(r'^(?:noncomputable )?(?:def|abbrev|theorem|instance)\s+([A-Za-z0-9_]+)',s,re.M)
assert len(declaration_names)==len(set(declaration_names))
assert re.findall(rb'^instance\s+(\w+)',b'\n'.join(bodies),re.M)==[]
header=''.join('import '+i+'\n'for i in external).encode();merged=header+b'\n'.join(bodies)
assert merged[len(header):]==b'\n'.join(bodies)
local={'.'.join(p.relative_to(L).with_suffix('').parts):p for root in ['TransposeFollowup','FixedTapeCompiler']for p in (L/root).rglob('*.lean')}
G={n:set(re.findall(r'^import\s+([A-Za-z0-9_.]+)',p.read_text(),re.M))&local.keys()for n,p in local.items()}
def closure(seeds):
 seen=set();pending=list(seeds)
 while pending:
  n=pending.pop()
  if n in seen:continue
  seen.add(n);pending.extend(G[n])
 return seen
outside_consumers=sorted(n for n,ds in G.items()if n not in GROUP and ds&GROUP)
assert outside_consumers==[],('Unexpected external mathematical consumer',outside_consumers)
assert sum(len(b.splitlines())for b in source.values())==517,'Original group no longer exactly517lines'
local_external=set(external)&local.keys();assert closure(local_external).isdisjoint(GROUP),'Merged prerequisites transitively import declarations being defined.'
# Check exact quotient graph; this also catches new cross-imports after refactoring.
Q={('@merged'if n in GROUP else n):set()for n in G}
for n,ds in G.items():
 k='@merged'if n in GROUP else n
 Q[k].update('@merged'if d in GROUP else d for d in ds if ('@merged'if d in GROUP else d)!=k)
active=set();done=set()
def visit(n):
 assert n not in active,('Quotient cycle',n)
 if n in done:return
 active.add(n)
 for d in Q[n]:visit(d)
 active.remove(n);done.add(n)
for n in Q:visit(n)
validation={}
if a.run:
 assert (L/'TransposeFollowup/MobiusMatrixGeometryCore.lean').is_file(),'Defer until geometry core is applied/validated.'
 assert 'import TransposeFollowup.RealMobiusL2\n'in (L/'TransposeFollowup/RealMobiusAverage.lean').read_text()
 assert 'import TransposeFollowup.RationalMobiusAction\n'not in (L/'TransposeFollowup/RealMobiusAverage.lean').read_text()
 receipt=json.loads(a.validation_timing.read_text());assert receipt['exit_code']==0
 command=receipt['command'];assert 'build'in command
 after=command[command.index('build')+1:]
 assert not after or '+TransposeFollowup.UnconditionalPaidPadding'in after or 'TransposeFollowup'in after,'Validation must cover current group and prerequisites.'
 log=a.validation_log.read_text();assert 'Build completed successfully'in log and not re.search(r'error:|✖',log)
 validation={'timing':record(a.validation_timing),'log':record(a.validation_log),'receipt':receipt,'scope':'Root confirms this successful ordinary build validated CURRENT sources and artifacts after exact source restoration and prerequisite validation. Existing artifact presence alone is not validation.'}
D=Path(tempfile.mkdtemp(prefix='r1915-terminal-merge-',dir='external/temporary'))
variants={**{n:source[n]for n in NAMES},'Merged':merged,'ImportOnly':header}
for n,b in variants.items():(D/f'{n}.lean').write_bytes(b)
source_records=[record(local[n])for n in sorted(closure(GROUP))]
config_records=[record(L/n)for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']if (L/n).exists()]
artifacts=[]
# Direct cached import artifacts, including internal predecessors used by split
# copies, must be current validated artifacts. Root's ordinary successful target
# build validates their transitive dependencies; source closure is guarded above.
# Avoid repeatedly hashing hundreds of transitive oleans between timed samples.
direct_artifact_inputs=GROUP|set().union(*(G[n]for n in GROUP))
for n in sorted(direct_artifact_inputs):
 f=L/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean')
 assert f.is_file(),f'Missing current cached prerequisite: {f}'
 artifacts.append(record(f))
proposal_path=Path('external/temporary/r1915-terminal-merge/one/proposal.json')
proposal=json.loads(proposal_path.read_text())
assert proposal['scheme']=='one' and proposal['quotient_acyclic'] is True
for c in proposal['changes']:
 if c['path']in {'lean/TransposeFollowup/'+n+'.lean'for n in NAMES}:
  assert (P/c['path']).read_text()==c['old_text'],'Current source differs from reviewed proposal'
assert merged.decode()==next(c['new_text']for c in proposal['changes']if c['path']=='lean/TransposeFollowup/UnconditionalPaidPadding.lean')
manifest={'format':'r1915-terminal-merge-benchmark-v1','status':'PREPARED ONLY','scratch':str(D),'pairs':a.pairs,'order_by_pair':[['split','merged']if i%2==0 else['merged','split']for i in range(a.pairs)],'source_records':source_records,'configuration_records':config_records,'current_cached_local_artifacts':artifacts,'validation':validation,'proposal':record(proposal_path),'scratch_inputs':{n:record(D/f'{n}.lean')for n in variants},'group':NAMES,'source_lines':sum(len(b.splitlines())for b in source.values()),'external_imports':external,'proof_bodies_byte_identical_after_import_removal':True,'body_sha256':{n:sha(b)for n,b in zip(NAMES,bodies)},'global_instances_moved':0,'quotient_acyclic':True,'external_consumers':sorted(n for n,ds in G.items()if n not in GROUP and ds&GROUP),'artifact_flags':['-o <unique-scratch>.olean','-i <unique-scratch>.ilean','-c <unique-scratch>.c'],'baseline_scope':'Each split source is freshly checked, using current validated original predecessor artifacts, not scratch-produced predecessor artifacts. Split arm is sequential sum of six ordinary checks.','no_repository_or_cache_mutation':True,'profile_excluded_from_medians':True}
write(D/'manifest.json',manifest)
protected=source_records+config_records+artifacts+[manifest['proposal']]+list(manifest['scratch_inputs'].values())+([validation['timing'],validation['log']]if validation else[])
def check_fixed():
 for r in protected:assert record(Path(r['path']))==r,('Source/artifact/evidence changed',r['path'])
def cmd(n,label,profile=False):
 b=D/(label+'-'+n);return [LAKE,'env','lean','--root='+str(D)]+(['--profile']if profile else[])+['-o',str(b.with_suffix('.olean')),'-i',str(b.with_suffix('.ilean')),'-c',str(b.with_suffix('.c')),str(D/f'{n}.lean')]
print('Scratch:',D,flush=True)
for n in NAMES+['Merged','ImportOnly']:print(shlex.join(cmd(n,'example')),flush=True)
if not a.run:print('PREPARED ONLY: regenerate/run after CURRENT prerequisites are validated. No Lean/Lake executed.',flush=True);raise SystemExit(0)
rows=[]
def run_one(n,label,category,arm,profile=False):
 check_fixed();args=cmd(n,label,profile);b=D/(label+'-'+n)
 assert not any(b.with_suffix(e).exists()for e in ['.olean','.ilean','.c','.stdout','.stderr'])
 start=time.perf_counter()
 with b.with_suffix('.stdout').open('w')as out,b.with_suffix('.stderr').open('w')as err:
  child=subprocess.Popen(args,cwd=L,stdout=out,stderr=err,start_new_session=True)
  try:pid,status,usage=os.wait4(child.pid,0)
  except BaseException:
   try:os.killpg(child.pid,signal.SIGTERM)
   except ProcessLookupError:pass
   try:os.wait4(child.pid,0)
   except ChildProcessError:pass
   raise
  assert pid==child.pid;child.returncode=os.waitstatus_to_exitcode(status)
 row={'label':label,'module':n,'arm':arm,'category':category,'profile':profile,'wall_seconds':time.perf_counter()-start,'exit_code':child.returncode,'user_seconds':usage.ru_utime,'system_seconds':usage.ru_stime,'max_rss_bytes':usage.ru_maxrss if platform.system()=='Darwin'else usage.ru_maxrss*1024,'command':args,'stdout':str(b.with_suffix('.stdout')),'stderr':str(b.with_suffix('.stderr'))}
 rows.append(row);write(D/'measurements.json',rows);print(json.dumps(row),flush=True);check_fixed()
 if child.returncode:manifest['status']='FAILED; DO NOT ADOPT MERGE';write(D/'manifest.json',manifest);raise SystemExit(f'Lean failed: {row["stderr"]}')
 row['artifacts']=[record(b.with_suffix(e))for e in ['.olean','.ilean','.c']];write(D/'measurements.json',rows)
run_one('ImportOnly','probe','import_only','probe')
for i,order in enumerate(manifest['order_by_pair'],1):
 for arm in order:
  for n in NAMES if arm=='split'else['Merged']:run_one(n,f'pair{i}-{arm}','proof_pair',arm)
if a.profile:
 for arm,names in [('probe',['ImportOnly']),('merged',['Merged'])]:
  for n in names:run_one(n,'profile-'+arm,'profile',arm,True)
paired=[]
for i in range(1,a.pairs+1):
 item={'pair':i}
 for arm in ['split','merged']:
  rs=[r for r in rows if r['label']==f'pair{i}-{arm}'];item[arm+'_wall_seconds']=sum(r['wall_seconds']for r in rs);item[arm+'_max_reported_rss_bytes']=max(r['max_rss_bytes']for r in rs)
 final=next(r for r in rows if r['label']==f'pair{i}-split' and r['module']==NAMES[-1])
 item['split_final_only_seconds']=final['wall_seconds'];item['split_final_only_rss_bytes']=final['max_rss_bytes']
 item['merged_vs_final_only_overhead_seconds']=item['merged_wall_seconds']-item['split_final_only_seconds']
 item['merged_vs_split_peak_rss_ratio']=item['merged_max_reported_rss_bytes']/item['split_max_reported_rss_bytes']
 paired.append(item)
summary={'status':'passed','pairs':paired,'median_split_seconds':statistics.median(r['split_wall_seconds']for r in paired),'median_merged_seconds':statistics.median(r['merged_wall_seconds']for r in paired),'all_checks_exit_zero':True,'current_validated_inputs_unchanged':True,'proof_body_bytes_preserved':True,'whole_project_speedup_ratio':None,'caution':'Split sum is sequential fresh six-source work; previous originals provide cached predecessor artifacts. Ordinary full target build and statement/axiom checks still required before adoption. Import-only elapsed is not a pure import timer; RSS is maximum per sequential child, not total memory.'}
summary['observed_median_target_ratio']=summary['median_split_seconds']/summary['median_merged_seconds']
summary['median_reduction_fraction']=1-summary['median_merged_seconds']/summary['median_split_seconds']
summary['median_split_final_only_seconds']=statistics.median(r['split_final_only_seconds']for r in paired)
summary['median_merged_vs_final_only_overhead_seconds']=summary['median_merged_seconds']-summary['median_split_final_only_seconds']
summary['allowed_final_only_overhead_seconds']=max(3.0,.25*summary['median_split_final_only_seconds'])
summary['median_split_peak_rss_bytes']=statistics.median(r['split_max_reported_rss_bytes']for r in paired)
summary['median_merged_peak_rss_bytes']=statistics.median(r['merged_max_reported_rss_bytes']for r in paired)
summary['median_split_final_only_rss_bytes']=statistics.median(r['split_final_only_rss_bytes']for r in paired)
summary['median_merged_vs_split_peak_rss_ratio']=summary['median_merged_peak_rss_bytes']/summary['median_split_peak_rss_bytes']
summary['median_merged_vs_final_only_rss_ratio']=summary['median_merged_peak_rss_bytes']/summary['median_split_final_only_rss_bytes']
summary['adoption_gates']={'three_alternating_pairs':a.pairs==3,'six_chain_reduction_at_least_35_percent':summary['median_reduction_fraction']>=.35,'final_only_overhead_at_most_max_3s_25_percent':summary['median_merged_vs_final_only_overhead_seconds']<=summary['allowed_final_only_overhead_seconds'],'median_peak_rss_increase_at_most_10_percent':summary['median_merged_vs_split_peak_rss_ratio']<=1.10}
summary['adoption_eligible']=all(summary['adoption_gates'].values())
summary['profile_diagnostic_modules']=[r['module']for r in rows if r['category']=='profile']
check_fixed();write(D/'summary.json',summary);manifest['status']='BENCHMARK COMPLETE; NOT APPLIED TO REPOSITORY';write(D/'manifest.json',manifest);print(json.dumps(summary),flush=True)
