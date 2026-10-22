#!/usr/bin/env python3
"""Prepare-only by default. Root alone may use --run --confirm-idle.
Compare identical RealMobiusAverage proof bodies under two direct imports.
No repository, Mathlib cache, dependency artifact, trace, or timestamp is changed.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,platform,re,shlex,signal,statistics,subprocess,tempfile,time
P=Path('.')
L=P/'lean';LAKE='lake'
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--run',action='store_true',help='Launch sequential ordinary Lean checks; otherwise prepare scratch inputs only.')
ap.add_argument('--confirm-idle',action='store_true',help='Acknowledge all other Lean/Lake handles are terminal and sources will remain fixed.')
ap.add_argument('--pairs',type=int,choices=[1,2,3],default=3)
ap.add_argument('--profile',action='store_true',help='After unprofiled timing pairs, run one --profile check for each proof arm and each import-only probe; excluded from timing medians.')
ap.add_argument('--scratch-parent',type=Path,default=Path('external/temporary'))
a=ap.parse_args()
if a.run and not a.confirm_idle:ap.error('--run requires --confirm-idle')
D=Path(tempfile.mkdtemp(prefix='r1914-real-mobius-average-',dir=a.scratch_parent))
sha=lambda b:hashlib.sha256(b).hexdigest()
def file_record(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def write(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
source_path=L/'TransposeFollowup/RealMobiusAverage.lean';original=source_path.read_bytes()
old_header=b'import TransposeFollowup.RationalMobiusAction\n';new_header=b'import TransposeFollowup.RealMobiusL2\n'
assert original.startswith(old_header),'Run before changing the original direct import; current source is not the expected baseline.'
body=original[len(old_header):];candidate=new_header+body
assert candidate[len(new_header):]==body and original.count(old_header)==1
assert re.findall(rb'^import\s+([^\n]+)',body,re.M)==[], 'Unexpected additional imports require review.'
variants={'Baseline':original,'Candidate':candidate,'ImportBaseline':old_header,'ImportCandidate':new_header}
for name,content in variants.items():(D/f'{name}.lean').write_bytes(content)
# Check direct/transitive local import safety without invoking Lean or Lake.
local_sources={'.'.join(p.relative_to(L).with_suffix('').parts):p for root in ['TransposeFollowup','FixedTapeCompiler']for p in (L/root).rglob('*.lean')}
imports={n:re.findall(r'^import\s+([A-Za-z0-9_.]+)',p.read_text(),re.M)for n,p in local_sources.items()}
def closure(n):
 seen=set();pending=[n]
 while pending:
  n=pending.pop()
  if n in seen:continue
  seen.add(n);pending.extend(x for x in imports.get(n,[])if x in local_sources)
 return seen
roots={'Baseline':'TransposeFollowup.RationalMobiusAction','Candidate':'TransposeFollowup.RealMobiusL2'}
closures={arm:closure(root)for arm,root in roots.items()}
assert all('TransposeFollowup.RealMobiusAverage'not in c for c in closures.values()),'A dependency imports the benchmarked declarations.'
source_records=[file_record(source_path)]+[file_record(local_sources[n])for n in sorted(set.union(*closures.values()))]
config_records=[file_record(L/n)for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']if (L/n).exists()]
artifact_records=[]
for root in roots.values():
 p=L/'.lake/build/lib/lean'/Path(*root.split('.')).with_suffix('.olean')
 assert p.is_file(),f'Expected validated current cached prerequisite missing: {p}'
 artifact_records.append(file_record(p))
manifest={'format':'r1914-real-mobius-average-paired-benchmark-v1','status':'PREPARED ONLY','prepared_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scratch':str(D),'pairs':a.pairs,'order_by_pair':[['Baseline','Candidate']if i%2==0 else['Candidate','Baseline']for i in range(a.pairs)],'baseline_import':roots['Baseline'],'candidate_import':roots['Candidate'],'proof_body_sha256':sha(body),'proof_body_bytes':len(body),'proof_bodies_byte_identical_after_import':True,'source_records':source_records,'configuration_records':config_records,'direct_cached_prerequisite_artifacts':artifact_records,'local_dependency_closures':{k:sorted(v)for k,v in closures.items()},'scratch_inputs':{n:file_record(D/f'{n}.lean')for n in variants},'artifact_flags':['-o <unique-scratch>.olean','-i <unique-scratch>.ilean','-c <unique-scratch>.c'],'profile_mode':'extra separately labeled checks after timing pairs; excluded from timing medians'if a.profile else'disabled','scope':'Ordinary source elaboration/kernel checking plus explicit olean/ilean/C output in separate scratch paths, using the current lake env and validated cached prerequisites; not a whole-project benchmark.','no_repository_or_dependency_cache_mutation':True,'timing_note':'Per-invocation wall time includes lake env/startup/import/proof/artifact/shutdown. Import-only probes are not an exact decomposition of proof versus import time.','profile_support_evidence':'Pinned Lean/Shell.lean178,405-406 advertises --profile and enables the profiler.'}
write(D/'manifest.json',manifest)
def check_fixed_inputs():
 for rec in source_records+config_records+artifact_records+list(manifest['scratch_inputs'].values()):
  assert file_record(Path(rec['path']))==rec,('Input changed during benchmark',rec['path'])
def command(name,label,profile=False):
 out=D/(label+'-'+name)
 args=[LAKE,'env','lean','--root='+str(D)]
 if profile:args.append('--profile')
 return args+['-o',str(out.with_suffix('.olean')),'-i',str(out.with_suffix('.ilean')),'-c',str(out.with_suffix('.c')),str(D/f'{name}.lean')]
print('Scratch:',D,flush=True)
print('PREPARED ONLY unless --run --confirm-idle was supplied.',flush=True)
for name in variants:print(shlex.join(command(name,'example')),flush=True)
if not a.run:raise SystemExit(0)
rows=[]
def run_one(name,label,category,profile=False):
 check_fixed_inputs();args=command(name,label,profile);outbase=D/(label+'-'+name)
 assert not any(outbase.with_suffix(ext).exists()for ext in ['.olean','.ilean','.c','.stdout','.stderr'])
 start=time.perf_counter();start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
 with outbase.with_suffix('.stdout').open('w')as out,outbase.with_suffix('.stderr').open('w')as err:
  child=subprocess.Popen(args,cwd=L,stdout=out,stderr=err,start_new_session=True)
  try:pid,status,usage=os.wait4(child.pid,0)
  except BaseException:
   try:os.killpg(child.pid,signal.SIGTERM)
   except ProcessLookupError:pass
   try:os.wait4(child.pid,0)
   except ChildProcessError:pass
   raise
  assert pid==child.pid;child.returncode=os.waitstatus_to_exitcode(status)
 elapsed=time.perf_counter()-start
 row={'label':label,'arm':name,'category':category,'profile':profile,'started_at_utc':start_utc,'wall_seconds':elapsed,'exit_code':child.returncode,'user_seconds':usage.ru_utime,'system_seconds':usage.ru_stime,'max_rss_bytes':usage.ru_maxrss if platform.system()=='Darwin'else usage.ru_maxrss*1024,'command':args,'stdout':str(outbase.with_suffix('.stdout')),'stderr':str(outbase.with_suffix('.stderr')),'input_sha256':sha(variants[name])}
 rows.append(row);write(D/'measurements.json',rows);print(json.dumps(row),flush=True);check_fixed_inputs()
 if child.returncode:
  manifest['status']='FAILED; DO NOT ADOPT CANDIDATE';write(D/'manifest.json',manifest);raise SystemExit(f'Lean check failed: {row["stderr"]}')
 row['artifacts']=[file_record(outbase.with_suffix(ext))for ext in ['.olean','.ilean','.c']]
 write(D/'measurements.json',rows)
 return row
# Both import-only probes warm their respective import paths before paired proofs.
for arm in ['ImportBaseline','ImportCandidate']:run_one(arm,'probe','import_only')
for i,order in enumerate(manifest['order_by_pair'],1):
 for arm in order:run_one(arm,f'pair{i}','proof_pair')
if a.profile:
 for arm in ['Baseline','Candidate','ImportBaseline','ImportCandidate']:run_one(arm,'profile','profile',True)
proofs={arm:[r for r in rows if r['category']=='proof_pair'and r['arm']==arm]for arm in roots}
summary={'format':'r1914-real-mobius-average-paired-summary-v1','status':'passed','scratch':str(D),'pairs':a.pairs,'medians':{arm:{key:statistics.median(r[key]for r in rs)for key in ['wall_seconds','max_rss_bytes']}for arm,rs in proofs.items()},'all_exit_codes_zero':all(r['exit_code']==0 for r in rows),'inputs_unchanged':True,'proof_bodies_byte_identical_after_import':True,'paired_wall_seconds':[{'pair':i,'baseline':next(r['wall_seconds']for r in rows if r['label']==f'pair{i}'and r['arm']=='Baseline'),'candidate':next(r['wall_seconds']for r in rows if r['label']==f'pair{i}'and r['arm']=='Candidate')}for i in range(1,a.pairs+1)],'whole_project_speedup_ratio':None,'rss_caution':'Per-child reported maximum RSS; not aggregate simultaneous-memory use.','profile_in_timing_medians':False}
summary['observed_median_target_ratio']=summary['medians']['Baseline']['wall_seconds']/summary['medians']['Candidate']['wall_seconds']
check_fixed_inputs();write(D/'summary.json',summary);manifest['status']='BENCHMARK COMPLETE; NOT APPLIED TO REPOSITORY';write(D/'manifest.json',manifest);print(json.dumps(summary),flush=True)
