#!/usr/bin/env python3
"""Prepare by default. Run ONLY next round after every Lean/Lake handle is terminal."""
from pathlib import Path
import argparse, hashlib, json, platform, re, shlex, subprocess, tempfile, time
P=Path('.')
L=P/'lean'; LAKE='lake'
NAMES=['SourceEndpointsMachine','SourceEndpointsCalls','SourceEndpointsStages','SourceEndpointsRun','SourceEndpointsMeaning']
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--run',action='store_true',help='Launch sequential Lean checks; otherwise only prepare files and print commands')
ap.add_argument('--confirm-idle',action='store_true',help='Explicitly acknowledge all previous Lean/Lake handles are terminal')
ap.add_argument('--pairs',type=int,default=1,choices=[1,2,3])
ap.add_argument('--probe',action='store_true',help='Also time an import-only dependency probe')
a=ap.parse_args()
if a.run and not a.confirm_idle:ap.error('--run requires --confirm-idle; do not run during another Lean/Lake session')
D=Path(tempfile.mkdtemp(prefix='r1911-source-endpoints-benchmark-',dir='external/temporary'))
source={n:(L/'TransposeFollowup'/f'{n}.lean').read_bytes() for n in NAMES}
sha=lambda b:hashlib.sha256(b).hexdigest()
external=set(); bodies=[]
for n in NAMES:
 s=source[n].decode();imps=re.findall(r'^import (\S+)\s*$',s,re.M)
 assert imps and not re.search(r'^\s*(private|local|scoped)\b',s,re.M),(n,'review scoping before use')
 for i in imps:
  if i not in {'TransposeFollowup.'+x for x in NAMES}:external.add(i)
 body=re.sub(r'^import [^\n]+\n','',s,flags=re.M)
 assert body.count('namespace TransposeFollowup.SourceEndpoints')==1,n
 assert body.count('end TransposeFollowup.SourceEndpoints')==1,n
 bodies.append(body);(D/f'{n}.lean').write_bytes(source[n])
assert external=={'TransposeFollowup.SourceEndpointsData'},external
header='\n'.join('import '+x for x in sorted(external))+'\n'
merged=header+'\n'.join(bodies)
(D/'MergedSourceEndpoints.lean').write_text(merged)
(D/'ImportOnly.lean').write_text(header)
# Source preservation is byte-for-byte after removing the five import lines.
assert merged[len(header):]=='\n'.join(bodies)
manifest={'status':'PREPARED ONLY','sources':{str(L/'TransposeFollowup'/f'{n}.lean'):sha(b)for n,b in source.items()},'external_imports':sorted(external),'source_lines':sum(b.count(b'\n')for b in source.values()),'merged_lines':merged.count('\n'),'merged_sha256':sha(merged.encode()),'scratch':str(D),'pairs':a.pairs,'mode':'sequential full proof elaboration/kernel checks; no repository output/cache edits'}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
def check_sources():
 for p,h in manifest['sources'].items():assert sha(Path(p).read_bytes())==h,('source changed',p)
def cmd(n,label):
 return [LAKE,'env','lean','--root='+str(D),'-o',str(D/f'{label}-{n}.olean'),str(D/f'{n}.lean')]
print('Scratch:',D,flush=True)
print('These commands are PREPARED ONLY until --run --confirm-idle is supplied:',flush=True)
for n in NAMES+['MergedSourceEndpoints']:print(shlex.join(cmd(n,'example')),flush=True)
if not a.run:raise SystemExit(0)
check_sources();rows=[]
def run_one(n,label):
 check_sources();args=cmd(n,label)
 # BSD time's -l reports peak memory; both arms use precisely the same wrapper.
 timed=['/usr/bin/time','-lp',*args] if platform.system()=='Darwin' else ['/usr/bin/time','-v',*args]
 start=time.perf_counter()
 with (D/f'{label}-{n}.stdout').open('w') as out,(D/f'{label}-{n}.stderr').open('w') as err:
  r=subprocess.run(timed,cwd=L,stdout=out,stderr=err,check=False)
 elapsed=time.perf_counter()-start
 row={'label':label,'module':n,'wall_seconds':elapsed,'returncode':r.returncode,'command':args}
 rows.append(row);(D/'measurements.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True)
 check_sources()
 if r.returncode:raise SystemExit('Benchmark failed; see scratch stderr. Do not adopt the merge.')
 return elapsed
if a.probe:run_one('ImportOnly','probe')
for i in range(a.pairs):
 for arm in (['split','merged'] if i%2==0 else ['merged','split']):
  names=NAMES if arm=='split' else ['MergedSourceEndpoints']
  seconds=sum(run_one(n,f'pair{i+1}-{arm}')for n in names)
  print(json.dumps({'pair':i+1,'arm':arm,'total_wall_seconds':seconds}),flush=True)
manifest['status']='BENCHMARK COMPLETE; NOT APPLIED TO REPOSITORY'
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Review measurements, memory logs, and source hashes before proposing any real merge.',flush=True)
