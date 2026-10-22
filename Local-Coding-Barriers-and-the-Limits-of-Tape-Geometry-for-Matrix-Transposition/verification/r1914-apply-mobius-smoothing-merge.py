#!/usr/bin/env python3
"""Root-only, benchmark-gated five-module consolidation. DOES NOTHING until invoked.
Default invocation prepares a reviewable scratch proposal; --apply mutates only
reviewed local Lean sources after archiving originals. Never runs Lean/Lake and
never deletes generated artifacts or edits dependency caches/traces/timestamps.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,math,os,re,statistics,tempfile
P=Path('.');L=P/'lean'
A=Path('external/research-workspace/research/10-linear-decision/archive/r1914-analytic-build-speed')
NAMES=['TransposeFollowup.MobiusNearIdentity','TransposeFollowup.MobiusPairwiseComparison','TransposeFollowup.MobiusActionContinuity','TransposeFollowup.MobiusGroupAverage','TransposeFollowup.MobiusGroupSmoothing'];DEST=NAMES[-1]
IM=re.compile(r'^import ([A-Za-z_][A-Za-z0-9_.]*)\n',re.M)
def require(ok,message):
 if not ok:raise ValueError(message)
def unique(pairs):
 out={}
 for k,v in pairs:require(k not in out,f'Duplicate JSON key: {k}');out[k]=v
 return out
def read(p):return json.loads(Path(p).read_text(),object_pairs_hook=unique)
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def record(p):
 p=Path(p);b=p.read_bytes();return {'path':str(p.resolve()),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check_record(r):require(record(r['path'])==r,f'Evidence/source/artifact changed: {r["path"]}')
def write_new(p,x):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x')as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def rel(m):return 'lean/'+m.replace('.','/')+'.lean'
def body(s):return IM.sub('',s)
def snapshot():
 d={str(p.relative_to(P)):p.read_text()for root in [L/'TransposeFollowup',L/'FixedTapeCompiler']for p in root.rglob('*.lean')};d['lean/SupportAxioms.lean']=(L/'SupportAxioms.lean').read_text();return d
def expected_merge(before):
 # Exactly the algorithm in r1914-final-source-review.py:expected_merge.
 mapping={m:DEST for m in NAMES};removed={rel(m)for m in NAMES if m!=DEST};after={}
 for r,s in before.items():
  if r in removed:continue
  imps=list(dict.fromkeys(mapping.get(m,m)for m in IM.findall(s)))
  after[r]=''.join('import '+m+'\n'for m in imps)+body(s)
 external=list(dict.fromkeys(mapping.get(i,i)for m in NAMES for i in IM.findall(before[rel(m)])if i not in NAMES))
 require(DEST not in external,'Merged self import')
 after[rel(DEST)]=''.join('import '+m+'\n'for m in external)+'\n'.join(body(before[rel(m)])for m in NAMES)
 return after,mapping,external

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--pilot-dir',type=Path,required=True,help='Complete current r1914-mobius-smoothing-merge benchmark directory.')
 ap.add_argument('--execution-state',type=Path,required=True,help='Root-owned current state JSON with live_handles: []. Required even for proposal generation.')
 ap.add_argument('--confirm-idle',action='store_true',help='Root confirms all Lean/Lake/timed handles are terminal and no source editing runs concurrently.')
 ap.add_argument('--apply',action='store_true',help='Archive then apply the reviewed changes; absent means scratch proposal only.')
 ap.add_argument('--archive-dir',type=Path,default=A/'five-module-merge')
 ap.add_argument('--receipt',type=Path,default=P/'verification/r1914-merge-application.json')
 ap.add_argument('--proposal-output',type=Path,default=Path('external/temporary/r1914-mobius-smoothing-merge-proposal.json'))
 a=ap.parse_args()
 require(a.confirm_idle,'Root idle confirmation required; never execute during timed work.')
 state=read(a.execution_state);require(state.get('live_handles')==[],'Root still has live handles, or the explicit live_handles list is missing.')
 pilot=a.pilot_dir.resolve();manifest=read(pilot/'manifest.json');summary=read(pilot/'summary.json');rows=read(pilot/'measurements.json')
 require(manifest['format']=='r1914-mobius-smoothing-merge-benchmark-v1','Wrong pilot manifest')
 require(manifest['status']=='BENCHMARK COMPLETE; NOT APPLIED TO REPOSITORY','Pilot incomplete/failed')
 require(manifest['pairs']==3 and manifest['order_by_pair']==[['split','merged'],['merged','split'],['split','merged']],'Require three alternating pairs')
 require(manifest['group']==[m.rsplit('.',1)[1]for m in NAMES],'Unexpected pilot group')
 require(manifest['quotient_acyclic']is True and manifest['proof_bodies_byte_identical_after_import_removal']is True,'Pilot preservation/graph gate failed')
 require(summary['status']=='passed'and summary['all_checks_exit_zero']is True and summary['current_validated_inputs_unchanged']is True and summary['proof_body_bytes_preserved']is True,'Pilot summary did not pass')
 require(rows and all(r['exit_code']==0 for r in rows),'Some pilot process did not pass')
 paired=[]
 for i,order in enumerate(manifest['order_by_pair'],1):
  selected=[r for r in rows if r['category']=='proof_pair'and r['label'].startswith(f'pair{i}-')]
  expected=[(arm,n)for arm in order for n in ([m.rsplit('.',1)[1]for m in NAMES]if arm=='split'else['Merged'])]
  require([(r['arm'],r['module'])for r in selected]==expected,f'Pair{i} coverage/order differs')
  require(all(r['profile']is False and math.isfinite(r['wall_seconds'])and r['wall_seconds']>0 for r in selected),'Invalid/profiled timing in primary pairs')
  paired.append({arm:sum(r['wall_seconds']for r in selected if r['arm']==arm)for arm in ['split','merged']})
 require(len([r for r in rows if r['category']=='proof_pair'])==18,'Unexpected extra/missing primary check')
 split=statistics.median(r['split']for r in paired);merged=statistics.median(r['merged']for r in paired)
 require(split==summary['median_split_seconds']and merged==summary['median_merged_seconds'],'Summary medians differ from raw measurements')
 reduction=1-merged/split;require(reduction>=.35,f'Median reduction {100*reduction:.2f}% below required35%; do not apply')
 # Recheck the exact source/configuration/prerequisite snapshot from the actual
 # current pilot, not any archived R1912 dependency artifacts.
 for field in ['source_records','configuration_records','current_cached_local_artifacts']:
  for r in manifest[field]:check_record(r)
 for r in manifest['scratch_inputs'].values():check_record(r)
 for field in ['timing','log']:check_record(manifest['validation'][field])
 require(manifest['validation']['receipt']['exit_code']==0,'Prerequisite validation failed')
 before=snapshot();require(all(rel(m)in before for m in NAMES),'Five original source files no longer present')
 require('lean/TransposeFollowup/MobiusMatrixGeometryCore.lean'in before,'Geometry core not applied')
 require(before[rel('TransposeFollowup.RealMobiusAverage')].startswith('import TransposeFollowup.RealMobiusL2\n'),'Import narrowing not applied')
 for m in NAMES:
  short=m.rsplit('.',1)[1];require(sha(body(before[rel(m)]))==manifest['body_sha256'][short],f'Pilot body mismatch:{m}')
 after,mapping,external=expected_merge(before)
 merged_expected=Path(manifest['scratch_inputs']['Merged']['path']).read_text()
 require(after[rel(DEST)]==merged_expected,'Applied concatenation differs from benchmarked merged source')
 named='instance instGroupSecondCountableTopology'
 require(sum(s.count(named)for s in before.values())==sum(s.count(named)for s in after.values())==1,'Named instance lost or duplicated')
 require(named in after[rel(DEST)],'Named instance not in merged body')
 old_audit=re.findall(r'^#print axioms (\S+)\s*$',before['lean/SupportAxioms.lean'],re.M)
 new_audit=re.findall(r'^#print axioms (\S+)\s*$',after['lean/SupportAxioms.lean'],re.M)
 require(old_audit==new_audit and len(old_audit)==len(set(old_audit))==6306,'Audit declarations/order changed')
 G={r.removeprefix('lean/').removesuffix('.lean').replace('/','.'):IM.findall(s)for r,s in after.items()if r!='lean/SupportAxioms.lean'}
 colors={}
 def visit(n):
  require(colors.get(n)!=1,f'Quotient cycle:{n}')
  if colors.get(n)==2:return
  colors[n]=1
  for d in G[n]:
   if d in G:visit(d)
   else:require(not d.startswith(('TransposeFollowup.','FixedTapeCompiler.')),f'Missing local import:{n}->{d}')
  colors[n]=2
 for n in G:visit(n)
 for d in IM.findall(after['lean/SupportAxioms.lean']):require(d in G or not d.startswith(('TransposeFollowup.','FixedTapeCompiler.')),f'Missing audit import:{d}')
 changes=[]
 for r in sorted(set(before)|set(after)):
  old,new=before.get(r),after.get(r)
  if old!=new:changes.append({'path':r,'old_text':old,'new_text':new,'old_sha256':None if old is None else sha(old),'new_sha256':None if new is None else sha(new)})
 removed=[r for r in before if r not in after];require(set(removed)=={rel(m)for m in NAMES[:-1]},'Unexpected source deletion')
 consumers={m:sorted(r for r,s in before.items()if m in IM.findall(s)and r not in {rel(x)for x in NAMES})for m in NAMES}
 obsolete=[]
 for m in NAMES[:-1]:
  stem=Path(*m.split('.'))
  for base in [L/'.lake/build/lib/lean',L/'.lake/build/ir']:
   parent=base/stem.parent
   if parent.is_dir():obsolete.extend({'path':str(p),'bytes':p.stat().st_size,'action':'report only; NOT deleted'}for p in sorted(parent.glob(stem.name+'.*'))if p.is_file())
 receipt={'format':'r1914-five-module-merge-application-v1','status':'PREPARED ONLY','prepared_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'project':str(P),'changes':changes,'members':NAMES,'destination':DEST,'module_map':mapping,'external_imports':external,'external_direct_consumers_before':consumers,'source_files_retired':sorted(removed),'body_sha256':{m:sha(body(before[rel(m)]))for m in NAMES},'merged_nonimport_body_exact':True,'named_instance_preserved':True,'original_audit_names_exact':6306,'quotient_acyclic':True,'pilot_evidence':{n:record(pilot/n)for n in ['manifest.json','summary.json','measurements.json']},'pilot_medians_seconds':{'split':split,'merged':merged},'median_reduction_fraction':reduction,'required_reduction_fraction':.35,'root_execution_state':record(a.execution_state),'root_idle_confirmed':True,'obsolete_generated_artifacts':obsolete,'generated_artifacts_removed':False,'no_Lean_Lake_invoked':True,'archive_dir':str(a.archive_dir.resolve()),'reviewer_compatibility':'changes entries path/old_text/new_text/old_sha256/new_sha256; deletion has null new_text/new_sha256. Exact expected_merge algorithm from r1914-final-source-review.py.'}
 if not a.apply:
  write_new(a.proposal_output,receipt);print(json.dumps({'status':'PREPARED ONLY','proposal':str(a.proposal_output),'changed_sources':len(changes),'retired_sources':len(removed),'median_reduction_fraction':reduction}));return
 archive=a.archive_dir.resolve();require(A.resolve()in archive.parents,'Archive must be beneath designated R1914 archive')
 require(not archive.exists(),'Refusing to overwrite archive');require(not a.receipt.exists(),'Refusing to overwrite application receipt')
 require(a.receipt.resolve().parent==(P/'verification').resolve(),'Application receipt must be in project verification directory')
 require(read(a.execution_state).get('live_handles')==[],'Root acquired live handles before apply')
 require(snapshot()==before,'Sources changed during application preparation')
 archive.mkdir(parents=True)
 write_new(archive/'old-sources.json',{c['path']:c['old_text']for c in changes if c['old_text']is not None})
 write_new(archive/'module-map.json',mapping);write_new(archive/'obsolete-generated-artifacts.json',obsolete)
 write_new(archive/'prepared-application.json',receipt)
 for c in changes:
  if c['old_text']is not None:
   p=archive/'sources'/c['path'];p.parent.mkdir(parents=True,exist_ok=True)
   with p.open('x')as f:f.write(c['old_text'])
   require(p.read_text()==c['old_text'],f'Archive verification failed:{p}')
 require(read(archive/'old-sources.json')=={c['path']:c['old_text']for c in changes if c['old_text']is not None},'Archived original inventory mismatch')
 # New/modified sources first, retire only the four exact archived old sources last.
 for c in changes:
  if c['new_text']is None:continue
  path=P/c['path'];require(path.read_text()==c['old_text'],'Source changed before write')
  fd,tmp=tempfile.mkstemp(prefix='.'+path.name+'.r1914-',dir=path.parent)
  try:
   os.chmod(tmp,path.stat().st_mode & 0o777)
   with os.fdopen(fd,'w')as f:f.write(c['new_text'])
   os.replace(tmp,path)
  finally:
   if Path(tmp).exists():Path(tmp).unlink()
 for c in changes:
  if c['new_text']is not None:continue
  path=P/c['path'];require(path.read_text()==c['old_text'],'Retired source changed before removal');path.unlink()
 require(snapshot()==after,'Applied sources differ from exact prepared merge')
 receipt['status']='APPLIED; NORMAL BUILD AND TYPE/AXIOM AUDIT STILL REQUIRED';receipt['applied_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 receipt['final_source_sha256']={r:sha(s)for r,s in sorted(after.items())}
 write_new(a.receipt,receipt);write_new(archive/'applied-receipt.json',receipt)
 print(json.dumps({'status':receipt['status'],'receipt':str(a.receipt),'archive':str(archive),'changes':len(changes),'retired_sources':len(removed),'obsolete_generated_artifacts_reported':len(obsolete),'generated_artifacts_deleted':0}))
if __name__=='__main__':main()
