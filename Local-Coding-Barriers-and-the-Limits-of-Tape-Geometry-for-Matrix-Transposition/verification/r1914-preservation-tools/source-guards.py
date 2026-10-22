#!/usr/bin/env python3
"""Read-only source/contract/receipt guards. No Lean execution or source writes.
A passing guard certifies the listed source contracts and protected dependencies;
it does not substitute for all6306 exported-type checks or the full axiom audit.
Other changed mathematical bodies are listed for explicit proposal-level review.
"""
from pathlib import Path
import argparse,hashlib,json,re
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition')
FAMILIES={
 'adaptive_separator_treewidth':['GraphSeparatorBound','SeparatorSharpness','Treewidth','AdaptiveTreewidth'],
 'nonlinear_row_fixed_xor':['XorComponentCount','XorDegreeBound','XorPathCycleBound'],
 'affine_motion':['CountableAffinePathLabels','OpenAffineTimeBound','AffineTimeScaling','NativeAffineMotion','BoundedAffineCovers','AffineApproximationObstruction','PhysicalAffineApproximationObstruction'],
 'paid_padding':['UnconditionalPaidPadding'],
 'two_stage_helper':['TwoStageRows','TwoStageHelper','TwoStageHelperEntropy'],
 'scan_and_recursion':['MatrixPaletteObstructions','RawMixedBinaryWordObstruction','NativeRegularRecursion','NativeExceptionalRecursion','ExceptionalStageClock']}
MODELS=['TransposeFollowup/MatrixView','TransposeFollowup/RowCode','TransposeFollowup/ProtocolTruncation','TransposeFollowup/FiniteProgramEncodingCore','TransposeFollowup/NativeMicrocodeCore','TransposeFollowup/NativeIOCore','TransposeFollowup/NativeReadFusionCore','TransposeFollowup/NativeIOFusionCore','TransposeFollowup/NativeRunLimits','FixedTapeCompiler/Microcode','FixedTapeCompiler/OperationalTrace']
def read(p):return json.loads(p.read_text())
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def filehash(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def body(s):return re.sub(r'^import [^\n]+\n','',s,flags=re.M)
def clean(s):
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
  if s[i]=='"':string=True;out[i]=' '
  i+=1
 assert depth==0 and not string
 return ''.join(out)
def main():
 global P
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--project',type=Path,default=P);p.add_argument('--capture',type=Path,default=Path('/private/tmp/r1914-preservation/capture'));p.add_argument('--output',type=Path,required=True);a=p.parse_args();P=a.project.resolve()
 C=a.capture;before=read(C/'baseline-sources.json');receipt=read(C/'before-receipt.json');frozen=read(C/'names.json')
 assert filehash(C/'baseline-sources.json')==frozen['baseline_sources_sha256']
 for r,s in before.items():assert sha(s)==receipt['source_sha256'][r]
 paths=[*(P/'lean/TransposeFollowup').rglob('*.lean'),*(P/'lean/FixedTapeCompiler').rglob('*.lean'),P/'lean/SupportAxioms.lean'];after={str(p.relative_to(P)):p.read_text() for p in paths}
 audits=re.findall(r'^#print axioms (\S+)\s*$',clean(after['lean/SupportAxioms.lean']),re.M)
 assert len(audits)==len(set(audits)) and set(frozen['names'])<=set(audits)
 protected={}
 for family,modules in FAMILIES.items():
  for m in modules:protected['lean/TransposeFollowup/'+m+'.lean']=family
 for m in MODELS:protected['lean/'+m+'.lean']='shared_model'
 matches={}
 for r,label in protected.items():
  assert r in before,r
  old=body(before[r]);current_matches=[s for s,t in after.items() if old in body(t)]
  assert len(current_matches)==1,(r,'contract/model body changed or ambiguous',current_matches)
  matches[r]={'family':label,'current_location':current_matches[0],'non_import_body_sha256':sha(old)}
 forbidden=set('sorry admit axiom unsafe native_decide implemented_by extern trustLevel addDecl addAndCompile mkAxiom mkSorry setEnv run_meta elab_rules initialize syntax macro_rules elab run_tac'.split());opts={}
 G={}
 for r,t in after.items():
  s=clean(t);assert not (set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',s))&forbidden),r
  options=re.findall(r'^\s*set_option\s+(.+)$',s,re.M);assert all(x.strip()=='autoImplicit false' for x in options),(r,options)
  for opt in options:opts[opt.strip()]=opts.get(opt.strip(),0)+1
  module=r.removeprefix('lean/').removesuffix('.lean').replace('/','.')
  G[module]=re.findall(r'^import (\S+)\s*$',s,re.M)
 color={}
 def visit(m):
  assert color.get(m)!=1,('import cycle',m)
  if color.get(m)==2:return
  color[m]=1
  for n in G[m]:
   if n in G:visit(n)
   else:assert not n.startswith(('TransposeFollowup.','FixedTapeCompiler.')),('missing local import',m,n)
  color[m]=2
 for m in G:visit(m)
 for key in ['configuration_sha256','external_source_sha256']:
  for r,h in receipt[key].items():
   f=Path(r);f=f if f.is_absolute() else P/f;assert filehash(f)==h,(key,r)
 upstream=read(P/'verification/upstream-baseline.json');U=P.parent/upstream['directory']
 assert {str(f.relative_to(U)):filehash(f) for f in U.rglob('*') if f.is_file()}==upstream['files']
 assert sorted(str(f.relative_to(U)) for f in U.rglob('*') if f.is_dir())==upstream['directories']
 mutable={'README.md','paper/verified-results.txt','verification/progress.txt'}
 for r,h in receipt['log_sha256'].items():
  if r not in mutable:assert filehash(P/r)==h,('immutable historical receipt evidence changed',r)
 changed=[r for r in before.keys()&after.keys() if before[r]!=after[r]]
 result={'format':'r1914-source-preservation-guards-v1','status':'protected_contracts_and_models_unchanged','six_families':FAMILIES,'protected_source_bodies':matches,'original_audit_names':6306,'current_audit_names':len(audits),'new_audit_names':sorted(set(audits)-set(frozen['names'])),'source_sha256':{r:sha(t) for r,t in after.items()},'changed_files':sorted(changed),'changed_non_import_bodies_requiring_proposal_review':sorted(r for r in changed if body(before[r])!=body(after[r])),'added_files':sorted(after.keys()-before.keys()),'removed_files':sorted(before.keys()-after.keys()),'protected_original_files':len(upstream['files']),'configuration_files':len(receipt['configuration_sha256']),'external_files':len(receipt['external_source_sha256']),'immutable_prior_logs':len(receipt['log_sha256'])-len(mutable),'permitted_options':opts,'local_import_graph_acyclic':True,'no_Lean_executed':True,'limitation':'This source guard does not alone certify all exported types or all altered mathematical bodies. Complete exact-type/semantic checks and the normal full build/axiom audit remain required.'}
 with a.output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ['source_sha256','protected_source_bodies','six_families']}))
if __name__=='__main__':main()
