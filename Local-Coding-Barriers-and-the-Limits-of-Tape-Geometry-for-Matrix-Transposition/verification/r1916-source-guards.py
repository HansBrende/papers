#!/usr/bin/env python3
"""Compact read-only R1916 source/proposal/provenance closure; no Lean execution.
This checks reviewed source contracts, not every exported elaborated Expr type.
"""
from pathlib import Path
import argparse,hashlib,json,re
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition');V=P/'verification'
A=Path('/Users/hansbrende/Documents/Codex/2026-10-09/a/research/10-linear-decision/archive/r1916-strengthening-reuse')
def read(p):return json.loads(p.read_text())
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def filehash(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def record(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':filehash(p)}
legacy=V/'r1915-preservation-tools/source-guards.py';scope={'__name__':'r1916_reused_static_guard','__file__':str(legacy)}
exec(compile(legacy.read_text(),str(legacy),'exec'),scope)
clean,body,FAMILIES,MODELS=[scope[x] for x in ['clean','body','FAMILIES','MODELS']]
MUTABLE={'README.md','paper/verified-results.txt','verification/progress.txt'}
NEW={
 'TransposeFollowup.AffineMotion.AffineTimeRequired.not_pointwise_affine_approximation',
 'TransposeFollowup.AffineMotion.no_subsequential_physical_pointwise_affine_fast_approximation',
 'TransposeFollowup.RecodedXorCode.broadcast_bound_of_ball_budget_real',
 'TransposeFollowup.RecodedXorCode.linear_ball_error_le_sqrt',
 'TransposeFollowup.RecodedXorCode.linear_ball_broadcast_lower_bound',
 'TransposeFollowup.RecodedXorCode.subcycle_broadcast_lower_bound',
 'TransposeFollowup.FinitePortBinding.embed_bank_project'}
def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=V/'r1916-source-guards.json');args=parser.parse_args()
 before=read(A/'baseline-sources.json');old=read(A/'before-receipt.json')
 assert {r:sha(t) for r,t in before.items()}==old['source_sha256']
 expected=dict(before);proposals=[];changed_math=[]
 for folder,key in [('affine-proposal','changes'),('xor-proposal','files'),('embedding-proposal','changes')]:
  path=A/folder/'proposal.json';proposal=read(path)
  for row in proposal[key]:
   rel=row['path'];assert rel not in changed_math
   before_sha=row.get('before_sha256',row.get('old_sha256'));after_sha=row.get('after_sha256',row.get('new_sha256'))
   assert sha(expected[rel])==before_sha,(folder,rel,'baseline')
   if 'old_text' in row:assert expected[rel]==row['old_text']
   assert sha(row['new_text'])==after_sha
   expected[rel]=row['new_text'];changed_math.append(rel)
  proposals.append({'kind':folder,'proposal':record(path),'files':len(proposal[key])})
 paths=[*(P/'lean/TransposeFollowup').rglob('*.lean'),*(P/'lean/FixedTapeCompiler').rglob('*.lean'),P/'lean/SupportAxioms.lean']
 after={str(p.relative_to(P)):p.read_text() for p in paths};assert set(after)==set(before)
 assert len(changed_math)==8
 for rel,t in expected.items():
  if rel!='lean/SupportAxioms.lean':assert after[rel]==t,('unreviewed change or repair',rel)
 actual_changed=sorted(r for r in before if before[r]!=after[r]);assert set(actual_changed)==set(changed_math)|{'lean/SupportAxioms.lean'}
 oldnames=re.findall(r'^#print axioms (\S+)\s*$',clean(before['lean/SupportAxioms.lean']),re.M)
 names=re.findall(r'^#print axioms (\S+)\s*$',clean(after['lean/SupportAxioms.lean']),re.M)
 assert oldnames==old['verified_declarations'] and len(oldnames)==6306
 assert names[:len(oldnames)]==oldnames and len(names)==len(set(names))==6313
 assert set(names)-set(oldnames)==NEW
 preserved={}
 for family,modules in FAMILIES.items():
  if family in ['nonlinear_row_fixed_xor','affine_motion']:continue
  for module in modules:
   rel='lean/TransposeFollowup/'+module+'.lean';assert before[rel]==after[rel]
   preserved[rel]={'family':family,'source_sha256':sha(after[rel])}
 for module in MODELS:
  rel='lean/'+module+'.lean';assert before[rel]==after[rel]
  preserved[rel]={'family':'shared_model','source_sha256':sha(after[rel])}
 forbidden=set('sorry admit axiom unsafe native_decide implemented_by extern trustLevel addDecl addAndCompile mkAxiom mkSorry setEnv run_meta elab_rules initialize syntax macro_rules elab run_tac'.split())
 opts={};before_opts={};G={}
 for rel,t in after.items():
  s=clean(t);assert not set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',s))&forbidden,rel
  settings=re.findall(r'^\s*set_option\s+(.+)$',s,re.M);assert all(x.strip()=='autoImplicit false' for x in settings),(rel,settings)
  for opt in settings:opts[opt.strip()]=opts.get(opt.strip(),0)+1
  for opt in re.findall(r'^\s*set_option\s+(.+)$',clean(before[rel]),re.M):before_opts[opt.strip()]=before_opts.get(opt.strip(),0)+1
  module=rel.removeprefix('lean/').removesuffix('.lean').replace('/','.')
  G[module]=re.findall(r'^import (\S+)\s*$',s,re.M)
 assert opts==before_opts
 color={}
 def visit(m):
  assert color.get(m)!=1,('cycle',m)
  if color.get(m)==2:return
  color[m]=1
  for n in G[m]:
   if n in G:visit(n)
   else:assert not n.startswith(('TransposeFollowup.','FixedTapeCompiler.')),('missing local import',m,n)
  color[m]=2
 for m in G:visit(m)
 for key in ['configuration_sha256','external_source_sha256']:
  for rel,h in old[key].items():
   path=Path(rel);path=path if path.is_absolute() else P/path;assert filehash(path)==h,(key,rel)
 upstream=read(V/'upstream-baseline.json');U=P.parent/upstream['directory']
 assert {str(f.relative_to(U)):filehash(f) for f in U.rglob('*') if f.is_file()}==upstream['files']
 assert sorted(str(f.relative_to(U)) for f in U.rglob('*') if f.is_dir())==upstream['directories']
 for rel,h in old['log_sha256'].items():
  if rel not in MUTABLE:assert filehash(P/rel)==h,('prior immutable evidence',rel)
 # Current summaries remain original at this pre-publication stopping point.
 for rel in MUTABLE:assert filehash(P/rel)==old['log_sha256'][rel],('summary already changed; verify archived original before rerunning',rel)
 affine=read(V/'r1916-affine-xor-review.json');assert affine['status']=='passed'
 for row in affine['sources']:assert sha(after[row['path']])==row['after_sha256']
 embedding=read(V/'r1916-embedding-independent-review.json')
 assert embedding['status'] in ['source_review_passed_compile_pending','source_review_passed_compile_passed','passed']
 for row in embedding['rows']:assert sha(after[row['path']])==row['new_sha256']
 runs=[]
 for label in ['affine-check','xor-check','xor-old-statements','embedding-check-v2']:
  timing=V/f'r1916-{label}-timing.json';log=V/f'r1916-{label}.log';run=read(timing)
  assert run['exit_code']==0 and 'error:' not in log.read_text(),label
  runs.append({'label':label,'timing':record(timing),'log':record(log)})
 before_loc=sum(len(s.splitlines()) for r,s in before.items() if r!='lean/SupportAxioms.lean')
 after_loc=sum(len(s.splitlines()) for r,s in after.items() if r!='lean/SupportAxioms.lean')
 assert before_loc==105741 and after_loc-before_loc==51
 result={'format':'r1916-reviewed-source-provenance-guards-v1','status':'passed','baseline_sources':record(A/'baseline-sources.json'),'before_receipt':record(A/'before-receipt.json'),'proposals':proposals,'exact_proposal_replay':True,'explicit_proof_repairs':[],'source_sha256':{r:sha(t) for r,t in sorted(after.items())},'changed_math_files':sorted(changed_math),'changed_files':actual_changed,'added_files':[],'removed_files':[],'local_sources':len(after),'mathematical_modules':len(after)-1,'baseline_math_lines':before_loc,'final_math_lines':after_loc,'net_math_lines':after_loc-before_loc,'original_audit_names':len(oldnames),'current_audit_names':len(names),'old_audit_order_preserved':True,'new_audit_names':sorted(NEW),'new_proved_declarations':5,'preexisting_newly_audited_declarations':2,'four_unaffected_families_and_shared_models_exact':preserved,'shared_model_sources':len(MODELS),'local_import_graph_acyclic':True,'forbidden_tokens_found':[],'permitted_options':opts,'configuration_files':len(old['configuration_sha256']),'external_files':len(old['external_source_sha256']),'protected_original_files':len(upstream['files']),'prior_receipt_logs':len(old['log_sha256']),'immutable_prior_logs':len(old['log_sha256'])-len(MUTABLE),'original_mutable_summary_hashes':{r:old['log_sha256'][r] for r in sorted(MUTABLE)},'mutable_summary_policy':'These three summaries are still byte-exact here; publication may update them only after archiving their original bytes/hashes.','scoped_independent_reviews':[record(V/'r1916-affine-xor-review.json'),record(V/'r1916-affine-xor-review.txt'),record(V/'r1916-embedding-independent-review.json'),record(V/'r1916-embedding-independent-review.py')],'successful_scoped_runs':runs,'reused_parser':record(legacy),'guard':record(Path(__file__)),'no_Lean_executed_by_guard':True,'full_exported_Expr_types_compared':False,'limitation':'Reviewed source/proof-body preservation and explicit strengthening evidence; not a new full exported-type AST comparison or whole-environment kernel replay. Full build and complete axiom audit are separate final gates.'}
 with args.output.open('x') as out:json.dump(result,out,indent=2);out.write('\n')
 print(json.dumps({k:result[k] for k in ['status','local_sources','mathematical_modules','baseline_math_lines','final_math_lines','net_math_lines','original_audit_names','current_audit_names','immutable_prior_logs']}))
if __name__=='__main__':main()
