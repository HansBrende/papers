#!/usr/bin/env python3
"""Post-publication R1916 receipt validation; read-only except result JSON.
No Lean, full type capture, archive expansion, or proof replay is performed.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,re
P=Path('.');V=P/'verification'
A=Path('external/research-workspace/research/10-linear-decision/archive/r1916-strengthening-reuse')
MUTABLE={'README.md','paper/verified-results.txt','verification/progress.txt'}
EXCLUDED={'verification/r1916-in-progress.json','verification/r1916-final-receipt-check.json'}
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify_record(r):
 p=Path(r['path']);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],r['path']
def verify_records(x):
 if isinstance(x,dict):
  if {'path','bytes','sha256'} <= x.keys():verify_record(x)
  else:
   for y in x.values():verify_records(y)
 elif isinstance(x,list):
  for y in x:verify_records(y)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=V/'r1916-final-receipt-check.json');args=p.parse_args()
 receipt=read(V/'support-build.json');old=read(A/'before-receipt.json');guard=read(V/'r1916-source-guards.json');completion=read(V/'r1916-completion.json');state=read(V/'r1916-in-progress.json')
 assert completion['checkpoint']=='R1916' and completion['status']=='complete'
 assert guard['status']=='passed' and not state['live_handles'] and completion['no_live_execution_handles']
 assert state['status']=='R1916 complete'
 assert len({x['session'] for x in state['terminal_handles']})==len(state['terminal_handles'])
 assert all(isinstance(x.get('exit_code'),int) for x in state['terminal_handles'])
 sources=[*(P/'lean/TransposeFollowup').rglob('*.lean'),*(P/'lean/FixedTapeCompiler').rglob('*.lean'),P/'lean/SupportAxioms.lean']
 hashes={str(f.relative_to(P)):sha(f) for f in sources}
 assert hashes==receipt['source_sha256']==guard['source_sha256']
 assert len(hashes)==completion['source_files']==guard['local_sources']==889
 for key in ['configuration_sha256','external_source_sha256']:
  assert receipt[key]==old[key]
  for rel,h in receipt[key].items():
   path=Path(rel);path=path if path.is_absolute() else P/path;assert sha(path)==h,(key,rel)
 for rel,h in receipt['log_sha256'].items():assert sha(P/rel)==h,rel
 assert not EXCLUDED & set(receipt['log_sha256'])
 assert len(old['log_sha256'])==586
 for rel,h in old['log_sha256'].items():
  if rel in MUTABLE:assert sha(A/'before'/rel)==h,('old summary backup',rel)
  else:assert receipt['log_sha256'].get(rel)==h and sha(P/rel)==h,('immutable prior log',rel)
 for path in V.glob('r1916-*'):
  if path.is_file() and str(path.relative_to(P)) not in EXCLUDED:
   assert receipt['log_sha256'].get(str(path.relative_to(P)))==sha(path),('unreceipted R1916 evidence',str(path))
 verify_records(guard)
 scoped=read(V/'r1916-affine-xor-review.json');assert scoped['status']=='passed';verify_records(scoped)
 plan=read(V/'r1916-xor-old-statements.json');verify_record(plan['baseline_sources']);verify_record(plan['current_source']);verify_record(plan['checker'])
 assert len(plan['checks'])==5
 embedding=read(V/'r1916-embedding-independent-review.json')
 assert len([r for r in embedding['rows'] if 'replacement_count' in r])==4
 assert sum(r.get('replacement_count',0) for r in embedding['rows'])==13
 for r in embedding['rows']:assert hashes[r['path']]==r['new_sha256']
 upstream=read(V/'upstream-baseline.json');U=P.parent/upstream['directory']
 assert {str(f.relative_to(U)):sha(f) for f in U.rglob('*') if f.is_file()}==upstream['files']
 assert sorted(str(f.relative_to(U)) for f in U.rglob('*') if f.is_dir())==upstream['directories']
 names=re.findall(r'^#print axioms (\S+)\s*$',(P/'lean/SupportAxioms.lean').read_text(),re.M)
 assert names==receipt['verified_declarations'] and len(names)==len(set(names))==6313
 assert len(old['verified_declarations'])==6306 and names[:6306]==old['verified_declarations']
 assert set(names[6306:])==set(guard['new_audit_names'])
 claims={'original_audit_names_retained':6306,'audited_declarations':6313,'new_declarations':5,'prior_unaudited_names_added':2,'embedding_proofs_reused':13,'embedding_net_lines_removed':30,'source_lines_before':105741,'source_lines_after':105792,'net_source_lines':51}
 for k,v in claims.items():assert completion[k]==v,(k,completion[k])
 assert completion['all_six_main_targets_preserved'] and completion['strengthened_families']==[2,3] and completion['unchanged_families']==[1,4,5,6]
 assert completion['changed_files']==guard['changed_files'] and len(completion['changed_files'])==9
 assert set(x['family'] for x in guard['four_unaffected_families_and_shared_models_exact'].values())=={'adaptive_separator_treewidth','paid_padding','two_stage_helper','scan_and_recursion','shared_model'}
 assert len([x for x in guard['four_unaffected_families_and_shared_models_exact'].values() if x['family']=='shared_model'])==11
 assert sum(len(f.read_text().splitlines()) for f in sources if f.name!='SupportAxioms.lean')==105792
 for key,label in [('full_build','full-build'),('axiom_audit','final-axioms')]:
  timing=read(V/f'r1916-{label}-timing.json');assert timing==completion[key] and timing['exit_code']==0
  assert datetime.datetime.fromisoformat(timing['finished_at']).timestamp()>=max(f.stat().st_mtime for f in sources)
 axiomlog=(V/'r1916-final-axioms.log').read_text();found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",axiomlog);none=re.findall(r"'([^']+)' does not depend on any axioms",axiomlog)
 assert len(found)+len(none)==6313 and {n for n,_ in found}|set(none)==set(names)
 assert all({a.strip() for a in row.split(',') if a.strip()} <= set(old['allowed_axioms']) for _,row in found)
 assert guard['full_exported_Expr_types_compared'] is False
 result={'format':'r1916-final-receipt-validation-v1','status':'passed','checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_files':889,'audit_declarations':6313,'original_audit_declarations':6306,'new_declarations':5,'prior_unaudited_names_added':2,'net_math_lines':51,'all_six_families_preserved':True,'three_mutable_original_backups_verified':True,'prior_immutable_logs_verified':583,'receipt_logs_verified':len(receipt['log_sha256']),'current_sources_pins_external_sibling_and_evidence_hashes_verified':True,'scoped_reviews_and_guard_provenance_verified':True,'no_live_execution_handles':True,'no_Lean_executed':True,'full_exported_Expr_comparison_performed':False,'receipt_sha256':sha(V/'support-build.json'),'validator_sha256':sha(Path(__file__))}
 with args.output.open('x') as out:json.dump(result,out,indent=2);out.write('\n')
 print(json.dumps(result))
if __name__=='__main__':main()
