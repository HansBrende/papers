#!/usr/bin/env python3
"""Assemble a compact, explicit type-preservation receipt. Never runs Lean.
Exact matches need no second proof. Every mismatch needs actual successful kernel
output; optional archived-source-header checks are distinguished, never silently
substituted for old-Expr conversion. Raw comparison files remain unchanged.
"""
from pathlib import Path
import argparse,hashlib,json,re
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--capture',type=Path,default=Path('/private/tmp/r1915-preservation/capture'));p.add_argument('--plan',type=Path);p.add_argument('--execution',type=Path);p.add_argument('--log',type=Path);p.add_argument('--source-headers',type=Path);p.add_argument('--output',type=Path);a=p.parse_args();C=a.capture
read=lambda p:json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rec(p):return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':sha(p)}
comparison=read(C/'comparison.json')
for key,file in [('baseline','baseline-compact.json'),('final','final-compact.json'),('differences','differences.json')]:
 expected=comparison[key];actual=rec(C/file)
 assert all(actual[k]==expected[k] for k in ['path','bytes','sha256']),('comparison input changed',key)
different=read(C/'differences.json')['differences'];target_names=[r['name'] for r in different];assert len(target_names)==len(set(target_names))==comparison['raw_different']
assert comparison['original_declarations']==comparison['raw_identical']+comparison['raw_different']==6306
checks={};inputs=[];outputs=[];header_rows={};extras={};counts={'original_expr_kernel':0,'archived_source_header_kernel':0}
if different:
 assert comparison['status']=='differences_require_review' and a.execution and a.log
 plan_path=a.plan or C/'kernel/plan.json';plan=read(plan_path);checker=Path(plan['checker'])
 assert sha(checker)==plan['checker_sha256'] and sha(C/'comparison.json')==plan['comparison_sha256']
 assert plan['names']==target_names and plan['kernel_targets']==len(different)
 execution=read(a.execution);assert execution['exit_code']==0 and str(checker) in execution['command']
 log=a.log.read_text();assert not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)',log)
 assert sum('R1915 kernel conversion chunk passed:' in s for s in log.splitlines())==len(plan['chunks'])
 if plan.get('source_headers'):
  assert a.source_headers and rec(a.source_headers)==plan['source_headers']
 if plan.get('prior_attempt'):
  prior=plan['prior_attempt'];assert prior['status']=='failed_preserved'
  def verify_prior(value):
   if isinstance(value,dict):
    if {'path','bytes','sha256'}<=value.keys():assert rec(Path(value['path']))==value
    else:
     for child in value.values():verify_prior(child)
   elif isinstance(value,list):
    for child in value:verify_prior(child)
  verify_prior(prior);assert read(Path(prior['execution']['path']))['exit_code']!=0
  extras['prior_attempt']=prior
 if a.source_headers:
  headers=read(a.source_headers);baseline=read(C/'baseline-sources.json');checker_text=checker.read_text()
  assert headers['checker_sha256']==sha(checker) and headers['baseline_inventory_sha256']==sha(C/'baseline-sources.json')
  header_rows={r['name']:r for r in headers['declarations']};assert len(header_rows)==len(headers['declarations'])==headers['count'] and set(header_rows)<=set(target_names)
  for n,r in header_rows.items():
   source=baseline[r['baseline_source']];header=r['original_header'];old=n.rsplit('.',1)[1];new=r['auditor_declaration'].rsplit('.',1)[1]
   assert hashlib.sha256(source.encode()).hexdigest()==r['baseline_source_sha256']
   assert source.count(header)==1 and hashlib.sha256(header.encode()).hexdigest()==r['original_header_sha256']
   assert header.startswith('theorem '+old+' ') and header.replace('theorem '+old+' ','theorem '+new+' ',1)==r['renamed_header']
   assert r['renamed_header']+' := by\n' in r['source_check_text'] and checker_text.count(r['source_check_text'])==1
   assert hashlib.sha256(r['source_check_text'].encode()).hexdigest()==r['source_check_text_sha256']
  extras['exact_source_headers']=rec(a.source_headers)
 expected={r['name']:r for r in different}
 for chunk in plan['chunks']:
  ip=Path(chunk['input']);op=Path(chunk['output']);assert sha(ip)==chunk['input_sha256'];transport=read(ip);out=read(op)
  assert transport['comparisonSHA256']==out['comparisonSHA256']==sha(C/'comparison.json')
  assert transport['decoderSHA256']==out['decoderSHA256']==plan['reused_parser_sha256']
  rows=transport['declarations'];assert transport['expectedDeclarations']==len(rows)<=8 and rows
  assert [r['name'] for r in rows]==chunk['names']==[r['name'] for r in out['results']]
  assert out['status']=='passed' and out['checked_declarations']==len(rows) and out['input']==str(ip)
  assert out['kernel_positive_and_negative_controls'] is True
  for row,check in zip(rows,out['results']):
   n=row['name'];assert n not in checks and n in expected;b=expected[n]['baseline'];f=expected[n]['final']
   assert row['baselineRepr']==b['type'] and row['currentRepr']==f['type']
   assert row['levelParams']==row['currentLevelParams']==check['levelParams']==b['levelParams']==f['levelParams']
   for text,prefix in [(b['type'],'baseline'),(f['type'],'current')]:assert hashlib.sha256(text.encode()).hexdigest()==row[prefix+'ReprSHA256']==check[prefix+'ReprSHA256']
   for flag in ['original_repr_roundtrip_exact','current_repr_matches_final_capture','ordered_universe_parameters_exact']:assert check[flag] is True
   if n in header_rows:
    assert check['validation_route']=='archived_source_header_kernel' and check['kernel_identity_application_checked'] is False and check['original_source_header_kernel_checked'] is True and check['auditor_declaration']==header_rows[n]['auditor_declaration']
   else:
    assert check['validation_route']=='original_expr_kernel' and check['kernel_identity_application_checked'] is True and check['original_source_header_kernel_checked'] is False and check['auditor_declaration'] is None
   counts[check['validation_route']]+=1;checks[n]=check
  inputs.append(rec(ip));outputs.append(rec(op))
 assert set(checks)==set(target_names)
 extras.update({'plan':rec(plan_path),'checker':rec(checker),'execution':rec(a.execution),'log':rec(a.log),'inputs':inputs,'outputs':outputs})
else:assert comparison['status']=='exact' and not a.source_headers
result={'format':'r1915-type-preservation-v1','status':'passed','original_declarations':6306,'raw_identical':comparison['raw_identical'],'raw_different':len(different),'original_expr_kernel_conversions':counts['original_expr_kernel'],'archived_source_header_checks':counts['archived_source_header_kernel'],'raw_comparison':rec(C/'comparison.json'),'checks':checks,**extras,'claim':'Every original audited declaration contract is retained, with raw-identical, original-Expr kernel conversion and separately proven archived source-header routes explicitly distinguished. This receipt does not replace model-definition/source preservation or the axiom audit.'}
outpath=a.output or C/'type-preservation.json'
with outpath.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
print(outpath)
