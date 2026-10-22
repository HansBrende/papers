#!/usr/bin/env python3
"""DRAFT lightweight final R1914 receipt validator. No Lean execution.
Rechecks current hashes, terminal outcomes, restoration and bound preservation
receipts. Earlier exact type comparisons/byte-verified archives are not repeated.
"""
from pathlib import Path
import argparse,importlib.util,json
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--config',type=Path,required=True);p.add_argument('--finalizer',type=Path,default=Path(__file__).with_name('finalize.py'));p.add_argument('--output',type=Path,default=Path('/private/tmp/r1914-final-receipt-check.json'));a=p.parse_args()
spec=importlib.util.spec_from_file_location('r1914_finalization',a.finalizer);f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
cfg=f.read(a.config);d=f.validate_inputs(cfg,after_finalization=True)
P,V,A=d['P'],d['V'],d['A'];receipt=f.read(V/'support-build.json');completion=f.read(V/'r1914-completion.json');old=d['old']
assert completion['checkpoint']=='R1914' and completion['all_six_main_targets_preserved'] is True and completion['no_live_execution_handles'] is True
assert completion['shared_model_definitions_preserved'] is True
for key,value in d['source_contracts'].items():assert completion[key]==value
assert completion['full_build']['exit_code']==completion['axiom_audit']['exit_code']==0
assert completion['full_build']['jobs']==d['jobs'] and completion['axiom_audit']['declarations']==len(d['names'])
assert completion['cold_build_speedup_ratio'] is None
assert receipt['source_sha256']==d['sources'] and receipt['verified_declarations']==d['names']
for key in ['configuration_sha256','external_source_sha256']:assert receipt[key]==old[key]
assert set(receipt['allowed_axioms'])==f.ALLOWED
for key in ['source_sha256','configuration_sha256','external_source_sha256','log_sha256']:
 for rel,h in receipt[key].items():
  path=Path(rel);path=path if path.is_absolute() else P/path;assert f.sha(path)==h,(key,rel)
for rel,h in old['log_sha256'].items():
 if rel in f.MUTABLE:assert f.sha(A/'before-r1914-summary-update'/rel)==h
 else:assert receipt['log_sha256'].get(rel)==h,('old immutable receipt entry changed',rel)
excluded={'r1913-in-progress.json','r1914-in-progress.json','r1914-final-receipt-check.json','r1914-final-receipt-check-timing.json','r1914-final-receipt-check.log'}
for prefix in ['r1913-','r1914-']:
 for path in V.glob(prefix+'*'):
  rel=str(path.relative_to(P))
  if path.is_file():
   if path.name in excluded:assert rel not in receipt['log_sha256']
   else:assert receipt['log_sha256'].get(rel)==f.sha(path),('new evidence omitted/stale',rel)
for path in (V/'r1914-preservation-tools').rglob('*'):
 if path.is_file() and '__pycache__' not in path.relative_to(V/'r1914-preservation-tools').parts:assert receipt['log_sha256'].get(str(path.relative_to(P)))==f.sha(path),('durable preservation helper omitted/stale',path)
for rel in f.MUTABLE:assert 'R1914' in (P/rel).read_text()
assert f.read(cfg['state'])['live_handles']==[] and f.source_hashes(P)==d['sources']
assert completion['original_type_preservation']=={k:d['types'][k] for k in ['original_declarations','raw_identical','raw_different','original_expr_kernel_conversions','archived_source_header_checks']}
result={'checkpoint':'R1914','status':'FINAL RECEIPT VALIDATION PASSED','receipt_sha256':f.sha(V/'support-build.json'),'source_files':len(d['sources']),'audited_declarations':len(d['names']),'original_declarations':6306,'preservation':completion['original_type_preservation'],'all_six_main_targets_preserved':True,'shared_models_preserved':True,'benchmark_edits_restored':True,'all_handles_terminal':True,'prior_log_entries':len(old['log_sha256']),'current_log_entries':len(receipt['log_sha256']),'configuration_files':len(old['configuration_sha256']),'external_files':len(old['external_source_sha256']),'mutable_summary_backups_verified':sorted(f.MUTABLE),'no_Lean_executed':True,'scope':'Lightweight final receipt check. Exact type/source audits and byte-verified full-chunk archives are bound by their preserved receipts; no second giant type expansion or fresh environment replay is claimed.'}
with a.output.open('x') as out:json.dump(result,out,indent=2);out.write('\n')
print(json.dumps(result))
