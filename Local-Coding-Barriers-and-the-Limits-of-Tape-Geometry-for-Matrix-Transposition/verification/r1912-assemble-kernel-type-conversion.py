#!/usr/bin/env python3
"""Assemble conversion evidence only after root's Lean execution succeeds.
No Lean execution; no proof source changes. Raw comparison remains immutable.
"""
from pathlib import Path
import argparse,hashlib,json,re,datetime
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition'); V=P/'verification'
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--comparison',type=Path,default=V/'r1912-type-comparison.json')
ap.add_argument('--inventory',type=Path,default=Path('/private/tmp/r1912-original-types-ast-chunks/inventory.json'))
ap.add_argument('--checker',type=Path,default=Path('/private/tmp/r1912-kernel-type-checker-v2.lean'))
ap.add_argument('--output-dir',type=Path,default=Path('/private/tmp/r1912-kernel-type-conversion-v2'))
ap.add_argument('--source-headers',type=Path,default=Path('/private/tmp/r1912-source-header-checks.json'))
ap.add_argument('--lean-log',type=Path,required=True)
ap.add_argument('--execution-record',type=Path,required=True,help='Root timing/execution JSON containing exit_code=0')
ap.add_argument('--output',type=Path,default=Path('/private/tmp/r1912-kernel-type-conversion.json'))
a=ap.parse_args()
def unique(pairs):
 d={}
 for k,v in pairs:
  assert k not in d,('duplicate key',k);d[k]=v
 return d
def read(p):return json.loads(p.read_text(),object_pairs_hook=unique)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def record(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
raw=read(a.comparison);inv=read(a.inventory);exec_record=read(a.execution_record)
assert exec_record['exit_code']==0,'Kernel checker execution did not complete successfully'
log=a.lean_log.read_text();assert not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)',log)
assert raw['status']=='failed' and raw['different_declarations']==269
assert all(raw[k]==6297 for k in ['expected_original_declarations','baseline_declarations','final_declarations'])
names=[r['name'] for r in raw['mismatches']];assert len(names)==len(set(names))==269
assert all(r['levelParams_equal'] is True and r['type_equal'] is False for r in raw['mismatches'])
assert inv['declarations']==269 and len(inv['chunks'])==34
assert sha(Path(inv['source']))==inv['sourceSHA256']
compact={side:read(Path(raw['compact_outputs'][side]))['types'] for side in ['baseline','final']}
assert all(len(v)==6297 for v in compact.values())
headers=read(a.source_headers);assert headers['count']==len(headers['declarations'])==2
assert headers['checker_sha256']==sha(a.checker)
baseline_sources=read(Path(headers['baseline_inventory']));assert sha(Path(headers['baseline_inventory']))==headers['baseline_inventory_sha256']
header_names={r['name']:r for r in headers['declarations']}
assert set(header_names)=={'TransposeFollowup.NativePaddedField.tail_trace','TransposeFollowup.CountedFill.emit_step'}
checker_text=a.checker.read_text()
for n,r in header_names.items():
 source=baseline_sources[r['baseline_source']];assert hashlib.sha256(source.encode()).hexdigest()==r['baseline_source_sha256']
 original_header=r['original_header'];assert source.count(original_header)==1
 assert hashlib.sha256(original_header.encode()).hexdigest()==r['original_header_sha256']
 old_name=n.rsplit('.',1)[1];new_name=r['auditor_declaration'].rsplit('.',1)[1]
 assert original_header.replace('theorem '+old_name+' ','theorem '+new_name+' ',1)==r['renamed_header']
 assert r['renamed_header'] in r['source_check_text'] and checker_text.count(r['source_check_text'])==1
 assert hashlib.sha256(r['source_check_text'].encode()).hexdigest()==r['source_check_text_sha256']
checks={};input_records=[];output_records=[]
for i,chunk in enumerate(inv['chunks']):
 assert chunk['index']==i
 path=Path(chunk['path']);assert sha(path)==chunk['sha256'] and path.stat().st_size==chunk['bytes']
 transport=read(path);rows=transport['declarations']
 assert transport['comparisonSHA256']==sha(a.comparison)
 assert transport['expectedDeclarations']==len(rows)<=8 and rows
 assert [r['name'] for r in rows]==chunk['declarations']
 out=a.output_dir/f'r1912-kernel-type-conversion-{i:03d}.json';result=read(out)
 assert result['format']=='r1912-kernel-type-conversion-chunk-v1' and result['status']=='passed'
 assert result['checked_declarations']==len(rows) and result['input']==str(path)
 assert result['kernel_positive_and_negative_controls'] is True
 assert result['comparisonSHA256']==transport['comparisonSHA256'] and result['decoderSHA256']==transport['decoderSHA256']
 assert [r['name'] for r in result['results']]==chunk['declarations']
 for old,check in zip(rows,result['results']):
  n=old['name'];assert n not in checks and n in names
  for key in ['original_repr_roundtrip_exact','current_repr_matches_final_capture','ordered_universe_parameters_exact']:
   assert check[key] is True,(n,key)
  if n in header_names:
   assert check['validation_route']=='archived_source_header_kernel'
   assert check['kernel_identity_application_checked'] is False and check['original_source_header_kernel_checked'] is True
   assert check['auditor_declaration']==header_names[n]['auditor_declaration']
  else:
   assert check['validation_route']=='original_expr_kernel'
   assert check['kernel_identity_application_checked'] is True and check['original_source_header_kernel_checked'] is False
   assert check['auditor_declaration'] is None
  for side,field,prefix in [('baseline','baselineRepr','baseline'),('final','currentRepr','current')]:
   text=old[field];encoded=text.encode('utf-8');h=hashlib.sha256(encoded).hexdigest()
   assert old[prefix+'ReprSHA256']==check[prefix+'ReprSHA256']==h==compact[side][n]['type_sha256']
   assert len(encoded)==compact[side][n]['type_utf8_bytes'] and len(text)==compact[side][n]['type_characters']
  assert old['levelParams']==old['currentLevelParams']==check['levelParams']==compact['baseline'][n]['levelParams']==compact['final'][n]['levelParams']
  checks[n]=check
 input_records.append(record(path));output_records.append(record(out))
assert set(checks)==set(names) and sum('R1912 kernel conversion chunk passed:' in line for line in log.splitlines())==34
out={'format':'r1912-kernel-type-conversion-v1','status':'passed','finished_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'original_declarations':6297,'raw_identical_declarations':6028,'raw_different_declarations':269,'kernel_converted_declarations':267,'source_header_checked_declarations':2,
 'method':'Reconstruct original Expr from explicit AST; require exact repr roundtrip and exact current capture, same ordered universe parameters; for267 native Lean.Kernel.check in an empty local context checks (fun h : originalType => h) currentConstant. For2 types with retired generated proof constants, exact archived source headers (only auditor identifier changed) are re-elaborated and proved by direct application of the current theorem, then independently checked by native kernel identity application. Positive and deliberately ill-typed negative controls required in each of 34 chunks. No axioms or aliases added;2 ordinary scratch theorems certify the archived source headers. Proof library and configurations unchanged.',
 'claim':'6028 original exported types are literally unchanged in saved representations; 267 are kernel-definitionally equal to the exact original Expr;2 retired generated-proof cases preserve the exact archived source statements by ordinary kernel-checked proofs. Exact original/current Expr provenance retained for all269. Raw literal comparison remains failed with 269 differences.',
 'declarations':names,'checks':checks,'exact_source_headers':record(a.source_headers),'raw_comparison':record(a.comparison),'checker':record(a.checker),'input_inventory':record(a.inventory),'input_chunks':input_records,'output_chunks':output_records,'lean_log':record(a.lean_log),'execution_record':record(a.execution_record),'archive':None}
a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(a.output)
