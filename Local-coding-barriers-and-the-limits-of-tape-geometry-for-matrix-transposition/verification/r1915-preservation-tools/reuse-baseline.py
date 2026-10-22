#!/usr/bin/env python3
"""Bind the verified R1914 final capture as R1915 baseline; no Lean execution.
Only frozen metadata/source snapshots are read. The current working tree may
contain a benchmark edit. Full raw chunk hashes are rechecked during compare,
not here; no baseline inspection, raw-type copy or archive expansion is needed.
"""
from pathlib import Path
import argparse, datetime, hashlib, importlib.util, json, re, shutil
ROOT = Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition')
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('r1915_types', HERE/'types.py')
t = importlib.util.module_from_spec(spec); spec.loader.exec_module(t)
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--project', type=Path, default=ROOT)
p.add_argument('--baseline-sources', type=Path, required=True)
p.add_argument('--before-receipt', type=Path, required=True)
p.add_argument('--capture', type=Path, default=HERE/'capture')
a = p.parse_args(); P=a.project.resolve(); V=P/'verification'; C=a.capture.resolve()
C.mkdir(parents=True, exist_ok=True)
assert not any(C.iterdir()), 'Refusing to replace a prepared capture'
sources=t.read(a.baseline_sources); receipt=t.read(a.before_receipt)
assert {r:hashlib.sha256(s.encode()).hexdigest() for r,s in sources.items()} == receipt['source_sha256']
audit=sources['lean/SupportAxioms.lean']
names=re.findall(r'^#print axioms (\S+)\s*$', audit, re.M)
assert len(names)==len(set(names))==6306 and names==receipt['verified_declarations']
paths={
 'compact':V/'r1914-final-type-hashes.json',
 'preservation':V/'r1914-type-preservation.json',
 'comparison':V/'r1914-exact-type-comparison.json',
 'source_review':V/'r1914-final-source-review.json',
 'source_guards':V/'r1914-source-guards.json',
 'archive_receipt':V/'r1914-type-archive.json',
}
for path in paths.values():
 rel=str(path.relative_to(P))
 assert t.sha(path)==receipt['log_sha256'][rel], ('Prior completed evidence differs from frozen receipt', rel)
old=t.read(paths['compact']); preservation=t.read(paths['preservation'])
comparison=t.read(paths['comparison']); review=t.read(paths['source_review']); guard=t.read(paths['source_guards'])
assert old['side']=='final' and old['declarations']==6306 and set(old['types'])==set(names)
assert len(old['chunks'])==79 and [n for c in old['chunks'] for n in c['names']]==names
assert preservation['status']=='passed' and preservation['original_declarations']==6306
assert preservation['raw_identical']+preservation['original_expr_kernel_conversions']+preservation['archived_source_header_checks']==6306
assert preservation['raw_comparison']['sha256']==t.sha(paths['comparison'])
assert comparison['final']['sha256']==t.sha(paths['compact'])
assert review['status']=='passed' and review['final_source_sha256']==receipt['source_sha256']==guard['source_sha256']
assert guard['status']=='protected_contracts_and_models_unchanged' and guard['original_audit_names']==guard['current_audit_names']==6306
for key in ['descriptor','inspection_script','frozen_names','execution','log']:t.verify(old[key])
old_descriptor=t.read(old['descriptor']['path']); execution=t.read(old['execution']['path'])
assert execution['exit_code']==0 and old['inspection_script']['path'] in execution['command']
assert old_descriptor['active_audit_sha256']==hashlib.sha256(audit.encode()).hexdigest()
assert [n for c in old_descriptor['chunks'] for n in c['names']]==names
# Copy the exact root-frozen metadata; the currently edited working source is not read.
shutil.copyfile(a.baseline_sources,C/'baseline-sources.json')
shutil.copyfile(a.before_receipt,C/'before-receipt.json')
frozen={'format':'r1915-frozen-audit-names-v1','count':6306,'names':names,'project':str(P),
 'audit_sha256':hashlib.sha256(audit.encode()).hexdigest(),'receipt_sha256':t.sha(C/'before-receipt.json'),
 'baseline_sources_sha256':t.sha(C/'baseline-sources.json'),'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
t.write(C/'names.json',frozen)
reuse={'format':'r1915-reused-verified-baseline-v1','status':'metadata_bound_raw_chunks_pending_comparison',
 'source_round':'R1914','source_side':'final','destination_round':'R1915','destination_side':'baseline',
 'declarations':6306,'raw_chunks':79,'baseline_sources':t.record(C/'baseline-sources.json'),
 'before_receipt':t.record(C/'before-receipt.json'),'frozen_names':t.record(C/'names.json'),
 'prior_evidence':{k:t.record(v) for k,v in paths.items()},
 'prior_capture_provenance':{k:old[k] for k in ['descriptor','inspection_script','frozen_names','execution','log']},
 'full_chunk_verification_deferred_to_exact_comparison':True,'working_tree_sources_read':False,
 'Lean_executed':False,'raw_type_files_copied':False,
 'basis':'Root-frozen source inventory equals the completed R1914 receipt and its final source review/guards. The prior final compact is receipt-bound and is the exact final side of the successfully resolved R1914 comparison. All original audit names and their order are identical. The raw chunks remain immutable references and will be hash-checked and string-compared against the new final capture.'}
t.write(C/'baseline-reuse.json',reuse)
descriptor={'format':'r1915-reused-type-capture-v1','side':'baseline','declarations':6306,'chunk_size':80,
 'chunks':[{'index':r['index'],'path':r['path'],'names':r['names']} for r in old['chunks']],
 'frozen_names':str(C/'names.json'),'frozen_names_sha256':t.sha(C/'names.json'),
 'inspection_script':old['inspection_script']['path'],'inspection_script_sha256':old['inspection_script']['sha256'],
 'audit_imports':old_descriptor['audit_imports'],'active_audit_sha256':frozen['audit_sha256'],
 'reused_prior_descriptor':old['descriptor'],'reuse_receipt':t.record(C/'baseline-reuse.json'),
 'no_aggregate':True,'no_new_baseline_Lean_execution':True}
t.write(C/'baseline-capture.json',descriptor)
compact={**old,'format':'r1915-reused-sealed-type-capture-v1','side':'baseline',
 'descriptor':t.record(C/'baseline-capture.json'),'frozen_names':t.record(C/'names.json'),
 'reused_capture':t.record(paths['compact']),'reuse_receipt':t.record(C/'baseline-reuse.json')}
t.write(C/'baseline-compact.json',compact)
print(json.dumps({'status':'baseline reuse prepared','capture':str(C),'declarations':6306,'raw_chunks':79,
 'baseline_Lean_executed':False,'raw_type_files_copied':False,'working_tree_sources_read':False,
 'raw_chunk_hash_verification':'deferred to final exact comparison'}))
