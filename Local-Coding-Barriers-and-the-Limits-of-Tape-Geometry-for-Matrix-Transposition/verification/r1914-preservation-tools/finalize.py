#!/usr/bin/env python3
"""DRAFT R1914 finalizer. Root reviews the evidence config and runs --apply only
when all checks are terminal. No Lean/Lake execution. Without --apply, validates
and prints the report without writing repository files.
"""
from pathlib import Path
import argparse,copy,datetime,hashlib,json,re,statistics
MUTABLE={'README.md','paper/verified-results.txt','verification/progress.txt'}
ALLOWED={'propext','Classical.choice','Quot.sound'}
def read(p):return json.loads(Path(p).read_text())
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def write(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def check_record(r):
 p=Path(r['path']);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],('evidence changed',p)
def evidence_records(x):
 if isinstance(x,dict):
  if {'path','bytes','sha256'}<=x.keys():check_record(x)
  else:
   for y in x.values():evidence_records(y)
 elif isinstance(x,list):
  for y in x:evidence_records(y)
def timing_log(spec):
 timing=read(spec['timing']);assert timing['exit_code']==0
 text=Path(spec['log']).read_text();assert not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)|✖',text)
 return timing,text
def source_hashes(P):
 files=[*(P/'lean/TransposeFollowup').rglob('*.lean'),*(P/'lean/FixedTapeCompiler').rglob('*.lean'),P/'lean/SupportAxioms.lean']
 return {str(f.relative_to(P)):sha(f) for f in files}
def validate_inputs(cfg,after_finalization=False):
 P=Path(cfg['project']);V=P/'verification';C=Path(cfg['capture']);A=Path(cfg['archive']);old=read(C/'before-receipt.json')
 state=read(cfg['state']);assert state['checkpoint']=='R1914' and state['live_handles']==[]
 terminal=state['terminal_handles'];assert len({r['session'] for r in terminal})==len(terminal) and all(isinstance(r['exit_code'],int) for r in terminal)
 full,blog=timing_log(cfg['full_build']);axioms,alog=timing_log(cfg['axiom_audit'])
 match=re.search(r'Build completed successfully \((\d+) jobs\)',blog);assert match; jobs=int(match[1])
 names=re.findall(r'^#print axioms (\S+)\s*$',(P/'lean/SupportAxioms.lean').read_text(),re.M)
 originals=read(C/'names.json')['names'];assert len(originals)==len(set(originals))==6306
 assert len(names)==len(set(names)) and set(originals)<=set(names)
 parsed=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",alog)
 none=re.findall(r"'([^']+)' does not depend on any axioms",alog)
 assert len(parsed)+len(none)==len(names) and {n for n,_ in parsed}|set(none)==set(names)
 assert all({x.strip() for x in ax.split(',') if x.strip()}<=ALLOWED for _,ax in parsed)
 assert set(old['allowed_axioms'])==ALLOWED
 types=read(cfg['types']);assert types['format']=='r1914-type-preservation-v1' and types['status']=='passed'
 assert types['original_declarations']==6306 and types['raw_identical']+types['raw_different']==6306
 assert types['original_expr_kernel_conversions']+types['archived_source_header_checks']==types['raw_different']
 assert len(types['checks'])==types['raw_different'];evidence_records(types)
 raw=read(types['raw_comparison']['path']);assert raw['different_names']==list(dict.fromkeys(raw['different_names']))
 assert set(raw['different_names'])==set(types['checks']) and raw['raw_different']==types['raw_different']
 assert raw['raw_identical']==types['raw_identical'] and raw['original_declarations']==6306
 # Earlier exact comparison/semantic assembler remains authoritative. This gate
 # binds its immutable evidence; it does not re-expand ~1.8GB of type JSON.
 archives=[];covered_sides=set()
 for path in cfg['type_archives']:
  ar=read(path);assert ar['status']=='byte_verified';check_record(ar['archive'])
  assert Path(ar['archive']['path']).resolve().is_relative_to(A.resolve()),'final evidence archive must be durable inside research archive'
  if ar['format']=='r1914-single-capture-archive-v1':covered_sides.add(ar['side']);assert ar['declarations']==6306
  else:assert ar['format']=='r1914-type-evidence-archive-v1';covered_sides.update(['baseline','final'])
  archives.append(ar)
 assert covered_sides=={'baseline','final'}
 guard=read(cfg['source_guards']);assert guard['status']=='protected_contracts_and_models_unchanged'
 assert len(guard['six_families'])==6 and guard['original_audit_names']==6306 and guard['current_audit_names']==len(names)
 assert guard['local_import_graph_acyclic'] is True
 review=read(cfg['source_review']);assert review['format']=='r1914-independent-source-review-v1' and review['status']=='passed'
 sources=source_hashes(P);assert guard['source_sha256']==review['final_source_sha256']==sources
 evidence_records(review)
 assert review['baseline_sources']==len(old['source_sha256']) and review['final_sources']==len(sources)
 assert review['mathematical_modules']==len(sources)-1
 assert review['original_audit_names_preserved']==6306 and review['original_audit_order_exact'] is True
 assert review['forbidden_tokens']==review['missing_local_imports']==[] and review['local_imports_acyclic'] is True
 assert review['set_options']==guard['permitted_options'] and set(review['set_options'])<={'autoImplicit false'}
 assert review['geometry_proof_headers_and_bodies_exact'] is True and review['global_geometry_instance_moved'] is False
 # Bind the replay's baseline and stage evidence, not synthetic success flags.
 baseline=read(review['baseline']['path'])
 assert {r:hashlib.sha256(t.encode()).hexdigest() for r,t in baseline.items()}==old['source_sha256']
 before=set(old['source_sha256']);after=set(sources)
 changed=sorted(r for r in before&after if old['source_sha256'][r]!=sources[r])
 assert changed==guard['changed_files'] and sorted(after-before)==guard['added_files'] and sorted(before-after)==guard['removed_files']
 stages=review['stages'];kinds=[r['kind'] for r in stages]
 assert kinds[:2]==['imports','geometry'] and set(kinds)<={'imports','geometry','merge','import-repair','approved-repair'}
 assert all(kinds.count(k)<=1 for k in ['imports','geometry','merge'])
 assert set().union(*(set(r['changed_sources']) for r in stages))==set(changed)|set(guard['added_files'])|set(guard['removed_files'])
 if 'approved-repair' not in kinds:assert review['explicit_approved_repairs']==[]
 else:assert review['explicit_approved_repairs'],'proof repairs require concrete independently approved receipts'
 geometry=read(review['geometry_proposal']['path']);moved=geometry['relocations']
 assert len(moved)==len({r['declaration'] for r in moved})==8
 assert review['geometry_relocations']==[r['declaration'] for r in moved]
 for row in moved:assert hashlib.sha256(row['source_text'].encode()).hexdigest()==row['source_sha256']
 merge=review['optional_merge']
 assert ('merge' in kinds)==(merge is not None)
 if merge:
  assert len(merge['members'])==len(set(merge['members']))==5 and merge['destination'] in merge['members']
  assert set(merge['body_sha256'])==set(merge['members']) and len(merge['removed'])==4
  assert set(merge['removed'])=={'lean/'+m.replace('.','/')+'.lean' for m in merge['members'] if m!=merge['destination']}
  assert set(merge['removed'])<=set(guard['removed_files'])
 # Family/model claims are derived from the guard's exact original body records.
 expected_families={'adaptive_separator_treewidth','nonlinear_row_fixed_xor','affine_motion','paid_padding','two_stage_helper','scan_and_recursion'}
 assert set(guard['six_families'])==expected_families
 protected=guard['protected_source_bodies'];family_paths={'lean/TransposeFollowup/'+m+'.lean':f for f,ms in guard['six_families'].items() for m in ms}
 model_paths={'lean/'+m+'.lean' for m in ['TransposeFollowup/MatrixView','TransposeFollowup/RowCode','TransposeFollowup/ProtocolTruncation','TransposeFollowup/FiniteProgramEncodingCore','TransposeFollowup/NativeMicrocodeCore','TransposeFollowup/NativeIOCore','TransposeFollowup/NativeReadFusionCore','TransposeFollowup/NativeIOFusionCore','TransposeFollowup/NativeRunLimits','FixedTapeCompiler/Microcode','FixedTapeCompiler/OperationalTrace']}
 assert len(family_paths)==23 and set(protected)==set(family_paths)|model_paths
 for rel,row in protected.items():
  expected_family=family_paths.get(rel,'shared_model');assert row['family']==expected_family
  original_body=re.sub(r'^import [^\n]+\n','',baseline[rel],flags=re.M)
  assert hashlib.sha256(original_body.encode()).hexdigest()==row['non_import_body_sha256']
  assert row['current_location'] in sources
  current_body=re.sub(r'^import [^\n]+\n','',(P/row['current_location']).read_text(),flags=re.M)
  assert original_body in current_body,('protected original body changed',rel)
 source_contracts={'all_six_main_targets_preserved':set(family_paths)<=set(protected),'shared_model_definitions_preserved':model_paths<=set(protected),'protected_family_bodies':len(family_paths),'protected_model_bodies':len(model_paths)}
 # No proof source may have been rewritten after the successful checks.
 latest_source=max((P/r).stat().st_mtime for r in sources)
 for run in [full,axioms]:assert datetime.datetime.fromisoformat(run['finished_at']).timestamp()>=latest_source,'proof sources changed after final check'
 upstream=read(P/'verification/upstream-baseline.json');U=P.parent/upstream['directory']
 assert {str(f.relative_to(U)):sha(f) for f in U.rglob('*') if f.is_file()}==upstream['files']
 assert sorted(str(f.relative_to(U)) for f in U.rglob('*') if f.is_dir())==upstream['directories']
 for key in ['configuration_sha256','external_source_sha256']:
  for rel,h in old[key].items():
   p=Path(rel);p=p if p.is_absolute() else P/p;assert sha(p)==h,(key,rel)
 for rel,h in old['log_sha256'].items():
  p=A/'before-r1914-summary-update'/rel if after_finalization and rel in MUTABLE else P/rel
  assert sha(p)==h,('prior receipt evidence changed',rel)
 assert cfg['restoration_records'],'at least the paired workflow source-restoration record is required'
 for path in cfg['restoration_records']:
  r=read(path);assert r['restored'] is True
  source=Path(r['source']);source=source if source.is_absolute() else P/source
  assert sha(source)==r['original_sha256'],('benchmark edit not exactly restored',source)
 confirmation=read(cfg['confirmation']);assert confirmation['status']=='passed' and confirmation['pairs']==3
 for key in ['all_exit_codes_zero','inputs_unchanged','proof_bodies_byte_identical_after_import']:assert confirmation[key] is True
 before=confirmation['medians']['Baseline']['wall_seconds'];after=confirmation['medians']['Candidate']['wall_seconds']
 assert abs(before-14.39473008364439)<1e-9 and abs(after-5.33443508297205)<1e-9
 merge_target=read(cfg['merge_target']);assert merge_target['status']=='passed' and len(merge_target['pairs'])==3
 for flag in ['all_checks_exit_zero','current_validated_inputs_unchanged','proof_body_bytes_preserved']:assert merge_target[flag] is True
 assert merge_target['whole_project_speedup_ratio'] is None
 assert statistics.median(r['split_wall_seconds'] for r in merge_target['pairs'])==merge_target['median_split_seconds']
 assert statistics.median(r['merged_wall_seconds'] for r in merge_target['pairs'])==merge_target['median_merged_seconds']
 optimization_build,optimization_log=timing_log(cfg['optimization_build'])
 assert re.search(r'Build completed successfully \(\d+ jobs\)',optimization_log)
 workflow=None
 if cfg.get('workflow'):
  w=cfg['workflow'];assert w['matched_same_proof_edit'] is True and w['cached_prerequisites'] is True
  b,bl=timing_log(w['baseline']);f,fl=timing_log(w['candidate']);summary=read(w['summary'])
  assert summary['status']=='passed' and summary['scope']==w['scope']
  assert abs(summary['baseline_seconds']-b['wall_seconds'])<1e-9 and abs(summary['candidate_seconds']-f['wall_seconds'])<1e-9
  assert abs(summary['speedup_ratio']-b['wall_seconds']/f['wall_seconds'])<1e-9
  assert summary['baseline_rebuilt_modules']==len(re.findall(r'\]\s+Built\s+',bl))
  assert summary['candidate_rebuilt_modules']==len(re.findall(r'\]\s+Built\s+',fl))
  edit_path=Path(summary['same_edit_record']);edit_path=edit_path if edit_path.is_absolute() else V/edit_path
  assert edit_path.resolve() in {Path(p).resolve() for p in cfg['restoration_records']}
  edit=read(edit_path);assert [e['mode'] for e in edit['events']]==['apply-baseline','restore-baseline','apply-candidate','restore-candidate']
  workflow={k:summary[k] for k in ['baseline_seconds','candidate_seconds','speedup_ratio','baseline_rebuilt_modules','candidate_rebuilt_modules','scope','interference_note']}
  workflow.update(summary=str(Path(w['summary']).resolve()),cold_build_comparison=False,matched_pairs=1)
 return dict(P=P,V=V,C=C,A=A,old=old,state=state,full=full,axioms=axioms,jobs=jobs,names=names,types=types,sources=sources,confirmation=confirmation,before=before,after=after,workflow=workflow,review=review,source_contracts=source_contracts,merge_target=merge_target,optimization_build=optimization_build,optimization_rebuilt=len(re.findall(r'\]\s+Built\s+',optimization_log)),final_rebuilt=len(re.findall(r'\]\s+Built\s+',blog)))
def report_text(d,cfg):
 t=d['types'];workflow=d['workflow'];baseline_modules=len(d['old']['source_sha256'])-1;modules=len(d['sources'])-1
 wf='Matched edit-workflow speedup is not reported; no completed candidate comparison was supplied.' if not workflow else f"Matched cached edit workload ({workflow['scope']}): {workflow['baseline_seconds']:.3f}s -> {workflow['candidate_seconds']:.3f}s, {workflow['speedup_ratio']:.2f} times faster; {workflow['baseline_rebuilt_modules']} -> {workflow['candidate_rebuilt_modules']} rebuilt modules. This is one matched edit/rebuild pair, not a cold-build comparison. Timing caveat: {workflow['interference_note']}"
 return f'''R1914 — ANALYTIC BUILD-SPEED IMPLEMENTATION
The clean three-pair confirmation reduces the identical RealMobiusAverage proof
check from {d['before']:.4f}s to {d['after']:.4f}s median ({100*(1-d['after']/d['before']):.2f}% less).
The only pilot difference is its import boundary. This is a target measurement.
The three-pair five-module target reduces median sequential source-check work
from {d['merge_target']['median_split_seconds']:.4f}s to {d['merge_target']['median_merged_seconds']:.4f}s. Original predecessor
artifacts were cached in the split measurements; this is not a whole-build ratio.

{wf}
No cold-build or universal whole-project speedup ratio is claimed.

ADOPTED CHANGES
{chr(10).join(cfg['adopted_changes'])}
Mathematical modules: {baseline_modules} -> {modules}; counts reflect final sources.
No mathematical theorem strengthening is claimed by this build optimization.

PRESERVATION
All6306 pre-round audited contracts are covered: {t['raw_identical']} literal type
matches, {t['original_expr_kernel_conversions']} exact-original-Expr kernel conversions,
and {t['archived_source_header_checks']} separately checked original source headers.
Any raw differences and failed attempts remain preserved; source-header checks
are not mislabeled as literal original-Expr conversions. Shared model definitions
and the six theorem families are preserved by the independent source review.
The full build passes {d['jobs']} jobs and the axiom audit passes {len(d['names'])}
unique declarations using only propext, Classical.choice and Quot.sound.
The initial optimization validation build rebuilds {d['optimization_rebuilt']} modules in
{d['optimization_build']['wall_seconds']:.3f}s. The final build after exact benchmark restoration
rebuilds {d['final_rebuilt']} modules in {d['full']['wall_seconds']:.3f}s,
and the final axiom audit takes {d['axioms']['wall_seconds']:.3f}s. These are validation
costs for their actual source/cache states, not matched cold-build timings.

Normal Lean kernel checking validates rebuilt proofs. Fresh whole-environment
kernel replay was not repeated; historical replay certifies only its old snapshot.
Original sibling sources, pinned external sources and configurations are unchanged.
No sorry, new axiom, unsafe bypass, raised proof limit or disabled linter was added.
Benchmark edits are exactly restored and all execution handles are terminal.
Compact type receipts and byte-verified full-chunk archives replace a giant
aggregate file. Previous receipts/logs and pre-update summaries remain archived.
'''
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--config',type=Path,required=True);p.add_argument('--apply',action='store_true');a=p.parse_args();cfg=read(a.config);d=validate_inputs(cfg)
 report=report_text(d,cfg)
 if not a.apply:print(report);return
 P,V,A=d['P'],d['V'],d['A'];assert a.config.resolve().is_relative_to(V.resolve()),'copy final evidence config into verification before publishing';assert not (V/'r1914-completion.json').exists()
 archive=A/'before-r1914-summary-update'
 for rel in MUTABLE:assert not (archive/rel).exists()
 # Prepare all text before any mutation, including exact edit anchors.
 readme=(P/'README.md').read_text();needle='Start with the [exact statements, improvements, scope and relevance](paper/verified-results.txt).';assert readme.count(needle)==1
 results=(P/'paper/verified-results.txt').read_text();start=results.index('STATUS:');end=results.index('COMMON NOTATION AND INTERPRETATION')
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();t=d['types'];status='R1914 complete: measured analytic build improvements; all6306 original audited contracts and six theorem families preserved.'
 type_text=f"6306 original contracts: {t['raw_identical']} literal matches, {t['original_expr_kernel_conversions']} original-Expr kernel conversions, {t['archived_source_header_checks']} archived-source-header checks."
 insert=f"The [R1914 analytic build pass](verification/r1914-audit.txt) reduces the clean paired target proof check from **{d['before']:.2f}s to {d['after']:.2f}s**. All6306 original audited contracts and all six theorem families are preserved. See the report for the distinct matched-workload evidence and its limits.\n\n"
 readme=readme.replace(needle,insert+needle).replace('[current completion record](verification/r1912-completion.json)','[current completion record](verification/r1914-completion.json)')
 results=results[:start]+f"STATUS: All six original theorem families retain their strengthened statements. R1914 improves build dependencies and preserves mathematical contracts. {type_text} Full build passes {d['jobs']} jobs; axiom audit passes {len(d['names'])} declarations using only propext, Classical.choice and Quot.sound. See verification/r1914-audit.txt.\n\n"+results[end:]
 completion={'checkpoint':'R1914','checked_at':now,'status':status,**d['source_contracts'],'no_live_execution_handles':not d['state']['live_handles'],'full_build':{**cfg['full_build'],'exit_code':0,'jobs':d['jobs'],'wall_seconds':d['full']['wall_seconds']},'axiom_audit':{**cfg['axiom_audit'],'exit_code':0,'declarations':len(d['names'])},'original_type_preservation':{k:t[k] for k in ['original_declarations','raw_identical','raw_different','original_expr_kernel_conversions','archived_source_header_checks']},'mathematical_modules':len(d['sources'])-1,'local_sources_including_audit':len(d['sources']),'clean_paired_target':{'before_seconds':d['before'],'after_seconds':d['after'],'pairs':3},'matched_edit_workflow':d['workflow'],'merge_target':{'pairs':3,'split_seconds':d['merge_target']['median_split_seconds'],'merged_seconds':d['merge_target']['median_merged_seconds'],'scope':d['merge_target']['caution']},'optimization_validation_seconds':d['optimization_build']['wall_seconds'],'cold_build_speedup_ratio':None,'fresh_kernel_replay':'Not repeated; normal kernel checking of rebuilt proofs. Historical replay applies only to its historical snapshot.','evidence_config':str(a.config.resolve())}
 for rel in MUTABLE:
  target=archive/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((P/rel).read_bytes());assert sha(target)==d['old']['log_sha256'][rel]
 (V/'r1914-audit.txt').write_text(report);write(V/'r1914-completion.json',completion)
 (P/'README.md').write_text(readme);(P/'paper/verified-results.txt').write_text(results)
 with (V/'progress.txt').open('a') as out:out.write(f"\n{now} — {status}\nClean paired target {d['before']:.4f}->{d['after']:.4f}s. {type_text} Full build {d['jobs']} jobs; {len(d['names'])} axiom checks. No cold-build speedup claim. See r1914-audit.txt.\n")
 receipt=copy.deepcopy(d['old']);receipt.update(checked_at=now,scope=status,build=f"lake build: success, {d['jobs']} jobs; {cfg['full_build']['log']}",axiom_audit=f"SupportAxioms.lean: success, {len(d['names'])} declarations; {cfg['axiom_audit']['log']}",source_sha256=d['sources'],verified_declarations=d['names'],type_preservation=type_text)
 receipt['fresh_kernel_replay']['status']=completion['fresh_kernel_replay']
 logs=dict(receipt['log_sha256'])
 for rel in MUTABLE:logs[rel]=sha(P/rel)
 excluded={'r1913-in-progress.json','r1914-in-progress.json','r1914-final-receipt-check.json','r1914-final-receipt-check-timing.json','r1914-final-receipt-check.log'}
 for prefix in ['r1913-','r1914-']:
  for f in sorted(V.glob(prefix+'*')):
   if f.is_file() and f.name not in excluded:logs[str(f.relative_to(P))]=sha(f)
 for f in sorted((V/'r1914-preservation-tools').rglob('*')):
  if f.is_file() and '__pycache__' not in f.relative_to(V/'r1914-preservation-tools').parts:logs[str(f.relative_to(P))]=sha(f)
 receipt['log_sha256']=logs;write(V/'support-build.json',receipt)
 state=d['state'];state.update(status=status,completed_at=now,final_receipt='verification/support-build.json',report='verification/r1914-audit.txt');write(cfg['state'],state)
 print(json.dumps({'status':status,'receipt_logs':len(logs),'sources':len(d['sources']),'report':str(V/'r1914-audit.txt')}))
if __name__=='__main__':main()
