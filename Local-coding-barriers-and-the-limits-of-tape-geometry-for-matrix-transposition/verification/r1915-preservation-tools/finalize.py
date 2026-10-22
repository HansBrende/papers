#!/usr/bin/env python3
"""DRAFT R1915 finalizer. Root reviews the evidence config and runs --apply only
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
 state=read(cfg['state']);assert state['checkpoint']=='R1915' and state['live_handles']==[]
 terminal=state['terminal_handles'];assert len({r['session'] for r in terminal})==len(terminal) and all(isinstance(r['exit_code'],int) for r in terminal)
 full,blog=timing_log(cfg['full_build']);axioms,alog=timing_log(cfg['axiom_audit'])
 match=re.search(r'Build completed successfully \((\d+) jobs\)',blog);assert match; jobs=int(match[1])
 names=re.findall(r'^#print axioms (\S+)\s*$',(P/'lean/SupportAxioms.lean').read_text(),re.M)
 originals=read(C/'names.json')['names'];assert len(originals)==len(set(originals))==6306
 assert names==originals and len(names)==len(set(names))==6306
 parsed=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",alog)
 none=re.findall(r"'([^']+)' does not depend on any axioms",alog)
 assert len(parsed)+len(none)==len(names) and {n for n,_ in parsed}|set(none)==set(names)
 assert all({x.strip() for x in ax.split(',') if x.strip()}<=ALLOWED for _,ax in parsed)
 assert set(old['allowed_axioms'])==ALLOWED
 types=read(cfg['types']);assert types['format']=='r1915-type-preservation-v1' and types['status']=='passed'
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
  if ar['format']=='r1915-single-capture-archive-v1':covered_sides.add(ar['side']);assert ar['declarations']==6306
  else:assert ar['format']=='r1915-type-evidence-archive-v1';covered_sides.update(['baseline','final'])
  archives.append(ar)
 assert covered_sides=={'baseline','final'}
 guard=read(cfg['source_guards']);assert guard['status']=='protected_contracts_and_models_unchanged'
 assert len(guard['six_families'])==6 and guard['original_audit_names']==6306 and guard['current_audit_names']==len(names)
 assert guard['local_import_graph_acyclic'] is True
 review=read(cfg['source_review']);assert review['format']=='r1915-independent-source-review-v1' and review['status']=='passed'
 sources=source_hashes(P);assert guard['source_sha256']==review['final_source_sha256']==sources
 evidence_records(review)
 assert review['baseline_sources']==len(old['source_sha256']) and review['final_sources']==len(sources)
 assert review['mathematical_modules']==len(sources)-1
 assert review['original_audit_names_preserved']==6306 and review['original_audit_order_exact'] is True
 assert review['forbidden_tokens']==review['missing_local_imports']==[] and review['local_imports_acyclic'] is True
 assert review['set_options']==guard['permitted_options'] and set(review['set_options'])<={'autoImplicit false'}
 assert review['all_merged_nonimport_bodies_exact'] is True and review['global_instances_moved']==0
 # Bind the replay's baseline and stage evidence, not synthetic success flags.
 baseline=read(review['baseline']['path'])
 assert {r:hashlib.sha256(t.encode()).hexdigest() for r,t in baseline.items()}==old['source_sha256']
 before=set(old['source_sha256']);after=set(sources)
 changed=sorted(r for r in before&after if old['source_sha256'][r]!=sources[r])
 assert changed==guard['changed_files'] and sorted(after-before)==guard['added_files'] and sorted(before-after)==guard['removed_files']
 stages=review['stages'];assert [r['kind'] for r in stages]==['merge']
 assert set(stages[0]['changed_sources'])==set(changed)|set(guard['added_files'])|set(guard['removed_files'])
 assert review['explicit_approved_repairs']==[] and not guard['added_files']
 merge=review['merge'];assert len(merge['members'])==len(set(merge['members']))==6
 assert merge['destination'] in merge['members'] and set(merge['body_sha256'])==set(merge['members'])
 assert set(merge['removed'])=={'lean/'+m.replace('.','/')+'.lean' for m in merge['members'] if m!=merge['destination']}
 assert len(merge['removed'])==5 and set(merge['removed'])==set(guard['removed_files'])
 assert review['source_change_counts']=={'changed':len(changed),'removed':len(guard['removed_files']),'added':0}
 # Prior final types are explicitly reused; no new baseline run is claimed.
 reuse=read(C/'baseline-reuse.json');evidence_records(reuse)
 assert reuse['format']=='r1915-reused-verified-baseline-v1' and reuse['source_round']=='R1914'
 assert reuse['source_side']=='final' and reuse['destination_round']=='R1915' and reuse['destination_side']=='baseline'
 assert reuse['declarations']==6306 and reuse['raw_chunks']==79
 assert reuse['Lean_executed'] is False and reuse['raw_type_files_copied'] is False and reuse['working_tree_sources_read'] is False
 assert reuse['before_receipt']['sha256']==sha(C/'before-receipt.json') and reuse['baseline_sources']['sha256']==sha(C/'baseline-sources.json')
 assert raw['baseline']['sha256']==sha(C/'baseline-compact.json')
 reused=read(C/'baseline-compact.json');assert reused['side']=='baseline' and reused['reused_capture']==reuse['prior_evidence']['compact']
 assert reused['reuse_receipt']['sha256']==sha(C/'baseline-reuse.json')
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
  p=A/'before-r1915-summary-update'/rel if after_finalization and rel in MUTABLE else P/rel
  assert sha(p)==h,('prior receipt evidence changed',rel)
 edit=read(cfg['workflow_edit']);assert edit['restored'] is True
 assert set(edit['variants'])=={'baseline','candidate'}
 assert [e['mode'] for e in edit['events']]==['apply-baseline','restore-baseline','apply-candidate','restore-candidate']
 anchor='IntegrableOn (fun x => G.whole.weightedPullback f x*f x) (Icc (0:ℝ) 1) := by\n'
 for side,r in edit['variants'].items():
  assert r['restored'] is True
  original=baseline[r['source']] if side=='baseline' else (P/r['source']).read_text()
  assert hashlib.sha256(original.encode()).hexdigest()==r['original_sha256']
  assert original.count(anchor)==1
  assert hashlib.sha256(original.replace(anchor,anchor+'  apply id\n').encode()).hexdigest()==r['edited_sha256']
  if side=='candidate':assert r['source']=='lean/'+merge['destination'].replace('.','/')+'.lean'
 pilot=read(cfg['pilot']);assert pilot['status']=='passed' and len(pilot['pairs'])==3
 for key in ['all_checks_exit_zero','current_validated_inputs_unchanged','proof_body_bytes_preserved','adoption_eligible']:assert pilot[key] is True
 assert pilot['whole_project_speedup_ratio'] is None
 medians={'median_split_seconds':'split_wall_seconds','median_merged_seconds':'merged_wall_seconds','median_split_final_only_seconds':'split_final_only_seconds','median_split_peak_rss_bytes':'split_max_reported_rss_bytes','median_merged_peak_rss_bytes':'merged_max_reported_rss_bytes','median_split_final_only_rss_bytes':'split_final_only_rss_bytes'}
 for key,pair_key in medians.items():assert pilot[key]==statistics.median(r[pair_key] for r in pilot['pairs'])
 before=pilot['median_split_seconds'];after=pilot['median_merged_seconds'];last=pilot['median_split_final_only_seconds']
 derived={'observed_median_target_ratio':before/after,'median_reduction_fraction':1-after/before,'median_merged_vs_final_only_overhead_seconds':after-last,'allowed_final_only_overhead_seconds':max(3.0,.25*last),'median_merged_vs_split_peak_rss_ratio':pilot['median_merged_peak_rss_bytes']/pilot['median_split_peak_rss_bytes'],'median_merged_vs_final_only_rss_ratio':pilot['median_merged_peak_rss_bytes']/pilot['median_split_final_only_rss_bytes']}
 for key,value in derived.items():assert abs(pilot[key]-value)<1e-9
 gates={'three_alternating_pairs':True,'six_chain_reduction_at_least_35_percent':derived['median_reduction_fraction']>=.35,'final_only_overhead_at_most_max_3s_25_percent':derived['median_merged_vs_final_only_overhead_seconds']<=derived['allowed_final_only_overhead_seconds'],'median_peak_rss_increase_at_most_10_percent':derived['median_merged_vs_split_peak_rss_ratio']<=1.10}
 assert pilot['adoption_gates']==gates and all(gates.values())
 w=cfg['workflow'];b,bl=timing_log(w['baseline']);f,fl=timing_log(w['candidate']);workflow=read(w['summary'])
 assert Path(w['baseline']['timing']).name.startswith('r1915-'), 'Use the fresh R1915 baseline, not the historical R1914 measurement'
 assert workflow['status']=='passed' and workflow['cold_build_speedup_ratio'] is None
 same_edit=Path(workflow['same_edit_record']);same_edit=same_edit if same_edit.is_absolute() else V/same_edit
 assert same_edit.resolve()==Path(cfg['workflow_edit']).resolve()
 assert abs(workflow['baseline_seconds']-b['wall_seconds'])<1e-9 and abs(workflow['candidate_seconds']-f['wall_seconds'])<1e-9
 assert abs(workflow['speedup_ratio']-b['wall_seconds']/f['wall_seconds'])<1e-9
 assert workflow['baseline_rebuilt_modules']==len(re.findall(r'\]\s+Built\s+',bl))
 assert workflow['candidate_rebuilt_modules']==len(re.findall(r'\]\s+Built\s+',fl))
 # This is a single matched cached workflow; no historical cross-round ratio.
 workflow={**workflow,'matched_pairs':1,'cold_build_comparison':False}
 return dict(P=P,V=V,C=C,A=A,old=old,state=state,full=full,axioms=axioms,jobs=jobs,names=names,types=types,sources=sources,before=before,after=after,workflow=workflow,review=review,source_contracts=source_contracts,pilot=pilot,reuse=reuse,final_rebuilt=len(re.findall(r'\]\s+Built\s+',blog)))

def report_text(d,cfg):
 t=d['types'];p=d['pilot'];w=d['workflow']
 return f'''R1915 — SPECTRAL BUILD-SPEED IMPLEMENTATION
The six-source target median falls from {d['before']:.4f}s to {d['after']:.4f}s
in three alternating pairs. The split arm sums six sequential fresh source
checks using cached original predecessor artifacts. This is a target workload,
not a whole-project or cold-build speedup claim.

Against checking only the final original module, the median changes from
{p['median_split_final_only_seconds']:.4f}s to {d['after']:.4f}s:
{p['median_merged_vs_final_only_overhead_seconds']:+.4f}s difference, within the
predeclared {p['allowed_final_only_overhead_seconds']:.4f}s allowed overhead.
Median reported peak RSS: split arm {p['median_split_peak_rss_bytes']/2**30:.3f} GiB,
merged arm {p['median_merged_peak_rss_bytes']/2**30:.3f} GiB; final-only original
{p['median_split_final_only_rss_bytes']/2**30:.3f} GiB. Split RSS is the maximum
per sequential child, not a sum or simultaneous whole-workflow memory measure.

The fresh R1915 matched cached edit workload takes {w['baseline_seconds']:.3f}s
before and {w['candidate_seconds']:.3f}s after ({w['speedup_ratio']:.2f} times faster),
rebuilding {w['baseline_rebuilt_modules']} and {w['candidate_rebuilt_modules']} modules.
Scope: {w['scope']}
Timing caveat: {w['interference_note']}
This is one matched pair. R1914's historical 97.811s candidate is not the
baseline for this round, and no cross-round or universal speedup is inferred.

REMAINING COST
An import-only profiling run took about 12s, while the recorded tactic and
proof typechecking portions were small. Loading the broad imported environment
is the next likely bottleneck. This diagnostic is not a pure import timer or
another cold-build/whole-project speedup measurement.

ADOPTED CHANGE
{chr(10).join(cfg['adopted_changes'])}
Mathematical module count: {len(d['old']['source_sha256'])-1} -> {len(d['sources'])-1}.
Counts reflect actual final sources, not the planned target.

PRESERVATION
All 6306 original audited contracts are preserved: {t['raw_identical']} literal
matches, {t['original_expr_kernel_conversions']} exact-original-Expr kernel conversions,
and {t['archived_source_header_checks']} separately checked archived source headers.
The baseline reuses the completed R1914 final capture, explicitly bound to the
new frozen source/receipt snapshot. No new baseline Lean inspection occurred.
All referenced raw chunks were verified and exactly compared with the new final
capture; raw differences and their actual resolution remain recorded.
The first type-check attempt encountered a retired generated proof helper in
expansion_of_restrictedL2Gap. That single case is resolved by the exact archived
original theorem header with every premise retained, proved using the current
theorem and checked by the ordinary kernel. It is not labeled an original-Expr
conversion. No alias, environment patch or library lemma was introduced, and
the failed first attempt remains preserved alongside the successful check.
The 23 theorem-family and 11 shared-model bodies are preserved. No mathematical
theorem strengthening or new proof axiom is claimed by this organization change.

The final restored build passes {d['jobs']} jobs, rebuilding {d['final_rebuilt']}
modules in {d['full']['wall_seconds']:.3f}s. The final axiom audit checks all
{len(d['names'])} names in {d['axioms']['wall_seconds']:.3f}s, using only propext,
Classical.choice and Quot.sound. These are validation costs for actual cache
states, not additional matched benchmark arms. Ordinary Lean kernel checking
validates rebuilt proofs; fresh whole-environment kernel replay was not repeated.
Historical replay remains evidence only for its own snapshot.

Original sibling, source pins/configuration, and old immutable evidence are
unchanged. No sorry, unsafe bypass, raised proof limit or disabled linter was
added. Benchmark variants are exactly restored, all handles are terminal, and
full type/checker evidence is durably archived without a giant aggregate file.
'''

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--config',type=Path,required=True);p.add_argument('--apply',action='store_true');a=p.parse_args();cfg=read(a.config);d=validate_inputs(cfg)
 report=report_text(d,cfg)
 if not a.apply:print(report);return
 P,V,A=d['P'],d['V'],d['A'];assert a.config.resolve().is_relative_to(V.resolve()),'copy final evidence config into verification before publishing';assert not (V/'r1915-completion.json').exists()
 archive=A/'before-r1915-summary-update'
 for rel in MUTABLE:assert not (archive/rel).exists()
 # Prepare all text before any mutation, including exact edit anchors.
 readme=(P/'README.md').read_text();needle='Start with the [exact statements, improvements, scope and relevance](paper/verified-results.txt).';assert readme.count(needle)==1
 results=(P/'paper/verified-results.txt').read_text();start=results.index('STATUS:');end=results.index('COMMON NOTATION AND INTERPRETATION')
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();t=d['types'];status='R1915 complete: measured spectral module consolidation; all 6306 original audited contracts and six theorem families preserved.'
 type_text=f"6306 original contracts: {t['raw_identical']} literal matches, {t['original_expr_kernel_conversions']} original-Expr kernel conversions, {t['archived_source_header_checks']} archived-source-header checks."
 insert=f"The [R1915 spectral build pass](verification/r1915-audit.txt) reduces the matched cached proof-edit rebuild from **{d['workflow']['baseline_seconds']:.3f}s to {d['workflow']['candidate_seconds']:.3f}s** in one observed pair. All 6306 original audited contracts and all six theorem families are preserved. See the report for the distinct matched-workload evidence and its limits.\n\n"
 readme=readme.replace(needle,insert+needle).replace('[current completion record](verification/r1914-completion.json)','[current completion record](verification/r1915-completion.json)')
 results=results[:start]+f"STATUS: All six original theorem families retain their strengthened statements. R1915 improves build dependencies and preserves mathematical contracts. {type_text} Full build passes {d['jobs']} jobs; axiom audit passes {len(d['names'])} declarations using only propext, Classical.choice and Quot.sound. See verification/r1915-audit.txt.\n\n"+results[end:]
 completion={'checkpoint':'R1915','checked_at':now,'status':status,**d['source_contracts'],'no_live_execution_handles':not d['state']['live_handles'],'full_build':{**cfg['full_build'],'exit_code':0,'jobs':d['jobs'],'wall_seconds':d['full']['wall_seconds']},'axiom_audit':{**cfg['axiom_audit'],'exit_code':0,'declarations':len(d['names'])},'original_type_preservation':{k:t[k] for k in ['original_declarations','raw_identical','raw_different','original_expr_kernel_conversions','archived_source_header_checks']},'baseline_capture_reused_from':'R1914 final; no new baseline Lean inspection','mathematical_modules':len(d['sources'])-1,'local_sources_including_audit':len(d['sources']),'three_pair_target':d['pilot'],'matched_edit_workflow':d['workflow'],'cold_build_speedup_ratio':None,'fresh_kernel_replay':'Not repeated; normal kernel checking of rebuilt proofs. Historical replay applies only to its historical snapshot.','evidence_config':str(a.config.resolve())}
 for rel in MUTABLE:
  target=archive/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((P/rel).read_bytes());assert sha(target)==d['old']['log_sha256'][rel]
 (V/'r1915-audit.txt').write_text(report);write(V/'r1915-completion.json',completion)
 (P/'README.md').write_text(readme);(P/'paper/verified-results.txt').write_text(results)
 with (V/'progress.txt').open('a') as out:out.write(f"\n{now} — {status}\nClean paired target {d['before']:.4f}->{d['after']:.4f}s. {type_text} Full build {d['jobs']} jobs; {len(d['names'])} axiom checks. No cold-build speedup claim. See r1915-audit.txt.\n")
 receipt=copy.deepcopy(d['old']);receipt.update(checked_at=now,scope=status,build=f"lake build: success, {d['jobs']} jobs; {cfg['full_build']['log']}",axiom_audit=f"SupportAxioms.lean: success, {len(d['names'])} declarations; {cfg['axiom_audit']['log']}",source_sha256=d['sources'],verified_declarations=d['names'],type_preservation=type_text)
 receipt['fresh_kernel_replay']['status']=completion['fresh_kernel_replay']
 logs=dict(receipt['log_sha256'])
 for rel in MUTABLE:logs[rel]=sha(P/rel)
 excluded={'r1915-in-progress.json','r1915-final-receipt-check.json','r1915-final-receipt-check-timing.json','r1915-final-receipt-check.log'}
 for prefix in ['r1915-']:
  for f in sorted(V.glob(prefix+'*')):
   if f.is_file() and f.name not in excluded:logs[str(f.relative_to(P))]=sha(f)
 for f in sorted((V/'r1915-preservation-tools').rglob('*')):
  if f.is_file() and '__pycache__' not in f.relative_to(V/'r1915-preservation-tools').parts:logs[str(f.relative_to(P))]=sha(f)
 receipt['log_sha256']=logs;write(V/'support-build.json',receipt)
 state=d['state'];state.update(status=status,completed_at=now,final_receipt='verification/support-build.json',report='verification/r1915-audit.txt');write(cfg['state'],state)
 print(json.dumps({'status':status,'receipt_logs':len(logs),'sources':len(d['sources']),'report':str(V/'r1915-audit.txt')}))
if __name__=='__main__':main()
