#!/usr/bin/env python3
"""Independently bind R1915 type-check routes and scoped performance evidence.
No Lean/Lake execution; no full-chunk/archive expansion or proof-source writes.
"""
from pathlib import Path
import hashlib,json,re,statistics,datetime
P=Path('.');V=P/'verification';C=Path('external/temporary/r1915-preservation/capture')
def unique(pairs):
 d={}
 for k,v in pairs:
  assert k not in d,('duplicate JSON key',k);d[k]=v
 return d
def read(p):return json.loads(Path(p).read_text(),object_pairs_hook=unique)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(s):return hashlib.sha256(s.encode()).hexdigest()
def rec(p):
 p=Path(p);return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':sha(p)}
def check(r):assert rec(r['path'])==r,('changed evidence',r['path'])
def records(x):
 if isinstance(x,dict):
  if {'path','bytes','sha256'}<=x.keys():check({k:x[k]for k in ['path','bytes','sha256']})
  else:
   for y in x.values():records(y)
 elif isinstance(x,list):
  for y in x:records(y)
def write_new(p,x):
 with Path(p).open('x')as f:json.dump(x,f,indent=2);f.write('\n')
receipt=read(C/'type-preservation.json');records(receipt)
assert receipt['format']=='r1915-type-preservation-v1'and receipt['status']=='passed'
assert tuple(receipt[k]for k in ['original_declarations','raw_identical','raw_different','original_expr_kernel_conversions','archived_source_header_checks'])==(6306,6302,4,3,1)
raw=read(receipt['raw_comparison']['path']);records(raw);assert raw['status']=='differences_require_review'and(raw['raw_identical'],raw['raw_different'])==(6302,4)
diffs=read(raw['differences']['path'])['differences'];diffs={r['name']:r for r in diffs};assert len(diffs)==4 and set(diffs)==set(receipt['checks'])==set(raw['different_names'])
old=read(raw['baseline']['path']);new=read(raw['final']['path']);assert len(old['types'])==len(new['types'])==6306 and set(old['types'])==set(new['types'])
assert {n for n in old['types']if old['types'][n]!=new['types'][n]}==set(diffs)
plan=read(receipt['plan']['path']);headers=read(receipt['exact_source_headers']['path']);pre=read(V/'r1915-type-route-review.preexecution.json')
assert receipt['checker']['sha256']==pre['reviewed_checker']['sha256']==headers['checker_sha256']==plan['checker_sha256']
assert receipt['plan']==pre['reviewed_plan']and receipt['exact_source_headers']==pre['source_headers']
assert plan['names']==raw['different_names']and plan['comparison_sha256']==sha(receipt['raw_comparison']['path'])
assert receipt['prior_attempt']==plan['prior_attempt']==pre['prior_failed_attempt']
assert read(receipt['prior_attempt']['execution']['path'])['exit_code']==1
assert 'unknown constant' in Path(receipt['prior_attempt']['log']['path']).read_text()
assert receipt['prior_attempt']['outputs']==[]
assert headers['count']==len(headers['declarations'])==1;h=headers['declarations'][0]
name='TransposeFollowup.RationalUnitMobius.expansion_of_restrictedL2Gap';short=name.rsplit('.',1)[1];newshort='R1915_original_header_'+short
assert h['name']==name and plan['archived_source_header_targets']==[name]and plan['original_expr_kernel_targets']==3
B=read(C/'baseline-sources.json');assert sha(C/'baseline-sources.json')==headers['baseline_inventory_sha256'];s=B[h['baseline_source']]
start=s.index('theorem '+short+' ');end=s.index(' :=\n',start);header=s[start:end]
assert header==h['original_header']and digest(header)==h['original_header_sha256']and digest(s)==h['baseline_source_sha256']
assert not re.search(r'^\s*(?:variable|variables|include|omit|axiom|instance|local instance)\b',s[:start],re.M)
assert h['renamed_header']==header.replace('theorem '+short+' ','theorem '+newshort+' ',1)
context='namespace TransposeFollowup\nopen Classical Set MeasureTheory\nopen scoped BigOperators\nset_option autoImplicit false\n\nnamespace RationalUnitMobius\n\n'
code=context+h['renamed_header']+' := by\n  exact expansion_of_restrictedL2Gap F hc hK hnear he hdet hgap\n\nend RationalUnitMobius\nend TransposeFollowup\n'
assert code==h['source_check_text']and digest(code)==h['source_check_text_sha256'];checker=Path(receipt['checker']['path']).read_text();assert checker.count(code)==1
execution=read(receipt['execution']['path']);assert execution['exit_code']==0 and receipt['checker']['path']in execution['command']
log=Path(receipt['log']['path']).read_text();assert not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)|✖',log)
assert log.count('R1915 kernel conversion chunk passed:')==len(plan['chunks'])
checked={};routes=[]
for chunk in plan['chunks']:
 assert sha(chunk['input'])==chunk['input_sha256'];inp=read(chunk['input']);out=read(chunk['output'])
 assert [r['name']for r in inp['declarations']]==chunk['names']==[r['name']for r in out['results']]
 assert inp['comparisonSHA256']==out['comparisonSHA256']==plan['comparison_sha256']
 assert inp['decoderSHA256']==out['decoderSHA256']==plan['reused_parser_sha256']
 assert out['status']=='passed'and out['kernel_positive_and_negative_controls']is True and out['input']==chunk['input']
 assert out['checked_declarations']==len(out['results'])==inp['expectedDeclarations']
 for row,result in zip(inp['declarations'],out['results']):
  n=row['name'];assert n not in checked;checked[n]=result;d=diffs[n];b,f=d['baseline'],d['final']
  assert row['baselineRepr']==b['type']and row['currentRepr']==f['type']
  assert row['levelParams']==row['currentLevelParams']==result['levelParams']==b['levelParams']==f['levelParams']
  for text,prefix in [(b['type'],'baseline'),(f['type'],'current')]:assert digest(text)==row[prefix+'ReprSHA256']==result[prefix+'ReprSHA256']
  for flag in ['original_repr_roundtrip_exact','current_repr_matches_final_capture','ordered_universe_parameters_exact']:assert result[flag]is True
  isheader=n==name;expected_route='archived_source_header_kernel'if isheader else'original_expr_kernel'
  assert result['validation_route']==expected_route and result['kernel_identity_application_checked']is(not isheader)and result['original_source_header_kernel_checked']is isheader
  assert result['auditor_declaration']==(h['auditor_declaration']if isheader else None);routes.append(expected_route)
assert checked==receipt['checks']and routes.count('original_expr_kernel')==3 and routes.count('archived_source_header_kernel')==1
assert [rec(x['input'])for x in plan['chunks']]==receipt['inputs']and[rec(x['output'])for x in plan['chunks']]==receipt['outputs']
diag=read(V/'r1915-type-route-review.diagnostic.json');assert diag['declaration']==name and diag['counts']=={'binder_name':1,'constant_name':1}
assert diag['baseline_repr_sha256']==receipt['checks'][name]['baselineReprSHA256']and diag['current_repr_sha256']==receipt['checks'][name]['currentReprSHA256']
assert diag['baseline_ast_matches_reparse']is True and diag['only_hygienic_binder_names_and_expected_generated_helper_differ']is True
# Performance summary review: separate the fresh matched pair from target medians.
w=read(V/'r1915-matched-workflow.json');runs={}
for side in ['baseline','candidate']:
 timing=read(V/f'r1915-{side}-edit-build-timing.json');text=(V/f'r1915-{side}-edit-build.log').read_text();assert timing['exit_code']==0 and 'Build completed successfully'in text
 assert w[side+'_seconds']==timing['wall_seconds']and w[side+'_rebuilt_modules']==len(re.findall(r'\]\s+Built\s+',text));runs[side]=timing['wall_seconds']
assert(w['baseline_rebuilt_modules'],w['candidate_rebuilt_modules'])==(6,1)and w['cold_build_speedup_ratio']is None
assert w['speedup_ratio']==runs['baseline']/runs['candidate']and w['reduction_fraction']==1-runs['candidate']/runs['baseline']
pilot=read(V/'r1915-merge-pilot-summary.json');assert pilot['status']=='passed'and len(pilot['pairs'])==3 and pilot['whole_project_speedup_ratio']is None
for key,pairkey in [('median_split_seconds','split_wall_seconds'),('median_merged_seconds','merged_wall_seconds'),('median_split_final_only_seconds','split_final_only_seconds'),('median_split_peak_rss_bytes','split_max_reported_rss_bytes'),('median_merged_peak_rss_bytes','merged_max_reported_rss_bytes')]:assert pilot[key]==statistics.median(x[pairkey]for x in pilot['pairs'])
assert pilot['median_reduction_fraction']==1-pilot['median_merged_seconds']/pilot['median_split_seconds']>=.35
assert pilot['median_merged_vs_final_only_overhead_seconds']==pilot['median_merged_seconds']-pilot['median_split_final_only_seconds']<=max(3.,.25*pilot['median_split_final_only_seconds'])
assert pilot['median_merged_vs_split_peak_rss_ratio']==pilot['median_merged_peak_rss_bytes']/pilot['median_split_peak_rss_bytes']<=1.1
assert pilot['adoption_eligible']is True and all(pilot['adoption_gates'].values())
report={'format':'r1915-independent-type-route-review-v1','status':'passed','reviewed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'semantic_receipt':rec(C/'type-preservation.json'),'preexecution_review':rec(V/'r1915-type-route-review.preexecution.json'),'diagnostic':rec(V/'r1915-type-route-review.diagnostic.json'),'reviewer':rec(__file__),'coverage':{'original_declarations':6306,'raw_identical':6302,'raw_different':4,'original_expr_kernel_conversions':3,'archived_source_header_checks':1},'header_exception':name,'all_four_preserved_original_repr_and_current_capture_checks':True,'ordered_universe_parameters_preserved':True,'kernel_positive_and_negative_controls_passed':True,'complete_archived_header_and_context_verified':True,'no_extra_assumptions_aliases_or_environment_patches_added':True,'failed_v1_evidence_preserved':True,'fresh_workflow':{'baseline_seconds':runs['baseline'],'candidate_seconds':runs['candidate'],'ratio':w['speedup_ratio'],'rebuilt_modules':[6,1],'matched_pairs':1,'cold_build_comparison':False},'target':{'pairs':3,'split_median_seconds':pilot['median_split_seconds'],'merged_median_seconds':pilot['median_merged_seconds'],'final_only_original_seconds':pilot['median_split_final_only_seconds'],'final_only_overhead_seconds':pilot['median_merged_vs_final_only_overhead_seconds'],'peak_RSS_ratio':pilot['median_merged_vs_split_peak_rss_ratio']},'scope':'Independent route/header/provenance and scoped performance review. Raw6302 exact matches are supported by preserved exact-comparator evidence; not a second full raw-chunk comparison. One source-header route is not mislabeled old-Expr conversion. Diagnostic field diff is explanatory only, never normalization for acceptance. No full archive expansion or fresh kernel environment replay.','Lean_executed_by_reviewer':False,'mathematical_sources_changed_by_reviewer':False}
write_new(V/'r1915-type-route-review.json',report)
text=f'''Independent R1915 type-route and performance review — PASSED

All6306 original audited contracts are covered by distinct evidence:6302 literal matches,3 native-kernel conversions of faithfully reconstructed original Exprs, and1 separately checked complete archived source header. The4 raw differences remain explicitly recorded.

The exception is {name}. Its entire frozen header is retained with only the theorem identifier renamed, under the original namespace, opens, scoped notation and autoImplicit option. There are no inherited variable/include assumptions to lose or new premises. An ordinary Lean theorem directly applies the current theorem using every original binder. Native Kernel.check additionally checks the current constant against that re-elaborated archived statement. This is a source-contract route, NOT a conversion check against the historical Expr containing the retired helper.

The executed checker is exactly the reviewed v2 checker. All4 records verify original repr roundtrip, the current captured type, ordered universes and positive/negative kernel controls. The other3 use the actual old Expr. No helper alias, axiom or environment patch was introduced. The failedv1 checker/input/plan, nonzero execution and error log remain preserved by hashes.

Independent structural diagnosis found precisely2 old/current Expr field differences for the exception: one hygienic binder owner changed from SpectralGapInterface to UnconditionalPaidPadding, and one generated helper constant changed from expansion_of_restrictedL2Gap._proof_1 to expansion_of_restrictedCorrelationGap._proof_1. Every other parsed expression field matches. This diagnosis is explanatory and was never used to normalize away a failure.

The fresh matched cached proof-edit pair measures {runs['baseline']:.6f}s -> {runs['candidate']:.6f}s, {w['speedup_ratio']:.6f} times faster, rebuilding6 ->1 modules. It is one pair, not a cold-build or universal improvement. Separate3-pair target medians are {pilot['median_split_seconds']:.6f}s -> {pilot['median_merged_seconds']:.6f}s. Final-only original median {pilot['median_split_final_only_seconds']:.6f}s gives +{pilot['median_merged_vs_final_only_overhead_seconds']:.6f}s overhead for the merged check; peak reported RSS increases by {100*(pilot['median_merged_vs_split_peak_rss_ratio']-1):.4f}%. All predeclared adoption gates pass. RSS is a per-child peak, not aggregate simultaneous memory.

This reviewer executed no Lean/Lake and changed no mathematical source. Existing exact comparison/archival results are bound through their preserved records; no redundant giant type expansion or whole-environment kernel replay is claimed. Final source/model/axiom guards remain separate evidence.
'''
with(V/'r1915-type-route-review.txt').open('x')as f:f.write(text)
print(json.dumps({k:v for k,v in report.items()if k not in ['scope']},indent=2))
