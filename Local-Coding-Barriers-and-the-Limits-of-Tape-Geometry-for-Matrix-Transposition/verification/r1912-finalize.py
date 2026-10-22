"""Finalize R1912 only after all normal Lean checks have succeeded and terminated."""
from pathlib import Path
import datetime,hashlib,json,re,shutil
P=Path('.');V=P/'verification';L=P/'lean'
R=Path('external/research-workspace/research/10-linear-decision');A=R/'archive/r1912-build-speed'
def read(p): return json.loads(Path(p).read_text())
def write(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def timing(label):
 x=read(V/f'r1912-{label}-timing.json');assert x['exit_code']==0;return x
s=read(V/'r1912-in-progress.json');assert s['live_handles']==[]
assert not (V/'r1912-completion.json').exists(),'already finalized'
before=read(A/'before-receipt.json');review=read(V/'r1912-final-source-review.json');types=read(V/'r1912-type-comparison.json')
# The raw literal comparison is immutable evidence, including its 269 differences.
assert types['status']=='failed' and types['different_declarations']==269
assert types['baseline_declarations']==types['final_declarations']==types['expected_original_declarations']==6297
assert types['chunk_pairs']==79 and types['archive'] is None
mismatch_names=[r['name'] for r in types['mismatches']]
assert len(mismatch_names)==len(set(mismatch_names))==269
assert all(r['type_equal'] is False and r['levelParams_equal'] is True for r in types['mismatches'])
conversion_path=V/'r1912-kernel-type-conversion.json';conversion=read(conversion_path)
type_archive=read(V/'r1912-type-archive.json')
expected_counts={'original_declarations':6297,'raw_identical_declarations':6028,'raw_different_declarations':269,'kernel_converted_declarations':267,'source_header_checked_declarations':2}
def check_record(record,path=None):
 target=Path(record['path']) if path is None else Path(path)
 assert target.is_file() and target.stat().st_size==record['bytes'] and sha(target)==record['sha256'],str(target)
 return target
assert conversion['format']=='r1912-kernel-type-conversion-v1' and conversion['status']=='passed'
assert conversion['archive'] is None
assert type_archive['format']=='r1912-semantic-type-archive-v1' and type_archive['status']=='passed'
assert all(conversion[k]==v and type_archive[k]==v for k,v in expected_counts.items())
assert conversion['declarations']==mismatch_names and set(conversion['checks'])==set(mismatch_names)
assert type_archive['raw_receipt_modified'] is False and type_archive['semantic_receipt_modified'] is False
check_record(conversion['raw_comparison'],V/'r1912-type-comparison.json')
check_record(type_archive['raw_comparison'],V/'r1912-type-comparison.json')
check_record(type_archive['semantic_comparison'],conversion_path)
check_record(type_archive['archive']);assert type_archive['archive']['verified_members']>0
for field in ['checker','lean_log','execution_record','exact_source_headers']:
 check_record(conversion[field])
assert read(conversion['execution_record']['path'])['exit_code']==0
kernel_log=Path(conversion['lean_log']['path']).read_text()
assert not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)',kernel_log)
assert sum('R1912 kernel conversion chunk passed:' in line for line in kernel_log.splitlines())==34
special={'TransposeFollowup.NativePaddedField.tail_trace','TransposeFollowup.CountedFill.emit_step'}
headers=read(conversion['exact_source_headers']['path'])
assert headers['format']=='r1912-exact-archived-source-header-checks-v1' and headers['count']==2
assert {r['name'] for r in headers['declarations']}==special and len(headers['declarations'])==2
assert headers['checker_sha256']==conversion['checker']['sha256']
assert sha(Path(headers['baseline_inventory']))==headers['baseline_inventory_sha256']==types['source_inventory_sha256']
header_by_name={r['name']:r for r in headers['declarations']}
archived_sources=read(headers['baseline_inventory']);checker_source=Path(conversion['checker']['path']).read_text()
for name,row in header_by_name.items():
 original=archived_sources[row['baseline_source']];header=row['original_header']
 assert hashlib.sha256(original.encode()).hexdigest()==row['baseline_source_sha256']
 assert original.count(header)==1 and original[original.index(header)+len(header):].startswith(' := by')
 assert row['renamed_header']==header.replace('theorem '+name.rsplit('.',1)[-1]+' ','theorem '+row['auditor_declaration'].rsplit('.',1)[-1]+' ',1)
 assert checker_source.count(row['source_check_text'])==1
 assert hashlib.sha256(header.encode()).hexdigest()==row['original_header_sha256']
 assert hashlib.sha256(row['source_check_text'].encode()).hexdigest()==row['source_check_text_sha256']
compact={side:read(Path(types['compact_outputs'][side]))['types'] for side in ['baseline','final']}
assert all(set(c)==set(before['verified_declarations']) and len(c)==6297 for c in compact.values())
for name in before['verified_declarations']:
 assert compact['baseline'][name]['levelParams']==compact['final'][name]['levelParams']
 if name not in set(mismatch_names):assert compact['baseline'][name]==compact['final'][name]
for name,check in conversion['checks'].items():
 for flag in ['original_repr_roundtrip_exact','current_repr_matches_final_capture','ordered_universe_parameters_exact']:
  assert check[flag] is True,(name,flag)
 assert check['levelParams']==compact['baseline'][name]['levelParams']==compact['final'][name]['levelParams']
 assert check['baselineReprSHA256']==compact['baseline'][name]['type_sha256']
 assert check['currentReprSHA256']==compact['final'][name]['type_sha256']
 if name in special:
  assert check['validation_route']=='archived_source_header_kernel'
  assert check['kernel_identity_application_checked'] is False and check['original_source_header_kernel_checked'] is True
  assert check['auditor_declaration']==header_by_name[name]['auditor_declaration']
 else:
  assert check['validation_route']=='original_expr_kernel'
  assert check['kernel_identity_application_checked'] is True and check['original_source_header_kernel_checked'] is False
  assert check['auditor_declaration'] is None
for name in ['README.txt','next-target.txt']:
 assert not (A/'before-r1912-summary-update/research'/name).exists()
assert not (V/'r1912-baseline-types.json').exists(),'bulky type data must be preserved in verified archive first'
full=timing('build');noop=timing('final-incremental');axiom=timing('axioms');type_run=timing('final-types');target=timing('final-target-restored')
blog=(V/'r1912-build.log').read_text();match=re.search(r'Build completed successfully \((\d+) jobs\)',blog);assert match
assert not re.search(r'warning:|error:|✖',blog);jobs=int(match[1])
assert not re.search(r'warning:|error:|✖',(V/'r1912-axioms.log').read_text())
names=re.findall(r'^#print axioms (\S+)\s*$',(L/'SupportAxioms.lean').read_text(),re.M)
assert len(names)==len(set(names))==6306 and set(before['verified_declarations'])<=set(names)
parsed=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",(V/'r1912-axioms.log').read_text())
none=re.findall(r"'([^']+)' does not depend on any axioms",(V/'r1912-axioms.log').read_text())
assert len(parsed)+len(none)==6306 and {n for n,a in parsed}|set(none)==set(names)
assert all({a.strip() for a in aa.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'} for n,aa in parsed)
files=sorted([* (L/'TransposeFollowup').rglob('*.lean'),*(L/'FixedTapeCompiler').rglob('*.lean')]);assert len(files)==896
sources={str(p.relative_to(P)):sha(p) for p in [*files,L/'SupportAxioms.lean']};assert sources==review['final_source_sha256']
lines=sum(len(p.read_text().splitlines()) for p in files);assert lines==105723
assert read(V/'r1912-final-target-edit.json')['restored'] is True
for key in ['configuration_sha256','external_source_sha256']:
 for rel,h in before[key].items():assert sha(P/rel)==h
mutable={'README.md','paper/verified-results.txt','verification/progress.txt'}
for rel,h in before['log_sha256'].items():assert sha((A/'before-r1912-summary-update'/rel) if rel in mutable else P/rel)==h
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
base=timing('baseline-pilot-rebuild');merged=timing('merged-pilot-rebuild');old_noop=timing('baseline-incremental')
ratio=base['wall_seconds']/target['wall_seconds'];remaining=target['wall_seconds']/base['wall_seconds'];memory=target['max_rss_bytes']/base['max_rss_bytes']
status='Complete: build-speed refactor and normal validation; all six main theorem families and all 6297 original audited declaration contracts preserved.'
report=f'''R1912 — BUILD SPEED IMPLEMENTATION AND VERIFICATION
Checked {now}

RESULT
The representative SourceEndpointsMeaning target rebuild takes {target['wall_seconds']:.3f}s,
versus {base['wall_seconds']:.3f}s before: {ratio:.2f} times faster, or {100*(1-remaining):.2f}% less elapsed time.
The final target contains twenty original source bodies rather than the original
five. This is a measured target result with cached prerequisites, not a matched
whole-project rebuild speed ratio. Whole-project speedup remains unmeasured.

MEASUREMENTS
Workload                                     Before       After
Five-body scratch proof check (3-pair median)  73.840s      15.798s
Actual five-body Lake target (single pair)    {base['wall_seconds']:.3f}s      {merged['wall_seconds']:.3f}s
Final broader twenty-body Lake target         {base['wall_seconds']:.3f}s      {target['wall_seconds']:.3f}s
No-change whole-project Lake invocation        {old_noop['wall_seconds']:.3f}s       {noop['wall_seconds']:.3f}s

The scratch paired trials alternate order and show a 78.60% median saving.
The first adopted five-body merge shows a 73.35% actual-target saving.
The final target's reported child-process peak RSS falls from
{base['max_rss_bytes']/1e9:.3f} GB to {target['max_rss_bytes']/1e9:.3f} GB ({100*(1-memory):.1f}% less).
This is not an aggregate peak across simultaneous build processes.

The {timing('final-pilot-rebuild')['wall_seconds']:.3f}s repair-inclusive run rebuilt seventeen prerequisites and
this target. It is recorded separately and is not used as the isolated target
measurement. The isolated {target['wall_seconds']:.3f}s run removed the harmless benchmark-only
apply-id proof step, restored exact final bytes, and rebuilt only the target.
All timing logs include normal Lake startup and artifact work; no dependency
cache, hash or timestamp was forged to avoid recompilation.

IMPLEMENTATION
Nineteen coherent compiler routines replace 287 former module locations,
retiring 268 internal modules and adding seven lightweight Core modules.
Mathematical modules: 1157 -> 896. Mathematical source: 105579 -> 105723
(+144 lines, principally compatibility bridges). This reduces repeated
compiler/import work; it does not claim a reduction of mathematical content.
The grouping preserves original declaration/proof bodies, with import updates.
The Core split preserves original model definitions and old bridge statements.
The original sibling paper and dependency versions are unchanged.

ClosedNativePadding's full local prerequisite path falls from 188 to 38.
For edits to the actual NativeMicrocode implementation, affected modules fall
from 566 to 306 and the serial local path from 176 to 36. The global longest
local path falls from 188 to 81 and now lies on the analytic branch. These
are dependency-graph measurements, not wall-time ratios. SourceEndpointsMeaning's
parsed dependency closure falls from 8941 to 3282 vertices. The graph is
acyclic and has no missing local imports.

PRESERVATION AND CHECKS
All 6297 original declaration contracts are covered: 6028 exported type
representations are literally identical; 267 differing representations pass
exact-original-Expr kernel conversion; the remaining two pass separate kernel
checks against their exact archived source-level theorem headers. All ordered
universe-parameter lists are identical. The raw comparison retains all 269
differences and its failed literal-equality status; no mismatch was erased.

The initial original-Expr checker could not resolve two retired generated proof
constant names after module consolidation. Those two checks are therefore
reported as source-header preservation, not as successful original-Expr
conversion. Their full expression differences consist only of binder hygiene
and the generated proof references. The complete axiom audit checks 6306 unique
declarations, including nine new Core definitions/lemmas, using only propext,
Classical.choice and Quot.sound. All six original main theorem families retain
their strengthened R1911 statements. No new mathematical result is claimed.

The final ordinary full build passes {jobs} jobs with no warnings/errors.
Its {full['wall_seconds']:.3f}s elapsed time is validation cost for this set of changed
sources, not a matched comparison with R1911. Cached jobs are included in the
job count. The no-change invocation above is a separate cache-overhead check.
Normal Lean kernel checking validates the rebuilt proofs. The historical R1909
fresh kernel replay was not repeated and does not certify this new snapshot.

Independent source review reconstructs the pilot, Core split, broad grouping
and two explicit repairs. The narrower imports exposed one implicit fun_prop
measurability proof; it now uses an explicit measurable composition with the
same theorem statement and hypotheses. A deprecated Real import is replaced
by its supported target. No sorry, new axioms, unsafe proof shortcuts, raised
proof limits, disabled linters or dependency upgrades. All 117 original files,
204 pinned external sources and eight configuration files remain unchanged.

ORGANIZATION AND REPRODUCTION
Use r1912-module-guide.txt for moved routines and r1912-module-map.json for
machine-readable old-to-current imports. Public declaration names remain.
Some internal import paths are intentionally retired; update such imports
using the map. Exact former sources are archived at:
{A}
Obsolete generated artifacts for retired modules were removed; no active
source or dependency cache was removed. Full type manifests are compressed in
a byte-verified archive there; compact per-name digests, raw comparisons
and kernel/source-header preservation receipts remain here. Archived failure logs distinguish repaired operational
failures from the clean final build.

Run normal verification from lean/: lake build; lake env lean SupportAxioms.lean.
The historical scratch benchmark needs a restored R1911 source baseline and
its compiled prerequisites; the complete baseline source inventory is archived.
Do not blindly replay it against retired source paths. The timing driver and
source-edit records document the controlled target measurement. Current source
hashes, pin hashes and validation artifacts are in support-build.json.

NEXT
The measured target reached about one fifth of its former rebuild time.
If another optimization round is requested, profile the remaining analytic
serial path before changing it. Warm no-change timing is not a clean rebuild
benchmark. Further grouping trades lower startup cost against rechecking more
proofs per edit. The separate r1912-concurrency-note.txt records supported
controls and one small future contention experiment; no gain is assumed. No further refactor, commits, pushes or autonomous research
are started by this checkpoint.
'''
(V/'r1912-audit.txt').write_text(report)
completion={'checkpoint':'R1912','checked_at':now,'status':status,'full_build':{'exit_code':0,'jobs':jobs,'log':'verification/r1912-build.log','wall_seconds':full['wall_seconds']},'axiom_audit':{'exit_code':0,'declarations':6306,'log':'verification/r1912-axioms.log','allowed_axioms':sorted(before['allowed_axioms'])},'original_type_preservation':{**expected_counts,'ordered_universe_parameters_exact':True,'raw_comparison_status':'failed','raw_comparison_report':'verification/r1912-type-comparison.json','semantic_report':'verification/r1912-kernel-type-conversion.json','archive_report':'verification/r1912-type-archive.json','source_header_names':sorted(special)},'local_math_modules':896,'local_sources_including_audit':897,'source_lines_before':105579,'source_lines_after':lines,'net_mathematical_line_change':144,'all_six_main_targets_preserved':True,'original_files_unchanged':117,'external_sources_unchanged':204,'configurations_unchanged':8,'no_live_execution_handles':True,'retired_internal_modules':268,'new_core_modules':7,'module_location_map':'verification/r1912-module-map.json','target_performance':{'baseline_seconds':base['wall_seconds'],'final_seconds':target['wall_seconds'],'speedup_ratio':ratio,'remaining_fraction':remaining,'baseline_original_bodies':5,'final_original_bodies':20},'whole_project_speedup_ratio':None,'fresh_kernel_replay':'Not repeated. Current new/rebuilt proofs checked by normal full Lean build; R1909 replay applies to its historical snapshot.'}
write(V/'r1912-completion.json',completion)
readme=(P/'README.md').read_text();needle='Start with the [exact statements, improvements, scope and relevance](paper/verified-results.txt).'
assert needle in readme
insert=f'''The [R1912 build-speed pass](verification/r1912-audit.txt) reduces the measured
compiler target rebuild from **{base['wall_seconds']:.1f}s to {target['wall_seconds']:.1f}s**, while its merged target now
contains twenty former source bodies. Modules fall from 1157 to 896; the compiler
prerequisite path falls from 188 to 38. All 6297 original audited declaration
contracts are preserved: 6028 exact type matches, 267 kernel conversions and
two checks of exact archived theorem headers. The full build and
6306-declaration axiom audit pass.
This target measurement is not a whole-project speedup claim. Use the
[module guide](verification/r1912-module-guide.txt) to locate moved proofs.

'''
readme=readme.replace(needle,insert+needle).replace('[current completion record](verification/r1911-completion.json)','[current completion record](verification/r1912-completion.json)');(P/'README.md').write_text(readme)
f=P/'paper/verified-results.txt';text=f.read_text();start=text.index('STATUS:');end=text.index('COMMON NOTATION AND INTERPRETATION')
text=text[:start]+f'''STATUS: All six original targets verified with the R1911 strengthenings below. R1912 reorganizes modules and imports for faster builds, preserving all 6297 original declaration contracts (6028 literal type matches, 267 original-Expr kernel conversions, two exact archived-source-header checks), with ordered universe parameters unchanged. See verification/r1912-audit.txt for measurements and verification/r1912-module-guide.txt for moved module locations. Mathematical statements are unchanged by R1912.
Full lake build passed {jobs} jobs without warnings/errors. Axiom audit passed 6306 unique declarations using only propext, Classical.choice and Quot.sound. 897 local sources, 204 unchanged pinned external sources, 8 unchanged configurations. Original 117 files and directory inventory unchanged. No sorry, new axioms, unsafe, native_decide, raised proof limits or disabled linters. All execution handles terminal. No commits or pushes.

'''+text[end:];f.write_text(text)
with (V/'progress.txt').open('a') as out:out.write(f'''\n21 October 2026 — R1912 BUILD-SPEED IMPLEMENTATION COMPLETE
{status}
Measured target {base['wall_seconds']:.3f}->{target['wall_seconds']:.3f}s; final target contains 20 old bodies versus 5 before. Whole-project speedup unmeasured. 1157->896 mathematical modules; compiler path 188->38. Final build {jobs} jobs, 6306 axiom checks, 6297 original contracts covered (6028 literal, 267 original-Expr kernel conversions, two archived-header checks); ordered universe parameters unchanged. Source 105579->105723. Archived 268 retired internal modules, seven Core modules added, pins/original sibling unchanged. All handles terminal. See r1912-audit.txt. No commits/pushes.
''')
# Update the live receipt; its historical R1911 copy remains archived unchanged.
receipt=dict(before);receipt.update(checked_at=now,scope=status,build=f'lake build: success, {jobs} jobs; no warnings/errors; verification/r1912-build.log',axiom_audit='lake env lean SupportAxioms.lean: success, 6306 declarations; verification/r1912-axioms.log',source_sha256=sources,verified_declarations=names)
receipt['fresh_kernel_replay']=dict(before['fresh_kernel_replay']);receipt['fresh_kernel_replay']['status']=completion['fresh_kernel_replay']
logs=dict(before['log_sha256'])
for rel in mutable:logs[rel]=sha(P/rel)
excluded={'r1912-in-progress.json','r1912-final-receipt-check.json'}
for f in sorted(V.glob('r1912-*')):
 if f.is_file() and f.name not in excluded:logs[str(f.relative_to(P))]=sha(f)
receipt['log_sha256']=logs;receipt['type_preservation']='6297 original contracts covered: 6028 literal type matches, 267 exact-original-Expr kernel conversions, two exact archived-source-header kernel checks; ordered universe lists identical. All 269 raw differences retained in verification/r1912-type-comparison.json; semantic evidence in verification/r1912-kernel-type-conversion.json; archive evidence in verification/r1912-type-archive.json.'
write(V/'support-build.json',receipt)
s.update(status=status,completed_at=now,final_receipt='verification/support-build.json',report='verification/r1912-audit.txt');write(V/'r1912-in-progress.json',s)
state=read(R/'state.json');state['latest_build_optimization']={'checkpoint':'R1912','status':status,'report':str(V/'r1912-audit.txt'),'completed_at':now};write(R/'state.json',state)
prefix=f'''CURRENT BUILD OPTIMIZATION — R1912 COMPLETE
All six theorem families retain their R1911 statements. The representative
compiler target rebuild is {target['wall_seconds']:.3f}s versus {base['wall_seconds']:.3f}s before; the final target
contains 20 former source bodies versus 5 before. Whole-project speedup unmeasured.
Full build {jobs} jobs and 6306 axiom checks pass; 6297 original contracts covered:
6028 literal type matches, 267 original-Expr kernel conversions and two archived
source-header checks. Ordered universe parameters are identical. No live execution handles, commits or pushes. No new research is
started. Report: {V/'r1912-audit.txt'}
The older checkpoint entries below remain historical provenance.

'''
for f in [R/'README.txt',R/'next-target.txt']:
 a=A/'before-r1912-summary-update'/'research'/f.name;a.parent.mkdir(parents=True,exist_ok=True);assert not a.exists();shutil.copy2(f,a);f.write_text(prefix+f.read_text())
print(json.dumps({'checkpoint':'R1912','status':'finalized; independent final receipt validation still required','source_count':len(sources),'log_count':len(logs),'target_speedup_ratio':ratio,'report':str(V/'r1912-audit.txt')}))
