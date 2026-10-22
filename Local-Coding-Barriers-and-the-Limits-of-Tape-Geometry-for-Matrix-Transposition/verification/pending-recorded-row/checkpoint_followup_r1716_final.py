from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib,subprocess
archive=Path('external/research-workspace');root=archive/'research/10-linear-decision'
paper=Path('.');ver=paper/'verification'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();now=datetime.now(timezone.utc).isoformat();log=archive/'research/state/research-log.txt'
assert 'R1716 —' not in log.read_text()
e=json.loads((root/'controls/evidence.json').read_text());assert len(e['files'])==384
for f,h in e['files'].items():assert sha(root/f)==h,f
r=json.loads((ver/'support-build.json').read_text());assert len(r['source_sha256'])==233
assert {f for f,h in r['source_sha256'].items() if sha(paper/f)!=h}=={'lean/SupportAxioms.lean'}
for f,h in r['configuration_sha256'].items():assert sha(paper/f)==h,f
for f,h in r['log_sha256'].items():
 if f not in {'verification/build.log','verification/axioms.log'}:assert sha(paper/f)==h,f
build=(ver/'build.log').read_text();assert 'Build completed successfully (9221 jobs).' in build;assert not re.search(r'\b(?:warning|error):',build)
audit=(ver/'axioms.log').read_text();rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]|'([^']+)' does not depend on any axioms",audit,re.S)
entries=[(a or c,{v.strip() for v in b.split(',') if v.strip()}) for a,b,c in rows]
assert len(entries)==1146 and len({n for n,_ in entries})==1146
for n,axs in entries:assert axs<={'propext','Classical.choice','Quot.sound'},(n,axs)
assert not re.search(r'\b(?:warning|error):',audit)
math=sorted((paper/'lean/TransposeFollowup').glob('*.lean'))+sorted((paper/'lean/FixedTapeCompiler').glob('*.lean'));assert len(math)==245
for p in math:assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide)\b',p.read_text()),p
up=json.loads(subprocess.run(['python3','verification/check_upstream.py'],cwd=paper,check=True,capture_output=True,text=True).stdout);assert up['unchanged'] and up['directories_unchanged'] and up['files_checked']==117
checks=[
 ('cleanup-primitive','cleanup_primitive_examples','([true, true, true, true, true, true, true], true, true, [true, true, true])\n','Twelve original NativeZipper checks:7 shuffled four-tape batches with varied widths0..5;one widths32..35 batch;one empty batch;3 scratch marker removals with negative/zero/positive positions. All selected cells blank,outside tapes retained,all heads and halt checked.'),
 ('row-cleanup','row_cleanup_examples','(18, 0)\n','Eighteen original39-tape cleanup executions:widths0..4 with zero/one/alternating words,plus8/16/32 alternating. All30 work words/temp marker cleared;6 seeds,deliberately nonblank counter,closed stream and39 heads preserved.'),
 ('reusable-row','reusable_row_examples','true\n','Full original39-tape ReusableRow execution for x/(x+1),N2,row1. Independently specified[true,false] output;all30 work words/temp/counter blank,all6 input/seed tapes and39 heads checked. Prepared-input caller only;stream consumption is separate.'),
 ('row-consumer','row_consumer_examples','[true, true, true, true, true, true]\n','Six complete original8-tape consumer executions:zero-width empty,positive-width empty,mixed,allfalse,alltrue,and five-bit mixed index words. Independent literal target lists specify output. All heads,all preserved input/template/fuel tapes,exact scratch START and every remaining blank cell,both cleared tapes,halt,and old output prefix checked.')]
# Check every output before any mutation: two long-running older execution checks may still be pending.
for stem,source,expected,purpose in checks:
 out=(ver/(stem+'-evaluation.log')).read_text();assert out==expected,(stem,out)
for stem,source,expected,purpose in checks:
 src=Path('external/temporary/'+source+'.lean')
 z={'purpose':purpose,'command':'lake env lean '+str(src),'exit_code':0,'source_sha256':sha(src),'source':src.read_text(),'observed_output':expected}
 if stem=='row-consumer':
  z.update(initial_test_source=Path('external/temporary/row_consumer_examples_initial.lean').read_text(),initial_test_output=Path('external/temporary/row-consumer-evaluation-initial.log').read_text(),diagnostic_source=Path('external/temporary/row_consumer_diagnostic.lean').read_text(),diagnostic_output=Path('external/temporary/row-consumer-diagnostic.log').read_text(),test_correction='Initial tests compared raw scratch zipper lists,incorrectly rejecting explicit blank tails. Diagnostic runs confirmed halt,output,all heads and other tapes. Only the test changed:it now requires the exact START marker and all remaining cells blank,as in the native tape semantics. Production program and proofs unchanged.',terminal_handles={'initial':21585,'diagnostic':12411,'corrected':93394})
 (ver/(stem+'-evaluation.json')).write_text(json.dumps(z,indent=2)+'\n')
status='In progress. R1716 proves actual row workspace reset plus a separate native row consumer. NativeBatchErase physically clears any fixed injected list of marked words in sum(4len+5),including empty lists;NativeUnprepare removes a scratch marker in2 transitions. NativeClosedStream proves rewind2N+4 and erase2N+3 with absolute positions. Explicit30-word row inventory and39-tape cleanup120m+154 are checked. ReusableRow composes row generation and cleanup,retaining exact denseRow and6 input/seed tapes;only stream advancesN. CostN(190m+451)+(674+36T)m+1539+104T;N-call budget fits inputLength. RowConsumer is separately proved:8 tapes,5 symbols,165 states;it rewinds a closed row,appends fixed-width pairs on true flags,increments a physical counter,and clears row/counter,with arbitrary prior output prefix retained. CostN(18m+58)+h(8m+12)+10m+30 <=N(26m+70)+10m+30. For unit1 and N<2^m,the output is exactly the selected indices;for denseRow,precisely F.neighbors with no within-row duplicates. N calls cost <=(72*size(E^2)+920)*inputLength.12 primitive,18 cleanup,1 integrated row and6 consumer execution checks pass. The actual40-tape row-to-record composition,raw input/seeds/index/outer rows,graph record normalization/clock/fetch/payload/full compiler,unconditional BY existence,motion and recursion remain.'
boundary='Prepared row computation,work reset,and a separate row consumer are all actual paid native computations. RowConsumer consumes/reset flags and preserves templates plus the old output prefix. ReusableRow alone retains the stream;the exact40-tape composition with separate persistent record storage is still pending. No per-row fresh storage/free discard is assumed. Raw input dimension/index loading,seed composition,index advance/outer iteration,map tags,inverse symmetrization,inter-map dedup/color/records,clock/fetch/payload/full generator remain. Unconditional Bourgain--Yehudayoff map-family existence is still unformalized. Affine motion200/210 and recursion206/208 remain required. Three of six families complete;referees after ALL. No improved main transpose bound or novelty claim.'
next_action='Complete actual40-tape RecordedRow composition:39 ReusableRow ports plus one separate persistent record-output tape. RowConsumer is fully checked;do not rebuild it. Use verification/pending-recorded-row draft. Bind its8 ports to stream,blank row counter,index/unit/zero/fuel/first scratch,and output. Prove embedding frames and absolute positions;compose ReusableRow.rational_trace and RowConsumer.complete_trace with2 paid jumps. Final row bank must equal original RowExecution.initial,all39 heads restored,only output advances,all6 seeds retained,exact neighbor index pairs appended. Derive total cost from existing row/consumer budgets. Then paid row-index increment and outer iteration,raw dimension/index/seed loading,record normalization and full clock/fetch/payload compiler. Unconditional BY existence,motion200/210,recursion206/208 remain separate. No commits/pushes;referees after ALL six families.'
req=json.loads((ver/'requirements.json').read_text());assert len(req['targets'])==6
for t in req['targets']:
 if t['id']=='paid_padding':t['status']=status
req['next_action']=next_action;req['updated_at']=now;req['open_dependency_boundary']['paid_padding']=boundary
for x in req['formalized_results']:
 if x['name']=='Supporting results':x['audit']='lean/SupportAxioms.lean;1146 declarations audited;standard Lean axioms only'
newfiles=['NativeBatchErase','NativeUnprepare','NativeClosedStream','RowCleanupInventory','RowCleanupMachine','RowCleanupRun','ReusableRow','RowConsumerData','RowConsumerMachine','RowConsumerCalls','RowConsumerLoop','RowConsumerRun','RowConsumerMeaning']
req['padding_support'].append({'name':'R1716 native workspace reuse and exact paid row consumer','scope':status,'files':['lean/TransposeFollowup/'+x+'.lean' for x in newfiles]})
req['native_arithmetic_reuse_audit']['row_cleanup_consumer']={'at':now,'finding':status};(ver/'requirements.json').write_text(json.dumps(req,indent=2)+'\n')
section='''
PAID WORKSPACE REUSE AND ROW CONSUMER — R1716
NativeBatchErase handles any fixed injection ofr distinct tapes,arbitrary
widths andr=0,in sum(4len+5),with8r+1 states. Outside tapes and all heads
survive. NativeUnprepare removes the temporary START in2 transitions.
NativeClosedStream gives native rewind2N+4 and erase2N+3 from STOP.
The actual row's30-word inventory and6 preserved input/seed tapes are
checked. RowCleanup uses39 tapes,5symbols,245states,cost120m+154.
ReusableRow combines row generation and cleanup in39 tapes and
198Slo+396Shi+396K+12073 states,with exact denseRow/source flag retained.
Only the stream head advancesN;all other workspace is reset. Cost:
 N(190m+451)+(674+36T)m+1539+104T.
ForN>=1,source valueN,length<=size(N+1),Ncalls cost at most
 ((1728+72T)*size(E^2)+21260+928T)*inputLength(N).

RowConsumer separately uses8tapes,5symbols,165states. It physically rewinds
closed flags,initializes a target index,appends(row index,target index) for
each true flag,increments the index,and erases both stream and counter.
No flags are destroyed during the forward scan;the existing eraser tail
resets them afterwards. Arbitrary old output prefix and all templates are
preserved. Stream returns from STOP by minusN;output advances2m*h.
CostN(18m+58)+h(8m+12)+10m+30 <= N(26m+70)+10m+30.
Exact native execution,framed call,length and no-wrap index semantics are
proved. For denseRow,the selected targets are exactly F.neighbors,without
within-row duplicates. N calls cost <=(72*size(E^2)+920)*inputLength.
This is still a separate consumer;the integrated40-tape caller is next.

VERIFICATION
Fullbuild9221 jobs,warning-free;1146 declarations audited with only
propext,Classical.choice and Quot.sound.245 mathematical modules(232new
follow-up,13own archived),plus audit=246 sources;5configs,65artifacts hashed.
12primitive,18cleanup,1integrated row and6consumer original executions pass.
The first consumer test rejected explicit scratch blank tails through raw
list equality;the retained diagnostics isolated this representation error.
The corrected test verifies START and every remaining blank cell. No
production code/proof changed. Exact independently supplied targets and
all heads/input words/prefix/cleanup are checked. Original117files/all
directories unchanged;archive384 intact. No commits/pushes. Three of six
families complete;referees after ALL. No new main-bound or novelty claim.

NEXT
'''+next_action+'\n'
p=ver/'progress.txt';s=p.read_text();a=s.index('\nVERIFICATION\n',s.index('COMPLETE PREPARED-INPUT NATIVE ROW — R1715'));b=s.index('\nSUBSTANTIAL OPEN DEPENDENCIES',a);p.write_text(s[:a]+section+s[b:])
p=paper/'README.md';s=p.read_text();old='''fits the input-size budget. Reusing stored preparation work and the stream,
raw-input dimension/index extraction and seed composition,''';new='''fits the input-size budget. Paid cleanup now returns the full30-word
preparation workspace blank. A separate8-tape165-state consumer converts
the retained row to exact duplicate-free neighbor index pairs,preserves
an existing output prefix,and resets the stream and index counter in
at most `N(26m+70)+10m+30` transitions. Six original consumer executions pass.
The integrated40-tape row-to-record caller,raw-input dimension/index extraction and seed composition,''';assert old in s;p.write_text(s.replace(old,new))
r.update(checked_at=now,scope=status+' Families181/186/188,181B,216 complete;referees pending.',build='lake build:success,9221jobs;no warnings',axiom_audit='lake env lean SupportAxioms.lean:success,1146declarations',verified_declarations=[n for n,_ in entries])
r['source_sha256']={str(p.relative_to(paper)):sha(p) for p in math+[paper/'lean/SupportAxioms.lean']}
for f in list(r['log_sha256'])+[f'verification/{stem}-evaluation.{ext}' for stem,_,_,_ in checks for ext in ['json','log']]:r['log_sha256'][f]=sha(paper/f)
assert len(r['source_sha256'])==246 and len(r['log_sha256'])==65
(ver/'support-build.json').write_text(json.dumps(r,indent=2)+'\n')
prefix='''CURRENT USER GOAL — FOLLOW-UP FORMALIZATION; R1716 CHECKPOINT
Formalize ALL SIX families;reuse original Lean. Original paper unchanged
without permission. No commits/pushes. Referees AFTER ALL formalization.
Three complete:181/186/188,181B,216. Padding201/202 in progress;
motion200/210 and recursion206/208 remain. No missing-dependency axioms.

'''+section+'''
Goal ACTIVE;PROGRESS. Research236/full080 unchanged.
The instructions/status below are historical wherever superseded here.
'''
marker='The instructions/status below are historical wherever superseded here.\n'
for name in ['README.txt','next-target.txt','research-policy.txt','follow-up-paper-plan.txt']:
 p=root/name;s=p.read_text();assert s.count(marker)==1;p.write_text(prefix+s.split(marker,1)[1])
s=json.loads((root/'state.json').read_text());s.update(current_unit='R1716 paid workspace reset and native row consumer checked;40-tape composition next',next_action=next_action,formalization_status=boundary,formalization_turn_classification='PROGRESS')
for k in ['last_formalization_progress_at','last_progress_at','last_status_at']:s[k]=now
f=s['followup_formalization'];f.update(next_action=next_action,last_build='9221jobs passed;no warnings',last_axiom_audit='1146declarations;standard axioms only',padding201202=status,open_dependencies=req['open_dependency_boundary'],native_arithmetic_reuse_audit=req['native_arithmetic_reuse_audit'],native_row_cleanup_consumer=boundary,execution_handles='All terminal:build9980exit0;finalaudit30342exit0;primitives52028exit0(12pass);cleanup26978exit0(18,0);integrated64928exit0(true);consumer initial21585exit0 had raw-scratch-list mismatch,diagnostic12411exit0 isolated it,corrected93394exit0(6pass). Earlier standalone builds and failed proof attempts documented in pending research history;no new missing axioms. RecordedRow draft is separate and not part of the verified production modules.')
(root/'state.json').write_text(json.dumps(s,indent=2)+'\n')
for name in ['README.txt','next-target.txt','research-policy.txt','follow-up-paper-plan.txt','state.json']:e['files'][name]=sha(root/name)
e['updated_at']=now;(root/'controls/evidence.json').write_text(json.dumps(e,indent=2)+'\n')
for f,h in e['files'].items():assert sha(root/f)==h,f
with log.open('a') as f:f.write('\nR1716 — PAID ROW WORKSPACE REUSE AND EXACT NATIVE CONSUMER\n'+now+'. Goal ACTIVE;PROGRESS.\n'+status+'\n'+section+'\n')
pending=ver/'r1716-pending.json'
if pending.exists():pending.unlink()
print(json.dumps({'checkpoint':'R1716','classification':'PROGRESS','build_jobs':9221,'declarations':1146,'mathematical_sources':245,'receipt_sources':246,'validation_artifacts':65,'execution_checks':[12,18,1,6],'archive_hashes':384,'goal':'ACTIVE'},indent=2))
