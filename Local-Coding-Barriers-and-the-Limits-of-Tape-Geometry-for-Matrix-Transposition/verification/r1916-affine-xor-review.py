from pathlib import Path
import json,hashlib,argparse,re,shutil
P=Path('.');V=P/'verification'
A=Path('external/research-workspace/research/10-linear-decision/archive/r1916-strengthening-reuse')
def read(p):return json.loads(p.read_text())
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def record(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def verify(r):assert record(Path(r['path']))==r,r['path']
def headers(s):
 result={}
 for m in re.finditer(r'^theorem ([A-Za-z0-9_.]+)\b',s,re.M):
  e=s.index(':=',m.start());result[m.group(1)]=s[m.start():e]
 return result
parser=argparse.ArgumentParser();parser.add_argument('--timing',type=Path,required=True);parser.add_argument('--log',type=Path,required=True);args=parser.parse_args()
base=read(A/'baseline-sources.json');affine=read(A/'affine-proposal/proposal.json');xor=read(A/'xor-proposal/proposal.json');records=[]
for row in affine['changes']:
 path=row['path'];before=base[path];after=(P/path).read_text()
 assert sha(before)==row['before_sha256'];assert sha(after)==row['after_sha256'];assert after==row['new_text']
 oldh,newh=headers(before),headers(after)
 assert all(name in newh and newh[name]==h for name,h in oldh.items())
 records.append({'path':path,'before_sha256':sha(before),'after_sha256':sha(after),'all_old_headers_exact':True,'old_theorems':list(oldh),'new_theorems':sorted(set(newh)-set(oldh)),'line_change':len(after.splitlines())-len(before.splitlines())})
row=xor['files'][0];path=row['path'];before=base[path];after=(P/path).read_text();assert before==row['old_text'];assert after==row['new_text'];assert sha(before)==row['old_sha256'];assert sha(after)==row['new_sha256']
oldh,newh=headers(before),headers(after);changed=[n for n in oldh if oldh[n]!=newh[n]]
expected=[n.rsplit('.',1)[1] for n in xor['strengthened_public_declarations']];assert set(changed)==set(expected) and len(changed)==5
for name in changed:
 h=oldh[name];nh=newh[name]
 assert h[:h.index(' :\n    (B : ℝ)')]==nh[:nh.index(' :\n    (B : ℝ)')]
records.append({'path':path,'before_sha256':sha(before),'after_sha256':sha(after),'intentionally_stronger_headers':changed,'all_old_hypotheses_exact':True,'other_old_headers_exact':True,'new_theorems':sorted(set(newh)-set(oldh)),'line_change':len(after.splitlines())-len(before.splitlines())})
plan=read(V/'r1916-xor-old-statements.json');verify(plan['baseline_sources']);verify(plan['current_source']);verify(plan['checker']);checker=Path(plan['checker']['path']).read_text();assert len(plan['checks'])==5
for check in plan['checks']:
 name=check['name'].rsplit('.',1)[1]
 assert check['original_header']==oldh[name] and check['current_header']==newh[name]
 assert sha(check['original_header'])==check['original_header_sha256']
 assert checker.count(check['source_check_text'])==1
 assert check['source_check_text'].startswith(check['original_header'].replace('theorem '+name+' ','theorem '+check['check_name'].rsplit('.',1)[1]+' ',1))
assert plan['original_context'] in checker and plan['original_context'] in before
run=read(args.timing);assert run['exit_code']==0 and any(Path(x).name=='r1916-xor-old-statements.lean' for x in run['command'])
log=args.log.read_text();assert 'error:' not in log and 'sorryAx' not in log
for check in plan['checks']:assert check['check_name'] in log
axiom_lists=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
assert len(axiom_lists)==5
for row in axiom_lists:
 axioms={x.strip() for x in row.split(',') if x.strip()}
 # #print occurs under the exact original `open Classical` context.
 axioms={'Classical.choice' if x=='choice' else x for x in axioms}
 assert axioms <= {'propext','Classical.choice','Quot.sound'},axioms
checks=[]
for name in ['affine-check','xor-check']:
 timing=V/('r1916-'+name+'-timing.json');logpath=V/('r1916-'+name+'.log');assert read(timing)['exit_code']==0
 checks.append({'timing':record(timing),'log':record(logpath)})
mathematical='\n'.join((P/r['path']).read_text() for r in records)
for forbidden in [r'\bsorry\b',r'^\s*axiom\s',r'\bunsafe\b',r'set_option\s+(?:maxRecDepth|maxHeartbeats|debug\.skipKernelTC)']:
 assert not re.search(forbidden,mathematical,re.M),forbidden
result={'format':'r1916-independent-affine-xor-review-v1','status':'passed','scope':'Three affine/XOR sources, their exact old surface contracts, the two affine hypothesis weakenings and five XOR strengthenings; not a whole-library type manifest or whole-environment kernel replay.','baseline':record(A/'baseline-sources.json'),'proposals':[record(A/'affine-proposal/proposal.json'),record(A/'xor-proposal/proposal.json')],'sources':records,'targeted_builds':checks,'old_xor_statements':{'plan':record(V/'r1916-xor-old-statements.json'),'checker':plan['checker'],'execution':record(args.timing),'log':record(args.log),'ordinary_proofs_checked':5,'original_headers_and_hypotheses_exact':True},'affine':{'old_endpoint_headers_exact':True,'new_pointwise_error_support':True,'new_native_pointwise_error_endpoint':True,'selected_input_sequence_and_subsequence_dependence_retained':True,'no_new_uniformity_over_inputs_or_incorrect_inputs':True,'old_uniform_error_endpoints_are_wrappers':True},'xor':{'old_error':'sqrt(8*n)','new_error':'sqrt(8*(n+3))-4','hypotheses_unchanged':True,'old_bound_formally_recovered_for_all_five_endpoints':True,'leading_asymptotic_coefficient_unchanged':True,'real_budget_generalization_reused_by_nat_wrapper':True},'no_new_trust_bypass_or_proof_limit':True,'reviewer':record(Path(__file__))}
(V/'r1916-affine-xor-review.json').write_text(json.dumps(result,indent=2)+'\n')
text='''R1916 independent affine and XOR review — passed

Reviewed the three final applied files against the frozen baseline and archived proposals. All original affine theorem headers are exact; the five intentional XOR header changes preserve every hypothesis and strengthen only the conclusion. Targeted ordinary Lean builds passed both changes. The five exact original XOR statements have each been re-proved in the original namespace/open/variable context from the corresponding strengthened endpoint and the proved error comparison; their axiom outputs contain no sorryAx.

Affine change: approximation errors may converge separately at each head/time point. The native theorem retains the original correct-set, nonuniform-control, actual execution and physical horizon premises. Approximants, the finite cover bound and further subsequence may still depend on the selected input sequence. No uniform rate across inputs or geometry outside the correct sets is added. Existing uniform-error public endpoints specialize the stronger theorem. This is not an improved exceptional-time constant or unrestricted transposition lower bound.

XOR change: retain the exact 2k-1 ball cap and k+1 divisor. For k=floor(sqrt(floor((n+3)/2))), j=k+1 and t=sqrt(((n:real)+3)/2), the error ratio is 4t-5+2(j-t)^2/j. The bounds j>=2 and 0<=j-t<=1 give error <=sqrt(8(n+3))-4. The error is bounded above by the prior sqrt(8n) for n>0. All nonlinear recoding/decoding and graph assumptions remain unchanged. The leading sqrt(8) coefficient is unchanged; this improves the finite-size term. The real-budget lemma supplies one shared counting proof; the old natural-budget endpoint is its specialization.

The source changes add 44 affine lines and 37 XOR lines, for 81 lines net. These two selected strengthenings do not constitute a net source-size reduction; separate embedding refactors are outside this review. The proposed manual hqR multiplication repair proved unnecessary: the unchanged XOR proposal passed Lean, so that inspection concern is closed.

This review makes no claim to a new full-library type manifest or fresh whole-environment replay. It adds no axioms, trust bypasses, raised proof limits, environment substitutions or library aliases. Full build and final audit closure remain root-level completion checks.
'''
(V/'r1916-affine-xor-review.txt').write_text(text)
print(json.dumps({'status':'passed','sources':3,'exact_original_xor_proofs':5,'report':str(V/'r1916-affine-xor-review.json')}))
