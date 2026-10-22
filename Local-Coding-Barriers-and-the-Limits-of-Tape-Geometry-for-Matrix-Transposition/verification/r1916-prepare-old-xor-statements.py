from pathlib import Path
import json,hashlib
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition');V=P/'verification';D=Path('/private/tmp/r1916-affine-xor-review')
A=Path('/Users/hansbrende/Documents/Codex/2026-10-09/a/research/10-linear-decision/archive/r1916-strengthening-reuse');B=A/'baseline-sources.json'
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def record(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
rel='lean/TransposeFollowup/XorPathCycleBound.lean';base=json.loads(B.read_text());old=base[rel];new=(P/rel).read_text();assert isinstance(old,str)
contexts='namespace TransposeFollowup\n\nopen Classical\nset_option autoImplicit false\n\nnamespace RecodedXorCode\n\nvariable {n b B : ℕ} (C : RecodedXorCode n b B)\n'
assert contexts in old and contexts in new
calls={'linear_ball_broadcast_lower_bound':'hc G hG hballs hn','cycle_embedding_broadcast_lower_bound':'hc G hG f hf hn','subcycle_broadcast_lower_bound':'hc G hG hcycle hn','cycle_broadcast_lower_bound':'hc hG hn','path_broadcast_lower_bound':'hc hG hn'}
source='import TransposeFollowup.XorPathCycleBound\n\n'+contexts+'\n';records=[]
for name,args in calls.items():
 start=old.index('theorem '+name+' ');end=old.index(':=',start);header=old[start:end]
 newname='r1916_original_'+name
 copied=header.replace('theorem '+name+' ','theorem '+newname+' ',1)
 assert copied.replace('theorem '+newname+' ','theorem '+name+' ',1)==header
 fragment=copied+''' := by
  have hstrong := C.'''+name+' '+args+'''
  have herror := linear_ball_error_le_sqrt n hn
  have hmul := mul_le_mul_of_nonneg_left herror
    (by positivity : 0 ≤ (b : ℝ) * n)
  linarith
'''
 source+=fragment+'\n#print axioms '+newname+'\n\n'
 ns=new.index('theorem '+name+' ');ne=new.index(':=',ns);nh=new[ns:ne]
 old_hyp=header[:header.index(' :\n    (B : ℝ)')];new_hyp=nh[:nh.index(' :\n    (B : ℝ)')];assert old_hyp==new_hyp
 records.append({'name':'TransposeFollowup.RecodedXorCode.'+name,'check_name':'TransposeFollowup.RecodedXorCode.'+newname,'original_header':header,'original_header_sha256':sha(header),'current_header':nh,'current_header_sha256':sha(nh),'all_hypotheses_exact':True,'source_check_text':fragment,'source_check_sha256':sha(fragment)})
source+='end RecodedXorCode\nend TransposeFollowup\n';out=V/'r1916-xor-old-statements.lean';assert not out.exists();out.write_text(source)
plan={'format':'r1916-original-xor-statements-v1','status':'prepared_not_executed','baseline_sources':record(B),'original_source_path':rel,'original_source_sha256':sha(old),'current_source':record(P/rel),'original_context':contexts,'checker':record(out),'preparer':record(Path(__file__)),'checks':records,'method':'Exact original full headers, changed only at declaration name, in the original namespace/open/variable context; ordinary proofs from strengthened current theorems and the independently proved error comparison. No source or environment substitutions.'}
(V/'r1916-xor-old-statements.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps({'checker':str(out),'checks':len(records),'sha256':sha(source)}))
