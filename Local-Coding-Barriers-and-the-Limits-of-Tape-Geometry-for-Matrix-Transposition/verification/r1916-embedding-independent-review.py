from pathlib import Path
import hashlib,json
D=Path('external/temporary/r1916-embedding')
p=D/'proposal.json'; raw=p.read_bytes(); plan=json.loads(raw)
rows=[]
for c in plan['changes']:
 old,new=c['old_text'],c['new_text']
 assert hashlib.sha256(old.encode()).hexdigest()==c['old_sha256']
 assert hashlib.sha256(new.encode()).hexdigest()==c['new_sha256']
 reps=[r for r in plan['replacements'] if r['path']==c['path']]
 if reps:
  lines=old.splitlines(keepends=True); edits=[]
  for r in reps:
   start=sum(map(len,lines[:r['line']-1]))
   assert old.startswith(r['declaration'],start),(c['path'],r['line'])
   body=old.index(':= by',start)+len(':= by')
   assert old.startswith(r['old_proof_body'],body),(c['path'],r['line'],'body')
   edits.append((body,body+len(r['old_proof_body']),r['new_proof_body']))
  replay=old
  for a,b,s in sorted(edits,reverse=True):replay=replay[:a]+s+replay[b:]
  replay='import TransposeFollowup.PortBindingFrame\n'+replay
  assert replay==new,c['path']
  rows.append({'path':c['path'],'replacement_count':len(reps),'all_nonproof_source_exact_except_one_import':True,'old_sha256':c['old_sha256'],'new_sha256':c['new_sha256']})
 else:
  suffix='end TransposeFollowup.FinitePortBinding\n'
  assert old.endswith(suffix) and new.endswith(suffix)
  prefix=old[:-len(suffix)]
  assert new.startswith(prefix)
  addition=new[len(prefix):-len(suffix)]
  assert addition.count('theorem ')==1 and 'theorem embed_bank_project ' in addition
  assert 'simp only [MicrocodeEmbedding.embed,← values_eq_extend,map_values,values_project]' in addition
  rows.append({'path':c['path'],'existing_source_exact':True,'addition':addition,'old_sha256':c['old_sha256'],'new_sha256':c['new_sha256']})
assert sum(r.get('replacement_count',0) for r in rows)==13
saved=sum(c['old_text'].count('\n')-c['new_text'].count('\n') for c in plan['changes'])
assert saved==30
out={'format':'r1916-embedding-independent-source-review-v1','status':'source_review_passed_compile_pending','proposal':{'path':str(p),'sha256':hashlib.sha256(raw).hexdigest()},'reviewer':'r1912_imports','rows':rows,'preserved_existing_theorem_headers':13,'net_lines_saved':saved,'semantic_review':{'generic_lemma':'Definitionally unfolds the same MicrocodeEmbedding.embed, uses the existing values_eq_extend and map_values for tape denotation, and values_project for absolute head positions. The port embedding and label map are unchanged.','machine_and_cost_definitions':'All old nonproof source, including every machine, program, configuration, trace, state count, runtime budget and binding definition, is byte-for-byte preserved; only four imports are added.','scope':'Conservative direct-bank/project batch only. Earlier expanded proposal involving bespoke lifted banks was excluded and is not approved by this review.','trust':'New proof uses existing equalities and ordinary simp only. No axioms, sorry, unsafe code, native_decide, options, macros, or elaborators added.','caveat':'No Lean/Lake execution by reviewer. Higher-order inference and reduction of source cfg definitions still require root compilation.'}}
Path('external/temporary/r1916-embedding-independent-review.json').write_text(json.dumps(out,indent=2)+'\n')
print({'status':out['status'],'files':len(rows),'wrappers':13,'net_lines_saved':saved,'proposal_sha256':out['proposal']['sha256']})
