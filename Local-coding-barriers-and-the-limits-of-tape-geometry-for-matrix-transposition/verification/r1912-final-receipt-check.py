#!/usr/bin/env python3
"""Read-only FINAL receipt validation; run after all R1912 work is terminal.
Does not execute Lean/Lake, mutate source/config/cache files, or trust a success
string in place of the saved logs. Writes only its requested scratch report.
Expected completion schema follows r1911-completion.json: checkpoint, full_build,
axiom_audit, all_six_main_targets_preserved, no_live_execution_handles.
"""
from pathlib import Path
import argparse,hashlib,json,re,io,tarfile
from contextlib import nullcontext
from itertools import zip_longest
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition');V=P/'verification'
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--receipt',type=Path,default=V/'support-build.json')
ap.add_argument('--state',type=Path,default=V/'r1912-in-progress.json')
ap.add_argument('--completion',type=Path,default=V/'r1912-completion.json')
ap.add_argument('--baseline-types',type=Path,default=V/'r1912-baseline-types.json')
ap.add_argument('--final-types',type=Path,default=V/'r1912-final-types.json')
ap.add_argument('--type-comparison',type=Path,default=V/'r1912-type-comparison.json')
ap.add_argument('--baseline-type-hashes',type=Path,default=V/'r1912-baseline-type-hashes.json')
ap.add_argument('--final-type-hashes',type=Path,default=V/'r1912-final-type-hashes.json')
ap.add_argument('--kernel-conversion',type=Path,default=V/'r1912-kernel-type-conversion.json')
ap.add_argument('--type-archive',type=Path,default=V/'r1912-type-archive.json')
ap.add_argument('--source-review',type=Path,default=V/'r1912-final-source-review.json')
ap.add_argument('--summary-archive-dir',type=Path,help='Contains prior README.md, paper/verified-results.txt and verification/progress.txt under original relative paths')
ap.add_argument('--output',type=Path,default=Path('/private/tmp/r1912-final-receipt-check.json'))
a=ap.parse_args()
def read(p):return json.loads(p.read_text())
def filehash(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def resolve(p):
 p=Path(p);return p if p.is_absolute() else P/p
state=read(a.state);completion=read(a.completion);receipt=read(a.receipt)
assert state['checkpoint']=='R1912' and completion['checkpoint']=='R1912'
assert state.get('live_handles')==[],('live handles',state.get('live_handles'))
assert completion.get('no_live_execution_handles') is True
assert completion.get('all_six_main_targets_preserved') is True
terminal=state['terminal_handles'];ids=[t['session'] for t in terminal]
assert len(ids)==len(set(ids)) and all(isinstance(t['exit_code'],int) for t in terminal)
assert 17582 in ids,'initial full-build handle lacks terminal record'
A=Path(state['archive']);old=read(A/'before-receipt.json');source_review=read(a.source_review)
allowed={'propext','Classical.choice','Quot.sound'}
assert set(receipt['allowed_axioms'])==set(old['allowed_axioms'])==allowed
counts={}
for key in ['source_sha256','configuration_sha256','external_source_sha256','log_sha256']:
 for r,h in receipt[key].items():assert filehash(resolve(r))==h,(key,r,'hash mismatch')
 counts[key]=len(receipt[key])
assert receipt['configuration_sha256']==old['configuration_sha256']
assert receipt['external_source_sha256']==old['external_source_sha256']
mutable_summaries={'README.md','paper/verified-results.txt','verification/progress.txt'}
summary_archive=a.summary_archive_dir or A/'before-r1912-summary-update'
archived_summaries={}
for r,h in old['log_sha256'].items():
 if r in mutable_summaries:
  assert r in receipt['log_sha256'],('current summary omitted from receipt',r)
  if receipt['log_sha256'][r]!=h:
   previous=summary_archive/r;assert filehash(previous)==h,('previous mutable summary not preserved',r)
   archived_summaries[r]=str(previous)
 else:assert receipt['log_sha256'].get(r)==h,('historical log receipt changed',r)
current={str(f.relative_to(P)) for root in [P/'lean/TransposeFollowup',P/'lean/FixedTapeCompiler'] for f in root.rglob('*.lean')};current.add('lean/SupportAxioms.lean')
assert current==set(receipt['source_sha256']),('source inventory differs',current^set(receipt['source_sha256']))
assert len(current)==897 and len(receipt['configuration_sha256'])==8 and len(receipt['external_source_sha256'])==204
assert receipt['source_sha256']==source_review['final_source_sha256'],'final independent source-review hashes are stale'
# Audit commands, receipt names, and actual axiom log all agree exactly.
names=re.findall(r'^#print axioms (\S+)\s*$',(P/'lean/SupportAxioms.lean').read_text(),re.M)
assert len(names)==len(set(names))==6306
original=old['verified_declarations'];assert len(original)==len(set(original))==6297
assert set(original)<=set(names)
assert len(receipt['verified_declarations'])==6306 and set(receipt['verified_declarations'])==set(names)
new=set(names)-set(original);assert new==set(source_review['new_audit_names']) and len(new)==9
assert completion['axiom_audit']['exit_code']==0 and completion['axiom_audit']['declarations']==6306
alog=resolve(completion['axiom_audit']['log']);atext=alog.read_text()
assert not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)',atext)
matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",atext)
noaxioms=re.findall(r"'([^']+)' does not depend on any axioms",atext)
parsed={n:{x.strip() for x in ax.split(',') if x.strip()} for n,ax in matches}
for n in noaxioms:assert n not in parsed;parsed[n]=set()
assert len(parsed)==len(matches)+len(noaxioms)==6306 and set(parsed)==set(names)
for n,ax in parsed.items():assert ax<=allowed,('forbidden axiom',n,ax-allowed)
assert completion['full_build']['exit_code']==0
blog=resolve(completion['full_build']['log']);btext=blog.read_text()
assert re.search(r'Build completed successfully',btext),'final build log lacks terminal success'
assert not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)|✖',btext),'final build has errors/warnings'
if 'jobs' in completion['full_build']:
 assert re.search(r'Build completed successfully\s*\('+str(completion['full_build']['jobs'])+r' jobs\)',btext),'full build job count differs'
# Decode top-level type-manifest entries incrementally: the baseline is ~894MB.
# Avoid retaining both full JSON dictionaries or allocating gigabytes unnecessarily.
def object_entries(path):
 decoder=json.JSONDecoder(object_pairs_hook=strict_object)
 with (path.open() if isinstance(path,Path) else nullcontext(path)) as f:
  buf='';pos=0;eof=False
  def more(size=262144):
   nonlocal buf,pos,eof
   buf=buf[pos:];pos=0;chunk=f.read(size);buf+=chunk;eof=not chunk
  def whitespace():
   nonlocal pos
   while True:
    while pos<len(buf) and buf[pos].isspace():pos+=1
    if pos<len(buf) or eof:return
    more()
  def expect(ch):
   nonlocal pos
   whitespace();assert pos<len(buf) and buf[pos]==ch,(str(path),'expected',ch,buf[pos:pos+20]);pos+=1
  def value():
   nonlocal pos
   whitespace()
   while True:
    try:v,end=decoder.raw_decode(buf,pos);pos=end;return v
    except json.JSONDecodeError:
     if eof:raise
     more(max(262144,len(buf)-pos))
  more();expect('{');whitespace()
  if pos<len(buf) and buf[pos]=='}':pos+=1
  else:
   while True:
    key=value();assert isinstance(key,str);expect(':');val=value();yield key,val
    whitespace();assert pos<len(buf)
    if buf[pos]=='}':pos+=1;break
    expect(',')
  whitespace();assert eof and pos==len(buf),(str(path),'trailing content')
def typesummary(path):
 result={}
 for n,v in object_entries(path):
  assert n not in result,('duplicate manifest name',n)
  assert set(v)=={'type','levelParams'} and isinstance(v['type'],str) and isinstance(v['levelParams'],list)
  result[n]=hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
 return result
def strict_object(pairs):
 out={}
 for k,v in pairs:
  assert k not in out,('duplicate JSON key',k)
  out[k]=v
 return out

def check_compact_type_archive(summary_path, original, baseline_compact_path, final_compact_path):
 summary=read(summary_path);bc=read(baseline_compact_path);fc=read(final_compact_path)
 semantic=read(a.kernel_conversion);archive_receipt=read(a.type_archive)
 assert summary['format']=='r1912-exact-lean-type-comparison-v1' and summary['status']=='failed'
 assert summary['different_declarations']==269 and len(summary['mismatches'])==269 and summary['archive'] is None
 different={r['name'] for r in summary['mismatches']};assert len(different)==269
 assert all(r['type_equal'] is False and r['levelParams_equal'] is True for r in summary['mismatches'])
 assert all(summary[k]==6297 for k in ['expected_original_declarations','baseline_declarations','final_declarations'])
 assert summary['chunk_pairs']==79 and summary['source_inventory_sha256']==filehash(A/'baseline-sources.json')
 assert semantic['format']=='r1912-kernel-type-conversion-v1' and semantic['status']=='passed'
 assert semantic['original_declarations']==6297 and semantic['raw_identical_declarations']==6028
 assert semantic['raw_different_declarations']==269 and semantic['kernel_converted_declarations']==267 and semantic['source_header_checked_declarations']==2
 assert len(semantic['declarations'])==len(set(semantic['declarations']))==269
 assert set(semantic['declarations'])==set(semantic['checks'])==different
 assert semantic['raw_comparison']['sha256']==filehash(summary_path) and semantic['archive'] is None
 assert archive_receipt['format']=='r1912-semantic-type-archive-v1' and archive_receipt['status']=='passed'
 assert archive_receipt['raw_comparison']['sha256']==filehash(summary_path)
 assert archive_receipt['semantic_comparison']['sha256']==filehash(a.kernel_conversion)
 for c,side in [(bc,'baseline'),(fc,'final')]:
  assert c['format']=='r1912-exact-lean-type-digests-v1' and c['side']==side and c['declarations']==6297
  assert set(c['types'])==set(original)
 names_path=summary_path.parent/Path(summary['compact_outputs']['original_names']).name
 record_names=read(names_path)
 assert record_names['names']==names[:6297] and record_names['count']==6297
 assert record_names['source_inventory_sha256']==summary['source_inventory_sha256']
 arc=archive_receipt['archive'];archive_path=Path(arc['path'])
 assert filehash(archive_path)==arc['sha256'] and archive_path.stat().st_size==arc['bytes']
 input_records={f"{r['side']}/chunks/{r['index']:03d}.json":r for r in summary['input_chunks']}
 assert len(input_records)==158 and all(f'{side}/chunks/{i:03d}.json' in input_records for side in ['baseline','final'] for i in range(79))
 def check_record(n,value,compact):
  assert set(value)=={'type','levelParams'} and isinstance(value['type'],str)
  assert isinstance(value['levelParams'],list) and all(isinstance(x,str) for x in value['levelParams'])
  encoded=value['type'].encode('utf-8')
  exact={'type_sha256':hashlib.sha256(encoded).hexdigest(),'type_utf8_bytes':len(encoded),'type_characters':len(value['type']),'levelParams':value['levelParams']}
  assert exact==compact[n],('compact digest does not describe archived type',n)
 class HashReader(io.RawIOBase):
  def __init__(self,stream):self.stream=stream;self.digest=hashlib.sha256();self.count=0
  def readable(self):return True
  def readinto(self,buf):
   block=self.stream.read(len(buf));n=len(block);buf[:n]=block;self.digest.update(block);self.count+=n;return n
 seen_members={};seen_names=set();pending={};inventory=None;small={};text_files={};aggregates={};actual_different={};same=0
 with tarfile.open(archive_path,'r|gz') as tar:
  for member in tar:
   assert member.isfile() and member.name not in seen_members,('unexpected/duplicate archive member',member.name)
   stream=tar.extractfile(member);assert stream is not None
   if member.name in ['baseline/aggregate.json','final/aggregate.json']:
    side=member.name.split('/')[0];comp=bc['types'] if side=='baseline' else fc['types'];aggregate_names=set();reader=HashReader(stream)
    with io.TextIOWrapper(io.BufferedReader(reader),encoding='utf-8') as text:
     for n,value in object_entries(text):
      assert n not in aggregate_names and n in comp;check_record(n,value,comp);aggregate_names.add(n)
    assert aggregate_names==set(original);digest=reader.digest.hexdigest();size=reader.count;aggregates[side]=len(aggregate_names)
   else:
    with stream:raw=stream.read()
    digest=hashlib.sha256(raw).hexdigest();size=len(raw)
    if member.name in input_records:
     expected=input_records[member.name];assert digest==expected['sha256'] and size==expected['bytes']
     data=json.loads(raw,object_pairs_hook=strict_object);assert isinstance(data,dict)
     side,index=expected['side'],expected['index'];comp=bc['types'] if side=='baseline' else fc['types']
     assert set(data)<=set(original)
     for n,value in data.items():check_record(n,value,comp)
     if side=='baseline':
      assert not pending and not (set(data)&seen_names);pending[index]=data
     else:
      assert index in pending;before=pending.pop(index);assert set(before)==set(data)
      for n in before:
       if before[n]==data[n]:same+=1
       else:actual_different[n]=(before[n],data[n])
      seen_names.update(data)
     del data
    elif member.name=='comparison/archive-inventory.json':inventory=json.loads(raw,object_pairs_hook=strict_object)
    elif member.name.endswith('.json'):small[member.name]=json.loads(raw,object_pairs_hook=strict_object)
    elif member.name.startswith('evidence/'):text_files[member.name]=raw.decode('utf-8')
    else:raise AssertionError(('unrecognized archive member',member.name))
   assert size==member.size;seen_members[member.name]={'bytes':size,'sha256':digest}
 assert not pending and seen_names==set(original) and same==6028 and set(actual_different)==different
 assert inventory is not None
 entries={r['member']:r for r in inventory['members']};assert len(entries)==len(inventory['members'])
 assert set(seen_members)==set(entries)|{'comparison/archive-inventory.json'}
 for name,r in entries.items():assert seen_members[name]=={'bytes':r['bytes'],'sha256':r['sha256']},('archive inventory mismatch',name)
 assert len(seen_members)==arc['verified_members']
 assert small['comparison/'+summary_path.name]==summary
 assert small['comparison/'+a.kernel_conversion.name]==semantic
 assert small['comparison/'+baseline_compact_path.name]==bc and small['comparison/'+final_compact_path.name]==fc
 assert small['comparison/'+names_path.name]==record_names
 assert seen_members['evidence/raw-compare-types.py']['sha256']==summary['comparator']['sha256']
 assert seen_members['evidence/baseline-sources.json']['sha256']==summary['source_inventory_sha256']
 provenance={'checker':'evidence/kernel-type-checker.lean','lean_log':'evidence/kernel-lean.log','execution_record':'evidence/kernel-execution.json','input_inventory':'evidence/ast-inventory.json','exact_source_headers':'evidence/source-header-checks.json'}
 for key,member in provenance.items():
  assert seen_members[member]=={'sha256':semantic[key]['sha256'],'bytes':semantic[key]['bytes']},('semantic provenance',key)
 execution=small['evidence/kernel-execution.json'];assert execution['exit_code']==0
 log=text_files['evidence/kernel-lean.log'];assert not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)',log)
 assert sum('R1912 kernel conversion chunk passed:' in line for line in log.splitlines())==34
 ast_inventory=small['evidence/ast-inventory.json'];ast=small['evidence/original-types-ast.json']
 assert ast_inventory['declarations']==269 and len(ast_inventory['chunks'])==34
 assert seen_members['evidence/original-types-ast.json']['sha256']==ast_inventory['sourceSHA256']
 assert ast['comparisonSHA256']==filehash(summary_path)
 assert seen_members['evidence/decode-expr-repr.py']['sha256']==ast['decoderSHA256']
 astrows={r['name']:r for r in ast['declarations']};assert len(astrows)==len(ast['declarations'])==269 and set(astrows)==different
 headers=small['evidence/source-header-checks.json'];assert headers['count']==len(headers['declarations'])==2
 header_names={r['name']:r for r in headers['declarations']}
 assert set(header_names)=={'TransposeFollowup.NativePaddedField.tail_trace','TransposeFollowup.CountedFill.emit_step'}
 assert headers['baseline_inventory_sha256']==summary['source_inventory_sha256'] and headers['checker_sha256']==semantic['checker']['sha256']
 checker=text_files['evidence/kernel-type-checker.lean'];baseline_sources=small['evidence/baseline-sources.json']
 for n,r in header_names.items():
  source=baseline_sources[r['baseline_source']];assert hashlib.sha256(source.encode()).hexdigest()==r['baseline_source_sha256']
  header=r['original_header'];assert source.count(header)==1 and hashlib.sha256(header.encode()).hexdigest()==r['original_header_sha256']
  old=n.rsplit('.',1)[1];new=r['auditor_declaration'].rsplit('.',1)[1]
  assert header.replace('theorem '+old+' ','theorem '+new+' ',1)==r['renamed_header']
  assert r['renamed_header'] in r['source_check_text'] and checker.count(r['source_check_text'])==1
  assert hashlib.sha256(r['source_check_text'].encode()).hexdigest()==r['source_check_text_sha256']
 covered=set();routes={'original_expr_kernel':0,'archived_source_header_kernel':0}
 for i in range(34):
  inp=f'semantic/input/{i:03d}.json';out=f'semantic/output/{i:03d}.json';entry=ast_inventory['chunks'][i]
  assert entry['index']==i and seen_members[inp]=={'sha256':entry['sha256'],'bytes':entry['bytes']}
  for member,key in [(inp,'input_chunks'),(out,'output_chunks')]:assert seen_members[member]=={'sha256':semantic[key][i]['sha256'],'bytes':semantic[key][i]['bytes']}
  transport=small[inp];result=small[out];rows=transport['declarations']
  assert transport['expectedDeclarations']==len(rows)<=8 and rows
  assert [r['name'] for r in rows]==entry['declarations']==[r['name'] for r in result['results']]
  assert transport['comparisonSHA256']==result['comparisonSHA256']==filehash(summary_path)
  assert transport['decoderSHA256']==result['decoderSHA256']==ast['decoderSHA256']
  assert result['status']=='passed' and result['checked_declarations']==len(rows) and result['kernel_positive_and_negative_controls'] is True
  assert result['input']==entry['path']==semantic['input_chunks'][i]['path']
  for row,check in zip(rows,result['results']):
   n=row['name'];assert n not in covered and n in different;covered.add(n)
   assert row==astrows[n] and check==semantic['checks'][n]
   for flag in ['original_repr_roundtrip_exact','current_repr_matches_final_capture','ordered_universe_parameters_exact']:assert check[flag] is True
   before,after=actual_different[n]
   assert row['baselineRepr']==before['type'] and row['currentRepr']==after['type']
   assert row['levelParams']==row['currentLevelParams']==check['levelParams']==before['levelParams']==after['levelParams']
   for side,field,prefix in [('baseline','baselineRepr','baseline'),('final','currentRepr','current')]:
    assert hashlib.sha256(row[field].encode()).hexdigest()==row[prefix+'ReprSHA256']==check[prefix+'ReprSHA256']
   if n in header_names:
    assert check['validation_route']=='archived_source_header_kernel' and check['kernel_identity_application_checked'] is False
    assert check['original_source_header_kernel_checked'] is True and check['auditor_declaration']==header_names[n]['auditor_declaration']
   else:
    assert check['validation_route']=='original_expr_kernel' and check['kernel_identity_application_checked'] is True
    assert check['original_source_header_kernel_checked'] is False and check['auditor_declaration'] is None
   routes[check['validation_route']]+=1
 assert covered==different and routes=={'original_expr_kernel':267,'archived_source_header_kernel':2}
 assert filehash(archive_path)==arc['sha256'],'archive changed during receipt validation'
 return {'method':'independent exact archived comparison:6028 raw-identical;267 original Expr kernel conversions;2 exact archived source-header kernel checks; complete semantic provenance and aggregate checks','original_types':6297,'raw_identical':6028,'raw_different':269,'original_expr_kernel':267,'archived_source_header_kernel':2,'chunk_pairs':79,'verified_archive_members':len(seen_members),'archive_path':str(archive_path),'archive_sha256':arc['sha256'],'aggregate_provenance_checked':aggregates,'baseline_compact_sha256':filehash(baseline_compact_path),'final_compact_sha256':filehash(final_compact_path),'comparison_summary_sha256':filehash(summary_path),'kernel_summary_sha256':filehash(a.kernel_conversion)}

if a.type_comparison.exists():
 type_evidence=check_compact_type_archive(a.type_comparison,original,a.baseline_type_hashes,a.final_type_hashes)
else:
 seen_type_names=set();sentinel=object()
 for before_item,after_item in zip_longest(object_entries(a.baseline_types),object_entries(a.final_types),fillvalue=sentinel):
  assert before_item is not sentinel and after_item is not sentinel,'full type manifest lengths differ'
  n,before_value=before_item;after_n,after_value=after_item
  assert n==after_n,('full type manifests need matching key order for bounded-memory exact comparison',n,after_n)
  assert n not in seen_type_names and n in original
  assert set(before_value)=={'type','levelParams'} and isinstance(before_value['type'],str) and isinstance(before_value['levelParams'],list)
  assert before_value==after_value,('exact original type changed',n)
  seen_type_names.add(n)
 assert seen_type_names==set(original),'full manifest original type names differ'
 type_evidence={'method':'exact decoded full JSON record equality in matching key order, streamed with bounded memory','baseline_types_sha256':filehash(a.baseline_types),'final_types_sha256':filehash(a.final_types)}
# Repeat independent lexical trust screening, not just its recorded boolean.
def clean(s):
 out=list(s);i=0;depth=0;string=False;line=False
 while i<len(s):
  if line:
   if s[i]=='\n':line=False
   else:out[i]=' '
   i+=1;continue
  if depth:
   if s.startswith('/-',i):out[i:i+2]=[' ',' '];depth+=1;i+=2;continue
   if s.startswith('-/',i):out[i:i+2]=[' ',' '];depth-=1;i+=2;continue
   if s[i]!='\n':out[i]=' '
   i+=1;continue
  if string:
   if s[i]=='\\' and i+1<len(s):out[i:i+2]=[' ',' '];i+=2;continue
   if s[i]=='"':string=False
   if s[i]!='\n':out[i]=' '
   i+=1;continue
  if s.startswith('--',i):out[i:i+2]=[' ',' '];line=True;i+=2;continue
  if s.startswith('/-',i):out[i:i+2]=[' ',' '];depth=1;i+=2;continue
  if s[i]=='"':out[i]=' ';string=True
  i+=1
 assert depth==0 and not string
 return ''.join(out)
forbidden=set('sorry admit axiom unsafe native_decide implemented_by extern trustLevel addDecl addAndCompile mkAxiom mkSorry setEnv run_meta elab_rules initialize syntax macro_rules elab run_tac'.split())
for r in current:
 s=clean((P/r).read_text());assert not set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',s))&forbidden,r
 assert all(x.strip()=='autoImplicit false' for x in re.findall(r'^\s*set_option\s+(.+)$',s,re.M)),r
upstream=read(V/'upstream-baseline.json');U=P.parent/upstream['directory']
assert {str(f.relative_to(U)):filehash(f) for f in U.rglob('*') if f.is_file()}==upstream['files']
assert sorted(str(f.relative_to(U)) for f in U.rglob('*') if f.is_dir())==upstream['directories']
# Documentation must identify the current completed checkpoint; historical older
# counts may remain in explicitly dated history. Content accuracy also needs review.
for r in ['README.md','paper/verified-results.txt','verification/progress.txt']:
 assert 'R1912' in (P/r).read_text(),('current checkpoint absent from',r)
assert read(a.state).get('live_handles')==[],'new execution started during validation'
for r,h in receipt['source_sha256'].items():assert filehash(resolve(r))==h,('source changed during receipt audit',r)
result={'checkpoint':'R1912','status':'FINAL RECEIPT VALIDATION PASSED','hash_counts':counts,'sources_including_audit':len(current),'original_declarations_retained':6297,'audit_declarations':6306,'new_audit_names':sorted(new),'original_types_checked':6297,'raw_identical_original_types':6028,'original_expr_kernel_conversions':267,'archived_source_header_kernel_checks':2,'allowed_axioms':sorted(allowed),'all_recorded_handles_terminal':True,'terminal_handles':len(terminal),'prior_mutable_summaries_archived':archived_summaries,'protected_original_files':len(upstream['files']),'source_review_hashes_match':True,'no_Lean_Lake_executed':True,'documentation_checkpoint_present':True,'receipt_sha256':filehash(a.receipt),'type_evidence':type_evidence}
a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
