#!/usr/bin/env python3
"""Seal bounded captures, compare exact types, and archive evidence. Never runs Lean.
Hashes index provenance, never replace the exact old/new string comparison.
An archive preserves evidence even when differences remain unresolved; it does
not certify those differences harmless. No input deletion is performed.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,re,tarfile,io,os
DEFAULT=Path('external/temporary/r1914-preservation/capture')
def unique(pairs):
 d={}
 for k,v in pairs:
  if k in d:raise ValueError(f'duplicate JSON key: {k}')
  d[k]=v
 return d
def read(p):return json.loads(Path(p).read_text(),object_pairs_hook=unique)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def record(p):
 p=Path(p);return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':sha(p)}
def verify(r):
 actual=record(r['path']);assert all(actual[k]==r[k] for k in ['path','bytes','sha256']),r['path']
def verify_archived_member(stream,source,expected,member):
 h=hashlib.sha256();size=0
 while True:
  block=stream.read(1048576);assert block==source.read(1048576),(member,'archive bytes differ')
  if not block:break
  h.update(block);size+=len(block)
 assert size==expected['bytes'] and h.hexdigest()==expected['sha256'],(member,'archive differs from frozen inventory')
def write(p,j):
 with Path(p).open('x') as f:json.dump(j,f,ensure_ascii=False,sort_keys=True,indent=2);f.write('\n')
def digest(v):
 assert set(v)=={'type','levelParams'} and isinstance(v['type'],str)
 assert isinstance(v['levelParams'],list) and all(isinstance(x,str) for x in v['levelParams'])
 raw=v['type'].encode();return {'type_sha256':hashlib.sha256(raw).hexdigest(),'type_utf8_bytes':len(raw),'type_characters':len(v['type']),'levelParams':v['levelParams']}
def seal(C,side,execution,log):
 descriptor=read(C/f'{side}-capture.json');frozen=read(C/'names.json');expected=frozen['names']
 assert descriptor['side']==side and descriptor['declarations']==len(expected)==6306
 assert descriptor['frozen_names_sha256']==sha(C/'names.json')
 assert descriptor['inspection_script_sha256']==sha(descriptor['inspection_script'])
 timing=read(execution);assert timing['exit_code']==0
 assert isinstance(timing['command'],list) and descriptor['inspection_script'] in timing['command'],'successful execution did not run the frozen inspector'
 assert not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)',log.read_text())
 compact={};chunks=[]
 for i,entry in enumerate(descriptor['chunks']):
  assert entry['index']==i and entry['names']==expected[i*80:(i+1)*80]
  path=Path(entry['path']);v=read(path);assert set(v)==set(entry['names']) and not set(v)&set(compact)
  compact.update({n:digest(t) for n,t in v.items()});chunks.append(record(path)|{'index':i,'names':entry['names']})
 assert len(compact)==6306 and set(compact)==set(expected) and len(chunks)==79
 result={'format':'r1914-sealed-type-capture-v1','side':side,'declarations':6306,'types':compact,'chunks':chunks,'descriptor':record(C/f'{side}-capture.json'),'inspection_script':record(descriptor['inspection_script']),'frozen_names':record(C/'names.json'),'execution':record(execution),'log':record(log)}
 target=C/f'{side}-compact.json';write(target,result);print(target)
def compare(C):
 old,new=read(C/'baseline-compact.json'),read(C/'final-compact.json');names=read(C/'names.json')['names'];assert len(names)==6306
 for x in [old,new]:
  assert x['declarations']==6306 and set(x['types'])==set(names) and len(x['chunks'])==79
  for k in ['descriptor','inspection_script','frozen_names','execution','log']:verify(x[k])
 changed=[];same=0;seen=set()
 for i,(b,f) in enumerate(zip(old['chunks'],new['chunks'])):
  assert b['index']==f['index']==i and b['names']==f['names']==names[i*80:(i+1)*80]
  verify(b);verify(f);before,after=read(b['path']),read(f['path']);assert set(before)==set(after)==set(b['names']) and not set(before)&seen
  for n in b['names']:
   assert digest(before[n])==old['types'][n] and digest(after[n])==new['types'][n]
   if before[n]==after[n]:same+=1
   else:changed.append({'name':n,'chunk':i,'type_equal':before[n]['type']==after[n]['type'],'levelParams_equal':before[n]['levelParams']==after[n]['levelParams'],'baseline':before[n],'final':after[n]})
  seen.update(before)
 assert seen==set(names) and same+len(changed)==6306
 diffs={'format':'r1914-exact-type-differences-v1','declarations':len(changed),'differences':changed};write(C/'differences.json',diffs)
 result={'format':'r1914-exact-type-comparison-v1','status':'exact' if not changed else 'differences_require_review','original_declarations':6306,'raw_identical':same,'raw_different':len(changed),'different_names':[r['name'] for r in changed],'differences':record(C/'differences.json'),'baseline':record(C/'baseline-compact.json'),'final':record(C/'final-compact.json'),'method':'Exact decoded Expr repr string AND ordered universe-parameter list comparison. No normalization or hash shortcut. Changes require separate kernel conversion or explicitly distinguished exact source-contract evidence.'}
 write(C/'comparison.json',result);print(json.dumps({k:v for k,v in result.items() if k not in ['different_names']}))
def archive(C,target):
 assert target.suffixes[-2:]==['.tar','.gz'] and not target.exists();target.parent.mkdir(parents=True,exist_ok=True)
 comparison=read(C/'comparison.json');verify(comparison['baseline']);verify(comparison['final']);verify(comparison['differences'])
 files=[('names.json',C/'names.json'),('baseline-sources.json',C/'baseline-sources.json'),('before-receipt.json',C/'before-receipt.json'),('comparison.json',C/'comparison.json'),('differences.json',C/'differences.json'),('evidence/types.py',Path(__file__).resolve()),('evidence/prepare.py',Path(__file__).resolve().parent/'prepare.py')]
 for side in ['baseline','final']:
  compact=read(C/f'{side}-compact.json')
  files += [(f'{side}-compact.json',C/f'{side}-compact.json'),(f'{side}-capture.json',C/f'{side}-capture.json'),(f'evidence/{side}-inspect.lean',Path(compact['inspection_script']['path'])),(f'evidence/{side}-execution.json',Path(compact['execution']['path'])),(f'evidence/{side}.log',Path(compact['log']['path']))]
  for r in compact['chunks']:verify(r);files.append((f'{side}/{r["index"]:03d}.json',Path(r['path'])))
 semantic=C/'type-preservation.json'
 if semantic.exists():
  result=read(semantic);assert result['format']=='r1914-type-preservation-v1' and result['status']=='passed'
  assert result['raw_comparison']==record(C/'comparison.json')
  files.append(('semantic/type-preservation.json',semantic));known={p.resolve() for _,p in files}
  def semantic_records(value):
   if isinstance(value,dict):
    if {'path','bytes','sha256'}<=value.keys():yield value
    else:
     for child in value.values():yield from semantic_records(child)
   elif isinstance(value,list):
    for child in value:yield from semantic_records(child)
  for r in semantic_records(result):
   verify(r);path=Path(r['path']).resolve()
   if path not in known:
    files.append((f'semantic/evidence/{len(files):03d}-{path.name}',path));known.add(path)
 members=[record(p)|{'member':name} for name,p in files];assert len(set(r['member'] for r in members))==len(members)
 inventory={'format':'r1914-type-evidence-archive-inventory-v1','members':members,'comparison':record(C/'comparison.json'),'raw_type_status':comparison['status'],'semantic_preservation_certified_by_archive':False}
 invraw=(json.dumps(inventory,sort_keys=True,indent=2)+'\n').encode();partial=target.with_name(target.name+'.partial');assert not partial.exists()
 with partial.open('xb') as f:
  with tarfile.open(fileobj=f,mode='w:gz',compresslevel=6) as tar:
   for r in members:verify(r);tar.add(r['path'],arcname=r['member'],recursive=False)
   ti=tarfile.TarInfo('inventory.json');ti.size=len(invraw);tar.addfile(ti,io.BytesIO(invraw))
 expected={r['member']:r for r in members};seen=set()
 with tarfile.open(partial,'r|gz') as tar:
  for m in tar:
   assert m.isfile() and m.name not in seen;seen.add(m.name)
   frozen={'bytes':len(invraw),'sha256':hashlib.sha256(invraw).hexdigest()} if m.name=='inventory.json' else expected[m.name]
   assert m.size==frozen['bytes'],(m.name,'archive size differs from frozen inventory')
   source=io.BytesIO(invraw) if m.name=='inventory.json' else Path(frozen['path']).open('rb')
   with source,tar.extractfile(m) as stream:verify_archived_member(stream,source,frozen,m.name)
 assert seen==set(expected)|{'inventory.json'}
 os.link(partial,target);partial.unlink()
 receipt={'format':'r1914-type-evidence-archive-v1','status':'byte_verified','archive':record(target),'members':len(seen),'comparison':record(C/'comparison.json'),'raw_type_status':comparison['status'],'semantic_preservation_certified_by_archive':False,'semantic_preservation_receipt':record(semantic) if semantic.exists() else None,'inputs_removed':False}
 write(C/'archive.json',receipt);print(json.dumps(receipt))
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--capture',type=Path,default=DEFAULT);sub=p.add_subparsers(dest='command',required=True)
 s=sub.add_parser('seal');s.add_argument('side',choices=['baseline','final']);s.add_argument('--execution',type=Path,required=True);s.add_argument('--log',type=Path,required=True)
 sub.add_parser('compare');s=sub.add_parser('archive');s.add_argument('--output',type=Path,required=True)
 a=p.parse_args()
 if a.command=='seal':seal(a.capture,a.side,a.execution,a.log)
 elif a.command=='compare':compare(a.capture)
 else:archive(a.capture,a.output)
if __name__=='__main__':main()
