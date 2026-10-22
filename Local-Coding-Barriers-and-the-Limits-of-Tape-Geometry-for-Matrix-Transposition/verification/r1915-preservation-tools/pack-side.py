#!/usr/bin/env python3
"""Pack one sealed capture; verify every decompressed byte before publishing.
Only scratch/archive metadata are written. Full chunks are always retained.
"""
from pathlib import Path
import argparse,importlib.util,json,io,tarfile,os,hashlib
spec=importlib.util.spec_from_file_location('r1915_types',Path(__file__).with_name('types.py'));t=importlib.util.module_from_spec(spec);spec.loader.exec_module(t)
p=argparse.ArgumentParser(description=__doc__);p.add_argument('side',choices=['baseline','final']);p.add_argument('--capture',type=Path,default=Path('/private/tmp/r1915-preservation/capture'));p.add_argument('--output',type=Path,required=True);a=p.parse_args()
C=a.capture;d=t.read(C/f'{a.side}-compact.json');assert d['side']==a.side and d['declarations']==6306
files=[(f'{a.side}/{r["index"]:03d}.json',Path(r['path']),r) for r in d['chunks']]
for name in ['names.json','baseline-sources.json','before-receipt.json',f'{a.side}-compact.json',f'{a.side}-capture.json']:
 files.append((name,C/name,None))
for key,member in [('inspection_script',f'evidence/{a.side}-inspect.lean'),('execution',f'evidence/{a.side}-execution.json'),('log',f'evidence/{a.side}.log')]:files.append((member,Path(d[key]['path']),d[key]))
for name in ['prepare.py','types.py','pack-side.py']:files.append(('evidence/'+name,Path(__file__).with_name(name),None))
records=[]
for member,path,expected in files:
 if expected:t.verify(expected)
 records.append(t.record(path)|{'member':member})
assert len(records)==len({r['member'] for r in records})
inventory={'format':'r1915-single-capture-archive-inventory-v1','side':a.side,'declarations':6306,'members':records,'semantic_claim':'No before/after comparison is claimed by this archival operation.'}
raw=(json.dumps(inventory,sort_keys=True,indent=2)+'\n').encode();target=a.output.resolve();target.parent.mkdir(parents=True,exist_ok=True);partial=target.with_name(target.name+'.partial');assert not target.exists() and not partial.exists()
with partial.open('xb') as f:
 with tarfile.open(fileobj=f,mode='w:gz',compresslevel=6) as tar:
  for r in records:t.verify(r);tar.add(r['path'],arcname=r['member'],recursive=False)
  info=tarfile.TarInfo('inventory.json');info.size=len(raw);tar.addfile(info,io.BytesIO(raw))
expected={r['member']:r for r in records};seen=set()
with tarfile.open(partial,'r|gz') as tar:
 for member in tar:
  assert member.isfile() and member.name not in seen;seen.add(member.name)
  frozen={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()} if member.name=='inventory.json' else expected[member.name]
  assert member.size==frozen['bytes'],(member.name,'archive size differs from frozen inventory')
  original=io.BytesIO(raw) if member.name=='inventory.json' else Path(frozen['path']).open('rb')
  with original,tar.extractfile(member) as f:t.verify_archived_member(f,original,frozen,member.name)
assert seen==set(expected)|{'inventory.json'}
os.link(partial,target);partial.unlink()
receipt={'format':'r1915-single-capture-archive-v1','status':'byte_verified','side':a.side,'declarations':6306,'members':len(seen),'archive':t.record(target),'compact':t.record(C/f'{a.side}-compact.json'),'inputs_retained':True,'verification':'Each decompressed archive member compared byte-for-byte with original and its size and SHA256 checked against the frozen inventory before publication.'}
t.write(C/f'{a.side}-archive.json',receipt);print(json.dumps(receipt))
