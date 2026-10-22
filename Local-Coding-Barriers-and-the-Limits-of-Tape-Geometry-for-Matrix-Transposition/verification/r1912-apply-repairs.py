from pathlib import Path
import json,hashlib
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition')
V=P/'verification'; A=Path('/Users/hansbrende/Documents/Codex/2026-10-09/a/research/10-linear-decision/archive/r1912-build-speed')
assert not json.loads((V/'r1912-in-progress.json').read_text())['live_handles']
proposals=json.loads((V/'r1912-queued-repairs.json').read_text())
for x in proposals:
 p=Path(x['path']); assert p.read_text()==x['old'],p
 assert p.is_relative_to(P/'lean')
 assert not (A/'repairs'/p.relative_to(P)).exists()
for x in proposals:
 p=Path(x['path']); a=A/'repairs'/p.relative_to(P); a.parent.mkdir(parents=True,exist_ok=True); a.write_text(x['old']); p.write_text(x['new'])
retired=[]
baseline=json.loads((A/'baseline-sources.json').read_text())
for rel in baseline:
 p=P/rel
 if p.exists(): continue
 assert p.suffix=='.lean' and p.parent.name in ('TransposeFollowup','FixedTapeCompiler')
 for folder in ('lib/lean','ir'):
  out=P/'lean/.lake/build'/folder/p.relative_to(P/'lean').parent
  for artifact in out.glob(p.stem+'.*'):
   assert artifact.is_file() and not artifact.is_symlink()
   retired.append(str(artifact.relative_to(P)));artifact.unlink()
report={'repairs':[{'path':str(Path(x['path']).relative_to(P)),'reason':x['reason'],'before_sha256':hashlib.sha256(x['old'].encode()).hexdigest(),'after_sha256':hashlib.sha256(x['new'].encode()).hexdigest()} for x in proposals], 'obsolete_generated_files_removed':retired, 'retired_source_count':sum(not (P/r).exists() for r in baseline)}
(V/'r1912-repairs-applied.json').write_text(json.dumps(report,indent=2)+'\n')
print('Applied',len(proposals),'repairs; removed',len(retired),'obsolete generated artifacts for',report['retired_source_count'],'retired sources.')
