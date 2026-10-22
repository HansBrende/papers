from pathlib import Path
import json,hashlib,shutil,sys,datetime
P=Path(__file__).resolve().parents[1];V=P/'verification';s=json.loads((V/'r1914-in-progress.json').read_text());assert not s['live_handles'];A=Path(s['archive'])
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
mode=sys.argv[1];changes=[]
if mode=='imports':
 for rel,old_header,new_header in [
  ('lean/TransposeFollowup/RealMobiusAverage.lean','import TransposeFollowup.RationalMobiusAction\n','import TransposeFollowup.RealMobiusL2\n'),
  ('lean/TransposeFollowup/SpectralGapInterface.lean','import TransposeFollowup.RealMobiusAverage\n','import TransposeFollowup.RealMobiusAverage\nimport TransposeFollowup.RationalMobiusAction\n')]:
  old=(P/rel).read_text();assert old.startswith(old_header);new=new_header+old[len(old_header):]
  changes.append(dict(path=rel,old_text=old,new_text=new,old_sha256=sha(old),new_sha256=sha(new)))
 assert json.loads((V/'r1914-import-confirmation-summary.json').read_text())['status']=='passed'
elif mode=='geometry':
 proposal=json.loads(Path('external/temporary/r1914-geometry/proposal.json').read_text());changes=proposal['changes'];assert len(proposal['relocations'])==8
else:raise SystemExit('Expected imports or geometry')
record=V/f'r1914-{mode}-application.json';assert not record.exists()
for c in changes:
 p=P/c['path'];old=c['old_text']
 assert (p.read_text() if p.exists() else None)==old,c['path']
 assert c['old_sha256']==(sha(old)if old is not None else None)
 assert c['new_sha256']==sha(c['new_text'])
for c in changes:
 p=P/c['path'];dest=A/mode/c['path'];dest.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():shutil.copy2(p,dest)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(c['new_text'])
record.write_text(json.dumps({'status':'applied; Lean validation pending','at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'changes':changes},indent=2)+'\n')
print('Applied',mode,len(changes),'files; normal Lean validation pending.')
