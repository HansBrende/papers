from pathlib import Path
import sys,json,hashlib
P=Path('.');V=P/'verification'
A=Path('external/research-workspace/research/10-linear-decision/archive/r1912-build-speed')
assert not json.loads((V/'r1912-in-progress.json').read_text())['live_handles']
p=P/'lean/TransposeFollowup/SourceEndpointsMeaning.lean';a=A/'final-target-before.lean';r=V/'r1912-final-target-edit.json'
old='Label.lower (GuardedEndpoint.program (A false) (B false) false (negative false) pc) := by\n  rcases pc with pc | pc'
new=old.replace(':= by\n',':= by\n  apply id\n')
if sys.argv[1]=='apply':
 assert not a.exists();s=p.read_text();assert s.count(old)==1; a.write_text(s); t=s.replace(old,new);p.write_text(t)
 r.write_text(json.dumps({'target':'TransposeFollowup.SourceEndpointsMeaning','original_body_count':20,'source_lines':len(s.splitlines()),'before_sha256':hashlib.sha256(s.encode()).hexdigest(),'temporary_sha256':hashlib.sha256(t.encode()).hexdigest(),'change':'Add ordinary apply id at the start of SourceEndpoints.lower_code; original source restored after target timing.','restored':False},indent=2)+'\n')
else:
 assert sys.argv[1]=='restore';s=a.read_text();assert p.read_text()==s.replace(old,new);p.write_text(s);row=json.loads(r.read_text());row['restored']=True;r.write_text(json.dumps(row,indent=2)+'\n')
print(sys.argv[1],p.name)
