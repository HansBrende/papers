from pathlib import Path
import json,hashlib,sys,datetime
P=Path(__file__).resolve().parents[1];V=P/'verification'
s=json.loads((V/'r1914-in-progress.json').read_text());assert not s['live_handles']
A=Path(s['archive']);rel='lean/TransposeFollowup/ConditionalSpectralExpansion.lean';p=P/rel
original=json.loads((A/'baseline-sources.json').read_text())[rel]
anchor='IntegrableOn (fun x => G.whole.weightedPullback f x*f x) (Icc (0:ℝ) 1) := by\n'
assert original.count(anchor)==1
modified=original.replace(anchor,anchor+'  apply id\n')
mode=sys.argv[1];assert mode in ['apply-baseline','restore-baseline','apply-candidate','restore-candidate']
apply=mode.startswith('apply-');assert p.read_text()==(original if apply else modified)
p.write_text(modified if apply else original)
f=V/'r1914-workflow-edit.json';r=json.loads(f.read_text()) if f.exists() else {'source':rel,'theorem':'TransposeFollowup.RationalUnitMobius.weighted_correlation_integrableOn','original_sha256':hashlib.sha256(original.encode()).hexdigest(),'edited_sha256':hashlib.sha256(modified.encode()).hexdigest(),'edit':'Insert ordinary apply id before the existing proof; exact same proof-only edit in both variants.','events':[]}
r['events'].append({'mode':mode,'at':datetime.datetime.now(datetime.timezone.utc).isoformat()});r['restored']=not apply;f.write_text(json.dumps(r,indent=2)+'\n');print(mode)
