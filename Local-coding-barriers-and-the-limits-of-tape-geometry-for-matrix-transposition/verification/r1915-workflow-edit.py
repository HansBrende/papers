"""Identical harmless proof edit before and after the R1915 module merge."""
from pathlib import Path
import datetime, hashlib, json, sys

P = Path(__file__).resolve().parents[1]
V = P / 'verification'
state = json.loads((V / 'r1915-in-progress.json').read_text())
assert not state['live_handles']
mode = sys.argv[1]
assert mode in ['apply-baseline', 'restore-baseline', 'apply-candidate', 'restore-candidate']
side = mode.split('-')[1]
if side == 'baseline':
    rel = 'lean/TransposeFollowup/ConditionalSpectralExpansion.lean'
    original = json.loads((Path(state['archive']) / 'baseline-sources.json').read_text())[rel]
else:
    rel = 'lean/TransposeFollowup/UnconditionalPaidPadding.lean'
    receipt = json.loads((V / 'r1915-merge-application.json').read_text())
    original = next(c['new_text'] for c in receipt['changes'] if c['path'] == rel)
anchor = 'IntegrableOn (fun x => G.whole.weightedPullback f x*f x) (Icc (0:ℝ) 1) := by\n'
assert original.count(anchor) == 1
edited = original.replace(anchor, anchor + '  apply id\n')
apply = mode.startswith('apply-')
path = P / rel
assert path.read_text() == (original if apply else edited)
path.write_text(edited if apply else original)
sha = lambda s: hashlib.sha256(s.encode()).hexdigest()
record = V / 'r1915-workflow-edit.json'
r = json.loads(record.read_text()) if record.exists() else {
    'theorem': 'TransposeFollowup.RationalUnitMobius.weighted_correlation_integrableOn',
    'edit': 'Insert ordinary apply id immediately before the unchanged proof body.',
    'variants': {}, 'events': []}
r['variants'][side] = {'source': rel, 'original_sha256': sha(original), 'edited_sha256': sha(edited), 'restored': not apply}
r['events'].append({'mode': mode, 'at': datetime.datetime.now(datetime.timezone.utc).isoformat()})
r['restored'] = all(v['restored'] for v in r['variants'].values())
record.write_text(json.dumps(r, indent=2) + '\n')
print(mode, rel)
