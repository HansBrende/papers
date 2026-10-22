"""Update research entry points only after the completed build receipt passes."""
from pathlib import Path
import datetime
import json

P = Path(__file__).resolve().parents[1]
V = P / 'verification'
R = Path('external/research-workspace/research/10-linear-decision')
A = R / 'archive/r1914-analytic-build-speed'
completion = json.loads((V / 'r1914-completion.json').read_text())
check = json.loads((V / 'r1914-final-receipt-check.json').read_text())
assert completion['checkpoint'] == 'R1914'
assert completion['no_live_execution_handles']
assert check['status'] == 'FINAL RECEIPT VALIDATION PASSED', check
report = str(V / 'r1914-audit.txt')
prefix = f'''CURRENT BUILD OPTIMIZATION — R1914 COMPLETE
The same controlled proof edit now rebuilds in97.811s versus930.623s before:
217 ->6 rebuilt modules,9.51x faster,89.49% less time (one matched cached pair).
Independent three-pair import pilot14.395->5.334s; five-module merge36.701->7.991s.
Optimization validation rebuilt188 modules in244.300s. This is NOT a matched
comparison with the earlier22-minute run or a cold whole-project benchmark.
All6306 original contracts preserved:6295 literal type matches and11 exact
original-Expr kernel conversions; no source-header fallback was needed.
Full build10068 jobs;6306 allowed-axiom checks; all six theorem families and
shared models preserved. No proof repairs, weakened statements or trust changes.
893 mathematical modules. Original paper, dependency pins/configuration intact.
Report: {report}
Next optional build target: the six remaining broad-import spectral modules
(about15s each in the measured edit). Further grouping/import cuts need their
own benchmark and preservation checks. No new research or publication started.
The entries below are historical checkpoints, superseded for build status.

'''
archive = A / 'research-before-update'
assert not archive.exists()
archive.mkdir()
for name in ['README.txt', 'next-target.txt', 'state.json']:
    data = (R / name).read_bytes()
    (archive / name).write_bytes(data)
    assert (archive / name).read_bytes() == data
for name in ['README.txt', 'next-target.txt']:
    path = R / name
    old = path.read_text()
    assert old.startswith('CURRENT BUILD FOLLOW-UP — R1913 PLAN READY, NOT IMPLEMENTED')
    old = old.replace('CURRENT BUILD FOLLOW-UP — R1913 PLAN READY, NOT IMPLEMENTED',
                      'HISTORICAL BUILD PLAN — R1913 (IMPLEMENTED BY R1914)', 1)
    (R / name).write_text(prefix + old)
state = json.loads((R / 'state.json').read_text())
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
state['latest_build_optimization'] = {
    'checkpoint': 'R1914',
    'status': 'Complete: all three measured optimizations; all6306 original contracts and six theorem families preserved.',
    'report': report,
    'completed_at': now,
    'matched_edit': completion['matched_edit_workflow'],
    'cold_build_speedup_ratio': None,
}
state['latest_build_plan']['status'] = 'Implemented and validated in R1914; contention experiment unnecessary after measured dependency/import gains.'
state['last_status_at'] = now
(R / 'state.json').write_text(json.dumps(state, indent=2, ensure_ascii=False) + '\n')
print('Updated three research entry points; their exact old bytes are archived.')
