from pathlib import Path
import copy, datetime, difflib, hashlib, json, re, sys

P = Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition')
V = P / 'verification'
R = Path('/Users/hansbrende/Documents/Codex/2026-10-09/a/research/10-linear-decision')
A = R / 'archive/r1916-strengthening-reuse'
def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p, d): p.write_text(json.dumps(d, indent=2) + '\n')
old = read(A / 'before-receipt.json')
base = read(A / 'baseline-sources.json')
state = read(V / 'r1916-in-progress.json')
assert not state['live_handles']
assert not (V / 'r1916-completion.json').exists()
full = read(V / 'r1916-full-build-timing.json')
axioms = read(V / 'r1916-final-axioms-timing.json')
assert full['exit_code'] == axioms['exit_code'] == 0
build_log = (V / 'r1916-full-build.log').read_text()
axiom_log = (V / 'r1916-final-axioms.log').read_text()
assert not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)|✖', build_log + axiom_log)
jobs = int(re.search(r'Build completed successfully \((\d+) jobs\)', build_log)[1])
names = re.findall(r'^#print axioms (\S+)\s*$', (P / 'lean/SupportAxioms.lean').read_text(), re.M)
assert len(names) == len(set(names)) == 6313
assert names[:len(old['verified_declarations'])] == old['verified_declarations']
found = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", axiom_log)
none = re.findall(r"'([^']+)' does not depend on any axioms", axiom_log)
assert len(found) + len(none) == len(names)
assert {n for n,_ in found} | set(none) == set(names)
assert all({a.strip() for a in ax.split(',') if a.strip()} <= set(old['allowed_axioms']) for _,ax in found)
sources = {str(p.relative_to(P)): p.read_text() for p in sorted((P/'lean').rglob('*.lean')) if '.lake' not in p.parts}
hashes = {r: hashlib.sha256(t.encode()).hexdigest() for r,t in sources.items()}
assert set(sources) == set(base)
changed = sorted(r for r in sources if sources[r] != base[r])
assert len(changed) == 9
guard = read(V / 'r1916-source-guards.json')
assert guard['source_sha256'] == hashes
assert guard['status'] == 'passed'
def verify_records(x):
    if isinstance(x, dict):
        if {'path','bytes','sha256'} <= x.keys():
            p=Path(x['path']); assert p.stat().st_size == x['bytes'] and sha(p) == x['sha256']
        else:
            for v in x.values(): verify_records(v)
    elif isinstance(x, list):
        for v in x: verify_records(v)
for k in ['baseline_sources','before_receipt','proposals','scoped_independent_reviews','successful_scoped_runs']:
    verify_records(guard[k])
for key in ['configuration_sha256', 'external_source_sha256']:
    for r,h in old[key].items():
        p=Path(r); p=p if p.is_absolute() else P/p
        assert sha(p) == h
mutable = {'README.md','paper/verified-results.txt','verification/progress.txt'}
for r,h in old['log_sha256'].items():
    assert sha(P/r) == h
latest = max((P/r).stat().st_mtime for r in sources)
assert all(datetime.datetime.fromisoformat(run['finished_at']).timestamp() >= latest for run in [full,axioms])
before_lines = sum(len(t.splitlines()) for r,t in base.items() if r != 'lean/SupportAxioms.lean')
after_lines = sum(len(t.splitlines()) for r,t in sources.items() if r != 'lean/SupportAxioms.lean')
assert (before_lines, after_lines) == (105741, 105792)
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
report = f'''R1916 — STRENGTHENING AND SHARED-PROOF PASS
Complete. Two theorem families strengthened; all six original targets retained.

AFFINE APPROXIMATION (FAMILY 3)
Approximation errors may now tend to zero separately at each fixed head/time
point. A single error envelope uniform over the whole time interval is no
longer required. The result is exposed both for the abstract obstruction and
for the native subsequential physical-head theorem. Native execution, correct
sets, entropy deficit, control cost and the full physical horizon are retained.
The cover still has a fixed finite number of affine pieces on the chosen
subsequence; approximants need not be Lipschitz. All input-sequence and
subsequence quantifiers remain. This is not an almost-everywhere assertion.
Existing uniform-error endpoints keep their exact statements and become
specializations. No exceptional-time constant is improved.

FINITE PATH/CYCLE XOR BOUND (FAMILY 2)
For n>0, P=n*n*b, the five real endpoints now give
  B >= P - b*n*(sqrt(8*(n+3))-4).
Previously the error was b*n*sqrt(8*n). All hypotheses on nonlinear row
bijections, all-input correctness, fixed XOR packets and graph locality are
unchanged. This improves a finite correction, not the leading sqrt(8)
coefficient or asymptotic order. The separate natural-number bound remains.
Take k=floor(sqrt(floor((n+3)/2))), j=k+1 and t=sqrt((n+3)/2) over the reals.
The exact error ratio is 4t-5+2(j-t)^2/j. Since j>=2 and 0<=j-t<=1, it is
at most 4t-4. The formal comparison lemma bounds this error by the old one.
A separate ordinary Lean file re-proves all five complete original statements
from the stronger current endpoints. A shared real ball-budget lemma now also
supplies the existing natural-budget theorem by specialization.
Deferred reuse observation (written algebra, not an additional Lean lemma):
the new real error also lies below 3*floor(sqrt(n)) for n>=1. Put m=floor(sqrt(n));
then m>=1 and n<=m*m+2*m, so 8*(n+3)<=(3*m+4)^2, since
m*m+8*m-8>=0. Thus the old natural bound could instead follow from the new
real bound. The existing short proof is retained; no size saving is claimed.

EMBEDDING REUSE AND SOURCE SIZE
One general framed-bank embedding identity, for arbitrary port and label
types, replaces 13 specialized proofs. It uses the existing map_values and
values_project lemmas. Labels, full tape contents, absolute head positions,
machine definitions, operational traces and all charged costs are unchanged.
This removes 30 net source lines, including the shared lemma and imports.
The two strengthenings add 81 lines, so TOTAL mathematical source changes
from {before_lines} to {after_lines}: NET +51 LINES. This pass is not a net
source-size reduction. No public theorem was retired to improve the count.
The reuse change touches four consumer modules and PortBindingFrame. Broader
cases with bespoke bank layouts were excluded because they need additional
layout reasoning; no blanket simplification or 38-module sweep is claimed.

SIX-FAMILY STATUS
1 Adaptive separators/treewidth: unchanged; arbitrary laws and sharp costs retained.
2 Nonlinear recoding/fixed XOR: sharper finite path/cycle bound above.
3 Affine motion: weaker pointwise-error approximation premise above.
4 Fully paid padding: unchanged, including universal resource formulas.
5 Two-stage helper: unchanged, including arbitrary-law entropy bounds.
6 Scan palettes/recursion: unchanged, including actual-native obligations.
Independent reviewers found no similarly inexpensive substantive improvement
to families 1, 4, 5 or 6 in this bounded pass. Main architecture restrictions
remain; these results do not decide unrestricted transposition or multiplication.

VALIDATION AND PRESERVATION
Full lake build passed {jobs} jobs in {full['wall_seconds']:.3f}s; axiom audit
passed all {len(names)} names in {axioms['wall_seconds']:.3f}s. Only propext,
Classical.choice and Quot.sound occur. All 6306 previously audited names remain;
seven audit entries add five new declarations and two existing XOR wrappers
that were not previously listed. The earlier wrappers were already compiled.
All focused checks and the five-original-XOR-statement recovery check passed.
Source/proposal replay and independent reviews verify unchanged old headers
except the five deliberate stronger XOR conclusions. No model definitions,
dependency pins, original sibling files, proof limits or trust settings changed.
No sorry, new axioms, unsafe bypass, disabled linter or environment substitution.
This is ordinary kernel compilation and targeted statement preservation, not a
fresh whole-environment replay or a new full exported-Expr comparison.
The full build replayed one pre-existing harmless ring-tactic info suggestion.
An initial embedding application script used the wrong JSON key and stopped
before any source write; its ensuing cached build is explicitly not counted as
validation. Corrected application passed without mathematical proof repairs.
All evidence and original sources are retained; no commits or pushes.

Main evidence: r1916-source-guards.json, r1916-affine-xor-review.txt,
r1916-embedding-independent-review.json, r1916-xor-old-statements.lean,
r1916-full-build.log and r1916-final-axioms.log.
Source archive: {A}
'''

if '--preview' in sys.argv:
    print(report)
    raise SystemExit(0)

# Prepare all human-readable updates before publishing.
readme = (P/'README.md').read_text()
anchor = 'Start with the [exact statements, improvements, scope and relevance](paper/verified-results.txt).'
assert readme.count(anchor) == 1
readme = readme.replace(anchor, 'The [R1916 strengthening pass](verification/r1916-audit.txt) improves the finite XOR bound and weakens the affine approximation premise to pointwise error. Thirteen compiler proofs now share one embedding lemma; total source grows by 51 lines after the stronger statements. All six theorem families remain proved.\n\n' + anchor)
readme = readme.replace('[current completion record](verification/r1915-completion.json)', '[current completion record](verification/r1916-completion.json)')
results = (P/'paper/verified-results.txt').read_text()
start = results.index('STATUS:'); end = results.index('COMMON NOTATION AND INTERPRETATION')
results = results[:start] + f'STATUS: R1916 complete. All six original theorem families remain proved. The path/cycle XOR bound and pointwise-error affine approximation obstruction are stronger; 13 compiler proofs share one general embedding lemma. Full build passes {jobs} jobs and the axiom audit passes {len(names)} names. Net mathematical source change +51 lines. See verification/r1916-audit.txt.\n\n' + results[end:]
assert results.count('  B >= P - b*n*sqrt(8*n).') == 1
results = results.replace('  B >= P - b*n*sqrt(8*n).', '  B >= P - b*n*(sqrt(8*(n+3))-4).')
anchor = 'These are finite improvements, not asymptotic changes.'
assert results.count(anchor) == 1
results = results.replace(anchor, anchor + '\nR1916 retains the exact ball cap and divisor to obtain the shifted square-root\nerror displayed above. Its five real endpoints keep every hypothesis; all five\noriginal statements were separately re-proved from the stronger versions.')
anchor = 'weaker pointwise premise; their statements remain unchanged.'
assert results.count(anchor) == 1
results = results.replace(anchor, anchor + '\nR1916 further removes the uniform error envelope in new abstract and native\nsubsequential endpoints: the approximation error need only vanish at each fixed\nhead/time point. The fixed finite affine-cover bound on the chosen subsequence\nremains. Existing uniform-error endpoints are exact specializations.')
results = results.replace('Total mathematical source is 105579 lines;', 'At R1911, total mathematical source was 105579 lines;')
results += '\nR1916 strengthens families 2 and 3 and shares 13 framed-bank embedding proofs.\nThe latter saves 30 lines; stronger statements add 81, giving 105792 total\nmathematical source lines (net +51 this pass). No old theorem is retired.\nSee verification/r1916-audit.txt for preservation scope and exact evidence.\n'
for r in mutable: assert sha(A/'before'/r) == old['log_sha256'][r]
(V/'r1916-audit.txt').write_text(report)
completion = dict(checkpoint='R1916', status='complete', checked_at=now,
    all_six_main_targets_preserved=True, strengthened_families=[2,3],
    unchanged_families=[1,4,5,6], original_audit_names_retained=6306,
    audited_declarations=len(names), new_declarations=5, prior_unaudited_names_added=2,
    embedding_proofs_reused=13, embedding_net_lines_removed=30,
    source_lines_before=before_lines, source_lines_after=after_lines, net_source_lines=51,
    changed_files=changed, source_files=len(sources), full_build=full, axiom_audit=axioms,
    preservation_scope='Reviewed source/header preservation plus five exact old-XOR proofs; no new full Expr comparison or fresh environment replay.',
    no_live_execution_handles=True, report='verification/r1916-audit.txt')
write(V/'r1916-completion.json',completion)
(P/'README.md').write_text(readme)
(P/'paper/verified-results.txt').write_text(results)
with (V/'progress.txt').open('a') as f:
    f.write(f'\n{now} — R1916 STRENGTHENING/REUSE COMPLETE\nFamilies 2 and 3 strengthened; all six original targets preserved.13 embedding proofs reused,30 lines saved;81 lines added for strengthenings,net+51. Full build{jobs} jobs;{len(names)} axiom checks;five original XOR statements recovered. No commits/pushes. See r1916-audit.txt.\n')
patch = ''.join(''.join(difflib.unified_diff(base[r].splitlines(True),sources[r].splitlines(True),fromfile='before/'+r,tofile='after/'+r)) for r in changed)
(V/'r1916-changes.patch').write_text(patch)
receipt = copy.deepcopy(old)
receipt.update(checked_at=now,scope='R1916: two families strengthened; 13 embedding proofs reused; six targets preserved.',
    build=f'lake build: success, {jobs} jobs; verification/r1916-full-build.log',
    axiom_audit=f'SupportAxioms.lean: success, {len(names)} declarations; verification/r1916-final-axioms.log',
    source_sha256=hashes,verified_declarations=names,
    type_preservation=completion['preservation_scope'])
receipt['fresh_kernel_replay']['status']='Not repeated for R1916. New/rebuilt proofs ordinarily kernel checked; historical replay belongs only to its snapshot.'
for r in mutable: receipt['log_sha256'][r]=sha(P/r)
excluded={'r1916-in-progress.json','r1916-final-receipt-check.json'}
for p in V.glob('r1916-*'):
    if p.is_file() and p.name not in excluded: receipt['log_sha256'][str(p.relative_to(P))]=sha(p)
write(V/'support-build.json',receipt)
state.update(status='R1916 complete',completed_at=now,report='verification/r1916-audit.txt')
write(V/'r1916-in-progress.json',state)
print(json.dumps(completion))
