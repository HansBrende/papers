#!/usr/bin/env python3
"""Bind existing build, source-review and visual-review evidence to the PDF.

Requires pypdf. This checks that recorded reviews still apply; it does not
perform new semantic/visual reviews or repeat the Lean build.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import sys
from pypdf import PdfReader
from source_guard import (verify_digest, load_proof_refactors, refactor_audit_source,
                          check_refactor_audit, PROOF_MANIFEST)
from source_extensions import load_source_extensions

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'verification/manuscript'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(name):
    return json.loads((OUT / name).read_text())


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def binding(item):
    path = Path(item['path'])
    if not path.is_absolute():
        path = ROOT / path
    require(path.is_file() and sha(path) == item['sha256'], f'Stale evidence: {path}')


def main():
    public_check = subprocess.run([sys.executable, str(ROOT.parent / 'tools/check_public_paths.py')],
                                  cwd=ROOT.parent, text=True, capture_output=True)
    require(public_check.returncode == 0, 'Public-path check failed: ' + public_check.stdout)
    ver, inv = read('verification.json'), read('declarations.json')
    require(ver['status'] == 'passed', 'Formal verification failed')
    refactors = load_proof_refactors()
    if refactors is not None:
        evidence = ver.get('proof_refactor_manifest', {})
        require(evidence.get('path') == PROOF_MANIFEST, 'Missing proof-refactor verification evidence')
        binding({'path': evidence['path'], 'sha256': evidence['sha256']})
        binding({'path': evidence['audit_source'], 'sha256': evidence['audit_source_sha256']})
        require((ROOT / evidence['audit_source']).read_text() == refactor_audit_source(refactors),
                'Proof-refactor audit source does not match its declared scope')
        require(check_refactor_audit((OUT / 'proof-refactor-audit.log').read_text(), refactors)
                == ver.get('proof_refactor_types'), 'Original type audit evidence differs')
        require({r['path'] for r in ver.get('proof_refactors', [])}
                == {r['path'] for r in refactors['files']}, 'Proof-refactor source coverage differs')
    manifests, added_files, expected_labels = load_source_extensions()
    extensions = ver['source_extensions']
    require([x['manifest'] for x in extensions] == [str(p.relative_to(ROOT)) for p, _ in manifests],
            'Extension manifest coverage mismatch')
    for extension, (_, manifest) in zip(extensions, manifests):
        binding({'path': extension['manifest'], 'sha256': extension['manifest_sha256']})
        require(extension['files'] == manifest['files'], 'Extension receipt/manifest mismatch')
    expected_inventory = set(read('formal-baseline.json')['files']) | set(added_files)
    current_inventory = {str(p.relative_to(ROOT)) for base in ('lean/TransposeFollowup', 'lean/FixedTapeCompiler')
                         for p in (ROOT / base).rglob('*.lean')}
    require(current_inventory == expected_inventory, 'Mathematical source inventory changed after verification')
    require({i['label'] for i in inv['numbered_results']} == expected_labels,
            'Numbered results differ from original inventory plus explicit extensions')
    groups = [ver['sources'], inv['sources'], read('formal-baseline.json')['files'], added_files]
    support = json.loads((ROOT / 'verification/support-build.json').read_text())
    groups += [support[g] for g in ['source_sha256', 'configuration_sha256', 'external_source_sha256']]
    for group in groups:
        for path, digest in group.items():
            absolute = Path(path) if Path(path).is_absolute() else ROOT / path
            verify_digest(absolute, digest)
    for step in ver['steps'].values():
        require(step['exit_code'] == 0, 'Failed verification step')
        binding({'path': step['log'], 'sha256': step['log_sha256']})
    binding({'path': 'lean/PaperAxioms.lean', 'sha256': ver['paper_axioms_sha256']})
    binding({'path': 'lean/PacketAxioms.lean', 'sha256': ver['packet_axioms']['audit_source_sha256']})
    binding({'path': 'verification/manuscript/declarations.json', 'sha256': ver['inventory_sha256']})
    for item in inv['annotations']:
        binding({'path': item['source'], 'sha256': item['source_sha256']})
    contract_files = ['parent-contracts.json', 'local-coding-contracts.json', 'motion-contracts.json']
    contract_files += [str((ROOT / m['contracts']).relative_to(OUT))
                       for _, m in manifests if 'contracts' in m]
    contracts = sum((read(name) for name in contract_files), [])
    require(len(contracts) == len(inv['numbered_results']), 'Numbered-result count mismatch')
    require({c['label'] for c in contracts} == {c['label'] for c in inv['numbered_results']}, 'Contract coverage mismatch')
    require(all(n in inv['unique_declarations'] for c in contracts for n in c['declarations']), 'Unaudited contract declaration')
    review_set = read('review-set.json')
    semantic_files = review_set['semantic_files']
    reviewed_sources = set()
    for name in semantic_files:
        review = read(name)
        require(review['status'] == 'passed' and not review['unresolved_required_corrections'],
                f'Unresolved semantic review: {name}')
        for path, digest in review['reviewed_sources'].items():
            binding({'path': path, 'sha256': digest})
            reviewed_sources.add(path)
        for path, digest in review.get('independent_reports', {}).items():
            binding({'path': path, 'sha256': digest})
    require(set(inv['sources']) | {'paper/main.tex'} <= reviewed_sources,
            'Current manuscript section lacks a cross-review')
    roles = read(review_set['program_roles'])
    require({i['label'] for i in roles['items']} == {c['label'] for c in contracts}
            and all(i['role'] for i in roles['items']), 'Missing statement program role')
    for path, digest in roles['sources'].items():
        binding({'path': path, 'sha256': digest})
    ledger = read('attribution-ledger.json')
    keys = set(re.findall(r'@\w+\s*\{\s*([^,\s]+)', (ROOT / 'paper/references.bib').read_text()))
    require(keys == {s['source'] for s in ledger['sources']}, 'Attribution coverage mismatch')
    families = ledger['family_comparisons']
    # Families 1--6 are the original scope; 7--8 are this declared extension.
    # Do not infer the required inventory from the ledger's current length:
    # that would silently accept a truncated (or empty) ledger.
    require({c['family'] for c in families} == set(range(1, 9)) and len(families) == 8,
            'Missing or duplicate original/extension family comparison')
    require(all(s['status'] == 'checked_with_stated_scope' for s in ledger['sources']), 'Unfinished attribution')
    for item in ledger['manuscript_artifacts']:
        binding(item)
    pdf = ROOT / 'paper/main.pdf'
    digest, build = sha(pdf), read('latex-build.json')
    require(build['exit_code'] == 0 and build['pdf_sha256'] == digest, 'PDF/build receipt mismatch')
    require(not re.search(r'Overfull|Underfull|Warning|undefined', (ROOT / 'paper/build/main.log').read_text()), 'LaTeX diagnostics remain')
    reader = PdfReader(pdf)
    text = '\n'.join(page.extract_text() for page in reader.pages)
    require(len(reader.pages) > 0, 'Empty PDF')
    require(reader.metadata.author == 'Hans Brende and GPT-6 Astra (OpenAI)', 'PDF authors mismatch')
    require('\ufffd' not in text, 'Replacement character in PDF text')
    for snippet in ['CutIneq d G r T 0 0 h', '#print axioms', 'lake build', '--source-root PATH']:
        require(snippet in text, f'Inline command not preserved: {snippet}')
    manuscript = '\n'.join((ROOT / p).read_text() for p in inv['sources'])
    require(not re.search(r'\b(?:TODO|FIXME|TBD|PLACEHOLDER)\b', manuscript), 'Unfinished manuscript marker')
    visual_files = review_set['visual_files']
    first, last = [read(name) for name in visual_files]
    for review in [first, last]:
        require(review['status'] == 'passed' and review['pdf']['sha256'] == digest, 'Stale/failed visual review')
    reviewed = set(first['pages']) | set(last['pages'])
    require(reviewed == set(range(1, len(reader.pages) + 1)), 'Visual review misses pages')
    receipts = ['verification.json', 'latex-build.json', 'declarations.json', 'attribution-ledger.json',
                'review-set.json', review_set['program_roles'], *semantic_files, *visual_files, *contract_files]
    record = {
        'status': 'ready_for_user_review', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'pdf': {'path': 'paper/main.pdf', 'sha256': digest, 'pages': len(reader.pages)},
        'public_path_check': {'exit_code': public_check.returncode, 'summary': public_check.stdout.strip(),
                              'script_sha256': sha(ROOT.parent / 'tools/check_public_paths.py')},
        'coverage': {'theorem_families': len(families), 'numbered_definitions_and_results': len(contracts),
                     'audited_declarations': ver['axioms']['declarations'], 'cited_sources': len(keys),
                     'visually_reviewed_pages': sorted(reviewed)},
        'axioms': ver['axioms'], 'mathematical_sources_unchanged': ver['formal_sources_unchanged'],
        'comment_only_amendments': ver.get('comment_only_amendments', []),
        'mathematical_code_unchanged': ver['mathematical_code_unchanged'],
        'baseline_sources_verified': ver.get('baseline_sources_verified', ver['mathematical_code_unchanged']),
        'proof_refactors': ver.get('proof_refactors', []),
        'proof_refactor_manifest': ver.get('proof_refactor_manifest'),
        'proof_refactor_types': ver.get('proof_refactor_types'),
        'source_extensions': extensions,
        'packet_axioms': ver['packet_axioms'],
        'sources': ver['sources'], 'review_receipts': {name: sha(OUT / name) for name in receipts},
        'reproduction_scripts': {name: sha(OUT / name) for name in ['prepare.py', 'verify.py', 'build_paper.py', 'completion_check.py', 'source_guard.py', 'source_extensions.py', 'portable_paths.py']},
        'limitations': ['Unrestricted canonical transposition remains open.',
                       'Reviews are AI-agent checks, not external human peer review.',
                       'Novelty is qualified; the attribution search is not exhaustive.',
                       'An ordinary build/audit is not a new empty-environment replay of every imported expression.']}
    (OUT / 'completion.json').write_text(json.dumps(record, indent=2) + '\n')
    plan = read('workplan.json')
    plan['status'] = 'ready_for_user_review'
    plan['requirements'] = {key: 'completed; see completion.json and linked receipts' for key in plan['requirements']}
    (OUT / 'workplan.json').write_text(json.dumps(plan, indent=2) + '\n')
    print(json.dumps({'status': record['status'], 'coverage': record['coverage'], 'pdf': record['pdf']}))


if __name__ == '__main__':
    main()
