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
from pypdf import PdfReader

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
    ver, inv = read('verification.json'), read('declarations.json')
    require(ver['status'] == 'passed', 'Formal verification failed')
    groups = [ver['sources'], inv['sources'], read('formal-baseline.json')['files']]
    support = json.loads((ROOT / 'verification/support-build.json').read_text())
    groups += [support[g] for g in ['source_sha256', 'configuration_sha256', 'external_source_sha256']]
    for group in groups:
        for path, digest in group.items():
            binding({'path': path, 'sha256': digest})
    for step in ver['steps'].values():
        require(step['exit_code'] == 0, 'Failed verification step')
        binding({'path': step['log'], 'sha256': step['log_sha256']})
    binding({'path': 'lean/PaperAxioms.lean', 'sha256': ver['paper_axioms_sha256']})
    binding({'path': 'verification/manuscript/declarations.json', 'sha256': ver['inventory_sha256']})
    for item in inv['annotations']:
        binding({'path': item['source'], 'sha256': item['source_sha256']})
    contract_files = ['parent-contracts.json', 'local-coding-contracts.json', 'motion-contracts.json']
    contracts = sum((read(name) for name in contract_files), [])
    require(len(contracts) == len(inv['numbered_results']) == 31, 'Numbered-result count changed')
    require({c['label'] for c in contracts} == {c['label'] for c in inv['numbered_results']}, 'Contract coverage mismatch')
    require(all(n in inv['unique_declarations'] for c in contracts for n in c['declarations']), 'Unaudited contract declaration')
    semantic_files = [f'final-pass-{part}-cross-review.json' for part in
                      ['local-coding', 'motion', 'padding-model', 'parent']]
    reviewed_sources = set()
    for name in semantic_files:
        review = read(name)
        require(review['status'] == 'passed' and not review['unresolved_required_corrections'],
                f'Unresolved semantic review: {name}')
        for path, digest in review['reviewed_sources'].items():
            binding({'path': path, 'sha256': digest})
            reviewed_sources.add(path)
    require(set(inv['sources']) | {'paper/main.tex'} <= reviewed_sources,
            'Current manuscript section lacks a cross-review')
    roles = read('final-pass-program-roles.json')
    require({i['label'] for i in roles['items']} == {c['label'] for c in contracts}
            and all(i['role'] for i in roles['items']), 'Missing statement program role')
    for path, digest in roles['sources'].items():
        binding({'path': path, 'sha256': digest})
    ledger = read('attribution-ledger.json')
    keys = set(re.findall(r'@\w+\s*\{\s*([^,\s]+)', (ROOT / 'paper/references.bib').read_text()))
    require(keys == {s['source'] for s in ledger['sources']}, 'Attribution coverage mismatch')
    require({c['family'] for c in ledger['family_comparisons']} == set(range(1, 7)), 'Missing family comparison')
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
    visual_files = ['final-pass-visual-part1.json', 'final-pass-visual-part2.json']
    first, last = [read(name) for name in visual_files]
    for review in [first, last]:
        require(review['status'] == 'passed' and review['pdf']['sha256'] == digest, 'Stale/failed visual review')
    reviewed = set(first['pages']) | set(last['pages'])
    require(reviewed == set(range(1, len(reader.pages) + 1)), 'Visual review misses pages')
    receipts = ['verification.json', 'latex-build.json', 'declarations.json', 'attribution-ledger.json',
                'final-pass-program-roles.json', *semantic_files, *visual_files, *contract_files]
    record = {
        'status': 'ready_for_user_review', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'pdf': {'path': 'paper/main.pdf', 'sha256': digest, 'pages': len(reader.pages)},
        'coverage': {'theorem_families': 6, 'numbered_definitions_and_results': len(contracts),
                     'audited_declarations': ver['axioms']['declarations'], 'cited_sources': len(keys),
                     'visually_reviewed_pages': sorted(reviewed)},
        'axioms': ver['axioms'], 'mathematical_sources_unchanged': ver['formal_sources_unchanged'],
        'sources': ver['sources'], 'review_receipts': {name: sha(OUT / name) for name in receipts},
        'reproduction_scripts': {name: sha(OUT / name) for name in ['prepare.py', 'verify.py', 'build_paper.py', 'completion_check.py']},
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
