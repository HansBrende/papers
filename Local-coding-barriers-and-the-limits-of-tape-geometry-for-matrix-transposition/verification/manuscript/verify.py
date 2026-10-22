#!/usr/bin/env python3
"""Reproducible manuscript declaration/build audit; no proof-source edits.

Semantic statement correspondence and visual review are separately recorded.
This script reports exactly an ordinary Lake build, an axiom audit of all
manuscript annotations, static citation/reference checks and source guards.
"""
from pathlib import Path
import datetime
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'verification/manuscript'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(name, command, cwd=ROOT):
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    tic = time.monotonic()
    log = OUT / (name+'.log')
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
    item = {'command': command, 'cwd': str(cwd), 'started_at': start,
            'seconds': time.monotonic()-tic, 'exit_code': result.returncode,
            'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log)}
    print(json.dumps({'step': name, **item}), flush=True)
    return item


def main():
    receipt = {'status': 'running', 'scope': 'ordinary build and manuscript-specific audit', 'steps': {}}
    receipt_path = OUT / 'verification.json'
    def save():
        receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
    def step(name, command, cwd=ROOT):
        receipt['steps'][name] = run(name, command, cwd)
        save()
        if receipt['steps'][name]['exit_code']:
            raise RuntimeError(f'{name} failed; inspect its log')
    save()
    try:
        step('prepare', [sys.executable, str(OUT / 'prepare.py')])
        inv = json.loads((OUT / 'declarations.json').read_text())
        texts = [(ROOT / path).read_text() for path in inv['sources']]
        combined = '\n'.join(texts) + (ROOT/'paper/generated/theorem-index.tex').read_text()
        labels = re.findall(r'\\label\{([^{}]+)\}', combined)
        if len(labels) != len(set(labels)):
            raise RuntimeError('Duplicate manuscript labels')
        refs = {name.strip() for group in re.findall(r'\\(?:[cC]ref|ref|eqref)\{([^{}]+)\}', combined)
                for name in group.split(',')}
        missing_refs = sorted(refs - set(labels))
        bib = (ROOT / 'paper/references.bib').read_text()
        keys = re.findall(r'@\w+\s*\{\s*([^,\s]+)', bib)
        citations = {name.strip() for group in re.findall(r'\\cite(?:\[[^\]]*\])*\{([^{}]+)\}', combined)
                     for name in group.split(',')}
        missing_citations = sorted(citations-set(keys))
        if missing_refs or missing_citations or len(keys) != len(set(keys)):
            raise RuntimeError(f'Reference/citation failure: {missing_refs}, {missing_citations}')
        receipt['static'] = {'labels': len(labels), 'citations': len(citations), 'bibliography_entries': len(keys),
                             'missing_references': missing_refs, 'missing_citations': missing_citations}
        baseline = json.loads((OUT / 'formal-baseline.json').read_text())['files']
        actual = {str(f.relative_to(ROOT)):sha(f) for base in ('lean/TransposeFollowup','lean/FixedTapeCompiler')
                  for f in (ROOT/base).rglob('*.lean')}
        if actual != baseline:
            raise RuntimeError('Mathematical sources differ from manuscript-start baseline')
        receipt['formal_sources_unchanged'] = len(actual)
        step('upstream', [sys.executable, 'verification/check_upstream.py'])
        step('openai-source', [sys.executable, 'verification/fetch_openai_metric.py', '--check'])
        # R1916's staging guard intentionally refuses already-updated publication
        # summaries. The final receipt is the correct source baseline now.
        prior_path = ROOT/'verification/support-build.json'
        prior = json.loads(prior_path.read_text())
        guard = {'basis': str(prior_path.relative_to(ROOT)), 'basis_sha256': sha(prior_path),
                 'scope': 'Exact source/configuration/external hash preservation against the final R1916 receipt',
                 'groups': {}}
        for group in ('source_sha256', 'configuration_sha256', 'external_source_sha256'):
            expected_hashes = prior[group]
            for relative, expected in expected_hashes.items():
                path = Path(relative)
                if not path.is_absolute():
                    path = ROOT/path
                if not path.is_file() or sha(path) != expected:
                    raise RuntimeError(f'Formal preservation failure: {group}: {relative}')
            guard['groups'][group] = len(expected_hashes)
        guard['status'] = 'passed'
        (OUT/'formal-guard.json').write_text(json.dumps(guard, indent=2)+'\n')
        receipt['formal_guard'] = guard
        lake = shutil.which('lake') or str(Path.home()/'.elan/bin/lake')
        step('lake-build', [lake, 'build'], ROOT/'lean')
        step('paper-imports', [lake, 'build', *inv['modules']], ROOT/'lean')
        step('paper-axioms', [lake, 'env', 'lean', 'PaperAxioms.lean'], ROOT/'lean')
        output = (OUT/'paper-axioms.log').read_text()
        parsed = {}
        for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
            if name in parsed:
                raise RuntimeError('Duplicate axiom report: '+name)
            parsed[name] = {v.strip() for v in values.split(',') if v.strip()}
        for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
            if name in parsed:
                raise RuntimeError('Duplicate axiom report: '+name)
            parsed[name] = set()
        expected = set(inv['unique_declarations'])
        if set(parsed) != expected:
            raise RuntimeError(f'Audit coverage mismatch: missing={expected-set(parsed)}, extra={set(parsed)-expected}')
        for name, axioms in parsed.items():
            if not axioms <= ALLOWED:
                raise RuntimeError(f'Forbidden axioms for {name}: {axioms-ALLOWED}')
        receipt['axioms'] = {'declarations': len(expected), 'allowed': sorted(ALLOWED),
                             'actual': sorted(set().union(*parsed.values()))}
        receipt['sources'] = {str(f.relative_to(ROOT)):sha(f) for f in (ROOT/'paper').rglob('*')
                              if f.is_file() and f.suffix in {'.tex','.bib'} and 'build' not in f.parts}
        receipt['paper_axioms_sha256'] = sha(ROOT/'lean/PaperAxioms.lean')
        receipt['inventory_sha256'] = sha(OUT/'declarations.json')
        receipt['status'] = 'passed'
    except Exception as error:
        receipt['status'] = 'failed'
        receipt['error'] = str(error)
        save()
        raise
    save()
    print(json.dumps({'status': receipt['status'], 'axioms': receipt['axioms'], 'static': receipt['static']}))


if __name__ == '__main__':
    main()
