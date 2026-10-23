#!/usr/bin/env python3
"""Build and audit the exact mapped Lean contracts and their local closure.

A complete map must include every authored local module. English prose and
visual PDF quality require separate reviews. Local logs and generated audit
sources live in ignored verification/build/.
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

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
OUT = ROOT / 'verification/build'
MAP = ROOT / 'verification/contracts.json'
NAME = re.compile(r'[A-Za-z_][A-Za-z_0-9.]*\Z')
IMPORT = re.compile(r'^\s*(?:public\s+)?import\s+([^\n]+)$', re.M)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(text):
    """Remove nested block/line comments and strings for a conservative guard."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.append(' ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unterminated Lean block comment')
    return ''.join(out)


def load_map():
    data = json.loads(MAP.read_text())
    if data.get('schema_version') != 1 or data.get('status') not in {'partial', 'complete'}:
        raise ValueError('Unsupported verification contract map')
    items = data['contracts']
    ids = [x['id'] for x in items + data['pending']]
    if not items or len(ids) != len(set(ids)):
        raise ValueError('Empty or duplicate contract identifiers')
    names, modules = [], set()
    for item in items:
        if item['status'] != 'checked_component' or not item['declarations']:
            raise ValueError('Invalid stable component contract')
        if not NAME.fullmatch(item['module']) or not item['module'].startswith('BitWord.'):
            raise ValueError('Invalid component module')
        modules.add(item['module'])
        for name in item['declarations']:
            if not NAME.fullmatch(name):
                raise ValueError('Invalid declaration name')
            names.append(name)
    if len(names) != len(set(names)):
        raise ValueError('Duplicate mapped declaration')
    if data['status'] == 'complete' and data['pending']:
        raise ValueError('Complete status has pending contracts')
    if data['status'] == 'partial' and not data['pending']:
        raise ValueError('Partial status must identify the outstanding contract')
    return data, sorted(modules), sorted(names)


def imports(code):
    result = []
    for clause in IMPORT.findall(code):
        words = clause.split()
        if not words or any(not NAME.fullmatch(word) for word in words):
            raise ValueError('Unsupported Lean import syntax')
        result.extend(words)
    return result


def source_closure(modules):
    """Follow actual local imports, not an independently maintained file list."""
    todo, result = list(modules), {}
    while todo:
        module = todo.pop()
        if module in result:
            continue
        path = LEAN / (module.replace('.', '/') + '.lean')
        if not path.is_file():
            raise ValueError(f'Missing mapped local module: {module}')
        code = lean_code(path.read_text())
        if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code):
            raise ValueError(f'Forbidden proof escape in {module}')
        if re.search(r'\b(?:debug\.skipKernelTC|debug\.trustCompiler)\b', code):
            raise ValueError(f'Forbidden trust option in {module}')
        result[module] = path
        todo += [m for m in imports(code) if m.startswith('BitWord.')]
    return result


def audit_source(modules, names):
    return '\n'.join([
        '-- Generated verification code, not a mathematical proof source.',
        'import Lean', *['import ' + m for m in modules],
        'open Lean Elab Command', 'set_option maxHeartbeats 0 in', 'run_cmd do',
        '  let env ← getEnv',
        '  let modules : Array Name := #[' + ', '.join('`' + m for m in modules) + ']',
        '  let expected : Array Name := #[' + ', '.join('`' + n for n in names) + ']',
        '  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]',
        '  let mut count : Nat := 0', '  let mut found : Array Name := #[]',
        '  let mut actual : Array Name := #[]',
        '  for (name, info) in env.constants.toList do',
        '    if let some idx := env.getModuleIdxFor? name then',
        '      if modules.contains env.header.moduleNames[idx]! then',
        '        let axioms ← collectAxioms name',
        '        for ax in axioms do',
        '          unless allowed.contains ax do',
        '            throwError "Forbidden axiom {ax} in {name}"',
        '          if !actual.contains ax then actual := actual.push ax',
        '        count := count + 1',
        '        if expected.contains name then',
        '          found := found.push name',
        '          logInfo m!"TYPE {name}: {reprStr info.type}; universes {info.levelParams}"',
        '  for name in expected do',
        '    unless found.contains name do throwError "Missing mapped declaration {name}"',
        '  if count == 0 then throwError "Empty declaration audit"',
        '  logInfo m!"BITWORD_AUDIT declarations={count} endpoints={found.size} axioms={actual}"',
        '',
    ])


def manuscript_check(data):
    sources = sorted((ROOT / 'paper').rglob('*.tex'))
    sources = [p for p in sources if 'build' not in p.relative_to(ROOT / 'paper').parts]
    text = '\n'.join(p.read_text() for p in sources)
    labels = re.findall(r'\\label\{([^{}]+)\}', text)
    if len(labels) != len(set(labels)):
        raise ValueError('Duplicate manuscript labels')
    refs = {v.strip() for group in re.findall(r'\\(?:[cC]ref|ref|eqref)\{([^{}]+)\}', text)
            for v in group.split(',')}
    bib = ROOT / 'paper/references.bib'
    keys = re.findall(r'@\w+\s*\{\s*([^,\s]+)', bib.read_text())
    cites = {v.strip() for group in re.findall(r'\\cite(?:\[[^\]]*\])*\{([^{}]+)\}', text)
             for v in group.split(',')}
    if refs - set(labels) or cites - set(keys) or len(keys) != len(set(keys)):
        raise ValueError('Unresolved or duplicate manuscript references/citations')
    for item in data['contracts']:
        if item.get('manuscript_label') and item['manuscript_label'] not in labels:
            raise ValueError('Mapped manuscript label is missing: ' + item['id'])
    numbered = re.compile(r'\\begin\{(?:theorem|lemma|corollary|proposition|definition)\}')
    actual = set()
    for source in sources:
        contents = source.read_text()
        matches = list(numbered.finditer(contents))
        for i, match in enumerate(matches):
            end = matches[i+1].start() if i+1 < len(matches) else len(contents)
            label = re.search(r'\\label\{([^{}]+)\}', contents[match.end():end])
            if label is None:
                raise ValueError('Unlabelled numbered result in ' + str(source.relative_to(ROOT)))
            actual.add(label[1])
    mapped = {item['manuscript_label'] for item in data['contracts'] + data['pending']
              if item.get('manuscript_label')}
    if actual != mapped:
        raise ValueError('Numbered result map differs: missing=' + str(sorted(actual - mapped)) +
                         ', extra=' + str(sorted(mapped - actual)))
    return {str(p.relative_to(ROOT)): sha(p) for p in [*sources, bib]}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    receipt = {'status': 'running', 'scope': 'Mapped Lean contracts and their local closure; semantic and visual manuscript reviews are separate',
               'started_at': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'steps': []}
    destination = OUT / 'verification.json'
    def save():
        destination.write_text(json.dumps(receipt, indent=2) + '\n')
    def run(label, args):
        log = OUT / (label + '.log')
        tick = time.monotonic()
        with log.open('w') as stream:
            proc = subprocess.run([lake, *args], cwd=LEAN, stdout=stream, stderr=subprocess.STDOUT)
        receipt['steps'].append({'step': label, 'command': ['lake', *args], 'cwd': 'lean',
                                 'exit_code': proc.returncode, 'seconds': time.monotonic() - tick,
                                 'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log)})
        save()
        print(f'{label}: exit {proc.returncode}', flush=True)
        if proc.returncode:
            raise RuntimeError(f'{label} failed; inspect {log.relative_to(ROOT)}')
    save()
    try:
        data, targets, names = load_map()
        closure = source_closure(targets)
        if data['status'] == 'complete':
            authored = {p.relative_to(LEAN).with_suffix('').as_posix().replace('/', '.')
                        for p in (LEAN / 'BitWord').rglob('*.lean')}
            if authored != set(closure):
                raise ValueError('Complete map leaves unaudited local modules: ' +
                                 str(sorted(authored - set(closure))))
        if imports(lean_code((LEAN / 'BitWord.lean').read_text())) != targets:
            raise ValueError('Aggregate imports differ from the stable theorem map')
        sources = {str(p.relative_to(ROOT)): sha(p) for p in closure.values()}
        configs = ['lean/BitWord.lean', 'lean/lakefile.toml', 'lean/lake-manifest.json',
                   'lean/lean-toolchain', 'verification/contracts.json', 'verification/verify.py']
        sources.update({p: sha(ROOT / p) for p in configs})
        receipt.update({'contract_status': data['status'], 'pending': data['pending'],
                        'targets': targets, 'local_modules': sorted(closure), 'sources': sources,
                        'manuscript_sources': manuscript_check(data), 'mapped_declarations': names,
                        'assumptions': ['propext', 'Classical.choice', 'Quot.sound']})
        lake = shutil.which('lake')
        if lake is None:
            raise RuntimeError('lake is not on PATH; install the pinned Lean toolchain through elan')
        audit = OUT / 'ComponentAxioms.lean'
        audit.write_text(audit_source(sorted(closure), names))
        receipt['audit_source_sha256'] = sha(audit)
        save()
        run('stable-build', ['build', *targets])
        run('aggregate-imports', ['env', 'lean', 'BitWord.lean'])
        run('component-axioms', ['env', 'lean', '../verification/build/ComponentAxioms.lean'])
        result = re.search(r'BITWORD_AUDIT declarations=(\d+) endpoints=(\d+) axioms=',
                           (OUT / 'component-axioms.log').read_text())
        if result is None or int(result[1]) == 0 or int(result[2]) != len(names):
            raise RuntimeError('Incomplete declaration audit output')
        if any(sha(ROOT / p) != digest for p, digest in sources.items()):
            raise RuntimeError('Audited source changed during verification; rerun after it stabilizes')
        receipt['audited_declarations'] = int(result[1])
        receipt['status'] = 'passed_components' if data['pending'] else 'passed_mapped_contracts'
        receipt['not_certified'] = ['English-to-Lean correspondence', 'visual PDF quality',
                                     *[p['id'] for p in data['pending']]]
        save()
        print(json.dumps({'status': receipt['status'], 'declarations': int(result[1]),
                          'mapped_endpoints': len(names), 'pending': [p['id'] for p in data['pending']]}))
    except Exception as error:
        receipt['status'] = 'failed'
        receipt['error'] = str(error)
        save()
        print(str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
