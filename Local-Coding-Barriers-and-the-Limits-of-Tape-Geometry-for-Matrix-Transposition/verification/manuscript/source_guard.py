"""Compare audited sources exactly, with explicitly bounded amendments.

Historical audit hashes remain immutable. The Lean amendment requires reversing
complete, uniquely occurring block comments to recover those bytes. Publication
metadata may replace private source locations by fixed logical identifiers;
every other JSON field and every destination file remains hash-checked.
Four named proof refactors additionally require exact reverse patches,
unchanged original headers, and a separate compiled type/axiom audit.
"""
from pathlib import Path
import difflib
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
ALLOWED_PATH = 'lean/TransposeFollowup/UnconditionalPaidPadding.lean'
MANIFEST = 'verification/manuscript/opus-review/source-comment-amendments.json'
PUBLICATION_PATH = 'verification/archive-source-provenance.json'
PUBLICATION_MANIFEST = 'verification/publication-config-amendment.json'
SOURCE_PREFIX = 'external/research-workspace/outputs/fixed-tape-compiler/'
PROOF_MANIFEST = 'verification/manuscript/packet-strengthening/proof-refactors.json'
PROOF_PATHS = tuple('lean/TransposeFollowup/' + name + '.lean' for name in
                    ('XorComponentCount', 'XorDegreeBound', 'XorPathCycleBound', 'SubmodularCover'))
MOVED_DECLARATIONS = {
    'TransposeFollowup.disjoint_family_size_bound': 'lean/TransposeFollowup/DisjointFamilyCount.lean',
    'TransposeFollowup.half_log_power_budget': 'lean/TransposeFollowup/DistanceNumerics.lean',
    'TransposeFollowup.log_le_twice_half_log': 'lean/TransposeFollowup/DistanceNumerics.lean'}


class SourceGuardError(RuntimeError):
    """A file differs from its audit outside the narrowly recorded changes."""


def digest(data):
    return hashlib.sha256(data).hexdigest()


def _require(condition, message):
    if not condition:
        raise SourceGuardError(message)


def _simple_comment(text):
    return (isinstance(text, str) and text.startswith('/-') and text.endswith('-/')
            and '/-' not in text[2:-2] and '-/' not in text[2:-2])


def _unique_standalone(text, block):
    if text.count(block) != 1:
        return False
    start = text.index(block)
    end = start + len(block)
    return ((start == 0 or text[start-1] == '\n')
            and (end == len(text) or text[end] == '\n'))


def _lean_mask(text):
    """Mask comments/strings, preserving positions for source-header checks."""
    out, i, depth = list(text), 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out[i:end] = ' ' * (end-i); i = end
        elif text[i] == '"':
            out[i] = ' '; i += 1
            while i < len(text) and text[i] != '"':
                if text[i] == '\\' and i+1 < len(text):
                    out[i:i+2] = '  '; i += 2
                else:
                    if text[i] != '\n': out[i] = ' '
                    i += 1
            _require(i < len(text), 'Unterminated Lean string')
            out[i] = ' '; i += 1
        else:
            i += 1
    _require(depth == 0, 'Unterminated Lean comment')
    return ''.join(out)


def _declarations(text):
    """Read the simple named declarations in these four fixed source files.

    This is a source-header guard, not a Lean parser or a substitute for the
    compiled type check. The latter retains all constants and instance terms.
    """
    masked = _lean_mask(text)
    pattern = re.compile(r'^(namespace|end|(?:noncomputable )?(?:theorem|lemma|def))\b([^\n]*)', re.M)
    commands, stack, result = list(pattern.finditer(masked)), [], {}
    for index, match in enumerate(commands):
        kind, tail = match.group(1), match.group(2).strip()
        if kind == 'namespace':
            stack.append(tail)
        elif kind == 'end':
            _require(stack and (not tail or stack[-1] == tail), 'Unsupported namespace scope')
            stack.pop()
        else:
            short = re.match(r'[A-Za-z_][A-Za-z_0-9]*', tail)
            _require(short is not None, 'Unsupported declaration name')
            name = '.'.join([*stack, short.group()])
            end = commands[index+1].start() if index+1 < len(commands) else len(text)
            # Named arguments inside a theorem type also contain `:=`.
            depth, assign = 0, -1
            for offset in range(match.start(), end):
                if masked[offset] in '([{': depth += 1
                elif masked[offset] in ')]}': depth -= 1
                elif depth == 0 and masked.startswith(':=', offset):
                    assign = offset
                    break
            _require(assign >= 0 and name not in result, 'Missing/duplicate declaration assignment')
            result[name] = {'kind': kind, 'header': text[match.start():assign],
                            'definition': text[match.start():end].strip() if kind.endswith('def') else None}
    _require(not stack, 'Unclosed namespace scope')
    return result


def _reverse_patch(current, patch, path):
    """Strictly reverse an inline unified diff; never invoke an external patcher."""
    lines = patch.splitlines(keepends=True)
    _require(lines[:2] == ['--- a/' + path + '\n', '+++ b/' + path + '\n'],
             'Proof patch has incorrect source labels')
    source, restored, cursor, index, old_cursor = current.splitlines(keepends=True), [], 0, 2, 0
    count = 0
    while index < len(lines):
        match = re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@\n', lines[index])
        _require(match is not None, 'Malformed proof patch hunk')
        old_start, old_count = int(match[1]), int(match[2] or 1)
        new_start, new_count = int(match[3]), int(match[4] or 1)
        old_start -= int(old_count > 0); new_start -= int(new_count > 0)
        index += 1
        old, new = [], []
        while index < len(lines) and not lines[index].startswith('@@ '):
            line = lines[index]
            _require(line[:1] in (' ', '+', '-'), 'Unsupported proof patch line')
            if line[0] != '+': old.append(line[1:])
            if line[0] != '-': new.append(line[1:])
            index += 1
        _require(len(old) == old_count and len(new) == new_count, 'Proof patch count mismatch')
        _require(new_start >= cursor and old_start >= old_cursor
                 and old_start-old_cursor == new_start-cursor, 'Overlapping/mispositioned proof patch')
        _require(source[new_start:new_start+new_count] == new, 'Proof patch context differs')
        restored.extend(source[cursor:new_start]); restored.extend(old)
        cursor, old_cursor = new_start+new_count, old_start+old_count
        count += 1
    _require(count > 0, 'Empty proof patch')
    restored.extend(source[cursor:])
    return ''.join(restored)


def load_proof_refactors():
    """Validate the complete, fixed four-file refactor and all original headers."""
    path = ROOT / PROOF_MANIFEST
    if not path.exists():
        return None
    manifest = json.loads(path.read_bytes())
    _require(manifest.get('schema_version') == 1, 'Unknown proof-refactor schema')
    entries = manifest.get('files', [])
    _require(len(entries) == len(PROOF_PATHS) and {e['path'] for e in entries} == set(PROOF_PATHS),
             'Proof refactors must name exactly the four allowed sources')
    baseline = json.loads((ROOT / 'verification/manuscript/formal-baseline.json').read_bytes())['files']
    originals = {}
    for entry in entries:
        relative = entry['path']
        data = (ROOT / relative).read_bytes()
        _require(entry['before_sha256'] == baseline[relative], 'Proof refactor changed its historical basis')
        _require(digest(data) == entry['after_sha256'], 'Proof refactor source is stale')
        restored = _reverse_patch(data.decode('utf-8'), entry['reverse_unified_diff'], relative)
        _require(digest(restored.encode('utf-8')) == entry['before_sha256'],
                 'Reversing proof refactor did not restore audited bytes')
        for name, declaration in _declarations(restored).items():
            _require(name not in originals, 'Duplicate original contract')
            originals[name] = (relative, declaration)
    contracts = manifest.get('contracts', [])
    _require(len(contracts) == len(originals) == 26
             and {c['name'] for c in contracts} == set(originals), 'Original contract inventory mismatch')
    for contract in contracts:
        name = contract['name']
        original_path, old = originals[name]
        destination = MOVED_DECLARATIONS.get(name, original_path)
        _require(contract['original_path'] == original_path and contract['current_path'] == destination,
                 'Unapproved declaration relocation')
        current = _declarations((ROOT / destination).read_text()).get(name)
        _require(current is not None and current['kind'] == old['kind'], 'Original declaration disappeared')
        _require(contract['header'] == old['header'] == current['header'], 'Original declaration header changed')
        _require(contract['header_sha256'] == digest(old['header'].encode('utf-8')), 'Header digest mismatch')
        if old['definition'] is not None:
            _require(current['definition'] == old['definition'], 'Original definition body changed')
        _require(re.fullmatch('[0-9a-f]{64}', contract.get('canonical_type_sha256', '')) is not None
                 and isinstance(contract.get('level_params'), list), 'Missing original elaborated type')
    return manifest


def _proof_amendment(path, expected_digest):
    manifest = load_proof_refactors()
    _require(manifest is not None, 'Unrecorded proof refactor')
    entry = next(e for e in manifest['files'] if e['path'] == path)
    _require(entry['before_sha256'] == expected_digest, 'Proof refactor audit basis differs')
    return {'status': 'proof_refactor', 'path': path,
            'expected_sha256': expected_digest, 'actual_sha256': entry['after_sha256'],
            'manifest': PROOF_MANIFEST, 'manifest_sha256': digest((ROOT / PROOF_MANIFEST).read_bytes()),
            'original_headers': sum(c['original_path'] == path for c in manifest['contracts']),
            'type_audit_required': True}


def refactor_audit_source(manifest):
    """Generate verification-only Lean code; it adds no mathematical declarations."""
    modules = sorted({p.removeprefix('lean/').removesuffix('.lean').replace('/', '.')
                      for p in [*PROOF_PATHS, *MOVED_DECLARATIONS.values()]})
    names = [c['name'] for c in manifest['contracts']]
    return '\n'.join(['-- Generated verification tooling, not a mathematical proof source.',
        'import Lean', *['import ' + m for m in modules], '', 'open Lean Elab Command', '',
        'private def eraseContractBinderLabels : Expr → Expr',
        '  | .forallE _ a b i => .forallE Name.anonymous (eraseContractBinderLabels a) (eraseContractBinderLabels b) i',
        '  | .lam _ a b i => .lam Name.anonymous (eraseContractBinderLabels a) (eraseContractBinderLabels b) i',
        '  | .letE _ t v b n => .letE Name.anonymous (eraseContractBinderLabels t) (eraseContractBinderLabels v) (eraseContractBinderLabels b) n',
        '  | .app f a => .app (eraseContractBinderLabels f) (eraseContractBinderLabels a)',
        '  | .mdata m e => .mdata m (eraseContractBinderLabels e)',
        '  | .proj s i e => .proj s i (eraseContractBinderLabels e)',
        '  | e => e', '', 'set_option maxHeartbeats 0 in', 'run_cmd do',
        '  let env ← getEnv',
        '  let names : Array Name := #[' + ', '.join('`'+n for n in names) + ']',
        '  let modules : Array Name := #[' + ', '.join('`'+m for m in modules) + ']',
        '  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]',
        '  let mut rows : Array Json := #[]', '  let mut checked : Array String := #[]',
        '  let mut actual : Array Name := #[]',
        '  for (name, _) in env.constants.toList do',
        '    if let some idx := env.getModuleIdxFor? name then',
        '      if modules.contains env.header.moduleNames[idx]! then',
        '        let axioms ← collectAxioms name', '        for ax in axioms do',
        '          unless allowed.contains ax do throwError "Forbidden axiom {ax} in {name}"',
        '          if !actual.contains ax then actual := actual.push ax',
        '        checked := checked.push name.toString',
        '  for name in names do',
        '    let some info := env.find? name | throwError "Missing original declaration {name}"',
        '    rows := rows.push (Json.mkObj [("name", toJson name.toString),',
        '      ("levels", toJson (info.levelParams.map Name.toString)),',
        '      ("type", toJson (reprStr (eraseContractBinderLabels info.type)))])',
        '  if checked.isEmpty then throwError "Empty proof-refactor axiom audit"',
        '  logInfo ("PROOF_REFACTOR_AUDIT " ++ (Json.mkObj [("types", Json.arr rows),',
        '    ("axiom_declarations", toJson checked), ("axioms", toJson (actual.map Name.toString))]).compress)', ''])


def check_refactor_audit(output, manifest):
    """Compare exact type ASTs modulo bound-variable labels; no type normalization."""
    matches = re.findall(r'^PROOF_REFACTOR_AUDIT (\{.*\})$', output, re.M)
    _require(len(matches) == 1, 'Missing/duplicate proof-refactor audit output')
    audit = json.loads(matches[0])
    rows = audit['types']
    expected = {c['name']: c for c in manifest['contracts']}
    _require(len(rows) == len(expected) and {r['name'] for r in rows} == set(expected),
             'Compiled original-type coverage differs')
    checked = {}
    for row in rows:
        contract = expected[row['name']]
        actual = digest(row['type'].encode('utf-8'))
        _require(actual == contract['canonical_type_sha256'] and row['levels'] == contract['level_params'],
                 'Original elaborated type changed: ' + row['name'])
        checked[row['name']] = {'canonical_type_sha256': actual, 'level_params': row['levels']}
    names, axioms = audit['axiom_declarations'], set(audit['axioms'])
    _require(len(names) == len(set(names)) and set(expected) <= set(names), 'Refactored-module axiom coverage differs')
    _require(axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, 'Forbidden refactor axiom')
    return {'status': 'passed', 'original_declarations': len(checked), 'contracts': checked,
            'method': 'Exact elaborated Expr representation and ordered universe parameters, erasing only bound-variable labels.',
            'axiom_declarations': sorted(names), 'axioms': sorted(axioms)}


def _publication_metadata(data, expected_digest):
    manifest_bytes = (ROOT / PUBLICATION_MANIFEST).read_bytes()
    manifest = json.loads(manifest_bytes)
    _require(manifest.get('schema_version') == 1
             and manifest.get('path') == PUBLICATION_PATH,
             'Publication amendment must name only the allowed metadata file')
    _require(manifest.get('before_sha256') == expected_digest,
             'Publication amendment is not based on the expected audit digest')
    actual = digest(data)
    _require(manifest.get('after_sha256') == actual,
             'Metadata differs from the recorded publication digest')
    metadata = json.loads(data)
    files = metadata.get('files', [])
    _require(isinstance(files, list) and len(files) == 13,
             'Publication metadata must preserve the thirteen-file inventory')
    destinations = set()
    for entry in files:
        destination = entry.get('destination')
        _require(isinstance(destination, str)
                 and Path(destination).parent.as_posix() == 'lean/FixedTapeCompiler'
                 and Path(destination).suffix == '.lean',
                 'Invalid publication metadata destination')
        _require(destination not in destinations, 'Duplicate publication metadata destination')
        destinations.add(destination)
        _require(entry.get('source') == SOURCE_PREFIX + destination,
                 'Source must be the corresponding logical research-workspace identifier')
        del entry['source']
    canonical = json.dumps(metadata, sort_keys=True, separators=(',', ':'),
                           ensure_ascii=False).encode('utf-8')
    _require(digest(canonical) == manifest.get('semantic_sha256'),
             'Publication normalization changed metadata outside source locations')
    for entry in files:
        destination = ROOT / entry['destination']
        _require(destination.is_file() and destination.resolve().is_relative_to(ROOT.resolve())
                 and digest(destination.read_bytes()) == entry.get('local_sha256'),
                 'Publication metadata destination no longer matches its recorded digest')
    return {'status': 'publication_metadata_normalization', 'path': PUBLICATION_PATH,
            'expected_sha256': expected_digest, 'actual_sha256': actual,
            'manifest': PUBLICATION_MANIFEST, 'manifest_sha256': digest(manifest_bytes),
            'semantic_sha256': digest(canonical), 'verified_destinations': len(files)}


def verify_digest(path, expected_digest):
    """Return an exact-byte or narrowly verified amendment record, or raise.

Relative paths are relative to the follow-up root. Only ALLOWED_PATH can use
the comment amendment; only PUBLICATION_PATH can normalize source-location
metadata. Only PROOF_PATHS may use a recorded reversible proof refactor.
All other paths require exact bytes, including external files.
"""
    path = Path(path)
    if not path.is_absolute():
        path = ROOT / path
    data = path.read_bytes()
    actual = digest(data)
    if actual == expected_digest:
        return {'status': 'byte_unchanged', 'sha256': actual}
    if path.resolve() == (ROOT / PUBLICATION_PATH).resolve():
        return _publication_metadata(data, expected_digest)
    for relative in PROOF_PATHS:
        if path.resolve() == (ROOT / relative).resolve():
            return _proof_amendment(relative, expected_digest)
    _require(path.resolve() == (ROOT / ALLOWED_PATH).resolve(),
             f'Source digest mismatch: {path}')
    manifest_bytes = (ROOT / MANIFEST).read_bytes()
    manifest = json.loads(manifest_bytes)
    _require(manifest.get('schema_version') == 1, 'Unknown comment manifest version')
    entries = manifest.get('amendments', [])
    _require(len(entries) == 1 and entries[0].get('path') == ALLOWED_PATH,
             'Comment manifest must name only the allowed source')
    entry = entries[0]
    _require(entry.get('before_sha256') == expected_digest,
             'Comment amendment is not based on the expected audit digest')
    _require(entry.get('after_sha256') == actual,
             'Source differs from the recorded amended digest')
    replacements = entry.get('replacements', [])
    _require(len(replacements) == 2, 'Expected exactly two recorded comment corrections')
    restored = data.decode('utf-8')
    for replacement in reversed(replacements):
        old, new = replacement.get('old'), replacement.get('new')
        _require(_simple_comment(old) and _simple_comment(new) and old != new,
                 'Amendment must replace entire simple block comments')
        _require(_unique_standalone(restored, new),
                 'New comment is not a unique standalone block')
        restored = restored.replace(new, old, 1)
        _require(_unique_standalone(restored, old),
                 'Restored comment is not a unique standalone block')
    _require(digest(restored.encode('utf-8')) == expected_digest,
             'Reversing comment corrections did not restore the audited source')
    return {'status': 'comment_only_amendment', 'path': ALLOWED_PATH,
            'expected_sha256': expected_digest, 'actual_sha256': actual,
            'manifest': MANIFEST, 'manifest_sha256': digest(manifest_bytes),
            'replacements': len(replacements)}


def seal_proof_refactors(before_root, before_types):
    """Record the approved exact source changes after their proofs stabilize.

    Inputs may be private snapshots; only project-relative paths, exact source
    patches and elaborated-type digests are written to the portable manifest.
    This does not claim that the required current Lean audit has passed.
    """
    baseline = json.loads((ROOT / 'verification/manuscript/formal-baseline.json').read_bytes())['files']
    captures = json.loads(before_types.read_bytes())
    types = {row['name']: row for row in captures}
    _require(len(types) == len(captures) == 26, 'Wrong baseline type inventory')
    entries, contracts = [], []
    for relative in PROOF_PATHS:
        old, new = (before_root / relative).read_text(), (ROOT / relative).read_text()
        _require(digest(old.encode('utf-8')) == baseline[relative], 'Snapshot differs from immutable source baseline')
        _require(old.endswith('\n') and new.endswith('\n') and old != new, 'Expected a newline-terminated changed source')
        patch = ''.join(difflib.unified_diff(old.splitlines(keepends=True), new.splitlines(keepends=True),
                        fromfile='a/'+relative, tofile='b/'+relative))
        entries.append({'path': relative, 'before_sha256': baseline[relative],
                        'after_sha256': digest(new.encode('utf-8')), 'reverse_unified_diff': patch})
        for name, declaration in _declarations(old).items():
            _require(name in types, 'Original declaration missing from baseline type capture')
            row = types[name]
            contracts.append({'name': name, 'original_path': relative,
                'current_path': MOVED_DECLARATIONS.get(name, relative),
                'header': declaration['header'], 'header_sha256': digest(declaration['header'].encode('utf-8')),
                'raw_type_sha256': digest(row['type'].encode('utf-8')),
                'canonical_type_sha256': digest(row['canonical_type'].encode('utf-8')),
                'level_params': row['levels']})
    _require({c['name'] for c in contracts} == set(types), 'Source and captured type inventories differ')
    manifest = {'schema_version': 1,
        'scope': 'Four explicitly approved proof refactors; historical sources are recovered by exact reverse patches. Current proofs and original elaborated contracts require a fresh Lean audit.',
        'baseline_type_capture_sha256': digest(before_types.read_bytes()),
        'type_comparison': 'Erase only forall/lam/let bound-variable labels; retain all other Expr structure and the ordered universe-parameter list.',
        'files': entries, 'contracts': sorted(contracts, key=lambda c: c['name'])}
    destination = ROOT / PROOF_MANIFEST
    destination.write_text(json.dumps(manifest, indent=2, ensure_ascii=False)+'\n')
    load_proof_refactors()
    return {'manifest': PROOF_MANIFEST, 'sha256': digest(destination.read_bytes()),
            'files': len(entries), 'original_contracts': len(contracts), 'compiled_audit': 'required'}


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Seal only the four explicitly approved proof refactors.')
    parser.add_argument('--before-source-root', type=Path, required=True)
    parser.add_argument('--before-types', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(seal_proof_refactors(args.before_source_root, args.before_types)))
