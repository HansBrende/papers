#!/usr/bin/env python3
"""Compare R1912 Lean Expr-repr manifests exactly, then make compact receipts.

Does not invoke Lean/Lake, edit Lean sources, or normalize expressions. The
original 6,297 names come from archived baseline SupportAxioms. Comparison is
per matching chunk to avoid retaining the complete ~894 MB manifest twice.
Optional archival is verified before the explicit, separate cleanup option.
"""
from __future__ import annotations
import argparse
import datetime as dt
import gc
import hashlib
import io
import json
import os
from pathlib import Path
import re
import sys
import tarfile
import tempfile

P = Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition')
A = Path('/Users/hansbrende/Documents/Codex/2026-10-09/a/research/10-linear-decision/archive/r1912-build-speed')
EXPECTED_COUNT = 6297
CHUNKS = 79
BLOCK = 1024 * 1024


def strict_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate JSON object key: {key!r}')
        result[key] = value
    return result


def load_json(path):
    with Path(path).open(encoding='utf-8') as stream:
        return json.load(stream, object_pairs_hook=strict_object)


def file_hash(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(BLOCK), b''):
            digest.update(block)
    return digest.hexdigest()


def stat_key(path):
    s = Path(path).stat()
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns)


def write_json(path, obj):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    # Only compact output receipts are atomically replaced; never input data.
    fd, tmp = tempfile.mkstemp(prefix=path.name + '.', suffix='.tmp', dir=path.parent)
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as stream:
            json.dump(obj, stream, ensure_ascii=False, sort_keys=True, indent=2)
            stream.write('\n')
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


def expected_names(source_inventory):
    data = load_json(source_inventory)
    text = data['lean/SupportAxioms.lean']
    # Ignore nested Lean block comments, line comments, and strings so disabled
    # or quoted commands cannot silently enter the trusted original name list.
    chars = []
    index = depth = 0
    line_comment = string_literal = False
    while index < len(text):
        c, pair = text[index], text[index:index+2]
        if depth:
            if pair == '/-':
                depth += 1; chars.extend('  '); index += 2; continue
            if pair == '-/':
                depth -= 1; chars.extend('  '); index += 2; continue
            chars.append('\n' if c == '\n' else ' '); index += 1; continue
        if line_comment:
            chars.append('\n' if c == '\n' else ' ')
            if c == '\n': line_comment = False
            index += 1; continue
        if string_literal:
            chars.append('\n' if c == '\n' else ' ')
            if c == '\\': chars.append(' '); index += 2; continue
            if c == '"': string_literal = False
            index += 1; continue
        if pair == '/-':
            depth = 1; chars.extend('  '); index += 2; continue
        if pair == '--':
            line_comment = True; chars.extend('  '); index += 2; continue
        if c == '"':
            string_literal = True; chars.append(' '); index += 1; continue
        chars.append(c); index += 1
    if depth or string_literal:
        raise ValueError('unterminated block comment or string in baseline audit')
    names = re.findall(r'^\s*#print axioms ([^\s]+)\s*$', ''.join(chars), re.M)
    if len(names) != EXPECTED_COUNT or len(set(names)) != EXPECTED_COUNT:
        raise ValueError(f'expected exactly {EXPECTED_COUNT} distinct baseline names; got {len(names)} commands and {len(set(names))} distinct names')
    return names


def validate_record(name, value):
    if not isinstance(value, dict) or set(value) != {'type', 'levelParams'}:
        raise ValueError(f'{name}: expected precisely type and levelParams fields')
    if not isinstance(value['type'], str):
        raise ValueError(f'{name}: type is not a string')
    if not isinstance(value['levelParams'], list) or not all(isinstance(v, str) for v in value['levelParams']):
        raise ValueError(f'{name}: levelParams is not an ordered list of strings')


def first_difference(a, b):
    for i, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return i
    return min(len(a), len(b))


def compare_record(name, before, after):
    """Actual exact comparisons happen here, BEFORE any per-name hashing."""
    validate_record(name, before)
    validate_record(name, after)
    type_equal = before['type'] == after['type']
    levels_equal = before['levelParams'] == after['levelParams']
    if type_equal and levels_equal:
        return None
    mismatch = {'name': name, 'type_equal': type_equal, 'levelParams_equal': levels_equal}
    if not levels_equal:
        mismatch.update(baseline_levelParams=before['levelParams'], final_levelParams=after['levelParams'])
    if not type_equal:
        offset = first_difference(before['type'], after['type'])
        mismatch.update(first_different_character=offset,
                        baseline_character_count=len(before['type']),
                        final_character_count=len(after['type']),
                        baseline_excerpt=before['type'][max(0, offset-50):offset+100],
                        final_excerpt=after['type'][max(0, offset-50):offset+100])
    return mismatch


def compact_record(value):
    # Hash the exact decoded UTF-8 Expr-repr string: no whitespace, newline,
    # alpha-equivalence, universe, notation, or Unicode normalization.
    digest = hashlib.sha256()
    byte_count = 0
    text = value['type']
    for start in range(0, len(text), BLOCK):
        block = text[start:start+BLOCK].encode('utf-8')
        digest.update(block)
        byte_count += len(block)
    return {'type_sha256': digest.hexdigest(), 'type_utf8_bytes': byte_count,
            'type_characters': len(text), 'levelParams': value['levelParams']}


def compare(args):
    names = expected_names(args.baseline_source_inventory)
    expected = set(names)
    seen_before = set()
    seen_after = set()
    before_manifest = {}
    after_manifest = {}
    mismatches = []
    inputs = []
    for index in range(CHUNKS):
        before_path = Path(args.baseline_pattern.format(index=index)).resolve()
        after_path = Path(args.final_pattern.format(index=index)).resolve()
        if before_path == after_path:
            raise ValueError(f'chunk {index}: baseline and final paths are identical')
        before_stat, after_stat = stat_key(before_path), stat_key(after_path)
        before, after = load_json(before_path), load_json(after_path)
        if not isinstance(before, dict) or not isinstance(after, dict):
            raise ValueError(f'chunk {index}: each manifest must be an object keyed by declaration name')
        if set(before) != set(after):
            raise ValueError(f'chunk {index}: declaration partitions differ; missing final {sorted(set(before)-set(after))[:12]}, unexpected final {sorted(set(after)-set(before))[:12]}. Use the same original name batches for both drivers.')
        if seen_before.intersection(before) or seen_after.intersection(after):
            raise ValueError(f'chunk {index}: duplicate declaration across chunks')
        if not set(before).issubset(expected):
            raise ValueError(f'chunk {index}: non-baseline declarations: {sorted(set(before)-expected)[:12]}')
        for name in before:
            mismatch = compare_record(name, before[name], after[name])
            if mismatch is not None:
                mismatches.append(mismatch)
            # Only after exact type AND ordered universe comparisons.
            before_manifest[name] = compact_record(before[name])
            after_manifest[name] = compact_record(after[name])
        seen_before.update(before)
        seen_after.update(after)
        if stat_key(before_path) != before_stat or stat_key(after_path) != after_stat:
            raise ValueError(f'chunk {index}: input file changed during exact comparison')
        for side, path, stat in [('baseline', before_path, before_stat), ('final', after_path, after_stat)]:
            inputs.append({'side': side, 'index': index, 'path': str(path),
                           'bytes': stat[2], 'sha256': file_hash(path)})
        if stat_key(before_path) != before_stat or stat_key(after_path) != after_stat:
            raise ValueError(f'chunk {index}: input changed while recording byte digest')
        del before, after
        gc.collect()
        if args.progress:
            print(f'Exact comparison: {index+1}/{CHUNKS} chunks, {len(seen_before)}/{EXPECTED_COUNT} declarations', flush=True)
    if seen_before != expected or seen_after != expected:
        raise ValueError(f'original declaration list incomplete; missing baseline {sorted(expected-seen_before)[:12]}, missing final {sorted(expected-seen_after)[:12]}')
    metadata = {'format': 'r1912-exact-lean-type-digests-v1',
                'declarations': EXPECTED_COUNT,
                'hash_algorithm': 'SHA256 of exact decoded type Expr-repr UTF-8 bytes; levelParams retained as an ordered list',
                'warning': 'Digests summarize a completed exact comparison; hash equality was not used to decide type equality.'}
    out = Path(args.output_dir)
    before_out = out / f'{args.prefix}-baseline-type-hashes.json'
    after_out = out / f'{args.prefix}-final-type-hashes.json'
    names_out = out / f'{args.prefix}-original-declaration-names.json'
    summary_out = out / f'{args.prefix}-type-comparison.json'
    write_json(before_out, metadata | {'side': 'baseline', 'types': before_manifest})
    write_json(after_out, metadata | {'side': 'final', 'types': after_manifest})
    write_json(names_out, {'count': EXPECTED_COUNT, 'names': names,
                          'source_inventory': str(Path(args.baseline_source_inventory).resolve()),
                          'source_inventory_sha256': file_hash(args.baseline_source_inventory)})
    summary = {'format': 'r1912-exact-lean-type-comparison-v1',
               'finished_at_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
               'status': 'passed' if not mismatches else 'failed',
               'comparison': 'Exact Python string equality of decoded Expr repr plus exact ordered-list equality of levelParams; no normalization or hash-based equality shortcut.',
               'expected_original_declarations': EXPECTED_COUNT,
               'baseline_declarations': len(seen_before), 'final_declarations': len(seen_after),
               'chunk_pairs': CHUNKS, 'different_declarations': len(mismatches),
               'mismatches': mismatches, 'input_chunks': inputs,
               'compact_outputs': {'baseline': str(before_out.resolve()), 'final': str(after_out.resolve()),
                                   'original_names': str(names_out.resolve())},
               'source_inventory_sha256': file_hash(args.baseline_source_inventory),
               'comparator': {'path': str(Path(__file__).resolve()),
                              'bytes': Path(__file__).stat().st_size,
                              'sha256': file_hash(__file__)},
               'archive': None}
    write_json(summary_out, summary)
    return summary, summary_out, [before_out, after_out, names_out, summary_out]


def verified_archive(args, summary, summary_out, compact_outputs):
    """Archive copies first, verify all members, optionally remove bulky inputs."""
    if summary['status'] != 'passed':
        raise ValueError('archive/cleanup refused because exact comparison did not pass')
    target = Path(args.archive).resolve()
    research_archive = A.resolve()
    if research_archive not in target.parents:
        raise ValueError(f'archive must be inside the research archive {research_archive}')
    if target.exists():
        raise FileExistsError(f'refusing to overwrite existing archive: {target}')
    records = []
    for item in summary['input_chunks']:
        records.append(item | {'member': f"{item['side']}/chunks/{item['index']:03d}.json", 'bulky': True})
    for side, source in [('baseline', args.baseline_aggregate), ('final', args.final_aggregate)]:
        if source is not None:
            path = Path(source).resolve()
            if not path.is_file():
                raise FileNotFoundError(path)
            records.append({'side': side, 'path': str(path), 'member': f'{side}/aggregate.json',
                            'bytes': path.stat().st_size, 'sha256': file_hash(path), 'bulky': True})
    for path in compact_outputs:
        path = path.resolve()
        records.append({'path': str(path), 'member': 'comparison/' + path.name,
                        'bytes': path.stat().st_size, 'sha256': file_hash(path), 'bulky': False})
    source = Path(args.baseline_source_inventory).resolve()
    records.append({'path': str(source), 'member': 'evidence/baseline-sources.json',
                    'bytes': source.stat().st_size, 'sha256': file_hash(source), 'bulky': False})
    comparator = summary['comparator']
    records.append(comparator | {'member': 'evidence/compare-types.py', 'bulky': False})
    members = [r['member'] for r in records]
    if len(set(members)) != len(members):
        raise ValueError('duplicate archive member paths')
    # Never allow cleanup to remove an input that is also a compact receipt.
    outputs = {str(p.resolve()) for p in compact_outputs}
    if any(r['bulky'] and r['path'] in outputs for r in records):
        raise ValueError('bulky source overlaps compact output')
    inventory = json.dumps({'format': 'r1912-full-type-archive-v1', 'members': records},
                           ensure_ascii=False, sort_keys=True, indent=2).encode('utf-8')
    inventory_name = 'comparison/archive-inventory.json'
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = target.with_name(target.name + '.partial')
    # Exclusive create prevents overwriting a previous unfinished archive.
    with temporary.open('xb') as raw:
        with tarfile.open(fileobj=raw, mode='w:gz', compresslevel=args.compression_level) as archive:
            for record in records:
                path = Path(record['path'])
                if path.stat().st_size != record['bytes'] or file_hash(path) != record['sha256']:
                    raise ValueError(f'input changed before archive: {path}')
                archive.add(path, arcname=record['member'], recursive=False)
            info = tarfile.TarInfo(inventory_name)
            info.size = len(inventory)
            archive.addfile(info, io.BytesIO(inventory))
    expected = {r['member']: r for r in records}
    expected[inventory_name] = {'bytes': len(inventory), 'sha256': hashlib.sha256(inventory).hexdigest()}
    verified = set()
    with tarfile.open(temporary, 'r:gz') as archive:
        for member in archive:
            if not member.isfile() or member.name not in expected or member.name in verified:
                raise ValueError(f'unexpected or duplicate archive member: {member.name}')
            digest = hashlib.sha256()
            size = 0
            stream = archive.extractfile(member)
            if stream is None:
                raise ValueError(f'unreadable archive member: {member.name}')
            with stream:
                for block in iter(lambda: stream.read(BLOCK), b''):
                    size += len(block)
                    digest.update(block)
            if size != expected[member.name]['bytes'] or digest.hexdigest() != expected[member.name]['sha256']:
                raise ValueError(f'archive verification failed: {member.name}')
            verified.add(member.name)
    if verified != set(expected):
        raise ValueError('archive has missing members')
    # Publish only the complete verified archive; original inputs still exist.
    os.link(temporary, target)
    temporary.unlink()
    summary['archive'] = {'path': str(target), 'bytes': target.stat().st_size,
                          'sha256': file_hash(target), 'verified_members': len(verified),
                          'verification': 'Every decompressed member byte count and SHA256 matches recorded original file bytes.',
                          'removed_inputs': []}
    write_json(summary_out, summary)
    if args.remove_archived_inputs:
        # This requires an explicit flag, a passing exact comparison, and a
        # complete independently reread archive. Preflight all source hashes.
        bulky = {r['path']: r for r in records if r['bulky']}
        for path, record in bulky.items():
            if file_hash(path) != record['sha256']:
                raise ValueError(f'input changed after archiving; cleanup refused: {path}')
        for path in bulky:
            Path(path).unlink()
            summary['archive']['removed_inputs'].append(path)
            write_json(summary_out, summary)
    return summary


def parser():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--baseline-pattern', default='/private/tmp/r1912-baseline-types-{index:03d}.json')
    p.add_argument('--final-pattern', default='/private/tmp/r1912-final-types-{index:03d}.json')
    p.add_argument('--baseline-source-inventory', type=Path, default=A/'baseline-sources.json')
    p.add_argument('--output-dir', type=Path, default=Path('/private/tmp'))
    p.add_argument('--prefix', default='r1912')
    p.add_argument('--progress', action='store_true')
    p.add_argument('--archive', type=Path, help='Optional fresh .tar.gz inside the existing research archive; default does not archive or remove anything.')
    p.add_argument('--baseline-aggregate', type=Path, help='Optional bulky combined baseline JSON to include in the verified archive.')
    p.add_argument('--final-aggregate', type=Path, help='Optional bulky combined final JSON to include in the verified archive.')
    p.add_argument('--compression-level', type=int, choices=range(1,10), default=6)
    p.add_argument('--remove-archived-inputs', action='store_true', help='Explicit opt-in: remove only bulky input chunks/aggregates after successful exact comparison and full archive verification; compact receipts/source inventory remain.')
    return p


def main():
    args = parser().parse_args()
    if args.remove_archived_inputs and args.archive is None:
        raise ValueError('--remove-archived-inputs requires --archive')
    if (args.baseline_aggregate or args.final_aggregate) and args.archive is None:
        raise ValueError('aggregate archive inputs require --archive')
    if args.archive is not None and Path(args.archive).exists():
        raise FileExistsError(f'refusing to overwrite existing archive: {args.archive}')
    summary, summary_path, outputs = compare(args)
    if args.archive is not None:
        summary = verified_archive(args, summary, summary_path, outputs)
    print(json.dumps({'status': summary['status'], 'declarations': summary['baseline_declarations'],
                      'different_declarations': summary['different_declarations'],
                      'summary': str(summary_path.resolve()), 'compact_outputs': summary['compact_outputs'],
                      'archive': summary['archive']}, indent=2))
    return 0 if summary['status'] == 'passed' else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f'Type-manifest comparison refused: {error}', file=sys.stderr)
        sys.exit(2)
