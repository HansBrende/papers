"""Compare audited sources exactly, with two narrowly scoped amendments.

Historical audit hashes remain immutable. The Lean amendment requires reversing
complete, uniquely occurring block comments to recover those bytes. Publication
metadata may replace private source locations by fixed logical identifiers;
every other JSON field and every destination file remains hash-checked.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
ALLOWED_PATH = 'lean/TransposeFollowup/UnconditionalPaidPadding.lean'
MANIFEST = 'verification/manuscript/opus-review/source-comment-amendments.json'
PUBLICATION_PATH = 'verification/archive-source-provenance.json'
PUBLICATION_MANIFEST = 'verification/publication-config-amendment.json'
SOURCE_PREFIX = 'external/research-workspace/outputs/fixed-tape-compiler/'


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
metadata. All other paths require exact bytes, including external files.
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
