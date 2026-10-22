"""Regression checks for the narrowly scoped historical-source amendment."""
from pathlib import Path
import copy
import json
import tempfile
import unittest
from unittest.mock import patch

import source_guard as guard


class SourceGuardTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.patch = patch.object(guard, 'ROOT', self.root)
        self.patch.start()
        self.addCleanup(self.patch.stop)
        self.path = self.root / guard.ALLOWED_PATH
        self.path.parent.mkdir(parents=True)
        self.changes = [{'old': '/-! Old module description. -/',
                         'new': '/-! New module description. -/'},
                        {'old': '/-- Old definition description. -/',
                         'new': '/-- New definition description. -/'}]
        self.before = ('import Mathlib\n\n' + self.changes[0]['old'] + '\n'
                       + self.changes[1]['old'] + '\ndef answer : Nat := 42\n')
        self.after = self.before
        for change in self.changes:
            self.after = self.after.replace(change['old'], change['new'])
        self.expected = guard.digest(self.before.encode())
        self.entry = {'path': guard.ALLOWED_PATH, 'before_sha256': self.expected,
                      'after_sha256': guard.digest(self.after.encode()),
                      'replacements': copy.deepcopy(self.changes)}
        self.manifest = {'schema_version': 1, 'amendments': [self.entry]}
        self.write()

    def write(self, contents=None):
        self.path.write_text(self.after if contents is None else contents)
        manifest_path = self.root / guard.MANIFEST
        manifest_path.parent.mkdir(parents=True, exist_ok=True)
        manifest_path.write_text(json.dumps(self.manifest))

    def reject(self, contents=None):
        self.write(contents)
        with self.assertRaises(guard.SourceGuardError):
            guard.verify_digest(self.path, self.expected)

    def test_exact_baseline(self):
        self.write(self.before)
        self.assertEqual(guard.verify_digest(self.path, self.expected)['status'],
                         'byte_unchanged')

    def test_exact_current(self):
        self.assertEqual(guard.verify_digest(self.path, self.entry['after_sha256'])['status'],
                         'byte_unchanged')

    def test_recorded_comments_restore_baseline(self):
        result = guard.verify_digest(guard.ALLOWED_PATH, self.expected)
        self.assertEqual(result['status'], 'comment_only_amendment')
        self.assertEqual(result['replacements'], 2)
        self.assertEqual(result['expected_sha256'], self.expected)

    def test_code_change_unrecorded(self):
        self.reject(self.after.replace('42', '43'))

    def test_code_change_with_updated_after_hash(self):
        changed = self.after.replace('42', '43')
        self.entry['after_sha256'] = guard.digest(changed.encode())
        self.reject(changed)

    def test_different_comment_unrecorded(self):
        self.reject(self.after.replace('New module', 'Different module'))

    def test_different_comment_with_updated_after_hash(self):
        changed = self.after.replace('New module', 'Different module')
        self.entry['after_sha256'] = guard.digest(changed.encode())
        self.reject(changed)

    def test_executable_replacement(self):
        new = '/-! New description. -/\naxiom illicit : False\n/- Another comment. -/'
        changed = self.after.replace(self.changes[0]['new'], new)
        self.entry['replacements'][0]['new'] = new
        self.entry['after_sha256'] = guard.digest(changed.encode())
        self.reject(changed)

    def test_nested_opener_rejected(self):
        new = '/-! Unclosed nested /- comment. -/'
        changed = self.after.replace(self.changes[0]['new'], new)
        self.entry['replacements'][0]['new'] = new
        self.entry['after_sha256'] = guard.digest(changed.encode())
        self.reject(changed)

    def test_comment_fragment_rejected(self):
        self.entry['replacements'][0] = {'old': 'Old module', 'new': 'New module'}
        self.reject()

    def test_nonstandalone_block_rejected(self):
        changed = self.after.replace(self.changes[0]['new'], '"' + self.changes[0]['new'] + '"')
        self.entry['after_sha256'] = guard.digest(changed.encode())
        self.reject(changed)

    def test_duplicate_new_comment_rejected(self):
        changed = self.after + self.changes[0]['new'] + '\n'
        self.entry['after_sha256'] = guard.digest(changed.encode())
        self.reject(changed)

    def test_wrong_baseline_hash_rejected(self):
        self.entry['before_sha256'] = '0' * 64
        self.reject()

    def test_wrong_after_hash_rejected(self):
        self.entry['after_sha256'] = '0' * 64
        self.reject()

    def test_other_path_cannot_use_manifest(self):
        other = self.root / 'lean/TransposeFollowup/Other.lean'
        other.write_text(self.after)
        with self.assertRaises(guard.SourceGuardError):
            guard.verify_digest(other, self.expected)

    def test_manifest_cannot_expand_path_scope(self):
        self.manifest['amendments'].append(copy.deepcopy(self.entry))
        self.reject()


class PublicationMetadataTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.patch = patch.object(guard, 'ROOT', self.root)
        self.patch.start()
        self.addCleanup(self.patch.stop)
        self.path = self.root / guard.PUBLICATION_PATH
        self.path.parent.mkdir(parents=True)
        files = []
        for index in range(13):
            destination = f'lean/FixedTapeCompiler/Example{index}.lean'
            file = self.root / destination
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text(f'def example{index} := {index}\n')
            sha = guard.digest(file.read_bytes())
            files.append({'source': 'old-location/' + destination, 'destination': destination,
                          'source_sha256': sha, 'local_sha256': sha, 'local_change': 'None.'})
        self.metadata = {'description': 'A preserved provenance record.', 'files': files,
                         'checked_at': 'fixed-test-date'}
        self.before = json.dumps(self.metadata).encode()
        self.expected = guard.digest(self.before)
        for entry in files:
            entry['source'] = guard.SOURCE_PREFIX + entry['destination']
        semantic = copy.deepcopy(self.metadata)
        for entry in semantic['files']:
            del entry['source']
        canonical = json.dumps(semantic, sort_keys=True, separators=(',', ':'),
                               ensure_ascii=False).encode('utf-8')
        self.manifest = {'schema_version': 1, 'path': guard.PUBLICATION_PATH,
                         'before_sha256': self.expected,
                         'semantic_sha256': guard.digest(canonical)}
        self.write(update_after=True)

    def write(self, update_after=False):
        data = json.dumps(self.metadata).encode()
        self.path.write_bytes(data)
        if update_after:
            self.manifest['after_sha256'] = guard.digest(data)
        (self.root / guard.PUBLICATION_MANIFEST).write_text(json.dumps(self.manifest))

    def reject(self, update_after=False):
        self.write(update_after)
        with self.assertRaises(guard.SourceGuardError):
            guard.verify_digest(self.path, self.expected)

    def test_normalization_preserves_semantics_and_destinations(self):
        result = guard.verify_digest(self.path, self.expected)
        self.assertEqual(result['status'], 'publication_metadata_normalization')
        self.assertEqual(result['verified_destinations'], 13)

    def test_original_bytes_are_still_accepted(self):
        self.path.write_bytes(self.before)
        self.assertEqual(guard.verify_digest(self.path, self.expected)['status'], 'byte_unchanged')

    def test_wrong_before_hash(self):
        self.manifest['before_sha256'] = '0' * 64
        self.reject()

    def test_wrong_after_hash(self):
        self.manifest['after_sha256'] = '0' * 64
        self.reject()

    def test_manifest_cannot_expand_path_scope(self):
        self.manifest['path'] = 'verification/other.json'
        self.reject()

    def test_unrecorded_file_cannot_use_metadata_bridge(self):
        other = self.root / 'verification/other.json'
        other.write_bytes(self.path.read_bytes())
        with self.assertRaises(guard.SourceGuardError):
            guard.verify_digest(other, self.expected)

    def test_code_cannot_use_metadata_bridge(self):
        code = self.root / 'lean/FixedTapeCompiler/Example0.lean'
        with self.assertRaises(guard.SourceGuardError):
            guard.verify_digest(code, self.expected)

    def test_nonlocation_metadata_edit_rejected_even_with_updated_after_hash(self):
        self.metadata['description'] += ' Changed.'
        self.reject(update_after=True)

    def test_destination_edit_rejected_even_with_updated_after_hash(self):
        entry = self.metadata['files'][0]
        entry['destination'] = 'lean/FixedTapeCompiler/Replacement.lean'
        entry['source'] = guard.SOURCE_PREFIX + entry['destination']
        self.reject(update_after=True)

    def test_recorded_file_hash_edit_rejected_even_with_updated_after_hash(self):
        self.metadata['files'][0]['local_sha256'] = '0' * 64
        self.reject(update_after=True)

    def test_destination_code_edit_rejected(self):
        (self.root / self.metadata['files'][0]['destination']).write_text('axiom illicit : False\n')
        self.reject()

    def test_missing_destination_rejected(self):
        (self.root / self.metadata['files'][0]['destination']).unlink()
        self.reject()

    def test_wrong_logical_source_filename_rejected(self):
        self.metadata['files'][0]['source'] = self.metadata['files'][1]['source']
        self.reject(update_after=True)

    def test_unapproved_logical_prefix_rejected(self):
        self.metadata['files'][0]['source'] = 'external/elsewhere/Example0.lean'
        self.reject(update_after=True)

    def test_added_file_rejected(self):
        self.metadata['files'].append(copy.deepcopy(self.metadata['files'][0]))
        self.reject(update_after=True)


if __name__ == '__main__':
    unittest.main()
