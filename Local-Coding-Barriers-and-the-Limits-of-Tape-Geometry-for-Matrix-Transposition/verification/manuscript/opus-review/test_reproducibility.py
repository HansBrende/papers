"""Focused regression checks for clean builds and upstream source inventories."""
from pathlib import Path
import hashlib
import importlib.util
import json
import subprocess
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'verification' / f'{name}.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


upstream_check = load('check_upstream')
audit = load('run_axiom_audit')


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.upstream = self.root / 'original'
        self.upstream.mkdir()
        self.write('lean/A.lean', 'theorem example : True := True.intro\n')
        self.write('paper/main.tex', 'source\n')
        self.baseline = {
            'directory': 'original',
            'baseline_commit': 'fixture-original-commit',
            'files': {str(p.relative_to(self.upstream)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in self.upstream.rglob('*') if p.is_file()},
            'directories': ['lean', 'paper'],
        }
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        (self.root / '.gitignore').write_text('.lake/\n.DS_Store\n*.log\n')
        subprocess.run(['git', '-C', str(self.root), 'add', '.'], check=True)

    def write(self, relative, text='generated'):
        p = self.upstream / relative
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        return p

    def check(self):
        return upstream_check.check(self.upstream, self.baseline)

    def test_generated_artifacts_ignored(self):
        for name in ('lean/.lake/build/lib/A.olean', 'paper/main.aux',
                     'paper/main.log', '.DS_Store', 'paper/build/page-1.png',
                     'verification/__pycache__/x.pyc'):
            self.write(name)
        result = self.check()
        self.assertTrue(result['unchanged'], result)
        self.assertEqual(result['inventory_mode'], 'git')

    def test_changed_missing_and_untracked_source_detected(self):
        self.write('lean/A.lean', 'changed')
        (self.upstream / 'paper/main.tex').unlink()
        self.write('lean/New.lean', 'new source')
        result = self.check()
        self.assertEqual(result['changed'], ['lean/A.lean'])
        self.assertEqual(result['removed'], ['paper/main.tex'])
        self.assertEqual(result['added'], ['lean/New.lean'])
        self.assertFalse(result['unchanged'])

    def test_new_tracked_file_under_ignored_directory_detected(self):
        self.write('lean/.lake/important.lean', 'tracked source')
        subprocess.run(['git', '-C', str(self.root), 'add', '-f',
                        'original/lean/.lake/important.lean'], check=True)
        self.assertEqual(self.check()['added'], ['lean/.lake/important.lean'])

    def test_baseline_cannot_be_hidden_by_ignore_rule(self):
        subprocess.run(['git', '-C', str(self.root), 'rm', '--cached', '-q',
                        'original/lean/A.lean'], check=True)
        with (self.root / '.gitignore').open('a') as stream:
            stream.write('A.lean\n')
        self.write('lean/A.lean', 'changed despite ignored')
        self.assertEqual(self.check()['changed'], ['lean/A.lean'])
        (self.upstream / 'lean/A.lean').unlink()
        self.assertEqual(self.check()['removed'], ['lean/A.lean'])

    def test_archive_fallback_checks_source_but_ignores_build(self):
        self.write('paper/build/page-1.png')
        self.write('lean/.lake/build/A.olean')
        self.write('.DS_Store')
        no_git = subprocess.CompletedProcess([], 128, b'', b'not a repository')
        with mock.patch.object(upstream_check.subprocess, 'run', return_value=no_git):
            result = self.check()
            self.assertTrue(result['unchanged'], result)
            self.assertEqual(result['inventory_mode'], 'source-archive')
            self.write('lean/New.lean', 'new source')
            self.assertEqual(self.check()['added'], ['lean/New.lean'])

    def editorial_amendment(self):
        current = self.write('paper/main.tex', 'reviewed editorial update')
        return {
            'baseline_sha256': 'fixture-baseline-digest',
            'baseline_commit': self.baseline['baseline_commit'],
            'directory': self.baseline['directory'],
            'reviewed_commit': 'fixture-reviewed-commit',
            'files': {'paper/main.tex': {
                'before': self.baseline['files']['paper/main.tex'],
                'after': hashlib.sha256(current.read_bytes()).hexdigest()}},
        }

    def test_exact_editorial_amendment_and_unlisted_change(self):
        amendment = self.editorial_amendment()
        result = upstream_check.check(self.upstream, self.baseline, amendment,
                                      'fixture-baseline-digest')
        self.assertTrue(result['unchanged'], result)
        self.assertTrue(result['proof_sources_unchanged'])
        self.assertEqual(result['status'], 'unchanged_since_reviewed_editorial_revision')
        self.assertEqual(result['historical_baseline_changes'], ['paper/main.tex'])
        self.write('lean/A.lean', 'unlisted change')
        result = upstream_check.check(self.upstream, self.baseline, amendment,
                                      'fixture-baseline-digest')
        self.assertFalse(result['unchanged'])
        self.assertFalse(result['proof_sources_unchanged'])
        self.assertEqual(result['changed'], ['lean/A.lean'])

    def test_amended_document_changed_or_missing_is_rejected(self):
        amendment = self.editorial_amendment()
        self.write('paper/main.tex', 'unreviewed second change')
        result = upstream_check.check(self.upstream, self.baseline, amendment,
                                      'fixture-baseline-digest')
        self.assertEqual(result['changed'], ['paper/main.tex'])
        (self.upstream / 'paper/main.tex').unlink()
        result = upstream_check.check(self.upstream, self.baseline, amendment,
                                      'fixture-baseline-digest')
        self.assertEqual(result['removed'], ['paper/main.tex'])

    def test_amendment_cannot_change_lean_or_reference_wrong_baseline(self):
        amendment = self.editorial_amendment()
        with self.assertRaises(ValueError):
            upstream_check.check(self.upstream, self.baseline, amendment, 'wrong-digest')
        amendment['files']['lean/A.lean'] = {
            'before': self.baseline['files']['lean/A.lean'], 'after': 'unreviewed-lean-hash'}
        with self.assertRaises(ValueError):
            upstream_check.check(self.upstream, self.baseline, amendment,
                                  'fixture-baseline-digest')


class AuditTests(unittest.TestCase):
    def test_import_comments_duplicates_and_plan(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'lean').mkdir()
            (root / 'lean/PaperAxioms.lean').write_text(
                '/- import Fake.Module /- nested -/ -/\n'
                'import Transpose.Tape.Statements.Coding -- real\n'
                'import Foo.A Foo.B /- suffix -/\n'
                'import Foo.A\n#print axioms proof\n')
            (root / 'lean/SupportAxioms.lean').write_text('import Foo.A\nimport Foo.C\n')
            plan = audit.audit_plan('both', root)
            self.assertEqual(plan['commands'][0], ['lake', 'build',
                'Transpose.Tape.Statements.Coding', 'Foo.A', 'Foo.B', 'Foo.C'])
            self.assertEqual(plan['commands'][1:], [
                ['lake', 'env', 'lean', 'PaperAxioms.lean'],
                ['lake', 'env', 'lean', 'SupportAxioms.lean']])

    def test_actual_imports_and_arbitrary_working_directory(self):
        paper = audit.import_modules(ROOT / 'lean/PaperAxioms.lean')
        self.assertIn('Transpose.Tape.Statements.Coding', paper)
        support = audit.import_modules(ROOT / 'lean/SupportAxioms.lean')
        self.assertTrue(support)
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run(['python3', str(ROOT / 'verification/run_axiom_audit.py'),
                                     'both', '--dry-run'], cwd=directory,
                                    check=True, capture_output=True, text=True)
        plan = json.loads(result.stdout)
        self.assertEqual(set(plan['commands'][0][2:]), set(paper) | set(support))

    def test_malformed_import_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'Invalid.lean'
            for malformed in ('import --bad', 'import ../escape'):
                p.write_text('import Good.Module\n' + malformed + '\n')
                with self.assertRaises(ValueError):
                    audit.import_modules(p)


if __name__ == '__main__':
    unittest.main()
