"""Regression tests for public command receipts; no Lean or TeX build needed."""
from pathlib import Path
import json
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from portable_paths import command_record
import verify


class PortableCommands(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve() / 'checkout'
        self.cwd = self.root / 'lean'
        self.cwd.mkdir(parents=True)

    def record(self, command, **kwargs):
        return command_record(command, root=self.root, cwd=self.cwd,
                              executable_label='python3', **kwargs)

    def test_absolute_path_is_relative_to_recorded_cwd(self):
        script = self.root / 'verification' / 'prepare.py'
        command = [str(self.root.parent / 'runtime' / 'python3'), str(script)]
        receipt = self.record(command, path_indices=(1,))
        self.assertEqual(receipt['command'], ['python3', '../verification/prepare.py'])
        self.assertEqual(receipt['cwd'], 'lean')
        self.assertNotIn(str(self.root.parent), json.dumps(receipt))
        self.assertEqual(command[1], str(script))  # Runtime argv is unmodified.

    def test_options_are_not_mistaken_for_paths(self):
        receipt = self.record(['python3', 'fetch.py', '--source-root', str(self.root / 'source'),
                               '--check', 'Package.Module'], path_indices=(3,))
        self.assertEqual(receipt['command'], ['python3', 'fetch.py', '--source-root',
                                              '../source', '--check', 'Package.Module'])

    def test_relative_operand_and_project_cwd(self):
        receipt = command_record(['lake', 'build', 'Package.Module'], root=self.root,
                                 cwd=self.root, executable_label='lake')
        self.assertEqual(receipt['cwd'], '.')
        self.assertEqual(receipt['command'], ['lake', 'build', 'Package.Module'])

    def test_unmarked_absolute_path_is_rejected(self):
        for operand in [str(self.root / 'input'), '--source-root=' + str(self.root / 'input'),
                        'C:\\private\\input']:
            with self.subTest(operand=operand), self.assertRaises(ValueError):
                self.record(['python3', operand])

    def test_external_operand_and_cwd_are_rejected(self):
        with self.assertRaises(ValueError):
            self.record(['python3', str(self.root.parent / 'private')], path_indices=(1,))
        with self.assertRaises(ValueError):
            command_record(['lake'], root=self.root, cwd=self.root.parent, executable_label='lake')

    def test_invalid_indices_and_executable_labels_are_rejected(self):
        for indices in [(0,), (2,), (-1,)]:
            with self.subTest(indices=indices), self.assertRaises(ValueError):
                self.record(['python3', 'script.py'], path_indices=indices)
        with self.assertRaises(ValueError):
            command_record(['python3'], root=self.root, cwd=self.cwd,
                           executable_label=str(self.root / 'python3'))

    def test_verify_executes_original_argv_and_records_portable_description(self):
        output = self.root / 'verification' / 'manuscript'
        output.mkdir(parents=True)
        executable = self.root.parent / 'runtime' / 'python3'
        command = [str(executable), str(output / 'prepare.py')]
        with patch.object(verify, 'ROOT', self.root), patch.object(verify, 'OUT', output), \
             patch.object(verify.subprocess, 'run', return_value=subprocess.CompletedProcess(command, 0)) as run, \
             patch('builtins.print'):
            receipt = verify.run('prepare', command, cwd=self.root,
                                 executable_label='python3', path_indices=(1,))
        self.assertEqual(run.call_args.args[0], command)
        self.assertEqual(run.call_args.kwargs['cwd'], self.root)
        self.assertEqual(receipt['command'], ['python3', 'verification/manuscript/prepare.py'])
        self.assertEqual(receipt['log'], 'verification/manuscript/prepare.log')
        self.assertNotIn(str(self.root.parent), json.dumps(receipt))


if __name__ == '__main__':
    unittest.main()
