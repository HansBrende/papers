#!/usr/bin/env python3
"""Compare the original paper's source files with the immutable baseline.

In a Git checkout, inventory tracked files and nonignored untracked sources;
exclude known artifacts only from the untracked set. Always check baseline
files even if ignore rules hide them. Without Git metadata, scan the source
archive, excluding only the artifact names listed below.
Directories are derived from inventoried files; empty/generated directories
are not source changes. An explicit editorial amendment may update exact
paper-document hashes; it cannot change any Lean file or the immutable baseline.
"""

from pathlib import Path
import fnmatch
import hashlib
import json
import os
import subprocess


ARTIFACT_DIRS = {'.git', '.lake', '__pycache__'}
ARTIFACT_FILES = ('.DS_Store', '*.aux', '*.blg', '*.fdb_latexmk', '*.fls',
                  '*.log', '*.out', '*.toc', '*.synctex.gz', '*.pyc', '*.pyo')


def is_artifact(name):
    path = Path(name)
    return (any(part in ARTIFACT_DIRS for part in path.parts)
            or path.parts[:2] == ('paper', 'build')
            or any(fnmatch.fnmatchcase(path.name, p) for p in ARTIFACT_FILES))


def source_names(upstream):
    """Return file names and inventory mode; preserve tracked ignored files."""
    try:
        names = set()
        for option in ('--cached', '--others'):
            result = subprocess.run(
                ['git', '-C', str(upstream), 'ls-files', option,
                 '--exclude-standard', '-z', '--', '.'],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
            )
            if result.returncode:
                break
            names.update(os.fsdecode(s) for s in result.stdout.split(b'\0') if s
                         and (option == '--cached' or not is_artifact(os.fsdecode(s))))
        else:
            return names, 'git'
    except FileNotFoundError:
        pass
    names = set()
    for directory, dirs, files in os.walk(upstream):
        relative = Path(directory).relative_to(upstream)
        dirs[:] = [d for d in dirs if d not in ARTIFACT_DIRS
                   and relative / d != Path('paper/build')]
        for name in files:
            if not is_artifact(str(relative / name)):
                names.add(str(relative / name))
    return names, 'source-archive'


def check(upstream, baseline, amendment=None, baseline_digest=None):
    expected = dict(baseline['files'])
    if amendment is not None:
        if (amendment['baseline_sha256'] != baseline_digest
                or amendment['baseline_commit'] != baseline['baseline_commit']
                or amendment['directory'] != baseline['directory']):
            raise ValueError('Editorial amendment does not match the immutable baseline')
        for name, hashes in amendment['files'].items():
            path = Path(name)
            if (path.parts[0] != 'paper' or '..' in path.parts
                    or path.suffix not in {'.tex', '.bib', '.bbl', '.pdf'}
                    or expected.get(name) != hashes['before']):
                raise ValueError(f'Invalid editorial amendment: {name}')
            expected[name] = hashes['after']
    names, mode = source_names(upstream)
    # A missing/changed baseline file must not be hidden by a new ignore rule.
    names.update(baseline['files'])
    files = {
        name: hashlib.sha256((upstream / name).read_bytes()).hexdigest()
        for name in sorted(names) if (upstream / name).is_file()
    }
    directories = sorted({str(parent) for name in files
                          for parent in Path(name).parents if parent != Path('.')})
    added = sorted(files.keys() - expected.keys())
    removed = sorted(expected.keys() - files.keys())
    changed = sorted(name for name in files.keys() & expected.keys()
                     if files[name] != expected[name])
    unchanged = not (added or removed or changed) and directories == baseline['directories']
    proof_files = {name: digest for name, digest in files.items() if name.startswith('lean/')}
    original_proof_files = {name: digest for name, digest in baseline['files'].items()
                            if name.startswith('lean/')}
    return {
        'unchanged': unchanged,
        'status': (('unchanged_since_reviewed_editorial_revision' if amendment
                    else 'unchanged_since_original_baseline') if unchanged else 'upstream_changed'),
        'proof_sources_unchanged': proof_files == original_proof_files,
        'reviewed_editorial_commit': amendment['reviewed_commit'] if amendment else None,
        'historical_baseline_changes': sorted(amendment['files']) if amendment else [],
        'inventory_mode': mode,
        'files_checked': len(files),
        'added': added,
        'removed': removed,
        'changed': changed,
        'directories_unchanged': directories == baseline['directories'],
        'directory_scope': 'ancestors of inventoried source files; empty directories excluded',
    }


def main():
    paper = Path(__file__).resolve().parents[1]
    baseline_path = paper / 'verification/upstream-baseline.json'
    baseline = json.loads(baseline_path.read_text())
    amendment_path = paper / 'verification/upstream-editorial-amendment.json'
    amendment = json.loads(amendment_path.read_text()) if amendment_path.exists() else None
    result = check(paper.parent / baseline['directory'], baseline, amendment,
                   hashlib.sha256(baseline_path.read_bytes()).hexdigest())
    print(json.dumps(result, indent=2))
    return 0 if result['unchanged'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
