#!/usr/bin/env python3
"""Build every direct import before running the selected Lean axiom reports.

Run from any working directory. Audit names are fixed choices, not paths.
--dry-run prints the exact planned commands without invoking Lake. This helper
prints Lean's axiom reports; the manuscript verifier additionally checks paper
report coverage and the permitted-axiom whitelist.
"""

from pathlib import Path
import argparse
import json
import re
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[1]
AUDITS = {'paper': 'PaperAxioms.lean', 'support': 'SupportAxioms.lean'}
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")


def import_modules(path):
    """Read this project's plain import headers, ignoring nested Lean comments."""
    modules = []
    depth = 0
    for line in path.read_text().splitlines():
        clean = ''
        i = 0
        while i < len(line):
            pair = line[i:i + 2]
            if pair == '/-':
                depth += 1
                clean += ' '
                i += 2
            elif depth and pair == '-/':
                depth -= 1
                i += 2
            elif depth:
                i += 1
            elif pair == '--':
                break
            else:
                clean += line[i]
                i += 1
        clean = clean.strip()
        if not clean:
            continue
        if re.match(r'import(?:\s|$)', clean) is None:
            break
        names = clean.split()[1:]
        if not names or any(MODULE.fullmatch(name) is None for name in names):
            raise ValueError(f'Unsupported import header in {path.name}: {clean}')
        modules.extend(names)
    if not modules or depth:
        raise ValueError(f'Missing imports or incomplete header comment in {path.name}')
    return list(dict.fromkeys(modules))


def audit_plan(choice, root=ROOT):
    audits = list(AUDITS.values()) if choice == 'both' else [AUDITS[choice]]
    modules = list(dict.fromkeys(module for audit in audits
                                for module in import_modules(root / 'lean' / audit)))
    return {
        'working_directory': 'lean',
        'audits': audits,
        'import_count': len(modules),
        'commands': [['lake', 'build', *modules]]
                    + [['lake', 'env', 'lean', audit] for audit in audits],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('audit', choices=(*AUDITS, 'both'), nargs='?', default='both')
    parser.add_argument('--dry-run', action='store_true')
    args = parser.parse_args()
    plan = audit_plan(args.audit)
    if args.dry_run:
        print(json.dumps(plan, indent=2))
        return
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    print(f"Building {plan['import_count']} imports, then reporting axioms for "
          + ', '.join(plan['audits']), flush=True)
    for command in plan['commands']:
        subprocess.run([lake, *command[1:]], cwd=ROOT / 'lean', check=True)


if __name__ == '__main__':
    main()
