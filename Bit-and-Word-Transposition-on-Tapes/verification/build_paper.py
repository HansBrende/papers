#!/usr/bin/env python3
"""Build the manuscript without recording machine-specific tool paths."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]

def main():
    executable = shutil.which(os.environ.get('LATEXMK', 'latexmk'))
    if executable is None:
        raise SystemExit('Install a TeX distribution and put latexmk on PATH.')
    paper = ROOT / 'paper'
    started = time.monotonic()
    command = [executable, '-pdf', '-interaction=nonstopmode', '-halt-on-error',
               '-file-line-error', '-outdir=build', 'main.tex']
    with (paper / 'build.log').open('w') as log:
        run = subprocess.run(command, cwd=paper, stdout=log, stderr=subprocess.STDOUT)
    record = {'command': ['latexmk', *command[1:]], 'cwd': 'paper',
              'seconds': time.monotonic()-started, 'exit_code': run.returncode}
    built = paper / 'build/main.pdf'
    if run.returncode == 0 and built.is_file():
        shutil.copy2(built, paper / 'main.pdf')
        record['pdf_sha256'] = hashlib.sha256(built.read_bytes()).hexdigest()
        record['pdf_bytes'] = built.stat().st_size
    (ROOT / 'verification/manuscript/build.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps(record))
    raise SystemExit(run.returncode)

if __name__ == '__main__':
    main()
