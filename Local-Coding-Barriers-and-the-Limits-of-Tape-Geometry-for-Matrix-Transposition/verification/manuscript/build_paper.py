#!/usr/bin/env python3
"""Build the multi-file LaTeX manuscript; retain diagnostics and a PDF hash."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import time
from portable_paths import command_record

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'paper'
OUT = ROOT / 'verification/manuscript'


def main():
    executable = shutil.which(os.environ.get('LATEXMK', 'latexmk'))
    if executable is None:
        raise SystemExit('Put latexmk on PATH or set LATEXMK to its executable; a LaTeX distribution is required.')
    command = [executable, '-pdf', '-interaction=nonstopmode', '-halt-on-error',
               '-file-line-error', '-outdir=build', 'main.tex']
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    tic = time.monotonic()
    with (OUT / 'latex-build.log').open('w') as log:
        run = subprocess.run(command, cwd=PAPER, stdout=log, stderr=subprocess.STDOUT)
    record = {**command_record(command, root=ROOT, cwd=PAPER, executable_label='latexmk'),
              'started_at': started, 'seconds': time.monotonic()-tic,
              'exit_code': run.returncode}
    built = PAPER / 'build/main.pdf'
    if run.returncode == 0 and built.is_file():
        shutil.copy2(built, PAPER / 'main.pdf')
        record['pdf_sha256'] = hashlib.sha256(built.read_bytes()).hexdigest()
        record['pdf_bytes'] = built.stat().st_size
    (OUT / 'latex-build.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps(record))
    raise SystemExit(run.returncode)


if __name__ == '__main__':
    main()
