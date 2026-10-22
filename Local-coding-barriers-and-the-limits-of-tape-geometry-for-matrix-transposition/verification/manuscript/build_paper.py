#!/usr/bin/env python3
"""Build the multi-file LaTeX manuscript; retain diagnostics and a PDF hash."""
from pathlib import Path
import datetime
import hashlib
import json
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'paper'
OUT = ROOT / 'verification/manuscript'


def main():
    executable = shutil.which('latexmk')
    if executable is None and Path('/Library/TeX/texbin/latexmk').is_file():
        executable = '/Library/TeX/texbin/latexmk'
    if executable is None:
        raise SystemExit('latexmk and a LaTeX distribution are required.')
    command = [executable, '-pdf', '-interaction=nonstopmode', '-halt-on-error',
               '-file-line-error', '-outdir=build', 'main.tex']
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    tic = time.monotonic()
    with (OUT / 'latex-build.log').open('w') as log:
        run = subprocess.run(command, cwd=PAPER, stdout=log, stderr=subprocess.STDOUT)
    record = {'command': command, 'started_at': started, 'seconds': time.monotonic()-tic,
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
