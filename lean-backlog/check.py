#!/usr/bin/env python3
"""Check the native row-spread modules using the existing pinned environment.

From High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean/:
    lake env python3 ../../lean-backlog/check.py

Optional positional module names check only those modules; their dependencies
must already have been checked. Outputs stay in the package's ignored .lake.
"""
import os
from pathlib import Path
import subprocess
import sys

SOURCE = Path(__file__).resolve().parent
PACKAGE = SOURCE.parent / "High-Rate-Separated-Storage-Codes-and-Tape-Transposition" / "lean"
CACHE = PACKAGE / ".lake" / "build" / "lean-backlog"
MODULES = [
    "StatementsRowSpread", "WindowAmortization", "WindowLabels",
    "WindowCounting", "WindowGuards", "WindowRows", "WindowConeWindows",
    "WindowWorkCounting", "WindowBudgets", "WindowRowCover", "WindowSpread",
    "WindowPages",
]


def main():
    selected = sys.argv[1:] or MODULES
    unknown = set(selected) - set(MODULES)
    if unknown:
        raise SystemExit("Unknown module(s): " + ", ".join(sorted(unknown)))
    CACHE.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(CACHE) + os.pathsep + env.get("LEAN_PATH", "")
    for module in selected:
        print(f"Checking {module}", flush=True)
        subprocess.run(
            ["lean", f"--root={SOURCE}", "-o", str(CACHE / f"{module}.olean"),
             str(SOURCE / f"{module}.lean")],
            cwd=PACKAGE, env=env, check=True,
        )


if __name__ == "__main__":
    main()
