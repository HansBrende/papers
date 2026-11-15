#!/usr/bin/env python3
"""Audit the already-built conditional Wall theorem; never constructs Answer.lean.

From High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean:
    lake env python3 ../../lean-backlog/tools/audit_wall_closure.py
    lake env python3 ../../lean-backlog/tools/audit_wall_closure.py --replay

Prepare pinned compiled dependencies and run lean-backlog/check.py first.
The default inventory and target axiom check, or optional fresh-kernel replay, run
in one Lean process. Raw output includes local paths: save it outside the
public repository. The timeout covers imports, audit and replay together.
"""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--all-axioms", action="store_true",
                        help="also scan every imported constant's axiom closure (may be slow)")
    parser.add_argument("--timeout", type=int, default=600, metavar="SECONDS")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    source = Path(__file__).resolve().parent
    root = source.parent.parent
    package = root / "High-Rate-Separated-Storage-Codes-and-Tape-Transposition" / "lean"
    cache = package / ".lake" / "build" / "lean-backlog"
    if not (cache / "Wall.olean").is_file():
        parser.error("Wall.olean is missing; prepare dependencies and run lean-backlog/check.py")
    env = os.environ.copy()
    env["LEAN_PATH"] = str(cache) + os.pathsep + env.get("LEAN_PATH", "")
    env["WALL_REPLAY"] = "1" if args.replay else "0"
    env["WALL_ALL_AXIOMS"] = "1" if args.all_axioms else "0"
    started = time.monotonic()
    print(f"AUDIT_START replay={args.replay} all_axioms={args.all_axioms} "
          f"timeout={args.timeout}s", flush=True)
    with tempfile.TemporaryDirectory(prefix="wall-audit-") as directory:
        progress = Path(directory) / "progress"
        env["WALL_AUDIT_PROGRESS"] = str(progress)
        process = subprocess.Popen(
            ["lean", "-j1", str(source / "audit_wall_closure.lean")],
            cwd=package, env=env,
        )
        last = ""
        try:
            while process.poll() is None:
                if progress.exists():
                    stage = progress.read_text()
                    if stage and stage != last:
                        print(f"AUDIT_PHASE {stage}", flush=True)
                        last = stage
                if time.monotonic() - started >= args.timeout:
                    process.kill()
                    process.wait()
                    print(f"AUDIT_TIMEOUT {args.timeout}s; last phase: {last}; "
                          "no completed replay claimed", flush=True)
                    return 124
                time.sleep(0.25)
        except BaseException:
            if process.poll() is None:
                process.kill()
            process.wait()
            raise
        code = process.returncode
    print(f"AUDIT_PROCESS seconds={time.monotonic() - started:.3f} exit={code}",
          flush=True)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
