#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check the memo's original source pins, without building or downloading.

Usage (from the memo directory):
    python3 tools/check_source_pins.py --output verification/source-check.json
The repository root is inferred from this script; --repo overrides it.
Requires only Python's standard library. See tools/README.md for scope.
"""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


HERE = Path(__file__).resolve().parent
DEFAULT_REPO = HERE.parents[2]
MANIFEST = HERE.parent / "verification" / "source-pins.json"


def verify(repo, manifest=MANIFEST):
    """Return a deterministic receipt, or raise ValueError on any mismatch."""
    data = json.loads(manifest.read_text())
    seen = set()
    for entry in data["files"]:
        path = PurePosixPath(entry["path"])
        if path.is_absolute() or ".." in path.parts or str(path) in seen:
            raise ValueError("invalid or duplicate manifest path: " + str(path))
        seen.add(str(path))
        actual = hashlib.sha256((repo / path).read_bytes()).hexdigest()
        if actual != entry["sha256"]:
            raise ValueError("source hash mismatch: " + str(path))
    return {
        "status": "PASS",
        "source_commit": data["source_commit"],
        "manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "files_checked": len(seen),
        "scope": data["scope"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=DEFAULT_REPO)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        report = verify(args.repo)
    except (ValueError, OSError, KeyError) as error:
        parser.exit(1, f"FAIL: {error}\n")
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
        print(f"PASS: {report['files_checked']} original source files match")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
