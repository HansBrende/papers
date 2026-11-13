#!/usr/bin/env python3
"""Wait for a committed change to chat/fable-astra.md on origin/master.

Run from anywhere: python3 path/to/clone/chat/watch.py
Standard library only. Fetch every 15 seconds; fast-forward a clean tracking
branch. Print incoming text and exit. Never stash, reset, rebase, commit or push.
"""

from __future__ import annotations

import argparse
import math
import os
from pathlib import Path
import subprocess
import sys
import time


CHAT = "chat/fable-astra.md"


class GitError(RuntimeError):
    pass


def git(root: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    env = os.environ.copy()
    env["GIT_TERMINAL_PROMPT"] = "0"
    try:
        result = subprocess.run(
            ["git", *args], cwd=root, env=env, capture_output=True, timeout=30,
        )
    except subprocess.TimeoutExpired as exc:
        raise GitError("Git command timed out after 30 seconds") from exc
    if check and result.returncode:
        raise GitError(result.stderr.decode("utf-8", errors="replace").strip())
    return result


def revision(root: Path, ref: str) -> str:
    return git(root, "rev-parse", "--verify", ref + "^{commit}").stdout.decode().strip()


def sync_if_safe(root: Path, commit: str, remote: str, branch: str) -> str:
    current = git(root, "symbolic-ref", "--quiet", "--short", "HEAD", check=False)
    upstream = git(root, "rev-parse", "--abbrev-ref", "--symbolic-full-name",
                   "@{upstream}", check=False)
    if (current.stdout.decode().strip() != branch or
            upstream.stdout.decode().strip() != f"{remote}/{branch}"):
        return "Working files unchanged: not on the watched tracking branch."
    if revision(root, "HEAD") == commit:
        return "Working files already at the fetched commit."
    if git(root, "status", "--porcelain", "--untracked-files=normal").stdout:
        return "Working files unchanged: uncommitted or untracked files are present."
    if git(root, "merge-base", "--is-ancestor", "HEAD", commit, check=False).returncode:
        return "Working files unchanged: local commits need manual reconciliation."
    git(root, "merge", "--ff-only", "--quiet", commit)
    return "Fast-forwarded the working branch."


def positive_seconds(value: str) -> float:
    seconds = float(value)
    if not math.isfinite(seconds) or seconds <= 0:
        raise argparse.ArgumentTypeError("interval must be finite and greater than zero")
    return seconds


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--interval", type=positive_seconds, default=15,
                        help="seconds between checks (default: 15)")
    parser.add_argument("--since", default="HEAD",
                        help="last-read commit (default: local HEAD at startup)")
    parser.add_argument("--remote", default="origin")
    parser.add_argument("--branch", default="master")
    parser.add_argument("--once", action="store_true", help="check once without waiting")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    remote_ref = f"refs/remotes/{args.remote}/{args.branch}"
    git(root, "check-ref-format", remote_ref)
    git(root, "check-ref-format", f"refs/heads/{args.branch}")
    baseline_commit = revision(root, args.since)
    baseline = git(root, "show", f"{baseline_commit}:{CHAT}").stdout
    print(f"Watching {args.remote}/{args.branch}:{CHAT} from {baseline_commit}; "
          f"checking every {args.interval:g}s. Ctrl-C stops the watcher.", flush=True)
    previous_status = None
    while True:
        try:
            git(root, "fetch", "--quiet", "--no-tags", "--", args.remote,
                f"refs/heads/{args.branch}:{remote_ref}")
        except GitError as exc:
            print(f"Fetch failed: {exc}", file=sys.stderr, flush=True)
            if args.once:
                return 2
            time.sleep(args.interval)
            continue
        commit = revision(root, remote_ref)
        incoming = git(root, "show", f"{commit}:{CHAT}").stdout
        changed = incoming != baseline
        if changed and not incoming.startswith(baseline):
            print("Chat histories differ before the append point. Working files unchanged; "
                  "reconcile both histories manually. Fetched chat follows:", flush=True)
            print(incoming.decode("utf-8"), end="", flush=True)
            print(f"\nFetched commit: {commit}", flush=True)
            return 2
        try:
            status = sync_if_safe(root, commit, args.remote, args.branch)
        except GitError as exc:
            status = f"Could not fast-forward; no automatic conflict resolution: {exc}"
        if changed or status != previous_status:
            print(status, flush=True)
            previous_status = status
        if changed:
            print(f"\nNew chat text at {commit}:\n", flush=True)
            print(incoming[len(baseline):].decode("utf-8"), end="", flush=True)
            print(f"\nAfter reading, use --since {commit} if your local HEAD is still older.",
                  flush=True)
            return 0
        if args.once:
            print("No new chat text.", flush=True)
            return 1
        time.sleep(args.interval)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\nStopped.", flush=True)
        sys.exit(130)
    except (GitError, OSError, UnicodeError) as exc:
        print(f"Watcher stopped: {exc}", file=sys.stderr, flush=True)
        sys.exit(2)
