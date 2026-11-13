#!/usr/bin/env python3
"""Fetch every 15 seconds; exit only for a peer message marked --wake.

Run: python3 chat/watch.py --as fable
No working-tree changes while waiting. On notification, fast-forward only a
clean tracking branch (disable with --no-pull). Standard library only.
"""

from __future__ import annotations

import argparse
import sys
import time

from chatlib import (ROOT, ChatError, GitError, actor_for, add_options, check_history,
                     fetch, parse_chat, read_chat, revision, sync_if_safe)


def listen(root, actor, *, remote="origin", branch="master", interval=15,
           since=None, once=False, no_pull=False):
    baseline = previous = None
    if since:
        since = revision(root, since)
        baseline = previous = parse_chat(read_chat(root, since))
    print(f"Listening as {actor} on {remote}/{branch}; fetch-only polling every "
          f"{interval:g}s. Only peer REVIEW REQUEST messages wake this listener.", flush=True)
    while True:
        try:
            commit = fetch(root, remote, branch)
        except GitError as exc:
            print(f"Fetch failed: {exc}", file=sys.stderr, flush=True)
            if once:
                return 2
            time.sleep(interval)
            continue
        current = parse_chat(read_chat(root, commit))
        if baseline is None:
            baseline = previous = current
            print(f"Startup baseline: {commit}. Existing messages are treated as read; "
                  "use --since to include earlier unread messages.", flush=True)
        check_history(previous, current)
        previous = current
        incoming = [message for key, message in current.messages.items()
                    if key not in baseline.messages and message.recipient == actor]
        if any(message.wake for message in incoming):
            if not no_pull:
                try:
                    print(sync_if_safe(root, commit, remote, branch), flush=True)
                except GitError as exc:
                    print(f"Could not fast-forward; message is still available: {exc}", flush=True)
            print(f"\nNew messages for {actor} at {commit}:\n", flush=True)
            for message in incoming:
                print(message.heading + "\n\n" + message.body + "\n", flush=True)
            print(f"Last-read commit: {commit}", flush=True)
            return 0
        if once:
            print(f"No new wake request for {actor}.", flush=True)
            return 1
        time.sleep(interval)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_options(parser)
    parser.add_argument("--once", action="store_true", help="check once without waiting")
    args = parser.parse_args()
    return listen(ROOT, actor_for(ROOT, args.actor), remote=args.remote, branch=args.branch,
                  interval=args.interval, since=args.since, once=args.once, no_pull=args.no_pull)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\nStopped.", flush=True)
        sys.exit(130)
    except (ChatError, OSError, UnicodeError) as exc:
        print(f"Watcher stopped: {exc}", file=sys.stderr, flush=True)
        sys.exit(2)
