#!/usr/bin/env python3
"""Publish one batched request, then listen for the peer's response.

Run: python3 chat/send.py --as astra 'Batch ready for review.'
Every message notifies the peer. Listening is automatic, with no separate command.
Only the chat is committed; local working files, HEAD and staging stay intact.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
import tempfile

from chatlib import (AGENTS, CHAT, ROOT, ChatError, GitError,
                     check_history, fetch, git, listen, new_message, parse_chat,
                     positive_seconds, read_chat)


def check_public_text(root, text):
    # Reuse the repository's path policy without rescanning unchanged PDFs.
    sys.path.insert(0, str(root / "tools"))
    from check_public_paths import text_issues
    findings = text_issues(text, CHAT)
    if findings:
        raise ChatError("Message fails the public-path policy: "
                        + ", ".join(sorted({issue.reason for issue in findings})))


def message_commit(root, base, text, actor):
    """Make a chat-only child of base without using the working index/branch."""
    check_public_text(root, text)
    with tempfile.TemporaryDirectory(prefix="chat-send-") as directory:
        env = {"GIT_INDEX_FILE": str(Path(directory) / "index")}
        git(root, "read-tree", base, env_extra=env)
        blob = git(root, "hash-object", "-w", "--stdin", data=text.encode()).stdout.decode().strip()
        git(root, "update-index", "--add", "--cacheinfo", "100644", blob, CHAT, env_extra=env)
        tree = git(root, "write-tree", env_extra=env).stdout.decode().strip()
        name, email = AGENTS[actor]
        description = f"send message\n\nCo-authored-by: {name} <{email}>\n"
        return git(root, "commit-tree", tree, "-p", base,
                   data=description.encode(), env_extra=env).stdout.decode().strip()


def publish(root, actor, body, *, remote="origin", branch="master"):
    """Append the next numbered message; a failed push stops for review."""
    check_public_text(root, body)
    base = fetch(root, remote, branch)
    text = read_chat(root, base)
    current = parse_chat(text)
    message = new_message(actor, body, len(current.messages) + 1)
    print(f"Message ID: {message.id}", flush=True)
    appended = text + ("\n" if text.endswith("\n") else "\n\n") + message.render() + "\n"
    commit = message_commit(root, base, appended, message.sender)
    try:
        result = git(root, "push", "--porcelain", "--", remote,
                     f"{commit}:refs/heads/{branch}", check=False)
        if result.returncode == 0:
            print(f"Sent message at {commit}.", flush=True)
            return base, commit
        error = result.stderr.decode("utf-8", errors="replace").strip()
    except GitError as exc:
        error = str(exc)
    # Show competing messages, but never merge or resend automatically.
    try:
        updated = fetch(root, remote, branch)
    except GitError as exc:
        raise ChatError(f"Delivery uncertain; check upstream before resending. Fetch failed: {exc}") from exc
    incoming = read_chat(root, updated)
    observed = parse_chat(incoming)
    check_history(current, observed)
    if incoming != text:
        print(f"\nNew chat messages received while sending at {updated}:\n", flush=True)
        added = observed.messages[len(current.messages):]
        for value in added:
            print(value.display() + "\n", flush=True)
        if not added:
            print(incoming[len(text):], flush=True)
        raise ChatError("Push did not report success. Review these messages before sending again.")
    if updated != base:
        raise ChatError("Upstream changed while sending (no new chat text). "
                        "Review the repository update before sending again.")
    raise ChatError(f"Push failed: {error}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--as", dest="actor", choices=AGENTS, required=True,
                        help="sender identity")
    parser.add_argument("--remote", default="origin")
    parser.add_argument("--branch", default="master")
    parser.add_argument("--interval", type=positive_seconds, default=15)
    parser.add_argument("--no-pull", action="store_true",
                        help="leave working files unchanged even when a reply arrives")
    source = parser.add_mutually_exclusive_group()
    source.add_argument("message", nargs="?", help="message text; otherwise use --file or stdin")
    source.add_argument("--file", type=Path, help="read a UTF-8 Markdown message from a file")
    args = parser.parse_args()
    actor = args.actor
    if args.file:
        body = args.file.read_text(encoding="utf-8")
    elif args.message is not None:
        body = args.message
    elif not sys.stdin.isatty():
        body = sys.stdin.read()
    else:
        parser.error("provide a message, --file, or stdin")
    baseline, _ = publish(ROOT, actor, body, remote=args.remote, branch=args.branch)
    # Use the PRE-send snapshot, not a fresh one: a reply racing with the push
    # or the rearm must not be swallowed. Own messages never qualify as replies.
    return listen(ROOT, actor, remote=args.remote, branch=args.branch, interval=args.interval,
                  since=baseline, no_pull=args.no_pull)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\nStopped. A message already reported as sent remains published.", flush=True)
        sys.exit(130)
    except (ChatError, OSError, UnicodeError) as exc:
        print(f"Sender stopped: {exc}", file=sys.stderr, flush=True)
        sys.exit(2)
