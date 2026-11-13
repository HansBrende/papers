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

from chatlib import (AGENTS, CHAT, ROOT, ChatError, GitError, actor_for,
                     check_history, fetch, git, listen, new_message, parse_chat,
                     positive_seconds, read_chat, revision)


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


def publish(root, message, *, remote="origin", branch="master"):
    """Try one append. A competing push stops for review, never auto-merges.

    A stable ID distinguishes an uncertain delivery from an unsent message.
    """
    check_public_text(root, message.body)
    base = fetch(root, remote, branch)
    text = read_chat(root, base)
    current = parse_chat(text)
    print(f"Message ID: {message.id}", flush=True)
    existing = current.messages.get(message.id)
    if existing:
        if not message.same_request(existing):
            raise ChatError("Short message ID collision: that ID belongs to a different body "
                            "or sender. Add context to distinguish your message, then send again.")
        print(f"Message already delivered at {base}.", flush=True)
        return base, base
    appended = text + ("\n" if text.endswith("\n") else "\n\n") + message.render() + "\n"
    check_history(current, parse_chat(appended))
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
    # Inspect a rejected/lost push, but never retry publication automatically.
    try:
        updated = fetch(root, remote, branch)
    except GitError as exc:
        raise ChatError("Delivery uncertain. Retry the exact same text to keep its ID. "
                        f"Fetch failed: {exc}") from exc
    incoming = read_chat(root, updated)
    observed = parse_chat(incoming)
    check_history(current, observed)
    delivered = observed.messages.get(message.id)
    if delivered:
        if not message.same_request(delivered):
            raise ChatError("Short message ID collision: that ID belongs to a different body "
                            "or sender. Add context to distinguish your message, then send again.")
        print(f"Delivery confirmed at {updated}.", flush=True)
        return base, updated
    if incoming != text:
        print(f"\nNew incoming chat text at {updated}:\n", flush=True)
        added = [value for key, value in observed.messages.items() if key not in current.messages]
        for value in added:
            print(value.display() + "\n", flush=True)
        if not added:
            print(incoming[len(text):], flush=True)
        raise ChatError("A new incoming message was received while sending. Your message was "
                        "not sent. Review the incoming message first, then send again.")
    if updated != base:
        raise ChatError("Upstream changed while sending (no new chat text). Your message was "
                        "not sent. Review the repository update before sending again.")
    raise ChatError(f"Push failed; retry the exact same text to keep its ID: {error}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--as", dest="actor", choices=AGENTS,
                        help="identity (default: local Git config chat.agent)")
    parser.add_argument("--remote", default="origin")
    parser.add_argument("--branch", default="master")
    parser.add_argument("--interval", type=positive_seconds, default=15)
    parser.add_argument("--since", help="last-read commit (required with --resume)")
    parser.add_argument("--no-pull", action="store_true",
                        help="leave working files unchanged even when a reply arrives")
    source = parser.add_mutually_exclusive_group()
    source.add_argument("message", nargs="?", help="message text; otherwise use --file or stdin")
    source.add_argument("--file", type=Path, help="read a UTF-8 Markdown message from a file")
    source.add_argument("--resume", action="store_true", help="listen without sending again")
    args = parser.parse_args()
    actor = actor_for(ROOT, args.actor)
    if args.since:
        args.since = revision(ROOT, args.since)
        parse_chat(read_chat(ROOT, args.since))
    if args.resume:
        if not args.since:
            parser.error("--resume needs --since <last-read-commit> so pending replies are not missed")
        return listen(ROOT, actor, remote=args.remote, branch=args.branch, interval=args.interval,
                      since=args.since, no_pull=args.no_pull)
    if args.file:
        body = args.file.read_text(encoding="utf-8")
    elif args.message is not None:
        body = args.message
    elif not sys.stdin.isatty():
        body = sys.stdin.read()
    else:
        parser.error("provide a message, --file, or stdin")
    message = new_message(actor, body)
    baseline, _ = publish(ROOT, message, remote=args.remote, branch=args.branch)
    # Use the PRE-send snapshot, not a fresh one: a reply racing with the push
    # or the rearm must not be swallowed. Own messages never qualify as replies.
    return listen(ROOT, actor, remote=args.remote, branch=args.branch, interval=args.interval,
                  since=args.since or baseline, no_pull=args.no_pull)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\nStopped. A message already reported as sent remains published.", flush=True)
        sys.exit(130)
    except (ChatError, OSError, UnicodeError) as exc:
        print(f"Sender stopped: {exc}", file=sys.stderr, flush=True)
        sys.exit(2)
