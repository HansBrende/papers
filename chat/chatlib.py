"""Shared Git and Markdown message helpers for the chat commands."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent.parent
CHAT = "chat/fable-astra.md"
AGENTS = {
    "astra": ("GPT-6 Astra", "noreply@openai.com"),
    "fable": ("Claude Fable 5.2", "noreply@anthropic.com"),
}
SEPARATOR = "-" * 46
DELIMITER = "\n" + SEPARATOR + "\n"
HEADER_PATTERN = re.compile(r"\n## FROM: ([^\n]+) at ([^\n]+)\nID: (C[1-9][0-9]*)\n\n")


class ChatError(RuntimeError):
    pass


class GitError(ChatError):
    pass


def git(root: Path, *args: str, check=True, data=None, env_extra=None):
    env = os.environ.copy()
    env["GIT_TERMINAL_PROMPT"] = "0"
    if env_extra:
        env.update(env_extra)
    try:
        result = subprocess.run(["git", *args], cwd=root, env=env, input=data,
                                capture_output=True, timeout=30)
    except subprocess.TimeoutExpired as exc:
        raise GitError("Git command timed out after 30 seconds") from exc
    if check and result.returncode:
        raise GitError(result.stderr.decode("utf-8", errors="replace").strip())
    return result


def revision(root: Path, ref: str) -> str:
    if ref.startswith("-"):
        raise ChatError("A revision cannot start with '-'")
    return git(root, "rev-parse", "--verify", ref + "^{commit}").stdout.decode().strip()


def fetch(root: Path, remote: str, branch: str) -> str:
    ref = f"refs/remotes/{remote}/{branch}"
    git(root, "check-ref-format", ref)
    git(root, "check-ref-format", f"refs/heads/{branch}")
    git(root, "fetch", "--quiet", "--no-tags", "--", remote,
        f"refs/heads/{branch}:{ref}")
    return revision(root, ref)


def read_chat(root: Path, commit: str) -> str:
    return git(root, "show", f"{commit}:{CHAT}").stdout.decode("utf-8")


def positive_seconds(value: str) -> float:
    seconds = float(value)
    if not math.isfinite(seconds) or seconds <= 0:
        raise argparse.ArgumentTypeError("interval must be finite and greater than zero")
    return seconds


@dataclass(frozen=True)
class Message:
    id: str
    sender: str
    timestamp: str
    body: str

    @property
    def recipient(self):
        return "fable" if self.sender == "astra" else "astra"

    @property
    def heading(self):
        return f"## FROM: {AGENTS[self.sender][0]} at {self.timestamp}"

    def display(self):
        return self.heading + "\nID: " + self.id + "\n\n" + self.body

    def render(self):
        return DELIMITER + "\n" + self.display()


def new_message(actor: str, body: str, number: int) -> Message:
    body = body.rstrip("\n")
    if actor not in AGENTS:
        raise ChatError("Unknown sender")
    if not body.strip():
        raise ChatError("Message must be nonempty")
    if DELIMITER in "\n" + body + "\n":
        raise ChatError("Message body contains the reserved 46-dash separator; use a different rule")
    timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    return Message(f"C{number}", actor, timestamp, body)


@dataclass
class Transcript:
    text: str
    messages: list[Message]


def parse_chat(text: str) -> Transcript:
    """Parse complete, immutable message blocks in their recorded order."""
    parts = text.split(DELIMITER)
    messages = []
    for part in parts[1:]:
        header = HEADER_PATTERN.match(part)
        if not header:
            raise ChatError("Malformed chat header; inspect the message history")
        name, timestamp, message_id = header.groups()
        sender = next((actor for actor, (display_name, _) in AGENTS.items()
                       if display_name == name), None)
        body = part[header.end():].rstrip("\n")
        if sender is None or not body.strip() or message_id != f"C{len(messages) + 1}":
            raise ChatError("Unknown sender, empty body or out-of-sequence ID; inspect the message history")
        messages.append(Message(message_id, sender, timestamp, body))
    return Transcript(text, messages)


def check_history(before: Transcript, after: Transcript):
    if not after.text.startswith(before.text):
        raise ChatError("Existing chat text was changed, removed or reordered; inspect before proceeding")


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
    return "Fast-forwarded the working branch after the notification."


def listen(root, actor, *, since, remote="origin", branch="master", interval=15,
           once=False, no_pull=False):
    """Wait after sending. Every new peer message ends the wait."""
    baseline = previous = parse_chat(read_chat(root, since))
    print(f"Listening as {actor} on {remote}/{branch}; fetch-only polling every "
          f"{interval:g}s. Every peer message requests a response.", flush=True)
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
        check_history(previous, current)
        previous = current
        incoming = [message for message in current.messages[len(baseline.messages):]
                    if message.recipient == actor]
        if incoming:
            if not no_pull:
                try:
                    print(sync_if_safe(root, commit, remote, branch), flush=True)
                except GitError as exc:
                    print(f"Could not fast-forward; message is still available: {exc}", flush=True)
            print(f"\nNew messages for {actor} at {commit}:\n", flush=True)
            for message in incoming:
                print(message.display() + "\n", flush=True)
            return 0
        if once:
            print(f"No new peer message for {actor}.", flush=True)
            return 1
        time.sleep(interval)
