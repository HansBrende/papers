"""Shared Git and message-envelope helpers for the chat commands."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time
import uuid


ROOT = Path(__file__).resolve().parent.parent
CHAT = "chat/fable-astra.md"
AGENTS = {
    "astra": ("GPT-6 Astra", "noreply@openai.com"),
    "fable": ("Claude Fable 5.2", "noreply@anthropic.com"),
}
START = "<!-- chat-message "
END = "<!-- /chat-message "
ID_PATTERN = re.compile(r"[0-9a-f]{32}")


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


def actor_for(root: Path, requested: str | None) -> str:
    actor = requested or git(root, "config", "--get", "chat.agent",
                             check=False).stdout.decode().strip()
    if actor not in AGENTS:
        raise ChatError("Use --as astra/fable, or set git config --local chat.agent astra/fable")
    return actor


def positive_seconds(value: str) -> float:
    seconds = float(value)
    if not math.isfinite(seconds) or seconds <= 0:
        raise argparse.ArgumentTypeError("interval must be finite and greater than zero")
    return seconds


@dataclass(frozen=True)
class Message:
    id: str
    sender: str
    recipient: str
    wake: bool  # Retained for old transcripts/readers; new messages always set it true.
    timestamp: str
    body: str

    @property
    def heading(self):
        label = "REVIEW REQUEST" if self.wake else "FYI — no wake-up"
        return (f"## {self.timestamp} — {AGENTS[self.sender][0]} → "
                f"{AGENTS[self.recipient][0]} — {label}")

    def render(self):
        metadata = dict(id=self.id, sender=self.sender, recipient=self.recipient,
                        wake=self.wake, timestamp=self.timestamp,
                        sha256=hashlib.sha256(self.body.encode()).hexdigest())
        return (START + json.dumps(metadata, ensure_ascii=False, sort_keys=True) + " -->\n"
                + self.heading + "\n\n" + self.body + "\n" + END + self.id + " -->")

    def same_request(self, other):
        return (self.id, self.sender, self.recipient, self.wake, self.body) == (
            other.id, other.sender, other.recipient, other.wake, other.body)


def new_message(actor: str, body: str, message_id=None) -> Message:
    body = body.rstrip("\n")
    if not body.strip() or START in body or END in body:
        raise ChatError("Message must be nonempty and cannot contain chat envelope markers")
    message_id = message_id or uuid.uuid4().hex
    if not ID_PATTERN.fullmatch(message_id):
        raise ChatError("Message ID must contain exactly 32 lowercase hexadecimal characters")
    timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    peer = "fable" if actor == "astra" else "astra"
    return Message(message_id, actor, peer, True, timestamp, body)


@dataclass
class Transcript:
    text: str
    preamble: str
    messages: dict[str, Message]


def parse_chat(text: str) -> Transcript:
    """Parse complete, immutable message blocks in their recorded order."""
    parts = text.split(START)
    if END in parts[0]:
        raise ChatError("Unmatched chat envelope terminator")
    messages = {}
    for part in parts[1:]:
        metadata, separator, rest = part.partition(" -->\n")
        try:
            meta = json.loads(metadata)
            if (not separator or set(meta) != {"id", "sender", "recipient", "wake", "timestamp", "sha256"}
                    or not isinstance(meta["id"], str) or not ID_PATTERN.fullmatch(meta["id"])
                    or meta["sender"] not in AGENTS or meta["recipient"] not in AGENTS
                    or meta["sender"] == meta["recipient"] or type(meta["wake"]) is not bool
                    or not isinstance(meta["timestamp"], str) or "\n" in meta["timestamp"]):
                raise ValueError("invalid metadata")
            visible, terminator, after = rest.partition("\n" + END + meta["id"] + " -->")
            heading, blank, body = visible.partition("\n\n")
            digest = meta.pop("sha256")
            message = Message(**meta, body=body)
            if (not terminator or after.strip() or not blank or heading != message.heading
                    or not body.strip() or END in body or meta["id"] in messages
                    or digest != hashlib.sha256(body.encode()).hexdigest()):
                raise ValueError("incomplete, interleaved, or duplicate message")
        except (ValueError, KeyError, TypeError) as exc:
            raise ChatError("Malformed chat envelope; inspect the message history") from exc
        messages[message.id] = message
    return Transcript(text, parts[0].rstrip("\n"), messages)


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
    """Internal send/resume loop. Every new peer message ends the wait."""
    since = revision(root, since)
    baseline = previous = parse_chat(read_chat(root, since))
    print(f"Listening as {actor} on {remote}/{branch}; fetch-only polling every "
          f"{interval:g}s from {since}. Every peer message requests a response.", flush=True)
    resume = ["python3", "chat/send.py", "--as", actor, "--resume", "--since", since]
    if remote != "origin":
        resume += ["--remote", remote]
    if branch != "master":
        resume += ["--branch", branch]
    if interval != 15:
        resume += ["--interval", str(interval)]
    if no_pull:
        resume += ["--no-pull"]
    print("To resume without resending: " + shlex.join(resume), flush=True)
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
        incoming = [message for key, message in current.messages.items()
                    if key not in baseline.messages and message.recipient == actor]
        if incoming:
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
            print(f"No new peer message for {actor}.", flush=True)
            return 1
        time.sleep(interval)
