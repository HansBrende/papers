"""Chat integration tests using disposable clones and a local bare remote.

Run: python3 -m unittest discover -s chat -p 'test_chat.py'
No GitHub access or real messages. Includes actual rejected pushes.
"""

from contextlib import redirect_stderr, redirect_stdout
from dataclasses import replace
from io import StringIO
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from chatlib import (DELIMITER, SEPARATOR, ChatError, check_history, listen,
                     new_message, parse_chat)
import send


SOURCE = Path(__file__).parent
CHAT = "chat/fable-astra.md"
INITIAL = "# Discussion\n\nAstra: initial message.\n"

# Exercise the real CLI/Git writes while bounding waits in individual checks.
# Separate live-process tests below cover the unmodified blocking workflow.
CLI_BOOTSTRAP = """
import runpy, sys
from pathlib import Path
directory = Path(sys.argv.pop(1))
sys.path.insert(0, str(directory))
import chatlib
chatlib.listen = lambda *a, **kw: 0
runpy.run_path(str(directory / 'send.py'), run_name='__main__')
"""


def git(root, *args):
    return subprocess.run(["git", *args], cwd=root, check=True,
                          capture_output=True, text=True).stdout.strip()


class RepoCase(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="chat-test-")
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        self.remote = base / "remote.git"
        self.writer = base / "writer clone"
        self.reader = base / "reader clone"
        git(base, "init", "--bare", str(self.remote))
        git(self.remote, "symbolic-ref", "HEAD", "refs/heads/master")
        self.writer.mkdir()
        git(self.writer, "init")
        git(self.writer, "symbolic-ref", "HEAD", "refs/heads/master")
        self.configure(self.writer)
        (self.writer / "chat").mkdir()
        for name in ("send.py", "chatlib.py"):
            shutil.copyfile(SOURCE / name, self.writer / "chat" / name)
        (self.writer / "tools").mkdir()
        shutil.copyfile(SOURCE.parent / "tools/check_public_paths.py",
                        self.writer / "tools/check_public_paths.py")
        shutil.copyfile(SOURCE.parent / ".gitignore", self.writer / ".gitignore")
        (self.writer / CHAT).write_text(INITIAL)
        (self.writer / "work.txt").write_text("published work\n")
        git(self.writer, "add", ".")
        git(self.writer, "commit", "-m", "Initial fixture")
        git(self.writer, "remote", "add", "origin", str(self.remote))
        git(self.writer, "push", "-u", "origin", "master")
        git(base, "clone", str(self.remote), str(self.reader))
        self.configure(self.reader)
        self.before = git(self.reader, "rev-parse", "HEAD")

    def configure(self, root):
        git(root, "config", "user.name", "Chat Test")
        git(root, "config", "user.email", "chat@example.invalid")
        git(root, "config", "commit.gpgsign", "false")
        hooks = root / ".git/empty-hooks"
        hooks.mkdir()
        git(root, "config", "core.hooksPath", str(hooks))

    def publish_file(self, name, text):
        (self.writer / name).write_text(text)
        git(self.writer, "add", name)
        git(self.writer, "commit", "-m", "Remote update")
        git(self.writer, "push")
        return git(self.writer, "rev-parse", "HEAD")

    def append(self, body="Please review this proposal.", actor="fable"):
        text = (self.writer / CHAT).read_text()
        message = new_message(actor, body, len(parse_chat(text).messages) + 1)
        text += "\n" + message.render() + "\n"
        return self.publish_file(CHAT, text)

    def watch(self, *, actor="astra", since=None, no_pull=False):
        output, errors = StringIO(), StringIO()
        with redirect_stdout(output), redirect_stderr(errors):
            try:
                status = listen(self.reader, actor, since=since or self.before,
                                once=True, no_pull=no_pull)
            except ChatError as exc:
                print(exc, file=sys.stderr)
                status = 2
        return subprocess.CompletedProcess([], status, output.getvalue(), errors.getvalue())

    def send_cli(self, *args, root=None, data=None):
        root = root or self.reader
        return subprocess.run([sys.executable, "-c", CLI_BOOTSTRAP,
                               str(root / "chat"), *args], input=data, capture_output=True,
                              text=True, timeout=15)

    def remote_chat(self):
        return git(self.remote, "show", "master:" + CHAT)


class ListenTests(RepoCase):
    def test_no_worktree_updates_on_unrelated_commits(self):
        self.publish_file("work.txt", "remote update\n")
        result = self.watch()
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)
        self.assertEqual((self.reader / "work.txt").read_text(), "published work\n")

    def test_waiting_reply_is_received_and_branch_fast_forwarded(self):
        head = self.append()
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)
        result = self.watch()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Please review", result.stdout)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), head)

    def test_reply_output_contains_all_bodies_without_separators_or_footer(self):
        self.append("First response.")
        self.append("Second **response**.\n\n---\n\nMore detail.")
        result = self.watch()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertLess(result.stdout.index("First response."), result.stdout.index("Second **response**."))
        self.assertNotIn(DELIMITER, result.stdout)
        self.assertNotIn("<!-- chat-message", result.stdout)
        for message in parse_chat(self.remote_chat()).messages:
            self.assertIn(message.heading + "\nID: " + message.id + "\n\n", result.stdout)
        self.assertTrue(result.stdout.endswith("More detail.\n\n"))

    def test_own_request_does_not_wake_self(self):
        self.append("Astra's outbound request", actor="astra")
        self.assertEqual(self.watch().returncode, 1)
        self.assertEqual(self.watch(actor="fable").returncode, 0)

    def test_dirty_work_and_staging_are_preserved(self):
        work = self.reader / "work.txt"
        work.write_text("staged proof\n")
        git(self.reader, "add", "work.txt")
        work.write_text("more unfinished proof\n")
        stage = git(self.reader, "write-tree")
        head = self.append()
        result = self.watch()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(git(self.reader, "write-tree"), stage)
        self.assertEqual(work.read_text(), "more unfinished proof\n")
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)
        self.assertEqual(self.watch(since=head).returncode, 1)

    def test_unpushed_chat_is_not_a_notification(self):
        draft = INITIAL + "\nAstra: unsent draft.\n"
        (self.reader / CHAT).write_text(draft)
        self.assertEqual(self.watch().returncode, 1)
        self.append()
        self.assertEqual(self.watch().returncode, 0)
        self.assertEqual((self.reader / CHAT).read_text(), draft)

    def test_untracked_file_is_not_overwritten(self):
        local = self.reader / "new-file.txt"
        local.write_text("local data\n")
        self.publish_file("new-file.txt", "remote data\n")
        self.append()
        self.assertEqual(self.watch().returncode, 0)
        self.assertEqual(local.read_text(), "local data\n")

    def test_diverged_branch_is_not_merged(self):
        (self.reader / "work.txt").write_text("local committed proof\n")
        git(self.reader, "add", "work.txt")
        git(self.reader, "commit", "-m", "Local work")
        head = git(self.reader, "rev-parse", "HEAD")
        self.append()
        result = self.watch()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("manual reconciliation", result.stdout)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), head)

    def test_other_branch_and_no_pull(self):
        self.append()
        result = self.watch(no_pull=True)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)
        git(self.reader, "checkout", "-b", "research")
        self.assertEqual(self.watch().returncode, 0)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)

    def test_rewritten_and_deleted_chat_stop(self):
        self.publish_file(CHAT, "# Changed history\n")
        self.assertEqual(self.watch().returncode, 2)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)
        git(self.writer, "rm", CHAT)
        git(self.writer, "commit", "-m", "Delete chat")
        git(self.writer, "push")
        self.assertEqual(self.watch().returncode, 2)

    def test_fetch_failure_is_not_a_reply(self):
        git(self.reader, "remote", "set-url", "origin", str(self.remote / "missing"))
        result = self.watch()
        self.assertEqual(result.returncode, 2)
        self.assertIn("Fetch failed", result.stderr)


class SendTests(RepoCase):
    def test_sender_identity_is_required_and_validated(self):
        result = self.send_cli("Do not guess my identity")
        self.assertEqual(result.returncode, 2)
        self.assertIn("required: --as", result.stderr)
        result = self.send_cli("--as", "opus", "Unsupported sender")
        self.assertEqual(result.returncode, 2)
        self.assertIn("invalid choice", result.stderr)
        self.assertEqual(git(self.remote, "rev-parse", "master"), self.before)

    def test_sender_preserves_index_head_and_unrelated_local_commits(self):
        (self.reader / "work.txt").write_text("unpublished local theorem\n")
        git(self.reader, "add", "work.txt")
        git(self.reader, "commit", "-m", "Local theorem")
        head = git(self.reader, "rev-parse", "HEAD")
        (self.reader / "work.txt").write_text("staged changes\n")
        git(self.reader, "add", "work.txt")
        (self.reader / "work.txt").write_text("unstaged changes\n")
        index = (self.reader / ".git/index").read_bytes()
        result = self.send_cli("--as", "astra", "Please check my argument")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), head)
        self.assertEqual((self.reader / ".git/index").read_bytes(), index)
        self.assertEqual((self.reader / "work.txt").read_text(), "unstaged changes\n")
        self.assertEqual(git(self.remote, "diff", "--name-only", self.before, "master"), CHAT)
        self.assertEqual(git(self.remote, "show", "master:work.txt"), "published work")
        self.assertIn("Co-authored-by: GPT-6 Astra <noreply@openai.com>",
                      git(self.remote, "log", "-1", "--format=%B"))

    def test_fable_identity_stdin_and_implicit_notification(self):
        result = self.send_cli("--as", "fable", data="A multiline message\n\nWith a proof.")
        self.assertEqual(result.returncode, 0, result.stderr)
        messages = parse_chat(self.remote_chat()).messages
        self.assertEqual(len(messages), 1)
        self.assertEqual(messages[0].recipient, "astra")
        self.assertEqual(messages[0].body, "A multiline message\n\nWith a proof.")
        self.assertIn("Co-authored-by: Claude Fable 5.2 <noreply@anthropic.com>",
                      git(self.remote, "log", "-1", "--format=%B"))

    def test_repeated_messages_get_consecutive_ids_across_senders(self):
        for actor in ("astra", "fable", "astra"):
            result = self.send_cli("--as", actor, "yes")
            self.assertEqual(result.returncode, 0, result.stderr)
        messages = parse_chat(self.remote_chat()).messages
        self.assertEqual([m.id for m in messages], ["C1", "C2", "C3"])
        self.assertEqual([m.body for m in messages], ["yes"] * 3)
        self.assertEqual([m.sender for m in messages], ["astra", "fable", "astra"])

    def test_push_race_stops_for_review_without_publishing_or_reordering(self):
        own = "My result\n\nShared paragraph\n\nEnd."
        peer = "My alternative\n\nShared paragraph\n\nEnd."
        original = send.message_commit
        raced = False

        def race(root, base, text, actor):
            nonlocal raced
            commit = original(root, base, text, actor)
            if not raced:
                raced = True
                send.publish(self.writer, "fable", peer)
            return commit

        with patch.object(send, "message_commit", side_effect=race):
            with self.assertRaisesRegex(ChatError, "Review these messages before sending"):
                send.publish(self.reader, "astra", own)
        messages = parse_chat(self.remote_chat()).messages
        self.assertEqual([(m.id, m.sender, m.body) for m in messages], [("C1", "fable", peer)])
        self.assertEqual(git(self.remote, "rev-list", "--count", self.before + "..master"), "1")
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)
        # Only an explicit later send, after review, appends our message.
        send.publish(self.reader, "astra", own)
        messages = parse_chat(self.remote_chat()).messages
        self.assertEqual([(m.id, m.sender, m.body) for m in messages],
                         [("C1", "fable", peer), ("C2", "astra", own)])
        self.assertEqual(git(self.remote, "rev-list", "--count", self.before + "..master"), "2")

    def test_unrelated_push_race_also_stops_without_automatic_retry(self):
        original = send.message_commit

        def race(root, base, text, actor):
            commit = original(root, base, text, actor)
            self.publish_file("work.txt", "A competing published result\n")
            return commit

        with patch.object(send, "message_commit", side_effect=race):
            with self.assertRaisesRegex(ChatError, "no new chat text.*Review"):
                send.publish(self.reader, "astra", "An outgoing message")
        self.assertEqual(parse_chat(self.remote_chat()).messages, [])

    def test_unconfirmed_push_stops_without_resending(self):
        body = "Delivered despite lost acknowledgement"
        original = send.git

        def lost_ack(root, *args, **kwargs):
            result = original(root, *args, **kwargs)
            if args[0] == "push" and result.returncode == 0:
                return subprocess.CompletedProcess(result.args, 1, b"", b"lost response")
            return result

        with patch.object(send, "git", side_effect=lost_ack):
            with self.assertRaisesRegex(ChatError, "Push did not report success.*Review"):
                send.publish(self.reader, "astra", body)
        messages = parse_chat(self.remote_chat()).messages
        self.assertEqual([(m.id, m.body) for m in messages], [("C1", body)])

    def test_send_rearms_before_send_baseline_and_catches_immediate_reply(self):
        def immediate_reply(root, actor, **options):
            self.assertEqual(options["since"], self.before)
            send.publish(self.writer, "fable", "Immediate response")
            return listen(root, actor, once=True, **options)

        with patch.object(send, "ROOT", self.reader), patch.object(send, "listen", immediate_reply), \
                patch.object(sys, "argv", ["send.py", "--as", "astra", "Please review"]):
            self.assertEqual(send.main(), 0)
        self.assertEqual(len(parse_chat(self.remote_chat()).messages), 2)

    def test_public_paths_and_reserved_separator_are_rejected_before_push(self):
        path = "/".join(("", "Users", "Example", "private-file"))
        result = self.send_cli("--as", "astra", "See " + path)
        self.assertEqual(result.returncode, 2)
        self.assertIn("public-path policy", result.stderr)
        result = self.send_cli("--as", "astra", "Beginning" + DELIMITER + "End")
        self.assertEqual(result.returncode, 2)
        self.assertIn("reserved 46-dash separator", result.stderr)
        self.assertEqual(git(self.remote, "rev-parse", "master"), self.before)

    def test_no_union_merge_rule(self):
        self.assertEqual(git(self.reader, "check-attr", "merge", "--", CHAT),
                         CHAT + ": merge: unspecified")

    def test_default_cli_sends_and_waits_without_extra_flags(self):
        process = subprocess.Popen(
            [sys.executable, str(self.reader / "chat/send.py"),
             "--as", "astra", "--interval", "0.05", "Completed batch; please review."],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
        try:
            lines = [process.stdout.readline() for _ in range(3)]
            self.assertTrue(any("Sent message" in line for line in lines), lines)
            self.assertTrue(any("Listening as astra" in line for line in lines), lines)
            self.assertIsNone(process.poll())
            self.assertEqual(len(parse_chat(self.remote_chat()).messages), 1)
            send.publish(self.writer, "fable", "Here is my review.")
            output, errors = process.communicate(timeout=10)
            self.assertEqual(process.returncode, 0, errors)
            self.assertIn("Here is my review.", output)
        finally:
            if process.poll() is None:
                process.kill()
            process.communicate()

    def test_obsolete_flags_are_removed(self):
        for flag in ("--wake", "--no-wait", "--id", "--resume", "--since"):
            self.assertEqual(self.send_cli("--as", "astra", flag, "Do not post").returncode, 2)
        self.assertEqual(git(self.remote, "rev-parse", "master"), self.before)


class MessageTests(unittest.TestCase):
    def test_visible_layout_and_original_preamble(self):
        a = new_message("astra", "A **proof**, with code:\n\n```lean\nexample : True := trivial\n```", 1)
        rendered = a.render()
        self.assertEqual(a.id, "C1")
        self.assertEqual(rendered, DELIMITER + "\n## FROM: GPT-6 Astra at "
                         + a.timestamp + "\nID: " + a.id + "\n\n" + a.body)
        self.assertNotIn("<!--", rendered)
        old = INITIAL + rendered
        b = new_message("fable", "My response.", 2)
        combined = old + "\n\n" + b.render()
        self.assertEqual(parse_chat(combined).messages, [a, b])
        check_history(parse_chat(old), parse_chat(combined))

    def test_body_preserves_unicode_and_internal_markdown(self):
        body = "\nAstra–Fable: π\n\n---\n\n<!-- a normal Markdown comment -->\n\nEnd."
        a = new_message("astra", body + "\n\n", 1)
        self.assertEqual(a.body, body)
        self.assertEqual(parse_chat(INITIAL + a.render() + "\n").messages, [a])

    def test_reserved_separator_boundaries_and_ordinary_rules(self):
        for body in (SEPARATOR, SEPARATOR + "\nafter", "before\n" + SEPARATOR,
                     "before" + DELIMITER + "after", "```" + DELIMITER + "```"):
            with self.subTest(body=body), self.assertRaisesRegex(ChatError, "46-dash"):
                new_message("astra", body, 1)
        for body in ("---", "-" * 45, "-" * 47, "inline " + SEPARATOR + " text"):
            message = new_message("astra", body, 1)
            self.assertEqual(parse_chat(INITIAL + message.render()).messages, [message])

    def test_append_requires_exact_prefix_without_reordering(self):
        a = new_message("astra", "First claim", 1)
        b = new_message("fable", "Second claim", 2)
        before = parse_chat(INITIAL + a.render())
        after = parse_chat(INITIAL + a.render() + "\n\n" + b.render())
        check_history(before, after)
        with self.assertRaises(ChatError):
            check_history(before, parse_chat(INITIAL + b.render() + "\n\n" + a.render()))
        with self.assertRaises(ChatError):
            check_history(before, parse_chat(INITIAL + b.render()))
        with self.assertRaises(ChatError):
            changed = replace(a, body="A changed claim")
            check_history(before, parse_chat(INITIAL + changed.render()))

    def test_bad_numbering_and_interleaved_messages_are_rejected(self):
        a = new_message("astra", "First claim", 1)
        b = new_message("fable", "Second claim", 2)
        with self.assertRaises(ChatError):
            parse_chat(INITIAL + a.render() + "\n" + a.render())
        with self.assertRaises(ChatError):
            parse_chat(INITIAL + a.render().replace("First claim", b.render()))
        with self.assertRaises(ChatError):
            parse_chat(INITIAL + a.render().replace("ID: C1", "ID: C3"))


if __name__ == "__main__":
    unittest.main()
