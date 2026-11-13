"""Integration checks with two disposable clones and a local bare remote.

Run from the repository root:
    python3 -m unittest discover -s chat -p 'test_watch.py'
"""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("watch.py")
CHAT = "chat/fable-astra.md"
INITIAL = "# Discussion\n\nAstra: initial message.\n"
REPLY = "\nFable: a new proposal.\n"


def git(root, *args):
    return subprocess.run(["git", *args], cwd=root, check=True,
                          capture_output=True, text=True).stdout.strip()


class WatchIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="chat-watch-")
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
        shutil.copyfile(SCRIPT, self.writer / "chat/watch.py")
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
        git(root, "config", "user.name", "Watcher Test")
        git(root, "config", "user.email", "watcher@example.invalid")
        git(root, "config", "commit.gpgsign", "false")
        empty_hooks = root / ".git/empty-hooks"
        empty_hooks.mkdir()
        git(root, "config", "core.hooksPath", str(empty_hooks))

    def publish(self, name=CHAT, text=INITIAL + REPLY):
        (self.writer / name).write_text(text)
        git(self.writer, "add", name)
        git(self.writer, "commit", "-m", "Remote update")
        git(self.writer, "push")
        return git(self.writer, "rev-parse", "HEAD")

    def watch(self, *args):
        return subprocess.run(
            [sys.executable, str(self.reader / "chat/watch.py"), "--once", *args],
            cwd=self.temp.name, capture_output=True, text=True, timeout=10,
        )

    def test_no_change_and_unrelated_commit(self):
        self.assertEqual(self.watch().returncode, 1)
        head = self.publish("work.txt", "new published work\n")
        result = self.watch()
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), head)
        self.assertIn("No new chat text", result.stdout)

    def test_reply_already_waiting_before_start(self):
        head = self.publish()
        result = self.watch()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(REPLY.strip(), result.stdout)
        self.assertNotIn("Astra: initial", result.stdout)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), head)
        self.assertEqual(self.watch().returncode, 1)

    def test_dirty_work_is_preserved_and_since_avoids_redelivery(self):
        work = self.reader / "work.txt"
        work.write_text("unfinished local proof\n")
        head = self.publish()
        result = self.watch()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(REPLY.strip(), result.stdout)
        self.assertEqual(work.read_text(), "unfinished local proof\n")
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)
        self.assertEqual(self.watch("--since", head).returncode, 1)

    def test_unpushed_chat_is_not_a_notification(self):
        chat = self.reader / CHAT
        draft = INITIAL + "\nAstra: local unsent draft.\n"
        chat.write_text(draft)
        self.assertEqual(self.watch().returncode, 1)
        self.publish()
        result = self.watch()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(REPLY.strip(), result.stdout)
        self.assertNotIn("local unsent draft", result.stdout)
        self.assertEqual(chat.read_text(), draft)

    def test_untracked_file_is_not_overwritten(self):
        local = self.reader / "new-file.txt"
        local.write_text("local data\n")
        self.publish("new-file.txt", "remote data\n")
        self.publish()
        result = self.watch()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(local.read_text(), "local data\n")
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)

    def test_diverged_branch_is_not_merged(self):
        (self.reader / "work.txt").write_text("local committed proof\n")
        git(self.reader, "add", "work.txt")
        git(self.reader, "commit", "-m", "Local work")
        head = git(self.reader, "rev-parse", "HEAD")
        self.publish()
        result = self.watch()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("manual reconciliation", result.stdout)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), head)
        self.assertEqual(git(self.reader, "status", "--porcelain"), "")

    def test_other_branch_is_not_updated(self):
        git(self.reader, "checkout", "-b", "research")
        self.publish()
        result = self.watch()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("not on the watched tracking branch", result.stdout)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)

    def test_rewritten_chat_stops_without_pulling(self):
        self.publish(text="# Replaced history\n")
        result = self.watch()
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("reconcile both histories", result.stdout)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)

    def test_deleted_chat_stops_without_pulling(self):
        git(self.writer, "rm", CHAT)
        git(self.writer, "commit", "-m", "Delete chat")
        git(self.writer, "push")
        result = self.watch()
        self.assertEqual(result.returncode, 2)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)

    def test_explicit_baseline_after_an_external_pull(self):
        self.publish()
        git(self.reader, "pull", "--ff-only")
        self.assertEqual(self.watch().returncode, 1)
        result = self.watch("--since", self.before)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(REPLY.strip(), result.stdout)

    def test_fetch_failure_is_not_a_reply(self):
        git(self.reader, "remote", "set-url", "origin", str(self.remote / "missing"))
        result = self.watch()
        self.assertEqual(result.returncode, 2)
        self.assertIn("Fetch failed", result.stderr)
        self.assertEqual(git(self.reader, "rev-parse", "HEAD"), self.before)

    def test_listening_process_exits_on_later_reply(self):
        process = subprocess.Popen(
            [sys.executable, str(self.reader / "chat/watch.py"), "--interval", "0.05"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
        try:
            self.assertIn("Watching", process.stdout.readline())
            self.assertIn("Working files already", process.stdout.readline())
            self.assertIsNone(process.poll())
            self.publish()
            output, errors = process.communicate(timeout=10)
            self.assertEqual(process.returncode, 0, errors)
            self.assertIn(REPLY.strip(), output)
        finally:
            if process.poll() is None:
                process.kill()
            process.communicate()


if __name__ == "__main__":
    unittest.main()
