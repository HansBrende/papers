"""Regression tests for the public-content privacy gate."""

import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import zipfile

import check_public_paths as gate


def home_path():
    return "/" + "Users" + "/sample/research.txt"


def zipped(name, contents):
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", zipfile.ZIP_DEFLATED) as archive:
        archive.writestr(name, contents)
    return buffer.getvalue()


class ContentTests(unittest.TestCase):
    def test_known_host_paths(self):
        samples = [home_path(), "/" + "home" + "/sample/a", "/" + "tmp" + "/scratch",
                   "/" + "private" + "/" + "var" + "/folders/random/a", "/" + "Library" + "/TeX/texbin/latexmk",
                   "/" + "usr" + "/local/bin/python", "C:" + "\\Users\\sample\\a",
                   "C:" + r"\\Users\\sample\\a",
                   "\\\\server" + "\\share\\a", "file" + ":///somewhere/a",
                   home_path().replace("/", "%2F"), home_path().replace("/", "\\/")]
        for sample in samples:
            with self.subTest(sample=sample):
                self.assertTrue(gate.text_issues(sample, "example.txt"))

    def test_generic_or_relative_content(self):
        samples = ["paper/main.pdf", "../other-paper/lean", "https://example.org/paper.pdf",
                   "#!/usr/bin/env python3", "/root/final_local_coding", "/private/instance",
                   r"i:\\mathbb N", "A theorem about home directories", "the file: an explanation"]
        for sample in samples:
            self.assertFalse(gate.text_issues(sample, "example.txt"), sample)

    def test_binary_and_zip_contents(self):
        self.assertTrue(gate.inspect_bytes(b"\x00\xff" + home_path().encode(), "binary.dat"))
        self.assertTrue(gate.inspect_bytes(zipped("a.txt", home_path()), "archive.zip"))
        self.assertTrue(gate.inspect_bytes(zipped("a.zip", zipped("b.txt", home_path())), "archive.zip"))
        self.assertFalse(gate.inspect_bytes(zipped("a.txt", "relative/path"), "archive.zip"))

    def test_archive_member_names_and_limits(self):
        self.assertTrue(gate.inspect_bytes(zipped(home_path(), "safe"), "archive.zip"))
        self.assertTrue(gate.inspect_bytes(zipped("a", "safe"), "archive.zip", depth=gate.MAX_DEPTH))
        self.assertTrue(gate.inspect_bytes(zipped("a", "safe"), "archive.zip", budget=[0, 100]))
        self.assertTrue(gate.inspect_bytes(zipped("a", "safe"), "archive.zip", budget=[10, 0]))
        self.assertTrue(gate.inspect_bytes(b"invalid", "archive.zip"))
        self.assertTrue(gate.inspect_bytes(b"\x1f\x8bcompressed", "archive.gz"))

    def test_messages_do_not_include_private_match(self):
        issues = gate.inspect_bytes(zipped(home_path(), home_path()), "archive.zip")
        self.assertNotIn(home_path(), repr(issues))

    def test_pdf_requires_dependency(self):
        with patch.dict("sys.modules", {"pypdf": None}):
            self.assertEqual(gate.pdf_issues(b"", "paper.pdf")[0].reason,
                             "PDF inspection requires pypdf")

    def test_pdf_metadata_and_streams(self):
        try:
            from pypdf import PdfWriter
            from pypdf.generic import DecodedStreamObject, NameObject
        except ImportError:
            self.skipTest("pypdf unavailable; the gate itself fails closed for PDFs")
        writer = PdfWriter()
        writer.add_blank_page(width=72, height=72)
        buffer = io.BytesIO()
        writer.write(buffer)
        self.assertFalse(gate.inspect_bytes(buffer.getvalue(), "paper.pdf"))
        writer.add_metadata({"/Subject": home_path()})
        buffer = io.BytesIO()
        writer.write(buffer)
        self.assertTrue(any(x.reason == "personal home directory"
                            for x in gate.inspect_bytes(buffer.getvalue(), "paper.pdf")))
        writer.add_metadata({"/Subject": "Safe subject"})
        stream = DecodedStreamObject()
        stream.set_data(home_path().encode())
        writer._root_object[NameObject("/PrivateTest")] = writer._add_object(stream.flate_encode())
        buffer = io.BytesIO()
        writer.write(buffer)
        issues = gate.inspect_bytes(buffer.getvalue(), "paper.pdf")
        self.assertTrue(any(x.reason == "personal home directory" for x in issues))


class RepositoryTests(unittest.TestCase):
    def test_exact_staged_content_and_deletions(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "file.txt").write_text(home_path())
            (root / "link").symlink_to(home_path())
            subprocess.run(["git", "add", "file.txt", "link"], cwd=root, check=True)
            (root / "file.txt").write_text("relative/path")
            (root / "link").unlink()
            (root / "link").symlink_to("file.txt")
            self.assertFalse(gate.scan_repository(root)[1])
            count, issues = gate.scan_index(root)
            self.assertEqual(count, 2)
            self.assertEqual({x.path for x in issues}, {"file.txt", "link"})
            self.assertTrue(any(x.reason == "absolute symlink target" for x in issues))
            # Removing entries from the index excludes them even if working
            # copies later contain disclosures again.
            subprocess.run(["git", "rm", "--cached", "-q", "-f", "file.txt", "link"],
                           cwd=root, check=True)
            (root / "file.txt").write_text(home_path())
            self.assertEqual(gate.scan_index(root), (0, []))
            self.assertTrue(gate.scan_repository(root)[1])

    def test_git_inventory_and_symlinks(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / ".gitignore").write_text("ignored*\n")
            (root / "ignored-tracked.txt").write_text(home_path())
            (root / "ignored-untracked.txt").write_text(home_path())
            (root / "new.txt").write_text(home_path())
            (root / "safe.txt").write_text("relative/path")
            (root / "absolute-link").symlink_to(home_path())
            (root / "relative-link").symlink_to("safe.txt")
            (root / "deleted.txt").write_text(home_path())
            subprocess.run(["git", "add", "-f", "ignored-tracked.txt", "deleted.txt"], cwd=root, check=True)
            (root / "deleted.txt").unlink()
            count, issues = gate.scan_repository(root)
            affected = {x.path for x in issues}
            self.assertIn("ignored-tracked.txt", affected)
            self.assertIn("new.txt", affected)
            self.assertIn("absolute-link", affected)
            self.assertNotIn("ignored-untracked.txt", affected)
            self.assertNotIn("safe.txt", affected)
            self.assertNotIn("relative-link", affected)
            self.assertNotIn("deleted.txt", affected)
            self.assertEqual(count, 6)


if __name__ == "__main__":
    unittest.main()
