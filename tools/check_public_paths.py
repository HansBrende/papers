#!/usr/bin/env python3
"""Reject host-specific paths in content that Git can publish.

Tracked files are checked even if an ignore rule matches them. New, nonignored
files are also checked. ZIP inspection is recursive, with a four-level nesting
limit, 10,000-member limit and 100 MiB total expanded-data limit per outer file.
PDF inspection requires pypdf and includes text, metadata, annotations and
decoded PDF objects. Agent identifiers and ordinary system shebangs are allowed.
Use --staged before committing to inspect the exact index blobs instead of
working files; a subsequent working-tree edit cannot hide a staged disclosure.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import io
from pathlib import Path, PureWindowsPath
import re
import subprocess
import sys
from urllib.parse import unquote
import zipfile


RULES = {
    "personal home directory": re.compile(r"(?<![\w:])/(?:Users|home)/[^\s/]+"),
    "host temporary directory": re.compile(
        r"(?<![\w:])/(?:private/(?:tmp|var)|tmp|var/folders)(?:/|\b)"
    ),
    "host tool directory": re.compile(
        r"(?<![\w:])/(?:Library/(?:TeX|Developer)|Applications|opt/homebrew|usr/local)(?:/|\b)"
    ),
    "Windows host directory": re.compile(
        r"(?<![\w:])[A-Za-z]:[\\/]+(?:Users|Documents and Settings|Temp|Windows|Program Files)(?:[\\/]|\b)",
        re.IGNORECASE,
    ),
    "Windows network share": re.compile(r"\\\\[A-Za-z0-9_.-]+\\[A-Za-z0-9_.-]+(?:\\|\b)"),
    "local file URI": re.compile(r"\bfile\s*:\s*(?:/|\\)", re.IGNORECASE),
}
MAX_DEPTH = 4
MAX_MEMBERS = 10_000
MAX_EXPANDED = 100 * 1024 * 1024


@dataclass(frozen=True)
class Issue:
    path: str
    reason: str
    count: int = 1


def text_issues(data: str | bytes, label: str) -> list[Issue]:
    """Inspect text or raw binary without reproducing matching private text."""
    if isinstance(data, bytes):
        data = data.decode("utf-8", errors="replace")
    # Handle URL escaping and the escaped slashes permitted by JSON.
    data = unquote(data).replace("\\/", "/")
    return [Issue(label, reason, len(matches))
            for reason, pattern in RULES.items()
            if (matches := pattern.findall(data))]


def pdf_issues(data: bytes, label: str) -> list[Issue]:
    try:
        from pypdf import PdfReader
        from pypdf.generic import IndirectObject, StreamObject
    except ImportError:
        return [Issue(label, "PDF inspection requires pypdf")]
    try:
        reader = PdfReader(io.BytesIO(data), strict=True)
        if reader.is_encrypted:
            return [Issue(label, "encrypted PDF cannot be inspected")]
        issues = text_issues(str(reader.metadata or {}), label)
        for page in reader.pages:
            issues += text_issues(page.extract_text() or "", label)
            for annotation in page.get("/Annots", []):
                issues += text_issues(str(annotation.get_object()), label)
        object_ids = {(oid, generation) for generation, objects in reader.xref.items()
                      for oid in objects if oid}
        object_ids.update((oid, 0) for oid in reader.xref_objStm)
        for oid, generation in object_ids:
            obj = reader.get_object(IndirectObject(oid, generation, reader))
            issues += text_issues(str(obj), label)
            if isinstance(obj, StreamObject):
                issues += text_issues(obj.get_data(), label)
        return issues
    except Exception:
        return [Issue(label, "PDF could not be fully inspected")]


def inspect_bytes(data: bytes, label: str, *, depth: int = 0,
                  budget: list[int] | None = None, format_name: str | None = None) -> list[Issue]:
    issues = text_issues(data, label)
    name = format_name or label
    if data.startswith(b"%PDF-") or name.lower().endswith(".pdf"):
        return issues + pdf_issues(data, label)
    is_zip = zipfile.is_zipfile(io.BytesIO(data))
    if not is_zip:
        if name.lower().endswith(".zip"):
            issues.append(Issue(label, "ZIP could not be inspected"))
        elif data.startswith((b"\x1f\x8b", b"7z\xbc\xaf\x27\x1c", b"Rar!", b"BZh", b"\xfd7zXZ")):
            issues.append(Issue(label, "unsupported compressed archive; inspect or remove before publishing"))
        return issues
    if depth >= MAX_DEPTH:
        return issues + [Issue(label, "ZIP nesting limit exceeded")]
    if budget is None:
        budget = [MAX_MEMBERS, MAX_EXPANDED]
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            for member in archive.infolist():
                budget[0] -= 1
                budget[1] -= member.file_size
                if min(budget) < 0:
                    return issues + [Issue(label, "ZIP inspection size or member limit exceeded")]
                # Report the outer relative name, never an unsafe archive member name.
                issues += text_issues(member.filename, label)
                if Path(member.filename).is_absolute() or PureWindowsPath(member.filename).is_absolute():
                    issues.append(Issue(label, "absolute ZIP member name"))
                if not member.is_dir():
                    issues += inspect_bytes(archive.read(member), label, depth=depth + 1,
                                            budget=budget, format_name=member.filename)
    except Exception:
        issues.append(Issue(label, "ZIP could not be fully inspected"))
    return issues


def public_files(root: Path) -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
        cwd=root, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    return sorted({Path(name.decode("utf-8", errors="surrogateescape"))
                   for name in result.stdout.split(b"\0") if name})


def scan_repository(root: Path) -> tuple[int, list[Issue]]:
    issues: list[Issue] = []
    count = 0
    for relative in public_files(root):
        path = root / relative
        label = relative.as_posix()
        if path.is_symlink():
            target = str(path.readlink())
            count += 1
            if Path(target).is_absolute() or PureWindowsPath(target).is_absolute():
                issues.append(Issue(label, "absolute symlink target"))
            issues += text_issues(target, label)
        elif path.is_file():
            count += 1
            try:
                issues += inspect_bytes(path.read_bytes(), label)
            except OSError:
                issues.append(Issue(label, "file could not be inspected"))
        elif path.exists():
            issues.append(Issue(label, "unsupported tracked file type"))
        # A deleted tracked file will not be part of the next committed tree.
    return count, issues


def scan_index(root: Path) -> tuple[int, list[Issue]]:
    """Inspect exact staged objects, including staged symlink targets."""
    result = subprocess.run(
        ["git", "ls-files", "--stage", "-z"], cwd=root, check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    entries = []
    issues: list[Issue] = []
    for raw in result.stdout.split(b"\0"):
        if not raw:
            continue
        metadata, name = raw.split(b"\t", 1)
        mode, oid, stage = metadata.split()
        label = name.decode("utf-8", errors="surrogateescape")
        if stage != b"0":
            issues.append(Issue(label, "unmerged index entry cannot be published"))
        elif mode not in (b"100644", b"100755", b"120000"):
            issues.append(Issue(label, "unsupported staged file type"))
        else:
            entries.append((mode, oid, label))
    if not entries:
        return 0, issues
    result = subprocess.run(
        ["git", "cat-file", "--batch"], cwd=root, check=True,
        input=b"".join(oid + b"\n" for _, oid, _ in entries),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    output = io.BytesIO(result.stdout)
    for mode, oid, label in entries:
        header = output.readline().split()
        if len(header) != 3 or header[0] != oid or header[1] != b"blob":
            issues.append(Issue(label, "staged object could not be inspected"))
            # A malformed batch response prevents reliable boundary parsing.
            return len(entries), issues
        size = int(header[2])
        data = output.read(size)
        if len(data) != size or output.read(1) != b"\n":
            issues.append(Issue(label, "staged object could not be inspected"))
            return len(entries), issues
        if mode == b"120000":
            target = data.decode("utf-8", errors="surrogateescape")
            if Path(target).is_absolute() or PureWindowsPath(target).is_absolute():
                issues.append(Issue(label, "absolute symlink target"))
            issues += text_issues(data, label)
        else:
            issues += inspect_bytes(data, label)
    return len(entries), issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--staged", action="store_true", help="inspect exact index blobs before committing")
    args = parser.parse_args()
    try:
        scanner = scan_index if args.staged else scan_repository
        count, issues = scanner(args.root.resolve())
    except (OSError, subprocess.CalledProcessError):
        print("Public path check failed: unable to enumerate Git files.", file=sys.stderr)
        return 2
    if issues:
        totals: dict[tuple[str, str], int] = {}
        for issue in issues:
            key = (issue.path, issue.reason)
            totals[key] = totals.get(key, 0) + issue.count
        for (path, reason), occurrences in sorted(totals.items()):
            print(f"{path}: {reason} ({occurrences})")
        print(f"Public path check failed: {len(totals)} findings in {count} files.")
        return 1
    print(f"Public path check passed: {count} files inspected.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
