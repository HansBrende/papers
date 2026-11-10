#!/usr/bin/env python3
"""Generate the memo's Lean index appendix and PaperAxioms.lean from its LaTeX sources.

Usage (from any directory):

    python3 tools/lean_index.py               # writes both files
    python3 tools/lean_index.py --index-only  # writes only paper/sections/leanindex.tex
    python3 tools/lean_index.py --check       # fails if any citation is unlocated or either file is stale

Collects every declaration named in a \\formal{file}{names} or \\partformal{file}{names}{...}
line of paper/sections/*.tex, and every name in a \\lean{name} reference, finds the module in
lean/ClassUniformMemo/ that declares each ClassUniformMemo declaration (warning when a status line
names another file; a status line may name several files, separated by commas), and writes
  * paper/sections/leanindex.tex: the declarations grouped by the Lean module that declares them,
    after a sentence listing the declarations of earlier and shared libraries cited in the text;
  * lean/PaperAxioms.lean: imports and one `#print axioms` per cited declaration (both ClassUniformMemo
    and the parent paper's SwapRigidity), unless --index-only is given.
Declarations without the prefix SwapRigidity are relative to the namespace ClassUniformMemo; files in
status lines are relative to lean/ClassUniformMemo/ (except status lines whose declarations all belong
to the parent paper's library).
"""
import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SECTIONS = ROOT / "paper" / "sections"
INDEX_PATH = SECTIONS / "leanindex.tex"
AXIOMS_PATH = ROOT / "lean" / "PaperAxioms.lean"
LEAN_DIR = ROOT / "lean" / "ClassUniformMemo"

FORMAL = re.compile(r"\\(?:formal|partformal)\{([^{}]+)\}\{([^{}]+)\}")
INLINE = re.compile(r"\\lean\{([^{}]+)\}")
CORE_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Earlier and shared libraries, by root namespace: how the index names them, and their citation key.
LIBRARIES = {
    "SwapRigidity": (r"the parent paper's library \texttt{SwapRigidity}", "SeventeenthPaper2026"),
}
FOREIGN = tuple(f"{k}." for k in LIBRARIES)

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([^\s(:{\[]+)"
)


def strip_lean_comments(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def declared() -> dict[str, str]:
    """Map each declaration of the library, relative to ClassUniformMemo, to its file."""
    where: dict[str, str] = {}
    for lean in sorted(LEAN_DIR.rglob("*.lean")):
        text = strip_lean_comments(lean.read_text())
        stack: list[tuple[str, str]] = []
        for line in text.splitlines():
            if m := re.match(r"^\s*namespace\s+(\S+)", line):
                stack.append(("ns", m.group(1)))
            elif re.match(r"^\s*(?:noncomputable\s+)?section\b", line):
                stack.append(("sec", ""))
            elif re.match(r"^\s*end\b", line):
                if stack:
                    stack.pop()
            elif m := DECL.match(line):
                ns = ".".join(n for kind, n in stack if kind == "ns")
                full = (ns + "." if ns else "") + m.group(1)
                if full.startswith("ClassUniformMemo."):
                    where[full[len("ClassUniformMemo."):]] = str(lean.relative_to(LEAN_DIR))
    return where


def collect() -> tuple[dict[str, set[str]], list[str], list[str]]:
    """Return status-line names by file, inline ClassUniformMemo names, and foreign names."""
    by_file: dict[str, set[str]] = {}
    inline: set[str] = set()
    foreign: set[str] = set()
    for tex in sorted(SECTIONS.glob("*.tex")):
        if tex.name == "leanindex.tex":
            continue
        text = tex.read_text()
        for file, names in FORMAL.findall(text):
            for n in (d.strip() for d in names.split(",") if d.strip()):
                if n in CORE_AXIOMS:
                    continue
                if n.startswith(FOREIGN):
                    foreign.add(n)
                else:
                    by_file.setdefault(file.strip(), set()).add(n)
        for n in (d.strip() for d in INLINE.findall(text)):
            if not n or n in CORE_AXIOMS:
                continue
            if n.startswith(FOREIGN):
                foreign.add(n)
            else:
                inline.add(n)
    listed = set().union(*by_file.values()) if by_file else set()
    return by_file, sorted(inline - listed), sorted(foreign)


def group(
    by_file: dict[str, set[str]], inline: list[str]
) -> tuple[dict[str, set[str]], list[str], list[str]]:
    """Group all cited ClassUniformMemo declarations by declaring file and collect warnings."""
    where = declared()
    grouped: dict[str, set[str]] = {}
    unknown: list[str] = []
    warnings: list[str] = []
    for file, names in sorted(by_file.items()):
        listed_files = [f.strip() for f in file.split(",")]
        for name in sorted(names):
            actual = where.get(name)
            if actual is None:
                unknown.append(name)
                continue
            if actual not in listed_files:
                warnings.append(f"warning: {name} is declared in {actual}, not in {file}")
            grouped.setdefault(actual, set()).add(name)
    for name in inline:
        actual = where.get(name)
        if actual is None:
            unknown.append(name)
        else:
            grouped.setdefault(actual, set()).add(name)
    for name in sorted(set(unknown)):
        warnings.append(f"warning: no declaration of {name} found in lean/ClassUniformMemo/")
    return grouped, sorted(set(unknown)), warnings


def foreign_sentence(foreign: list[str]) -> list[str]:
    """The sentence of the index that lists the cited declarations of other libraries."""
    parts = []
    for prefix, (desc, key) in LIBRARIES.items():
        names = [n for n in foreign if n.split(".")[0] == prefix]
        if names:
            cite = f"~\\cite{{{key}}}" if key else ""
            parts.append(", ".join(r"\lean{" + n + "}" for n in names) + f" in {desc}{cite}")
    if not parts:
        return []
    if len(parts) > 1:
        parts[-1] = "and " + parts[-1]
    return [
        r"{\raggedright The declarations of the parent paper's library named in the text are checked "
        r"both in that library and in \texttt{PaperAxioms.lean}: "
        + ("; " if len(parts) > 2 else " ").join(parts)
        + r".\par}"
    ]


def module(file: str) -> str:
    return "ClassUniformMemo." + file.removesuffix(".lean").replace("/", ".")


def tex_escape(name: str) -> str:
    return name.replace("_", r"\_")


def render_index(by_file: dict[str, set[str]], unknown: list[str], foreign: list[str]) -> str:
    lines = [
        r"\section{Index of Lean declarations}\label{app:leanindex}",
        "",
        "Every declaration of this memo's library cited in the text, grouped by the Lean module that contains it, relative to the namespace",
        r"\texttt{ClassUniformMemo}. All of them depend only on the axioms \texttt{propext}, \texttt{Classical.choice} and",
        r"\texttt{Quot.sound} (\cref{app:verification}).",
        *foreign_sentence(foreign),
        "",
    ]
    for file in sorted(by_file, key=module):
        decls = sorted(by_file[file])
        lines.append(r"\paragraph{\texttt{" + tex_escape(module(file)) + "}}")
        lines.append(
            r"{\small\raggedright "
            + ", ".join(r"\texttt{" + tex_escape(d) + "}" for d in decls)
            + r".\par}"
        )
        lines.append("")
    if unknown:
        lines.append(r"\paragraph{Not located by the index script}")
        lines.append(
            r"{\small\raggedright "
            + ", ".join(r"\texttt{" + tex_escape(d) + "}" for d in unknown)
            + r".\par}"
        )
        lines.append("")
    return "\n".join(lines)


def render_axioms(by_file: dict[str, set[str]], unknown: list[str], foreign: list[str]) -> str:
    imports = sorted({module(f) for f in by_file})
    out = [f"import {m}" for m in imports]
    out += [
        "",
        "/-! Generated by tools/lean_index.py from the memo's LaTeX sources: the axioms of every",
        "declaration cited in the memo. Each should report at most `propext`, `Classical.choice`",
        "and `Quot.sound`. -/",
        "",
    ]
    for file in sorted(by_file, key=module):
        out.append(f"-- {file}")
        for d in sorted(by_file[file]):
            out.append(f"#print axioms ClassUniformMemo.{d}")
    if foreign:
        out.append("-- the parent paper's library")
        for f in sorted(foreign):
            out.append(f"#print axioms {f}")
    if unknown:
        out.append("-- not located by the index script")
        for d in unknown:
            out.append(f"#print axioms ClassUniformMemo.{d}")
    return "\n".join(out) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--index-only",
        action="store_true",
        help="write only paper/sections/leanindex.tex, not lean/PaperAxioms.lean",
    )
    ap.add_argument(
        "--check",
        action="store_true",
        help="verify that all cited names resolve and that generated files are up to date",
    )
    args = ap.parse_args()

    by_file, inline, foreign = collect()
    by_file, unknown, warnings = group(by_file, inline)
    for w in warnings:
        print(w, file=sys.stderr if args.check else sys.stdout)

    idx_text = render_index(by_file, unknown, foreign)
    ax_text = render_axioms(by_file, unknown, foreign)

    if args.check:
        failed = bool(warnings or unknown)
        if not INDEX_PATH.exists() or INDEX_PATH.read_text() != idx_text:
            print("error: paper/sections/leanindex.tex is out of date", file=sys.stderr)
            failed = True
        if not args.index_only and (not AXIOMS_PATH.exists() or AXIOMS_PATH.read_text() != ax_text):
            print("error: lean/PaperAxioms.lean is out of date", file=sys.stderr)
            failed = True
        if failed:
            sys.exit(1)
        total = sum(len(v) for v in by_file.values())
        print(
            f"checked {total} ClassUniformMemo declarations in {len(by_file)} modules "
            f"(+{len(foreign)} from the parent paper's library)"
        )
        return

    INDEX_PATH.write_text(idx_text)
    if not args.index_only:
        AXIOMS_PATH.write_text(ax_text)
    total = sum(len(v) for v in by_file.values()) + len(unknown)
    print(
        f"{total} declarations in {len(by_file)} modules"
        + (f" (+{len(foreign)} from the parent paper's library)" if foreign else "")
        + (" (index only)" if args.index_only else "")
    )


if __name__ == "__main__":
    main()
