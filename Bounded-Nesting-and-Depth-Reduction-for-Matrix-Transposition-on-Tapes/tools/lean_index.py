#!/usr/bin/env python3
"""Generate the Lean index appendix and PaperAxioms.lean from the LaTeX sources.

Usage (from the paper directory, i.e. the parent of paper/ and lean/):

    python3 tools/lean_index.py               # writes both files
    python3 tools/lean_index.py --index-only  # writes only paper/sections/leanindex.tex

Collects every declaration named in a \\formal{file}{names} or \\partformal{file}{names}{...}
line of paper/sections/*.tex, and every name in a \\lean{name} reference to this library, finds the
module that declares each of them by scanning lean/BoundedNesting/ (warning when a status line names another
file), and writes
  * paper/sections/leanindex.tex: the declarations grouped by the Lean module that declares them, after a
    sentence listing the names of other libraries cited in \\lean{...} (those starting with a prefix in
    LIBRARIES), which are checked in their own libraries;
  * lean/PaperAxioms.lean: imports and one `#print axioms` per declaration (not with --index-only).
Declarations are relative to the namespace BoundedNesting; files are relative to
lean/BoundedNesting/. Names that the scan does not find are listed separately, with a warning.
"""
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SECTIONS = ROOT / "paper" / "sections"
FORMAL = re.compile(r"\\(?:formal|partformal)\{([^{}]+)\}\{([^{}]+)\}")
INLINE = re.compile(r"\\lean\{([^{}]+)\}")
# Other libraries, by namespace: how the index names them, and their citation key (None: no citation).
# lean-machine's Tutte--Berge formula lives in the namespace SimpleGraph.
LIBRARIES = {
    "Transpose": ("the first paper's library", "FirstPaper2026"),
    "MotionDepthCodes": ("the fourth paper's library", "FourthPaper2026"),
    "HalfRate": ("the seventh paper's library", "SeventhPaper2026"),
    "SimpleGraph": (r"the shared library \texttt{lean-machine}", None),
}
FOREIGN = tuple(LIBRARIES)
LEAN_DIR = ROOT / "lean" / "BoundedNesting"
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([^\s(:{\[]+)")


def declared():
    """Map each declaration of the library, relative to BoundedNesting, to its file."""
    where = {}
    for lean in sorted(LEAN_DIR.rglob("*.lean")):
        text = re.sub(r"/-.*?-/", "", lean.read_text(), flags=re.S)
        stack = []
        for line in text.splitlines():
            if m := re.match(r"^\s*namespace\s+(\S+)", line):
                stack.append(("ns", m.group(1)))
            elif re.match(r"^\s*section\b", line):
                stack.append(("sec", ""))
            elif re.match(r"^\s*end\b", line):
                if stack:
                    stack.pop()
            elif m := DECL.match(line):
                ns = ".".join(n for kind, n in stack if kind == "ns")
                full = (ns + "." if ns else "") + m.group(1)
                if full.startswith("BoundedNesting."):
                    where[full[len("BoundedNesting."):]] = str(lean.relative_to(LEAN_DIR))
    return where


def group(by_file, inline):
    """Group all cited declarations by the file that declares them."""
    where = declared()
    grouped, unknown = {}, []
    for file, names in by_file.items():
        for name in names:
            actual = where.get(name)
            if actual is None:
                unknown.append(name)
                continue
            if actual != file:
                print(f"warning: {name} is declared in {actual}, not in {file}")
            grouped.setdefault(actual, set()).add(name)
    for name in inline:
        actual = where.get(name)
        if actual is None:
            unknown.append(name)
        else:
            grouped.setdefault(actual, set()).add(name)
    for name in sorted(unknown):
        print(f"warning: no declaration of {name} found in lean/BoundedNesting/")
    return grouped, sorted(unknown)


def collect():
    """Return the status-line names by file, the other inline names of this library, and the foreign names."""
    by_file, inline, foreign = {}, set(), set()
    for tex in sorted(SECTIONS.glob("*.tex")):
        if tex.name == "leanindex.tex":
            continue
        text = tex.read_text()
        for file, names in FORMAL.findall(text):
            decls = [n.strip() for n in names.split(",") if n.strip()]
            by_file.setdefault(file.strip(), set()).update(decls)
        for n in (n.strip() for n in INLINE.findall(text)):
            (foreign if n.startswith(FOREIGN) else inline).add(n)
    listed = set().union(*by_file.values()) if by_file else set()
    return by_file, sorted(inline - listed), sorted(foreign)


def foreign_sentence(foreign):
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
    return [r"{\raggedright The declarations of other libraries named in the text are checked in those libraries: "
            + ("; " if len(parts) > 2 else " ").join(parts) + r".\par}"]


def module(file):
    return "BoundedNesting." + file.removesuffix(".lean").replace("/", ".")


def tex_escape(name):
    return name.replace("_", r"\_")


def write_index(by_file, inline, foreign):
    lines = [
        r"\section{Index of Lean declarations}\label{app:index}",
        "",
        "Every declaration of this paper's library cited in the text, grouped by the Lean module that contains it, relative to the namespace",
        r"\texttt{BoundedNesting}. All of them depend only on the axioms \texttt{propext}, \texttt{Classical.choice} and",
        r"\texttt{Quot.sound} (\cref{app:verify}).",
        *foreign_sentence(foreign),
        "",
    ]
    for file in sorted(by_file, key=module):
        decls = sorted(by_file[file])
        lines.append(r"\paragraph{\texttt{" + tex_escape(module(file)) + "}}")
        lines.append(r"{\small\raggedright " + ", ".join(r"\texttt{" + tex_escape(d) + "}" for d in decls) + r".\par}")
        lines.append("")
    if inline:
        lines.append(r"\paragraph{Not located by the index script}")
        lines.append(r"{\small\raggedright " + ", ".join(r"\texttt{" + tex_escape(d) + "}" for d in inline) + r".\par}")
        lines.append("")
    (SECTIONS / "leanindex.tex").write_text("\n".join(lines))


def write_axioms(by_file, inline):
    imports = sorted({module(f) for f in by_file})
    out = [f"import {m}" for m in imports]
    out += ["", "/-! Generated by tools/lean_index.py from the paper's LaTeX sources: the axioms of every",
            "declaration cited in the paper. Each should report at most `propext`, `Classical.choice`",
            "and `Quot.sound`. -/", ""]
    for file in sorted(by_file, key=module):
        out.append(f"-- {file}")
        for d in sorted(by_file[file]):
            out.append(f"#print axioms BoundedNesting.{d}")
    if inline:
        out.append("-- not located by the index script")
        for d in inline:
            out.append(f"#print axioms BoundedNesting.{d}")
    (ROOT / "lean" / "PaperAxioms.lean").write_text("\n".join(out) + "\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--index-only", action="store_true",
                    help="write only paper/sections/leanindex.tex, not lean/PaperAxioms.lean")
    args = ap.parse_args()
    by_file, inline, foreign = collect()
    by_file, inline = group(by_file, inline)
    write_index(by_file, inline, foreign)
    if not args.index_only:
        write_axioms(by_file, inline)
    total = sum(len(v) for v in by_file.values()) + len(inline)
    print(f"{total} declarations in {len(by_file)} modules"
          + (" (index only)" if args.index_only else ""))


if __name__ == "__main__":
    main()
