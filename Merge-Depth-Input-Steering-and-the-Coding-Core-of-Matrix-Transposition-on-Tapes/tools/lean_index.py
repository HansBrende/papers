#!/usr/bin/env python3
"""Generate the Lean index appendix and PaperAxioms.lean from the paper's LaTeX sources.

Usage, from any directory:

    python3 tools/lean_index.py           # regenerate both files
    python3 tools/lean_index.py --check   # fail if either file is stale; write nothing

The script reads paper/main.tex and the section files it inputs, recursively, and collects
  * every declaration in a \\formal{file}{names} or \\partformal{file}{names}{gap} line,
    where file is relative to lean/ (for example MergeDepth/Steps.lean) and the
    names are fully qualified Lean names;
  * every name in a \\lean{name} reference in the text.
It writes
  * paper/sections/leanindex.tex: the declarations grouped by Lean module;
  * lean/PaperAxioms.lean: `import MergeDepth` and one `#print axioms` per declaration, except for the names
    from the tenth paper's library, which this library does not import (they are checked there).

It stops with an error unless
  * every theorem, lemma, corollary and proposition has exactly one status line, a formal
    status line is followed by an outline, and \\notformalized by an informalproof;
  * every file in a status line exists and declares each declaration listed with it;
  * every \\lean name is declared in this paper's library or in the eighth or tenth paper's library.
Declarations are found by a namespace-aware scan of the Lean sources. The script does
not run Lean and does not check proofs.
"""
import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # the paper directory
PAPER = ROOT / "paper"
SECTIONS = PAPER / "sections"
INDEX = SECTIONS / "leanindex.tex"
LEAN = ROOT / "lean"
LIBRARY = "MergeDepth"
AXIOMS = LEAN / "PaperAxioms.lean"
# Libraries whose declarations may be named in the text, with the label used in the index.
LIBRARIES = [
    (LEAN / LIBRARY, "this paper's library"),
    (ROOT.parent / "Matrix-Transposition-and-the-Tape-Coding-Conjecture" / "lean" / "Transpose",
     "the first paper's library"),
    (ROOT.parent / "Bounded-Nesting-and-Depth-Reduction-for-Matrix-Transposition-on-Tapes" / "lean"
     / "BoundedNesting", "the eighth paper's library"),
    (ROOT.parent / "Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes" / "lean"
     / "MotionDepthCodes", "the fourth paper's library"),
    (ROOT.parent / "Directed-Recovery-Structures-in-Tape-Computations" / "lean" / "DirectedRecovery",
     "the fifth paper's library"),
    (ROOT.parent / "Source-Covers-and-Barriers-to-Tape-Transposition" / "lean" / "SourceCovers",
     "the ninth paper's library"),
    (ROOT.parent / "Directed-Reciprocity-and-Deep-Nesting-Bounds-for-Matrix-Transposition-on-Tapes" / "lean"
     / "DirectedReciprocity", "the tenth paper's library"),
]

# Libraries that this paper's library does not import: their names are indexed but not axiom-checked here.
EXTERNAL = {"the tenth paper's library"}

FORMAL = re.compile(r"\\(formal|partformal)\{([^{}]+)\}\{([^{}]+)\}")
INLINE = re.compile(r"\\lean\{([^{}]+)\}")
STATUS = re.compile(r"\\(formal|partformal|notformalized|cited)(?![A-Za-z])")
RESULT = re.compile(
    r"\\begin\{(theorem|lemma|corollary|proposition|definition)\}(.*?)\\end\{\1\}", re.DOTALL)
PROOF = {"formal": "outline", "partformal": "outline", "notformalized": "informalproof"}
DECL = re.compile(
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)\s+"
    r"([^\s:({\[⦃]+)")
PREFIX = re.compile(r"(?:open|include|omit)\b.*?\bin\s+(?=\S)")


def tex_sources():
    """The section files input by main.tex, recursively, without LaTeX comments."""
    out = []

    def visit(source):
        for name in re.findall(r"\\input\{(sections/[^}]+)\}", source):
            path = PAPER / (name.removesuffix(".tex") + ".tex")
            if path == INDEX:
                continue
            text = "\n".join(re.sub(r"(?<!\\)%.*", "", line) for line in path.read_text().splitlines())
            out.append((path, text))
            visit(text)

    visit((PAPER / "main.tex").read_text())
    return out


def strip_lean_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            out.append("\n" if text[i] == "\n" else "")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def lean_declarations(path):
    """Fully qualified names declared in one Lean file."""
    names, scopes = set(), []
    for raw in strip_lean_comments(path.read_text()).splitlines():
        line = raw.strip()
        while PREFIX.match(line):
            line = PREFIX.sub("", line, count=1)
        if m := re.fullmatch(r"namespace\s+(\S+)", line):
            scopes.append(m.group(1).split("."))
        elif re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+\S+)?", line):
            scopes.append([])
        elif re.fullmatch(r"end(?:\s+\S+)?", line):
            if scopes:
                scopes.pop()
        elif m := DECL.match(line):
            names.add(".".join([p for scope in scopes for p in scope] + [m.group(1)]))
    return names


def module(file):
    return file.removesuffix(".lean").replace("/", ".")


def collect(errors):
    by_file, inline = {}, set()
    for path, text in tex_sources():
        for match in RESULT.finditer(text):
            kind, body = match.groups()
            label = re.search(r"\\label\{([^}]+)\}", body)
            where = label.group(1) if label else f"{path.name}:{text.count(chr(10), 0, match.start()) + 1}"
            statuses = STATUS.findall(body)
            if kind == "definition":
                if any(s != "formal" for s in statuses) or len(statuses) > 1:
                    errors.append(f"{where}: a definition takes at most one \\formal line")
                continue
            if len(statuses) != 1:
                errors.append(f"{where}: expected one status line, found {len(statuses)}")
                continue
            need = PROOF.get(statuses[0])
            if need and not re.match(r"\s*\\begin\{" + need + r"\}", text[match.end():]):
                errors.append(f"{where}: \\{statuses[0]} must be followed by an {need} environment")
        for _, file, names in FORMAL.findall(text):
            file = file.strip()
            decls = [n.strip() for n in names.split(",") if n.strip()]
            if Path(file).is_absolute() or ".." in Path(file).parts or not (LEAN / file).is_file():
                errors.append(f"{path.name}: no Lean file lean/{file}")
                continue
            declared = lean_declarations(LEAN / file)
            for d in decls:
                if d not in declared:
                    errors.append(f"{path.name}: {d} is not declared in lean/{file}")
            by_file.setdefault(file, set()).update(decls)
        inline.update(n.strip() for n in INLINE.findall(text))
    listed = set().union(*by_file.values()) if by_file else set()
    inline -= listed
    owners = {}
    for directory, label in LIBRARIES:
        if not directory.is_dir():
            continue
        for path in sorted(directory.rglob("*.lean")):
            for d in lean_declarations(path) & inline:
                owners.setdefault(d, label)
    for d in sorted(inline - owners.keys()):
        errors.append(f"\\lean{{{d}}}: not declared in any scanned library")
    return by_file, owners


def render(by_file, owners):
    tex = [
        "% Generated by tools/lean_index.py from the status lines; do not edit by hand.",
        r"\section{Index of Lean declarations}\label{sec:leanindex}", "",
        r"The status lines of the paper cite the following declarations, listed by Lean module",
        r"with their fully qualified names. Module files are relative to the paper's",
        r"\path{lean/} directory. The axiom checks in \path{lean/PaperAxioms.lean} are generated",
        r"from the same sources.", "",
    ]
    for file in sorted(by_file, key=module):
        tex.append(r"\paragraph{\texttt{" + module(file) + "}}")
        tex.append(r"{\small\raggedright\leanlist{" + ",".join(sorted(by_file[file])) + r"}.\par}")
        tex.append("")
    if owners:
        tex.append(r"\paragraph{Also named in the text}")
        for _, label in LIBRARIES:
            names = sorted(d for d, owner in owners.items() if owner == label)
            if names:
                checked = " (checked there; this library does not import it)" if label in EXTERNAL else ""
                tex.append(r"{\small\raggedright From " + label + checked + r": \leanlist{"
                           + ",".join(names) + r"}.\par}")
        tex.append("")
    axioms = [
        f"import {LIBRARY}", "",
        "/-! Generated by tools/lean_index.py from the paper's LaTeX sources: one `#print axioms`",
        "for every declaration that the paper cites. Each should report at most `propext`,",
        "`Classical.choice` and `Quot.sound`. -/", "",
    ]
    for file in sorted(by_file, key=module):
        axioms.append(f"-- {file}")
        axioms.extend(f"#print axioms {d}" for d in sorted(by_file[file]))
    local = sorted(d for d, owner in owners.items() if owner not in EXTERNAL)
    if local:
        axioms.append("-- named in the text")
        axioms.extend(f"#print axioms {d}" for d in local)
    return {INDEX: "\n".join(tex), AXIOMS: "\n".join(axioms).rstrip() + "\n"}


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="fail if a generated file is stale")
    args = parser.parse_args()
    errors = []
    by_file, owners = collect(errors)
    if errors:
        sys.exit("lean_index.py: " + "\n  ".join(["errors:"] + errors))
    stale = []
    for path, content in render(by_file, owners).items():
        if args.check:
            if not path.exists() or path.read_text() != content:
                stale.append(str(path.relative_to(ROOT)))
        else:
            path.write_text(content)
    if stale:
        sys.exit("lean_index.py: stale generated files: " + ", ".join(stale))
    total = sum(len(v) for v in by_file.values())
    print(f"{'Checked' if args.check else 'Generated'}: {total} declarations in {len(by_file)} "
          f"modules, {len(owners)} more named in the text; axiom commands not executed.")


if __name__ == "__main__":
    main()
