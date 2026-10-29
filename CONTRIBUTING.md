# Contributing

Use each paper's README for its build and verification commands. Keep Lean
toolchain and dependency pins unchanged unless deliberately updating them.

## Writing a paper

These conventions come from the first paper, *Matrix Transposition and the
Tape Coding Conjecture*, and apply to every new paper here. The fourth paper,
*Curved Motion, Depth Reduction, and Storage Codes for Matrix Transposition on
Tapes*, is a complete example: start from its `paper/macros.tex`,
`paper/main.tex` and `tools/lean_index.py`.

### Layout

- **Directory.** One directory per paper at the repository root, named after
  the title with words joined by hyphens, for example
  `Bit-and-Word-Transposition-on-Tapes`.
- **Contents of the paper directory:**
  - `README.md` (see below).
  - `paper/`:
    - `main.tex`, `macros.tex` and `references.bib`;
    - `sections/`, one file per section plus `abstract.tex`;
    - the compiled `main.pdf`;
    - `LICENSE`: CC BY 4.0, naming the paper's title.
  - `lean/`:
    - `lakefile.toml`, `lean-toolchain` and `lake-manifest.json`;
    - the library directory, plus a root module that imports every public
      module;
    - `PaperAxioms.lean`;
    - `LICENSE`: Apache 2.0.
  - `tools/` (optional): scripts that regenerate generated material, such as
    certificates and indices. Document each script's usage at its top.
  - `verification/` (optional): fuller audit tooling, as in the second and third
    papers (declaration maps, receipts). It is not required.
- **Root README.** Add the paper to the table in the root `README.md`: title
  link, authors, month and year, contents.

### Lean

- **Pins.** Use the Lean and Mathlib versions of the existing papers (currently
  v4.34.1).
- **Reuse.** Build on earlier libraries instead of copying them: require the
  earlier paper's package through a relative path, for example
  ```toml
  [[require]]
  name = "transposeFollowup"
  path = "../../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/lean"
  ```
  Readers then need the whole repository, with sibling directories in place;
  the paper's README must say so.
- **Shared machinery.** [`lean-machine/`](lean-machine/) at the repository root holds Lean code that more
  than one paper can use, and external Lean code we have ported. A paper requires it like an earlier
  paper's library (`path = "../../lean-machine"`). Put general lemmas there rather than in a paper's
  library. Its README sets the rules for external code: a compatible licence, a pinned commit, a full
  read before building, and a record of the source and of every change.
- **Packages.** `.lake/` is ignored. Locally, `.lake/packages` may be a symbolic
  link to a sibling's packages at the same revisions, which avoids a second
  Mathlib download. It is a local convenience and is never committed.
- **Axioms.** Use Lean's standard axioms only.
  - No `sorry`, `admit`, `native_decide`, new `axiom`s, `unsafe` code, or
    metaprogramming that bypasses the kernel.
  - Every declaration cited in a paper depends at most on `propext`,
    `Classical.choice` and `Quot.sound`.
- **`PaperAxioms.lean`.** It runs `#print axioms` on every declaration the paper
  cites. Generate it from the LaTeX sources, together with the index appendix,
  so that the two cannot drift apart from the paper. The fourth paper's
  `tools/lean_index.py` does this.
- **Frozen files.** Never modify the first paper's frozen files
  `Transpose/Statement.lean` and `Verify.lean`; their hashes are in
  `FROZEN.sha256`.
- **Generated proofs.** Machine-generated proofs, such as linear-programming
  certificates, must be checked by Lean itself, for example by
  `linear_combination` with exact rational coefficients. Keep the generator in
  `tools/`; the Lean files are the record.
- **Heartbeats.** Raising `maxHeartbeats` for a long but routine computation is
  acceptable. Say so in the verification appendix.

### The manuscript

- **Front matter:**
  - the title;
  - the authors, as `Hans Brende \and <model> (<company>)`;
  - the month and year;
  - the abstract;
  - a short **Contributions** paragraph saying who chose the problem and
    directed the research, and who developed the mathematics, the Lean and the
    text;
  - a table of contents.
- **Section order:**
  - the introduction: the problem; the results; how to read the paper and its
    formal proofs; related work; organization;
  - the model or preliminaries;
  - the results;
  - a construction side: what a linear-time machine would need, and the
    mechanisms that fail;
  - open problems or a roadmap;
  - appendices: the index of Lean declarations, and how to build and verify.
- **Formal status.** Every numbered theorem, lemma, corollary and proposition
  states its status with the macros of `macros.tex`. A numbered definition
  carries `\formal` when it has a Lean counterpart and no status line
  otherwise. The macros:
  - `\formal{file}{declarations}` for a formalized result. It is followed by an
    *Outline of the formal proof* (`outline` environment), a faithful guide
    that is not itself the proof. The Lean statement is authoritative; the
    English may simplify only in harmless ways.
  - `\partformal{file}{declarations}{gap}` when the Lean covers everything but a
    named part, which the text proves or cites.
  - `\notformalized` for a result with no formal counterpart. It is followed by
    a complete proof (`informalproof` environment).
  - `\cited{...}` for a result of an earlier paper of the series that is used
    without proof. The line says where it is proved and whether it is
    Lean-verified there.
- **Not numbered results.**
  - A claim that has only a proof sketch is not a numbered result: state it in a
    remark beginning "Proof sketch only:", or in prose.
  - Numerical observations appear only in remarks labelled as numerical, and are
    never used in proofs.
  - Heuristics are labelled as heuristics.
- **Say what is unformalized.** The abstract and the introduction say plainly
  which results are not formalized.
- **Relevance.** For every theorem, make clear why it is there: what it
  requires of a construction, or what it leaves for an impossibility proof.
  A sentence wherever it fits best is enough; no fixed heading or separate
  paragraph is required. The paper ends with the precise open problems that
  would decide the question.
- **Self-contained.** Rely only on the published literature and on earlier
  papers of this series. Never cite internal notes, private files, agent runs or
  internal result numbers.
- **Notation.** Keep the series' notation: $d$ for the side length,
  $b(d)=\max(1,\lceil\log_2 d\rceil)$, $L=d^2b(d)$, and (T) for linear-time
  transposition.
- **Names and labels.**
  - Named theorems use letters (Theorem P, Theorem M*, Theorem C).
  - Labels carry the prefixes `thm:`, `lem:`, `cor:`, `prop:`, `def:`, `conj:`,
    `rem:`, `prob:`, `eq:` and `sec:`; refer to them with `\cref`.
- **Citations.**
  - Check every bibliographic entry against its source: title, authors, venue,
    year, and the numbering of any cited result. Never guess metadata.
  - Cite earlier papers of the series at a pinned revision (see the
    `FirstPaper2026` entries), and say when a cited result is Lean-verified
    there.
  - Keep novelty claims modest, after a literature search that includes theses.
- **Prose.** Precise, concise and plain. Define every symbol before using it.

### The README

Follow the first paper's README:
- title, authors and date;
- links to `paper/` and `lean/`, with their licenses;
- *The question*;
- *What is proved*: the formalized results, with the axiom statement, then the
  results that are proved in the paper but not formalized;
- *What is open*;
- *Building and verifying*: `lake exe cache get`, `lake build`,
  `lake env lean PaperAxioms.lean`, and how to regenerate any generated files.

### Before publishing

- **Audit the formalization.** Simplify, delete unused proof code, and check that
  every statement in the paper is at least as strong as claimed. Report any
  weakening, with its reason and its consequences for the paper.
- **Independent reviews.** Run at least two:
  - one compares every English statement with its Lean declaration;
  - one checks the unformalized proofs and the citations.
- **Build the PDF** with `latexmk -pdf main.tex` in `paper/`, with no undefined
  references or citations, and commit it.
- **Path checks.** Run the checks in the next section.
- **One commit.** Add a new paper, its Lean library and its README in a single
  commit, after the reviews.

## Portable files

Keep current sources and reproduction tools portable: use relative paths and
discover tools at runtime. Keep personal filesystem paths, private workspace
references, raw local logs, and backups outside this repository or in ignored
output. Adding an ignore rule does not untrack an already committed file.

Before publishing, run these checks from the repository root with `pypdf`
installed; run the second after staging changes:

```sh
python3 tools/check_public_paths.py
python3 tools/check_public_paths.py --staged
```

The checks cover publishable files, including PDF contents and archives; the
second checks the exact staged versions. This policy applies to current files
and future commits; existing Git history is retained.

## Historical verification records

The follow-up's historical records are sanitized views, not fresh verification
runs. Embedded historical hashes identify original artifacts, not edited public
copies. The [normalization manifest](Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/verification/publication-path-normalization.json)
links those views to privately preserved originals. Paths in these records are
relative to the follow-up paper root; `external/` labels denote private inputs,
not public build dependencies. Use the documented current verification commands;
historical scripts may depend on private inputs.
