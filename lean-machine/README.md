# lean-machine

Shared Lean machinery for the papers in this repository: results that more than one theorem could
use, and external Lean code we have pulled in. Results specific to one paper stay in that paper's
`lean/` library.

## What goes here

- General lemmas and constructions that are not tied to one paper.
- External Lean code that we reuse, ported to our Lean and Mathlib versions.
- Nothing with `sorry`, `admit`, `native_decide` or new axioms. Every exported theorem depends at
  most on `propext`, `Classical.choice` and `Quot.sound`.

## Layout

- One Lake package, `leanMachine`, with the library `LeanMachine`. It uses Lean and Mathlib v4.34.1,
  the same versions as the papers.
- A single, relatively short proof goes in one file, `LeanMachine/<Name>.lean`.
- A larger topic, or one that mixes external code with our own additions, gets a folder,
  `LeanMachine/<Topic>/`, with its own `README.md`.
- `LeanMachine.lean` imports every module. `Axioms.lean` prints the axioms of every exported
  theorem. Add new modules and theorems to both.

## Contents

| Path | Contents | Origin |
|---|---|---|
| [`LeanMachine/TutteBerge/`](LeanMachine/TutteBerge/) | Berge's augmenting-path theorem, the Tutte–Berge formula, the matching number, and the components of G − U as barrier blocks | external ([jtraverso/berge-matching](https://github.com/jtraverso/berge-matching) at `f01d042`), plus our additions |
| [`LeanMachine/RankCertificate.lean`](LeanMachine/RankCertificate.lean) | Arbitrary-field finite-dimensional rank identity from an intertwining defect | this repository |

## External code

Each external file keeps its copyright header and gets a provenance comment below it. Each folder
that contains external code has a README. Both record:
- the source URL, the commit, the original path, and the SHA-256 of the original file;
- the licence, which must be Apache 2.0 or compatible, and the copyright holder;
- every change made, however small.

Before an external file is built here:
- fetch it at a pinned commit;
- read all of it;
- check that it runs no code at build time: no `#eval`, `run_cmd`, `initialize`, custom syntax or
  elaborators, `@[extern]`, `implemented_by` or I/O.

Keep changes to external files minimal, and put our own additions in separate files.

## Using it from a paper

In the paper's `lean/lakefile.toml`:

```toml
[[require]]
name = "leanMachine"
path = "../../lean-machine"
```

Readers then need the whole repository with its sibling directories in place, as for the papers'
dependencies on each other.

## Building and checking

In this directory:

```bash
lake exe cache get
```

```bash
lake build
```

```bash
lake env lean Axioms.lean
```

`.lake/` is not committed. Locally, `.lake/packages` may be a symbolic link to a sibling paper's
packages at the same Mathlib revision, which avoids a second Mathlib download.

## License

Apache 2.0 ([`LICENSE`](LICENSE)). External files keep the copyright notices of their authors.
