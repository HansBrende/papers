# Tape Transposition and the Matrix Coding Conjecture

Hans Brende, Claude Fable 5.2 (Anthropic) and GPT-6 Astra (OpenAI) · November 2026

**Draft under review.** The proof sections and Lean package are supplied.
Independent statement and written-proof reviews have supplied corrections, now incorporated.
Final author review and a deeper related-work pass remain; the coding conjecture is open.

[Paper PDF](paper/main.pdf) · [LaTeX](paper/) (CC BY 4.0) · [Lean](lean/) (Apache 2.0)

## The question

Can a multitape Turing machine transpose a d × d matrix of ⌈log₂ d⌉-bit entries
in linear time? A *whole-row code* is a set of arrays in which each column is a
function of at most w complete rows. The **Matrix Coding Conjecture** asks for
a rate bound below one independent of w, with w fixed as d grows. (Mittal and Raz
conjectured such a bound at windows proportional to d; that version is false.) This paper proves that conjecture
implies the robust Tape Coding Conjecture and excludes adaptive linear-time
transposers as well as oblivious ones.

## What is proved

The maintained Lean modules, using only the standard axioms, include:

- [The common-deficit implication](lean/MatrixCoding/WholeRowTCC.lean) and the
  [weaker sufficient target](lean/MatrixCoding/Wall.lean), with their conditional
  conclusions against the first paper's frozen transposition proposition.
- [Row spread](lean/MatrixCoding/WindowSpread.lean) and
  [its coding transfer](lean/MatrixCoding/RowSpreadCrux.lean).
- [The general degree baseline](lean/MatrixCoding/KnownBounds.lean):
  `|C|^(w+1) ≤ q^(wd(d+1))`, the window-one bound, and the limiting rate
  `w/(w+1)` uniformly over finite alphabets. The sharper window-two bound
  remains the written multigraph argument in Paper 17.
- [The symmetric, reflexive, two-sided normal form](lean/MatrixCoding/NormalizedRateTransfer.lean).
- [Exact acyclic-set values](lean/MatrixCoding/WholeRowAcyclic.lean),
  [the assigned-rule bound](lean/MatrixCoding/ClosureBarriers.lean), and
  [the rectangle barrier](lean/MatrixCoding/RectangleBarrier.lean).
- [Fano's exact Shannon value](lean/MatrixCoding/FanoAttainment.lean),
  [the optimal three-lane code](lean/MatrixCoding/FanoLaneCode.lean) over every finite abelian base alphabet,
  [the grid upper certificate](lean/MatrixCoding/GridFull.lean), and
  [the conditional gap for mixing lifts](lean/MatrixCoding/FanoLift.lean).
- [Parities over induced matchings](lean/MatrixCoding/InducedMatchings.lean): half rate at fixed
  window, with the stronger range `w = o(d^(1/3))`, arbitrary finite abelian alphabets and
  prescribed sums; the finite counting proof is in the shared library.
- [Graph-to-code conversion](lean/MatrixCoding/GraphMatchingCode.lean): an edge partition
  into induced matchings gives exact-size whole-row codes over finite abelian groups;
  over any field the zero-sum code has codimension equal to the number of parts.
- The shared library's [pairing](../lean-machine/LeanMachine/WholeRow/Pairing.lean)
  and [parity](../lean-machine/LeanMachine/WholeRow/ParityTrimming.lean)
  bounds, included by this package's root module.

Complete written proofs, not Lean: existence of bounded-window mixing relations
and growing-girth Fano lifts; and
the exclusion of oblivious runs fragmented by a cheap cut into components with
few outputs. The exact finite certificate does not assert grid attainment or
attainment on the sparse lifts. The graph families used in the growing-window
remark remain cited existence results.

## What remains open

The Matrix Coding Conjecture and its weak form. The common form implies the
weak form; strict logical separation is not proved. There is no converse from
the existence of high-rate array codes to a machine. No unconditional solution
of the frozen transposition problem is supplied.

To work on the precise weak target, import `MatrixCoding.Wall` and prove or
refute `LeanBacklog.Wall.Conjecture`. The name is retained for compatibility;
the maintained source is in this paper. No admitted theorem is used.

## Building and verifying

Clone the whole repository, retaining sibling paper directories. Lean 4.34.1
and the pinned Mathlib revision are recorded in `lean/`; do not update the pins.

```sh
cd lean
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

From this paper's directory:

```sh
python3 tools/lean_index.py --check
python3 tools/fano-shannon/generate_lean.py --check
python3 tools/grid-shannon/generate_lean.py --check
python3 tools/fano-shannon/verify_certificate.py
python3 tools/grid-shannon/verify_certificate.py
cd paper
latexmk -pdf main.tex
```

Python 3.10 or later is needed for the certificate checkers. No LP solver is
needed. Omit `--check` to regenerate the corresponding files. The index tool
also generates `PaperAxioms.lean`, auditing every cited declaration. The build
covers the shared invariance dependencies; no separate backlog build is needed.
Old `lean-backlog` entry points remain compatibility imports.

A package build and an axiom audit are not a fresh replay of the entire import
closure by the frozen final verifier. That larger replay has not completed in
the capped audit. See the paper's verification appendix for formal scope.
