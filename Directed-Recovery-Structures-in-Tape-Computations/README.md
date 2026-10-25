# Directed Recovery Structures in Tape Computations (Draft)

Hans Brende and GPT-6 (OpenAI), October 2026.

[Paper and LaTeX sources](paper/) ([PDF](paper/main.pdf), [CC BY 4.0](paper/LICENSE)).
[Lean library](lean/) ([Apache 2.0](lean/LICENSE)).

## The question

Can one fixed multitape Turing machine transpose a matrix with canonical entry width
in linear time? This paper studies the directed recovery relations supplied by
fixed-depth dependency cones and the coding bounds needed by this approach.

## What is proved

The following results are formalized in Lean:

- Paid conditioning, index-code fibres, and independent-coordinate cardinality
  and entropy bounds, using the earlier papers' storage-code and entropy libraries.
- The finite independent-rectangle lemma, including coordinate and row deletions
  and consecutive buckets.
- Full threshold pullback through signed partial monotone row words, including
  exact exceptional-row and occupied-bucket bounds.
- Port-color and separated-component half bounds, the finite separator theorem,
  and the hyperfinite half-rate corollary with varying alphabets.
- The surviving-pair bound for damaged expanders, including arbitrary edge and
  vertex deletions across multiple copies.
- The arbitrary-field rank identity and full matrix-label certificate, including
  labels over field extensions and independent code and witness block widths.

Six results are partially formalized:

- **Paired distances and self-demands:** finite path counting and the logarithmic
  asymptotic bound are verified; native transport and its uniform constants remain
  written proofs.
- **Paid degree trimming:** finite counting and retained-degree bounds are
  verified; the native cone premise and paired-distance application remain.
- **Depth-independent code deficit:** the exact finite and asymptotic bounds are
  verified from an actual row-word cover. Native extraction and its uniform
  sublinear exception estimate remain.
- **Linear codes on the expanding family:** linearization of nonlinear recovery
  and the dimension bound from actual matrix labels are verified. Construction
  of the specific family and its witnesses remains.
- **Necessary torsion:** the exact modular rank-loss count and finite rank/nullity
  implication are verified from a supplied unimodular diagonalization. Smith-form
  existence, the analytic estimate, and the cokernel interpretation remain.

In total, 12 new numbered results are fully formalized, 6 are partially
formalized, and 18 retain written proofs; 2 additional numbered results are cited
from earlier papers. Every cited Lean declaration uses only `propext`,
`Classical.choice`, and `Quot.sound`. Status appears beside each numbered result;
the index and axiom checks are generated from those annotations. General
algebraic and counting lemmas are shared through `lean-machine`.

The remaining arguments include the native transport and construction machinery,
the complex linear half-rate theorem, and the characteristic-two expanding-family
construction. All statements retain the hypotheses printed in the paper; the
native examples are not transposition algorithms.

## What is open

The general finite-alphabet paired-distance coding question, unrestricted cheap
depth reduction, and an all-input treatment of adaptivity remain open. No
unrestricted transposition time lower bound is claimed.

## Building and verifying

Clone the entire repository: the Lean library requires the sibling `lean-machine`
package and the fourth paper's library (with its earlier-paper dependencies). Lean and Mathlib are pinned to v4.34.1. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

From this paper directory regenerate the declaration index and axiom checks:

```sh
python3 tools/lean_index.py
```

From `paper/`, compile the manuscript:

```sh
latexmk -pdf main.tex
```

Local `.lake/packages` caches may be shared only at the pinned revisions; they are
ignored and are not needed in the source distribution. No new axiom or proof
placeholder is permitted. Build instructions and the status of written proofs are
also recorded in the verification appendix.
