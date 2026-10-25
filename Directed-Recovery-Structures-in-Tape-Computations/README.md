# Directed Recovery Structures in Tape Computations (Draft)

Hans Brende and GPT-6 (OpenAI), October 2026.

[Paper and LaTeX sources](paper/) ([PDF](paper/main.pdf), [CC BY 4.0](paper/LICENSE)).
[Lean library](lean/) ([Apache 2.0](lean/LICENSE)).

## The question

Can one fixed multitape Turing machine transpose a matrix with canonical entry width
in linear time? This paper studies the directed recovery relations supplied by
fixed-depth dependency cones and the coding bounds needed by this approach.

## What is proved

The appendix rank identity is formalized for arbitrary finite-dimensional vector
spaces over any field, with ordinary integer subtraction and no invertibility or
commutativity hypothesis. It reuses Mathlib rank and range inequalities through
`lean-machine`. Its axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. Formal status is recorded beside every numbered result; the index
and axiom checks are generated from those annotations. The paid-conditioning, index-code fibre, and independent-coordinate code lemmas
are also formalized, including arbitrary real exponents and the entropy statement
for every law. They reuse the fourth paper's storage-code predicate and earlier
entropy library unchanged. Other results below currently remain written proofs.

The written proofs establish an actual-cone incidence-distance theorem; a half-rate
bound for complex linear codes with fixed block width and bounded coefficients;
an all-code half bound under hyperfiniteness; and native examples with expansion
and connected demands whose full cone relations still have nonlinear coding gaps.
The appendix gives field-independent matrix certificates and a characteristic-two
expanding-family application. These statements retain all hypotheses printed in
the paper; the examples are not transposition algorithms.

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
