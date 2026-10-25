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

Finite short-path packing and its exact logarithmic and asymptotic bounds are
formalized from the native transport estimates, whose uniform derivation from
tape semantics remains unformalized. The self-demand count is formalized from native one-edge transport, whose proof
remains unformalized. The finite counting and retained-degree part of paid trimming is formalized; its
native cone-size premise and asymptotic paired-distance application remain written
proofs. Linearization of nonlinear recovery on arbitrary directed block codes and
the resulting dimension bound from actual matrix-label witnesses are also
formalized; constructing the specific expanding family and its witnesses remains
unformalized. The exact finite and asymptotic depth-independent code deficit is
formalized from an actual row-word cover, with the native extraction and its
uniform sublinear exception estimate as the remaining gap. Every cited declaration uses only `propext`, `Classical.choice`, and
`Quot.sound`. Formal status is recorded beside each numbered result; the index and
axiom checks are generated from those annotations. General algebraic and counting
lemmas are shared through `lean-machine`.

The remaining written proofs establish the actual-cone incidence-distance theorem;
a complex linear half-rate bound with fixed block width and bounded coefficients;
and native examples with expansion and connected demands whose full cone relations
still have nonlinear coding gaps. The appendix applies the matrix certificate to
a characteristic-two expanding family. These statements retain all hypotheses
printed in the paper; the examples are not transposition algorithms.

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
