# Merge Depth, Input Steering, and the Coding Core of Matrix Transposition on Tapes

Hans Brende and Claude Opus 5.5 (Anthropic), October 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It builds on the libraries of the eighth, ninth, fifth and tenth papers, which it
  requires by relative paths, so the sibling directories of this repository must be in place.
- [`tools/`](tools/): [`lean_index.py`](tools/lean_index.py) generates the index of Lean declarations and
  `lean/PaperAxioms.lean` from the paper's LaTeX sources.

## The question

Does one deterministic multitape Turing machine transpose every square matrix with dimension `d` and entry width
`b(d) = max(1, ceil(log₂ d))` in time `O(L)`, where `L = d² b(d)`? This is question (T) of the series. By a reduction of
Harvey and van der Hoeven, a linear-time multiplication machine would give such a transposer.

## What is proved

Every numbered result is formalized in Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`; the
paper states each result with its Lean declarations and file, and its appendix lists them. Results marked [Q9.1] assume an
affirmative answer to Question 9.1 of *Directed Recovery Structures in Tape Computations* (storage codes on
paired-distance separated relations of bounded degree have rate at most 1/2 + o(1)); results marked [LinCrux] assume the
linear crux of *Bounded Nesting and Depth Reduction for Matrix Transposition on Tapes*; Theorem BP assumes Conjecture S.
In Lean these are explicit hypotheses (`MergeDepth.Q91`, or its binary form `MergeDepth.Q91Binary`, `MergeDepth.LinCrux`,
`MergeDepth.ConjectureS`). The formalization covers the machine model throughout: oblivious machines and prunings of their
field DAGs, skeleton classes and their block machines, frozen traces, external-memory simulation, and the deep-nesting
walk of the eighth paper.

- **Merge depth replaces schedule depth.** For oblivious machines, Theorem F cuts only the hops at boundedly entered
  cells (the cold genie), and the deep hops at the other cells are charged to checkpoints along the lineages of the code.
  If the code merges deep data lineages at most s times along every path from most outputs, then on every schedule,
  however deeply nested, the transposition matrix of a linear code splits into a low-rank part and a part supported on
  balls of bounded radius (Theorems HC and HC′), and for all codes the side information in such balls has a short index
  code (Theorem HC′(b)). Hence the linear crux excludes such transposers with linear codes (Corollary HC), and [Q9.1]
  excludes them for all codes (Corollary HC*). Routing through deep hops is limited by their number, the number of deep
  cells adds nothing, and a cheap cut of the code's merge structure suffices; what remains for oblivious machines is depth
  reduction of that structure (Conjecture HV*).
- **Skeleton entropy and input steering** [Q9.1]. A form of the eighth paper's Corollary F″ that is robust against
  padding of bounded entry: a linear-time transposer whose work heads enter every cell boundedly often has coarse
  skeleton entropy above (1/2 − η) L at every fixed scale, for every η > 0 at all large sizes (Theorem SE). Consequently
  no linear-time transposer, adaptive or not, has bounded entry on every tape (Corollary RV), and one whose work tapes
  have bounded entry must revisit input cells and carry about L/2 bits of the data in the coarse motion of its input head
  (Corollary IS), a condition that padding meets at no cost.
- **Localization** (Theorem L) [Q9.1]. Every linear-time transposer revisits some tape unboundedly often; an oblivious
  one revisits a work tape and merges deep lineages unboundedly often, for every pruning, cold genie and lineage
  assignment; one whose work tapes have bounded entry revisits input cells and carries about L/2 bits in the coarse
  motion of its input head.
- **Unconditional reductions.** A machine that has, for a small enough η, a trace of probability at least 2^{−ηL}
  falling under the uniform exclusions of *Source Covers and Barriers to Tape Transposition* is not a linear-time
  transposer (Theorem LA); the passage from a machine to that paper's admissible geometries is formal. At block scale,
  every linear-time transposer, adaptive or not, yields an external-memory transposition with O(d) I/Os that is oblivious
  on 2^{L−O(d)} inputs (Theorem EM); so an indivisibility-free external-memory lower bound for this oblivious, large-set
  form of transposition, even at a single dimension for each choice of constants, would refute (T) (Corollary EM).
- **Deep nesting** [Conjecture S]. The eighth paper's Conjecture A″ for pairs of block labels of bounded length on the
  deep-nesting pair at one odd shift, with no log q term and no cost hypothesis (Theorem BP), assuming Conjecture S: the
  straddle counts of most coarse classes concentrate as the shift varies. Partial results on Conjecture S: an exact
  Fourier form of the normalized variances, classes on which they stay large, and a reduction of the conjecture to the
  average of their non-local part.
- **A ruled-out building block** for constructions: in a projective plane of order q, a separated set of points, each
  recovered from one line through it, has at most max(4q, q^{3/2}+1) points (Lemma PG); so Tanner codes assembled from
  projective planes, with every coordinate recovered from one line, violate the paired-distance condition for every q ≥ 7.

Remarks labelled as proof sketches, heuristics or numerical observations are not used in any proof.

## What is open

(T) itself; Conjecture HV* (code-level depth reduction); adaptive machines that revisit some tape unboundedly often; an
indivisibility-free external-memory bound for transposition; Question 9.1 at large degree; Conjecture S. See the
open-problems section of the paper.

## Building and verifying

The Lean package requires the packages of the eighth, ninth, fifth and tenth papers by relative paths, and through them
those of the earlier papers and the shared library [`lean-machine`](../lean-machine/). Clone the whole papers repository
so that the sibling directories stay in place, and fetch the second paper's pinned external dependency as described in
its [README](../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/). Install
[elan](https://github.com/leanprover/elan), then in `lean/`:

```bash
lake exe cache get
```

```bash
lake build
```

Check the axioms of every declaration cited in the paper (generated from the paper's LaTeX sources):

```bash
lake env lean PaperAxioms.lean
```

Every declaration should report at most the axioms `propext`, `Classical.choice` and `Quot.sound`. After editing the paper,
regenerate the index of Lean declarations and `lean/PaperAxioms.lean` (from this directory):

```bash
python3 tools/lean_index.py
```

To build the PDF, run `latexmk -pdf -interaction=nonstopmode main.tex` in `paper/`.
