# Merge Depth, Input Steering, and the Coding Core of Matrix Transposition on Tapes

**Hans Brende and Claude Opus 5.5 (Anthropic)** — October 2026. **Draft.**

- [PDF](paper/main.pdf) and [LaTeX sources](paper/), licensed under [CC BY 4.0](paper/LICENSE).
- Status: every numbered result has a written proof in the PDF. None has been checked by an independent referee yet.
- Lean: every numbered result is formalized in [`lean/`](lean/) (Lean 4, Mathlib, built on the libraries of the eighth,
  ninth, fifth and tenth papers), on the standard axioms. Results that assume an affirmative answer to Question 9.1 of
  the fifth paper, the linear crux of the eighth paper, or Conjecture S take them as explicit hypotheses
  (`MergeDepth.Q91`, `MergeDepth.LinCrux`, `MergeDepth.ConjectureS`). The formalization covers the machine model
  throughout: oblivious machines and prunings of their field DAGs, skeleton classes and their block machines, frozen
  traces, external-memory simulation, and the deep-nesting walk of the eighth paper. Formalizing also gave several
  statements stronger than first written, now in the PDF, and closed a few gaps in the written proofs. The status line of
  every numbered result in the PDF names its declarations, and the appendix lists them.

## The question

Does one deterministic multitape Turing machine transpose every square matrix with dimension `d` and entry width
`b(d) = max(1, ceil(log₂ d))` in time `O(L)`, where `L = d² b(d)`? This is question (T) of the series.

## What the draft proves

Results marked [Q9.1] assume an affirmative answer to Question 9.1 of *Directed Recovery Structures in Tape
Computations* (the half bound for codes on paired-distance separated relations of bounded degree); results marked
[LinCrux] assume the linear crux of *Bounded Nesting and Depth Reduction*.

- **Merge depth replaces schedule depth.** For oblivious machines whose code merges deep data lineages only boundedly
  often along each path, a rank decomposition (Theorems HC and HC′) shows that the transposition matrix splits into a
  low-rank part and a part supported on balls of bounded radius, on every schedule, however deeply nested. Hence such
  transposers do not exist [LinCrux] (Corollary HC), and for all codes [Q9.1] (Corollary HC*). Deep routing is
  hop-limited, capacity is not the operative resource, and the remaining oblivious question is depth reduction of the
  code's merge structure (Conjecture HV*).
- **Skeleton entropy and input steering.** A form of the eighth paper's low-adaptivity corollary that is robust
  against padding of bounded entry: a bounded-entry transposer must have coarse skeleton entropy at least about `L/2` at
  every fixed scale [Q9.1] (Theorem SE). Consequently no linear-time transposer, adaptive or not, has bounded entry on
  every tape (Corollary RV), and one whose work tapes have bounded entry must revisit input cells and carry about `L/2`
  bits of the data in the coarse motion of its input head (Corollary IS), a condition that padding meets at no cost.
- **Localization** (Theorem L). Given [Q9.1], every linear-time transposer revisits some tape unboundedly often; an
  oblivious one revisits a work tape and merges deep lineages unboundedly often, and one whose work tapes have bounded
  entry revisits input cells.
- **Unconditional reductions.** Low adaptivity collapses to the oblivious exclusions of *Source Covers and Barriers to
  Tape Transposition* (Theorem LA). At block scale, every linear-time transposer, adaptive or not, yields an
  external-memory transposition with linearly many I/Os that is oblivious on `2^{L−O(d)}` inputs (Theorem EM), so an
  external-memory lower bound without the indivisibility assumption would refute (T).
- **Deep nesting.** The eighth paper's Conjecture A″ for pairs of block labels of bounded length on the deep-nesting
  pair at one odd shift, conditional on Conjecture S, that the straddle counts of most coarse classes concentrate as the
  shift varies (Theorem BP), with partial results on Conjecture S.
- **A ruled-out building block** for constructions: in a projective plane of order `q`, a set of points each
  recovered from one line through it, with the paired-distance separation that the crux setting requires, has at most
  `max(4q, q^{3/2}+1)` points (Lemma PG); so Tanner codes assembled from projective planes violate the paired-distance
  condition for every `q ≥ 7`.

## What is open

Conjecture HV* (code-level depth reduction); adaptive machines that revisit some tape unboundedly often; an
indivisibility-free external-memory bound for transposition; Question 9.1 at large degree; Conjecture S.

## Building

From `paper/`:

```sh
latexmk -pdf -interaction=nonstopmode main.tex
```

To check the Lean formalization, from `lean/`, with the libraries of the eighth, ninth, fifth and tenth papers built and
their dependencies linked into `.lake/packages` (see the eighth paper's README):

```sh
lake build
lake env lean PaperAxioms.lean
```

Every declaration should report at most the axioms `propext`, `Classical.choice` and `Quot.sound`.

