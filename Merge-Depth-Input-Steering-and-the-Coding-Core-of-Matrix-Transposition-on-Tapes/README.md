# Merge Depth, Input Steering, and the Coding Core of Matrix Transposition on Tapes

**Hans Brende and Claude Opus 5.5 (Anthropic)** — October 2026. **Draft.**

- [PDF](paper/main.pdf) and [LaTeX sources](paper/), licensed under [CC BY 4.0](paper/LICENSE).
- Status: every numbered result has a written proof in the PDF. None has been checked by an independent referee yet.
- Lean: the formalization is in progress and is published result by result in [`lean/`](lean/) (Lean 4, Mathlib,
  built on the libraries of the eighth, ninth, fifth and tenth papers). Formalized so far:
  - Section 3: the cold genie (Lemma 3.1), the covering lemma, Lemmas 3.9 and 3.11, Theorems HC and HC′ (field DAGs of
    prunings for machines oblivious up to their last output step, through the fourth paper's local recursion at the level
    of fields), Lemma 3.3, Lemma 3.14(a) and Proposition 3.16 with the machine's
    read and append steps as hypotheses, Proposition 3.17, Corollary HC at one size, Corollary HC* at one size given
    Lemma 3.14(b), and the merge DAG with Proposition 3.20.
  - Section 4: Lemmas 4.2, 4.5 (the block machine, in the frozen machine model), 4.6, 4.7, the paired-distance group
    (Lemmas 4.8–4.10 and Proposition 4.11, with better constants), Lemma 4.14 and Lemma 4.15 in part (with a small entropy
    library).
  - Section 6: Theorem LA, with the modelling step from a frozen trace; the external-memory model, Theorem EM and
    Corollary EM, whose conclusion is the negation of the frozen statement of (T).
  - Section 7: Definitions 7.1, 7.2, 7.6, Lemma 7.4 and Proposition 7.5; Lemmas 7.7–7.9 and Theorem BP (with Conjecture S
    as its only hypothesis) up to the identification of the Lean model's families, turns and potentials with the walk
    pair; the blindness bound of the eighth paper's Proposition 5.17 is proved on the way.
  - Section 8: Lemma PG.

  The status line of every numbered result in the PDF says what is formal, and its appendix lists the Lean declarations
  cited.

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

