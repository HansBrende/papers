# Bounded-Stack DAGs Reduce to Constant Depth

Hans Brende and Claude Opus 5.5 (Anthropic), November 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It builds on the eighth paper's library, which it requires by relative path,
  so the sibling directories of this repository must be in place. The corollaries also require the eleventh paper's
  library (*Merge Depth, Input Steering, and the Coding Core of Matrix Transposition on Tapes*), for its deep-nesting walk
  and for its traces, dependency DAGs and index codes in the first paper's frozen machine model. [`lean/README.md`](lean/README.md) is a guide to
  its modules.
- [`tools/lean_index.py`](tools/lean_index.py) generates the index of Lean declarations and `lean/PaperAxioms.lean`
  from the paper's LaTeX sources.

## The question

A DAG with a spine on [0, N) has the edges t → t − 1 and further arcs u → p with u ≥ p + 2. It is an s-stack DAG if
its arcs split into s families in which no two arcs cross and each vertex is the left end of at most one arc and the
right end of at most one. Is every family of such DAGs *depth-reducible*: for every ε > 0, is there a D such that
deleting some εN edges always leaves no path with more than D arcs?

For the walk DAGs of k tape heads this is the trajectory cut problem TCP(k) of the series: one of the two hypotheses
through which the fourth paper reduces a lower bound for oblivious linear-time matrix transposition, the other being a
coding bound, the *crux*. The eighth paper proved TCP for walks of bounded nesting load and left SR(3), the case of
three stacks, open; the series expected TCP(2) to fail on the deep-nesting pairs.

## What is proved

Proved in Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound` (the paper states each result
with its Lean declarations and file):

- **Theorem T.** For every k ≥ 1 and ε > 0, the walk DAG of any k walks of length T, with or without pauses, has a
  cut of at most εT edges after which every path carries at most K^P − 1 long hops, where K and P are explicit
  functions of k and ε (log log K^P = O(k² log(k/ε)) for ε ≤ 1/2). Hence TCP(k) holds for every k, and SR(s) holds for every s:
  bounded-stack DAGs with a spine reduce to constant depth.
- **Theorem A (one walk).** The decomposition of a walk into ladders of nested hops, frames and passages; summed over
  the offsets of a random grid of size h₀, at most 6 times the number of hops are lost, for upper and lower hops
  separately.
- **Corollary N, first statement (the deep-nesting pairs).** For every ε > 0, the walk DAG of the deep-nesting pair
  x₁ = U(s₀, m, 1), x₂ = x₁(· + ξ) on [0, T) has a cut of at most εT edges and depth at most D(2, ε), whatever the
  nesting depth m, the shift ξ and the length T: the pairs are not depth-robust.
- **Corollary O (oblivious machines).** In the frozen machine model of the first paper: every trace of every machine,
  up to a horizon T ≤ C(L + 1), has a genie of cost at most εL whose full depth is bounded in terms of k, C, the value
  width and ε, so depth-TCP holds; the crux
  Crux(S_{k,C,β,D}, ρ), for some ρ > ε at that depth, excludes oblivious transposers in time C(L + 1) at all large sizes,
  uniformly over the machines with k work tapes and value width at most β; and the linear crux does the same for machines
  with a linear data path.
- **Corollary HV (code-level depth reduction).** The ball systems of these machines, at the same bounded radius, have
  index codes of at most εL bits, and minrank at most εL for machines with a linear data path: Conjecture HV* of the
  eleventh paper holds in both its forms, so its Problem 9.1 has an affirmative answer.
- **The composition.** The label and Lemma V (along a kept hop the label increases unless the display is truncated,
  the shown set above the hop's group changes, or a digit wraps); displays of suspended frames as a least fixed point
  with random break bits; Lemma D (the size of the display has a tail independent of T and of the depth of the
  stacks); view invariance; the exposure bound; the event budgets and the accounting of all cut edges.

Proved in the paper with a complete written proof, not formalized:

- **Corollary N, second statement.** Conjectures A′ and A″ of the fourth and eighth papers are false (from the first
  statement, through Corollary 5.26 of the eighth paper, a written proof there).

The remarks are labelled as proof sketches, heuristics or numerical observations. They explain why simpler constructions
fail, estimate the crux rate that Corollary O needs, and note that the native half bound (the half bound for codes on the
cone relations of linear-time machines) would give the crux at rate one half, and so, by Corollary O, exclude oblivious
linear-time transposers.

## What is open

- (T) itself. For oblivious machines, what remains is the crux: index codes for the side information of the
  bounded-depth cones of linear-time schedules, or the native half bound for codes on their cone relations.
- The true order of the depth D(k, ε).
- Depth reduction for DAGs with a spine whose arcs form a bounded number of queues.
- Finding the cuts deterministically in near-linear time.

## Building and verifying

The Lean package imports the eighth and eleventh papers' packages and, through them, the earlier packages of the series and the
shared library [`lean-machine`](../lean-machine/), by relative paths. Clone the whole papers repository so that the
sibling directories stay in place. Then fetch the second paper's pinned external dependency as described in its
[README](../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/).
Install [elan](https://github.com/leanprover/elan), then in `lean/`:

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

Regenerate the index of Lean declarations and `PaperAxioms.lean` after editing the paper (from this directory):

```bash
python3 tools/lean_index.py
```

To build the PDF, run `latexmk -pdf main.tex` in `paper/`.
