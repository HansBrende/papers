# Bounded-Stack DAGs Reduce to Constant Depth

Hans Brende and Claude Opus 5.5 (Anthropic), November 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It builds on the eighth paper's library, which it requires by relative path,
  so the sibling directories of this repository must be in place. [`lean/README.md`](lean/README.md) is a guide to
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
- **The composition.** The label and Lemma V (along a kept hop the label increases unless the display is truncated,
  the shown set above the hop's group changes, or a digit wraps); displays of suspended frames as a least fixed point
  with random break bits; Lemma D (the size of the display has a tail independent of T and of the depth of the
  stacks); view invariance; the exposure bound; the event budgets and the accounting of all cut edges.

Proved in the paper with complete written proofs, not formalized:

- **Corollary N.** The deep-nesting pairs are cut to a depth independent of their nesting depth, so Conjectures A′
  and A″ of the fourth and eighth papers are false (through Corollary 5.26 of the eighth paper, a written proof there).
- **Corollary O.** Every oblivious machine with k work tapes running in linear time has genies of cost εL and bounded
  full depth; so the crux alone excludes oblivious linear-time transposers, and so would the native half bound for
  codes on the cone relations of linear-time machines (through Theorem D of the fourth paper and Lemma 2.6 and
  Theorem D_lin of the eighth paper, written proofs there).

The remarks that explain why simpler constructions fail are labelled as proof sketches or numerical observations.

## What is open

- (T) itself. For oblivious machines, what remains is the crux: index codes for the side information of the
  bounded-depth cones of linear-time schedules, or the native half bound for codes on their cone relations.
- The true order of the depth D(k, ε).
- Depth reduction for DAGs with a spine whose arcs form a bounded number of queues.
- Finding the cuts deterministically in near-linear time.

## Building and verifying

The Lean package imports the eighth paper's package and, through it, the earlier packages of the series and the
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
